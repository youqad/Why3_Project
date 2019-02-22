---
title: "Why3: Computational Real Numbers"
author: [Younesse Kaddar]
date: "2019-13-02"
subject: "Markdown"
keywords: [Why3, Computational-Reals, Project, MPRI]
subtitle: "MPRI Project Report"
titlepage: true
titlepage-color: "356aa0"
titlepage-text-color: "efefef"
titlepage-rule-color: "efefef"
titlepage-rule-height: 1
logo: "logo-why3.pdf"
logo-width: 1020
lang: "en"
fontsize: "11pt"
colorlinks: true
listings-disable-line-numbers: true
header-includes:
  - \usepackage{listings}
  - \lstset{basicstyle=\ttfamily}
  - \newcommand{\CodeEmphasis}[1]{\textcolor{red}{\textit{#1}}}
  - \newcommand{\CodeEmphasisLine}[1]{\textcolor{red}{\textit{#1}}}
---

<!-- pandoc report.md -o report.md.pdf --template eisvogel-min --pdf-engine=lualatex --listings --filter pandoc-emphasize-code -->


<!-- SKIM: pandoc %file -o %file.pdf --template eisvogel-min --pdf-engine=lualatex --listings --filter pandoc-emphasize-code -->

<!-- ```{.haskell emphasize=2:3-2:14,3:3-3:12}
myFunc = do
  newStuffHere
  andThisToo notThis
  notSoRelevant
``` -->

$$
\newcommand{\B}{\mathop{\tt \_B}\nolimits}
$$

Throughout this project, I installed and used the following solvers:

Solver|Version
-|-
Alt-Ergo|$2.2.0$
CVC4|$1.6$
Z3|$4.8.4$
CVC3|$2.4.1$
Eprover|$2.2$
Spass|$3.7$

Most of the assertions were proved with Alt-Ergo and CVC4 (less often with Z3, and even more rarely with CVC3, Eprover and Spass). As a macOS user, the installation of Z3 was problematic (its "counterexample" counterpart was the only one to be recognized by the Why3 IDE), so much so that I had choice but to modify my `.why3.conf` file by explicitely adding a block enforcing the use of Z3:

```sh
[prover]
command = "z3 -smt2 -T:%t sat.random_seed=42 nlsat.randomize=false smt.random_seed=42 %f"
command_steps = "z3 -smt2 sat.random_seed=42 nlsat.randomize=false smt.random_seed=42 memory_max_alloc_count=%S %f"
driver = "z3_440"
editor = ""
in_place = false
interactive = false
name = "Z3"
shortcut = "z3"
version = "4.8.4"
```

# 2. Functions on Integers

### Q1, 2, 3, 4. Give an implementation of
#### `power2`, `shift_left` using `power2`

- `power2` and `shift_left` are straightforward: the only notable point is the `for` loop invariant in `power2`:

    ```{.caml emphasize=2:19-2:49}
    let res = ref 1 in
    for i=0 to l-1 do invariant { !res = power 2 i }
      res *= 2
    done;
    !res
    ```

    which expresses the fact that the reference variable `res` stores the suitable power of $2$ at each iteration, and trivially ensures that the postcondition holds:

    - at the last iteration:
        - `!res` contains $2^{l-1}$ at the beginning of the body loop
        - its value is then doubled, which results in `!res` being equal to $2^l$
    - one exits the loop, and `!res` yielded at the end, whence satisfying the postcondition `result = power 2 l` of `power2`

#### `ediv_mod`, and `shift_right` using `ediv_mod`.

- given `ediv_mod` and `power2`, `shift_right` is easily defined as `let d, _ = ediv_mod z (power2 l) in d` and poses no difficulty.
- `ediv_mod` is slightly more tricky, but nothing to be afraid of: `d` and `r` are respectively the quotient and the rest of the well-known euclidean division of `x` by `y > 0`.

    1. we first tackle the case where $x = \overbrace{\vert x \vert}^{\text{denoted by } \texttt{x\_abs}} ≥ 0$: as it happens,

        ```{.caml emphasize=5-6}
        let x_abs = if x >= 0 then x else -x in
        let d = ref 0 in
        let r = ref x_abs in
        while !r >= y do
          invariant { !r >= 0 && x_abs = !d * y + !r}
          variant { !r }
          incr d;
          r -= y
        done;
        ```

        - the invariant $r ≥ 0 \quad ∧ \quad \texttt{x\_abs} = d y + r$ is initially true, and remains so at each iteration of the loop as $d$ (resp. $r$) is incremented (resp. decremented) by $1$ (resp. $y$).
        - the `while` loop condition $r ≥ y$ and the fact that $y > 0$ (precondition requirement of `ediv_mod`) justify the decreasing and well-founded variant `!r`
        - at the end the `while` loop:

            - $0 ≤ r < y$
            - $\texttt{x\_abs} = d y + r$

            which provides a trivially correct implementation of the euclidean division, provided $x ≥ 0$
    2. otherwise, if $x < 0$, we reduce this to the previous case, by computing the corresponding $\texttt{d\_abs}$ and $\texttt{r\_abs}$ for $\texttt{x\_abs} = \vert x \vert = -x$

        - if $\texttt{r\_abs} = 0$: then $\texttt{x\_abs} = \texttt{d\_abs} × y$, and $x = (- \texttt{d\_abs}) × y$.

            One yields $d \; ≝ \; - \texttt{d\_abs}, \quad r \; ≝ \; 0$. This is easily discharged by CVC4 (we can even go as far as to add the extra assertion `assert { x = - !d * y }` to help the provers, but it shouldn't be necessary).

        - else if $\texttt{r\_abs} > 0$: then

            $$
            \begin{cases}
              0 ≤ y - \texttt{r\_abs} < y \\
              x = -\texttt{x\_abs} = -\texttt{d\_abs} \, y - \texttt{r\_abs} = (-\texttt{d\_abs} - 1) \, y + (y - \texttt{r\_abs})
            \end{cases}
            $$

            Therefore, one yields $d \; ≝ \; - \texttt{d\_abs} - 1,\quad r \; ≝ \; y - \texttt{r\_abs}$.

            This is discharged by CVC4 too, but we can add the assertion `assert { x =  (- !d - 1) * y + y - !r && 0 <= y - !r < y }` to convince the provers.


### Q5. Give an implementation of `isqrt`

When it comes to the sheer body of the function, as seen in class:

```ml
let function isqrt (n:int) : int
  requires { 0 <= n }
  ensures { result = floor (sqrt (from_int n)) }
  =
    let count = ref 0 in
    let sum = ref 1 in
    while !sum <= n do
      incr count;
      sum += 2 * !count + 1
    done;
    !count
```

However, proving the postcondition `result = floor (sqrt (from_int n))` turns out to be trickier than [the one we saw in class](http://francois.bobot.eu/mpri2018/imp_isqrt_sol.mlw) (i.e. `sqr !count <= !n < sqr (!count + 1)`), in so far as all the specification pertaining to `floor` in [the standard library](http://why3.lri.fr/stdlib/real.html) is:

```ml
  function floor real : int

  axiom Floor_int :
    forall i:int. floor (from_int i) = i

  axiom Floor_down:
    forall x:real. from_int (floor x) <= x < from_int (Int.(+) (floor x) 1)

  axiom Floor_monotonic:
    forall x y:real. x <= y -> Int.(<=) (floor x) (floor y)
```

That is, the standard-library properties related to $\lfloor \bullet \rfloor$ on which the provers can rely are:

- $\lfloor \bullet \rfloor$ is increasing and left inverse of `from_int`
- and more importantly: $$∀ n ∈ ℤ, n = \lfloor x \rfloor \; ⟹ \; n ≤ x < n + 1 \qquad ⊛$$

On top of that, `sqrt` is only [assumed to be increasing](http://why3.lri.fr/stdlib/real.html#Square_), and not strictly increasing.

As a result, we:

- *neither* have the converse of $⊛$ (which is exactly the direction needed to prove the postcondition!)
- *nor* do we have the fact that $\sqrt{\bullet}$ is strictly increasing (which is problematic when dealing with strict inequalities).

So, which assertions where added to prove `isqrt`?

- concerning the `while` loop: nothing special, we proceed exactly as seen in class, apart from the extra variant: `variant {n - !sum}` which is easily seen to be strictly decreasing and well-founded.

- at the end of the loop:

    $$
    0 ≤ \texttt{count} \qquad \text{ and } \qquad
    \texttt{count}^2 ≤ n < \texttt{sum} = (\texttt{count} + 1)^2
    $$

    therefore, due to $\sqrt \bullet$ being strictly increasing and $\texttt{count} ≥ 0$:

    $$
    \texttt{count} ≤ \sqrt n < \texttt{count} + 1\\
    $$

    and the converse of $⊛$ would yield the expected postcondition.

    But to convince the provers, based solely on the standard-library specification, we proceed as follows:

    - we first show that $\texttt{count} ≤ \lfloor {\sqrt n} \rfloor$, which only resorts to $\lfloor \bullet \rfloor$ and $\sqrt \bullet$ being increasing and $\sqrt \bullet$ being a left inverse of $\bullet^2$ on $ℝ^+$ (axiom `Square_sqrt` of the [standard library](http://why3.lri.fr/stdlib/real.html#Square_)).
    - we then show the reverse inequality, that is: $\lfloor {\sqrt n} \rfloor < \texttt{count} + 1$ in a similar fashion. Except that this one is a bit trickier, as $\sqrt \bullet$ is not assumed to be strictly increasing, but we can get away with it by treating strict inequalities as being equivalent to non-strict ones *and* non-equalities.



# 3. Difficulty with Non-linear Arithmetic on Real Numbers

## 3.1 Power Function

### Prove that

- $\B$ is positive
- $\B n × \B m = \B (n+m)$
- $\B n × \B (-n) = 1$
- $0 ≤ a \quad ⟹ \quad \sqrt {a × \B {2n}} = \sqrt a × \B n$
- $0 ≤ y \quad ⟹ \quad \B y = \texttt{from_int } 4^y$
- $y < 0 \quad ⟹ \quad \B y = \frac 1 {\texttt{from_int } 4^{-y}}$
- $0 ≤ y \quad ⟹ \quad 2^{2y} = 4^y$




# 4. Computational Real Numbers

### 13. Could you find a reason why this definition is better than the other for automatic provers?

### 14. Prove these three functions

## 4.2 Subtraction

### 15. Define and prove the function `compute_neg`
### 16. Define `compute_sub` using `compute_neg` and `compute_add`

## 4.3 Conversion of Integer Constants

## 4.4 Square Root

### 17. Prove these two relations

### 18. Prove `compute_sqrt`

## 4.5 Compute

### 19. define a logic function `interp` that gives real interpretation of a term with the usual semantic for each operation

### 20. define `wf_term` that checks that square root is applied only to terms with non negative interpretation.

### 21. define and prove the `compute` function

# 5 Division

### 22. Prove these two properties

### 23. Prove the function `inv_simple_simple`

### 24. Prove the function `inv_simple`

### 25. extend the type `term`

### 26. prove both functions

### 27. prove the termination of the functions
