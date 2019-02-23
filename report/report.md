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
  - \newcommand{\B}{\mathop{\texttt{\_B}}\nolimits}
  - \newcommand{\fint}{\mathop{\texttt{from\_int }}\nolimits}
  - \newcommand{\para}{\,\mathbin{\!/\mkern-5mu/\!}\,}
  - \newcommand{\sincr}{\mathop{\texttt{\_sqrt\_incr}}\nolimits}

---

<!-- pandoc report.md -o report.md.pdf --template eisvogel-min --pdf-engine=lualatex --listings --filter pandoc-emphasize-code -->


<!-- SKIM: pandoc %file -o %file.pdf --template eisvogel-min --pdf-engine=lualatex --listings --filter pandoc-emphasize-code -->

<!-- ```{.haskell emphasize=2:3-2:14,3:3-3:12}
myFunc = do
  newStuffHere
  andThisToo notThis
  notSoRelevant
``` -->


Throughout this project, I installed and used the following solvers:

Solver|Version
-|-
Alt-Ergo|$2.2.0$
CVC4|$1.6$
Z3|$4.8.4$
CVC3|$2.4.1$
Eprover|$2.2$
Spass|$3.7$

Most of the assertions were proved with Alt-Ergo and CVC4 (less often with Z3, and even more rarely with CVC3, Eprover and Spass). As a macOS user, the installation of Z3 was problematic (its "counterexample" counterpart was the only one to be recognized by the Why3 IDE), so much so that I had choice but to modify my `.why3.conf` file by explicitly adding a block enforcing the use of Z3:

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

### Q1-4. Give an implementation of
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

### Q6-12. Prove that

1. $\B$ is positive
2. $\B n × \B m = \B (n+m)$
3. $\B n × \B (-n) = 1$
4. $0 ≤ a \quad ⟹ \quad \sqrt {a × \B (2n)} = \sqrt a × \B n$
5. $0 ≤ y \quad ⟹ \quad \B y = \fint 4^y$
6. $y < 0 \quad ⟹ \quad \B y = \frac 1 {\fint 4^{-y}}$
7. $0 ≤ y \quad ⟹ \quad 2^{2y} = 4^y$

All theses lemmas but the 5th and the 6th ones are straightforwardly discharged:

- for the 5th one (`_B_spec_pos`): we lend a hand to the provers with the command `assert (pow (from_int 4) (from_int n) = from_int (power 4 n))`:

    ![Why3 IDE: use of the `assert` command to prove `_B_spec_pos`](screenshot_command.png)

- for the 6th one (`_B_spec_neg`), we first prove an easily discharged (by Alt-Ergo) lemma:

    ```caml
    lemma _B_spec_neg_0:  
      forall n:int. n < 0 -> _B n *. from_int (power 4 (-n)) = 1.
    ```

    from which `_B_spec_neg` immediately ensues.


# 4. Computational Real Numbers

### Q13. Could you find a reason why this definition is better than the other for automatic provers?

- When it comes to using to two inequalities rather the terser (and perhaps more elegant)

    $$\vert x - p \, 4^{-n} \vert < 4^{-n}$$

    the two-inequalities version has the advantage of not involving the absolute value `abs`, which would just be a burden when proving framing-related postconditions. Indeed, almost every time we would want to show a non-trivial framing (first needing to unfold `abs`), provers would eventually have to resort to [the `Abs_le` lemma of the standard library](http://why3.lri.fr/stdlib/real.html#Abs_), leading to unnecessary proof clutter.

- As for using `_B`: this fosters the use of the relevant lemmas proved in section **3.6** by the provers, bringing about more efficient proofs.


### Q14. Prove these three functions

#### `round_z_over_4`

By dint of assertions, we show the two postconditions inequalities separately:

- $$\fint (\underbrace{\texttt{shift\_right } \, (z + 2) \, 2}_{= \, (z+2) \para 2^2}) ≤ (\fint z + 2) × \B (-1)$$ where $\para$ stands for the euclidean division quotient, which directly stems from $$4 ((z+2) \para 2^2) ≤ z+2 \qquad \text{(euclidean division)}$$

- Similarly (the $\fint$'s will be omitted from now on): $$z - 2 < 4 × \underbrace{\texttt{shift\_right } \, (z + 2) \, 2}_{= \, (z+2) \para 2^2}$$ due to $$z - 2 < z + 2 - (\underbrace{(z+2) \mod 2^2}_{< 4}) = 4 ((z+2) \para 2^2)$$

#### `compute_round` and `compute_add`

- For `compute_round`, assuming

    $$(z_p - 2) × \B (-(n+1)) < z ≤ (z_p + 2) × \B (-(n+1))$$

    we show that

    $$
    (\underbrace{\texttt{shift\_right } \, (z_p + 2) \, 2}_{= \, (z_p+2) \para 2^2} - 1) × \B (-n) < z < ((z_p+2) \para 2^2 + 1) × \B (-n)
    $$

    by means of two assertions (one for each inequality). Indeed:

    \begin{align*}
        ((z_p+2) \para 2^2 - 1) × \B (-n)  & ≤ \Big(\underbrace{\frac {z_p+2} 4 - 1}_{= \frac {z_p} 4 - \frac 1 2}\Big) × \B (-n) && \text{ since } 4 ((z_p+2) \para 2^2) ≤ z_p + 2  \\
        & = \frac {z_p-2} 4 × \B (-n) \\
        & = (z_p-2) × \B (-(n+1)) \\
        & < z \\
        & ≤ \frac {z_p + 2} 4 × \B (-n) \\
        & = \Big(\frac {z_p - 2} 4 + 1\Big) × \B (-n) \\
        & < \big((z_p+2) \para 2^2 + 1\big) × \B (-n) && \text{ since } z_p - 2 <  4 ((z_p+2) \para 2^2) \text{ as seen before}\\
    \end{align*}

- Given `compute_round`'s contract, `compute_add n x xp y yp` is straightforwardly defined as `compute_round n (x +. y) (xp + yp)`

## 4.2 Subtraction

### Q15-16. Define and prove the functions `compute_neg`, `compute_sub` using `compute_neg` and `compute_add`

Those pose no difficulty:

- `compute_neg n x xp` is nothing more than `-xp`, as demonstrated by multiplying the framing of `x` by $-1$
- `compute_sub n x xp y yp` compute_adds `x` and the compute_neg'ed approximation of `y`, owing to `x` and `y` being provided at approximation $n+1$. A little help for the provers: asserting `assert { framing (-.y) yp' (n+1) }` just before yielding the result.


## 4.3 Conversion of Integer Constants

`compute_cst` is easy on paper, but is a bit thornier in Why3: we show the relevant inequalities in each case

- if $n < 0$:

    - $(x \para 2^{-2n} - 1) × \B (-n) < x$ stems from $(x \para 2^{-2n}) × \B (-n) ≤ x$ (by definition of the euclidean division) and $\B (-n) > 0$
    - $x < (x \para 2^{-2n} + 1) × \B (-n)$ comes from $x$ being equal to $(x \para 2^{-2n}) × \B (-n) + \underbrace{(x \mod \B (-n))}_{< \B (-n)}$

- if $n ≥ 0$:

    - $(x × 2^{2n} - 1) × \B (-n) = \underbrace{x × 2^{2n} × \B (-n)}_{= \, x} - \underbrace{\B (-n)}_{> 0} < x$

    - $x < x + \underbrace{\B (-n)}_{> 0} = x × 2^{2n} × \B (-n) + \B (-n) = (x × 2^{-2n} + 1) × \B (-n)$

## 4.4 Square Root

### Q17. Prove these two relations

It can be noted that, for all $n ∈ ℕ$:

\begin{gather*}
(\sqrt {n+1} - \sqrt n)(\sqrt {n+1} + \sqrt n) = (n+1) - n = 1\\
\text{so that } \quad \sqrt {n+1} =  \sqrt n + \underbrace{\frac 1 {\sqrt {n+1} + \sqrt n}}_{\text{denoted by } \sincr n} \\
\text{where } \quad 0 < \sincr n ≤ 1
\end{gather*}

Based on this observation, we show two  lemma functions

```caml
let lemma _sqrt_incr_spec (n:int) : unit
  requires { n >= 0 }
  ensures { sqrt (from_int (n+1)) = sqrt (from_int n) +. _sqrt_incr n }
  =
  (* [...] *); ()

let lemma _sqrt_incr_bounds (n:int) : unit
  requires { n >= 0 }
  ensures { 0. <. _sqrt_incr n <=. 1. }
  =
  (* [...] *); ()
```

that will come in handy in what follows.

#### Relation 1 (`sqrt_ceil_floor` lemma): $\lceil \sqrt {n+1} \rceil - 1 ≤ \lfloor \sqrt n \rfloor$

The outline of the proof on paper is:

\begin{align*}
    \lceil \sqrt {n + 1} \rceil - 1  & < \lceil \sqrt {n + 1} \rceil \\
    & = \lceil \sqrt n + \sincr n \rceil && \text{ as } \sqrt {n + 1} = \sqrt n + \sincr n\\
    & ≤ \lceil \underbrace{(\lfloor \sqrt n \rfloor + 1) + 1}_{∈ \, ℤ} \rceil &&\text{ since } \begin{cases}
      \sqrt n ≤ \lfloor \sqrt n \rfloor + 1 \\
      \sincr n ≤ 1
    \end{cases} \text{ and } \lceil \bullet \rceil \text{ is increasing}\\
    & = \underbrace{\lfloor \sqrt n \rfloor + 1}_{\text{denoted by } a} + 1
\end{align*}

But we have actually more than that: $\lceil \sqrt {n + 1} \rceil$ is *strictly lower* than $a + 1$.

Indeed: if, by contradiction, we had $\lceil \sqrt {n + 1} \rceil = a+1$, given that:

$$\sqrt n < \lfloor \sqrt n \rfloor + 1 = a = \lceil \sqrt {n + 1} \rceil - 1 < \sqrt {n+1}$$

it would come that $n < a^2 < n+1$, which is absurd, since $a^2$ is an integer. So $$\lceil \sqrt {n + 1} \rceil - 1  <  \lceil \sqrt {n + 1} \rceil < a + 1 = \lfloor \sqrt n \rfloor + 2$$

and as all these are integers, the result follows.

The reasoning by contradiction is carried out in Why3 in this way:

```caml
if ceil x = a+1 then (
    assert {  n-1 < a*a < n
           by (* [...] *) };
    absurd);
(* [...] *)
```

#### Relation 2 (`sqrt_floor_floor` lemma): $\lfloor \sqrt n \rfloor ≤ \lfloor \sqrt {n-1} \rfloor + 1$

We proceed analogously, everything is similar:

\begin{align*}
    \lfloor \sqrt n \rfloor & = \lfloor \sqrt {n-1}  + \sincr n \rfloor\\
    & ≤ \lfloor (\lfloor \sqrt {n-1} \rfloor + 1) + 1 \rfloor \\
    & = \underbrace{\lfloor \sqrt {n-1} \rfloor + 1}_{\text{denoted by } a} + 1
\end{align*}

and $\lfloor \sqrt n \rfloor = a + 1$ is impossible, as otherwise $\sqrt {n-1} < \lfloor \sqrt {n-1} \rfloor + 1 = a = \lfloor \sqrt n \rfloor - 1 < \sqrt n$, which would imply $n-1 < a^2 < n$.

### Q18. Prove `compute_sqrt`

Assuming that

$$x ≥ 0 \quad \text{ and } \quad (x_p - 1) × \B (-2n) < x < (x_p + 1) × \B (-2n)$$

we show that

```caml
let compute_sqrt (n: int) (ghost x : real) (xp : int)
  = if xp <= 0 then 0 else isqrt xp
```

ensures that the $\texttt{result}$ is an $n$-framing of $\sqrt x$.

- if $x_p ≤ 0$, then: $$\quad-\B (-n) < 0 ≤ \sqrt x < \sqrt {\smash{\underbrace{(x_p + 1)}_{= 1}} × \B (-2n)} =  \B (-n)$$

- if $x_p > 0$:

    \begin{gather*}
    \sqrt x < \sqrt {x_p + 1} × \B (-n) ≤ \left\lceil \sqrt {x_p + 1} \, \right\rceil × \B (-n) \overset{\text{\tiny Relation 1}}{ ≤ } \left(\left\lfloor \sqrt {x_p} \right\rfloor + 1\right) × \B (-n)\\
    \sqrt x > \sqrt {x_p - 1} × \B (-n) ≥ \left\lfloor \sqrt {x_p - 1} \, \right\rfloor × \B (-n) \overset{\text{\tiny Relation 2}}{ ≥ } \left(\vphantom{\left\lfloor \sqrt {x_p} \right\rfloor}\smash{\underbrace{\left\lfloor \sqrt {x_p} \right\rfloor}_{= \, \texttt{isqrt } x_p}} - 1\right) × \B (-n)
    \end{gather*}

In Why3, we use the same trick as in `isqrt` to get around the fact that `sqrt` is not strictly increasing, by turning some strict inequalities into conjunctions of non-strict ones and non-equalities.

## 4.5 Compute

### Q19-20. Define: `interp` that gives real interpretation of a term, and `wf_term` that checks that square root is adequately applied.

- `interp` is recursively defined in a forthright manner
- `wf_term` is defined as an inductive predicate. For the time being, the only non-trivial constructor case (that actually does check something, rather than inductively propagating) is `wf_sqrt: forall t:term. interp t >=. 0. -> wf_term t -> wf_term (Sqrt t)`, ensuring that `Sqrt` is exclusively applied to terms whose interpretation is non-negative.


### Q21. define and prove the `compute` function

The first batch of the `compute` function is the following one:

```{.caml emphasize=4-4}
let rec compute (t:term) (n:int) : int
  requires { wf_term t }
  ensures { framing (interp t) result n }
  variant { t }
  =
  match t with
    | Cst x -> compute_cst n x
    | Add t' t'' ->
        let xp = compute t' (n+1) in
        let yp = compute t'' (n+1) in
          compute_add n (interp t') xp (interp t'') yp  
    | Neg t' -> compute_neg n (interp t') (compute t' n)
    | Sub t' t'' ->
        let xp = compute t' (n+1) in
        let yp = compute t'' (n+1) in
          compute_sub n (interp t') xp (interp t'') yp  
    | Sqrt t' -> compute_sqrt n (interp t') (compute t' (2*n))
  end
```

It is defined by structural induction over the term `t`, which makes the `variant` trivially correct, and as all the contracts of the auxiliary `compute_***` functions were specially written to ensure the correction of this final `compute`, CVC4 discharges the proof obligations with no trouble.

# 5 Division

### Q22. Prove these two properties

**Notations**: in what follows, we will denote by $d$ (resp. $d'$, resp. $d''$) and $r$ (resp. $r'$, resp. $r''$) the quotient and the rest of the euclidean division of $a$ by $b$ (resp. $b-1$, resp. $b+1$). In other words:

\begin{align*}
    a &= db + r  && 0 ≤ r < b\\
    a &= d'(b-1) + r' && 0 ≤ r' < b-1\\
    a &= d''(b+1) + r'' && 0 ≤ r'' < b+1\\
\end{align*}


#### Property 1 (`dividend_incr`)

$$\begin{cases}
  0 < a  \\
  0 < b \\
  d \; ≝ \; a \para b < b\\
\end{cases} \quad ⟹ \quad d'' \; ≝ \; a \para (b+1) =
\begin{cases}
  d - 1 &\text{ if } r \; ≝ \; a \mod b < d \qquad \textbf{(P1.1)}\\
  d &\text{ else } \qquad \textbf{(P1.2)}\\
\end{cases}
$$

Assume $a, b > 0$ and $d \; ≝ \; a \para b < b$.

- if $r \; ≝ \; a \mod b < d$:

    Let us show that $d'' \; ≝ \; a \para (b+1) = d-1$.

    To do so, based on the lemma function suggested in the problem statement at the end of section 2 (which is easily proved by CVC4):

    ```caml
    let lemma euclid_uniq (x y q : int) : unit
      requires { y > 0 }
      requires { q * y <= x < q * y + y }
      ensures { ED.div x y = q }
      = ()
    ```

    it suffices to show that

    $$(d-1)(b+1) ≤ a < d(b+1)$$

    And indeed

    - $(d-1)(b+1) = db + d - b - 1 ≤ db + r = a$ since $d ≤ b - 1 ≤ b + r + 1$
    - $a = db + r < db + b = d(b+1)$ as $r < b$

- if $r ≥ d$:

    Let us show that $d'' = d$. Similarly:

    $$d(b+1) ≤ a < (d+1)(b+1)$$

    in so far as

    - $d(b+1) = db + d ≤ db + r = a$
    - $a = db + r < db + d + b + 1 = (d+1)(b+1)$ since $r < b$

#### Property 2 (`dividend_decr`)

$$\begin{cases}
  0 < a  \\
  1 < b \\
  d \; ≝ \; a \para b < b - 1
\end{cases} \quad ⟹ \quad d' \; ≝ \; a \para (b-1) =
\begin{cases}
  d + 1 &\text{ if } b-1-d < r \; ≝ \; a \mod b \qquad \textbf{(P2.1)}\\
  d &\text{ else } \qquad \textbf{(P2.2)}
\end{cases}
$$

Assume $a > 0, b > 1$ and $d \; ≝ \; a \para b < b - 1$.

- if $b - 1 - d ≤ r \; ≝ \; a \mod b$:

    Let us show that $d' \; ≝ \; a \para (b-1) = d + 1$. Indeed:

    $$(d+1)(b-1) ≤ a < (d+2)(b-1)$$

    because

    - $(d+1)(b-1) = db + b - 1 - d ≤ db + r = a$ due to the hypothesis
    - $a = db + r < db - d + 2b - 2 = (d+2)(b-1)$ since $r < b + \underbrace{b - d - 2}_{≥ 0}$

- if $b - 1 - d > r$:

    Let us show that $d' = d$. Similarly:

    $$d(b-1) ≤ a < (d+1)(b-1)$$

    owing to the fact that

    - $d(b-1) = db - d ≤ db + r = a$ as $0 < a = db + r < (d+1) \overbrace{b}^{> 0}$ hence $d ≥ 0$, and $-d ≤ 0 ≤ r$
    - $a = db + r < db - d + b - 1 = (d+1)(b-1)$ because of the hypothesis

The two lemma functions `dividend_incr` and `dividend_decr` closely follow the proof sketches above in the Why3 implementation.

### Q23. Prove the function `inv_simple_simple`

We first prove two routine lemmas (`inv_decreasing`: the fact that `inv` is decreasing over $ℝ^\ast_+$ and `_B_inv`: $∀ n, \, \B n = \frac 1 {\B (-n)}$) that are subsequently used in `inv_simple_simple`.

```caml
let inv_simple_simple (ghost x:real) (p:int) (n:int)
    requires { framing x p (n+1) }
    requires { 0 ≤n }
    requires { 1. ≤. x }
    ensures { framing (inv x) result n }
    =
    let k = n + 1 in
    let d,r = ediv_mod (power2 (2*(n+k))) p in
    if 2*r ≤p then d
    else d+1
```

As far as I am concerned, `inv_simple_simple` was the most nettlesome function, and maybe the most confusing one too at first glance, for the following reason: as pointed out in the problem statement, we can (and we will) prove that

$$d = a \para b ≤ b − 1 − a \para b$$

which ensures that the conditions **P1.1** and **P2.1** cannot happen at the same time, that is: $\textbf{P1.1} ⟹ \textbf{P2.2}$ and $\textbf{P2.1} ⟹ \textbf{P1.2}$. From there, it is tempting to try to show (in each branch of `inv_simple_simple`'s `if` statement) one the first conditions of one property (**P1.1** or **P2.1**), since, as it happens, the second condition of the other property is obtained for free. But that's a misleading track! We will instead focus on the second conditions of one property (i.e. either **P1.2** or **P2.2**), disregarding the other property altogether (by just settling with the *coarsest upper/lower bound* we get from both of its conditions).


Let's delve into it in more details. Similarly to before, we set

\begin{gather*}
(d, r) = (4^{n+k} \para p, 4^{n+k} \mod p)\\
(d', r') = (4^{n+k} \para (p-1), 4^{n+k} \mod (p-1))\\
(d'', r'') = (4^{n+k} \para (p+1), 4^{n+k} \mod (p+1))
\end{gather*}

- Before entering the `if` statement: we prove a handful of useful assertions

    - $4 ≤ 4^k ≤ p$ and $4^n ≤ \frac p 4$

        since $1 ≤ x < (p + 1) 4^{-k}$, so $4^k < p + 1$, whence $4^k ≤ p$. On top of that: $k = n + 1$ (thus $4^n ≤ \frac p 4$) and $k ≥ 1$ (hence $p ≥ 4$).

    - then, as we have the precondition `framing x p (n+1)` (i.e. `framing x p k`):

        $$\frac {4^k} {p+1} < \frac 1 x <  \frac {4^k} {p-1}$$

        therefore

        $$d'' ≤ \frac {\overbrace{4^{n+k}}^{(p+1)d'' + r''}} {p+1} < \frac {4^n} x <  \frac {\overbrace{4^{n+k}}^{(p-1)d' + r'}} {p-1} ≤ d' + 1$$

    - $d ≤ \frac {p-1} 2$. Indeed:

        \begin{align*}
                & d = \frac{4^{n+k} - r}{p} ≤ \frac {p-1} 2\\
        ⟺ \quad & 4^{n+k} - r ≤ \frac {p(p-1)} 2\\
        ⟸ \quad & 4^{n+k} ≤ \frac {p(p-1)} 2\\
        ⟸ \quad & \frac {p^2} 4 ≤ \frac {p(p-1)} 2\\
        ⟸ \quad & \frac p 2 ≤ p-1\\
        ⟸ \quad &2 ≤ p && \text{ which is true as } p ≥ 4\\
        \end{align*}
    - last but not least (before entering the `if`): the *coarsest bounds* we hinted at earlier:

        - due to **P2**: $d' ≤ d + 1$
        - due to **P1**: $d - 1 ≤ d''$

- Inside the `if` statement:

    - **if $2r ≤ p$:**

        - Let us show that $\boxed{r+1 ≤ p-1-d}$:

            \begin{align*}
            & r + d + 1 < p\\
            ⟺ \quad & rp + \underbrace{dp}_{= \, 4^{n+k} - r \, ≤ \, \frac {p^2} 4 - r} + p < p^2\\
            ⟸ \quad & \underbrace{r}_{≤ \frac{p}{2}}(p-1) + \frac {p^2} 4 + p < p^2\\
            ⟸ \quad & 2p(p-1) + p^2 + 4 p < 4 p^2\\
            ⟺ \quad & 0 < p^2 - 2p = p(p-2) && \text{ which is true as } p ≥ 4\\
            \end{align*}
        - Thus, by **P2.2**, $d' = d$. And consequently:

            $$d - 1 \overset{\text{\tiny coarse bound}}{≤} d'' < \frac {4^n} x < d' + 1 = d + 1$$

    - **if $2r > p$:**

        - It comes that $\boxed{r ≥ d}$, since $2r ≥ p + 1 ≥ p - 1 ≥ 2d$
        - Thus, by **P1.2**, $d'' = d$. And consequently:

            $$(d + 1) - 1 = d'' < \frac {4^n} x < d' + 1 \overset{\text{\tiny coarse bound}}{≤} (d + 1) + 1$$

### Q24. Prove the function `inv_simple`

`inv_simple` take advantage of the fact that $1 ≤ x × \B m$ to resort to `inv_simple_simple`. We are given a $(n+1+2m)$-framing of $x$:

\begin{gather*}
(p-1) \B (-(n+1+2m)) < x < (p+1) \B (-(n+1+2m))\\
\text{hence } (p-1) \B (-(n+1+m)) < x × \B m < (p+1) \B (-(n+1+m))\\
\end{gather*}

and as $1 ≤ x × \B m$, `res = inv_simple_simple (x *. _B m) p (n+m)` provides a $(n+m)$-framing of $x × \B m$:

\begin{gather*}
(\texttt{res}-1) \B (-(n+m)) < x × \B m < (\texttt{res}+1) \B (-(n+m))\\
\text{thus } (\texttt{res}-1) \B (-n) < \underbrace{x × \B m × \B (-m)}_{= \, x} < (\texttt{res}+1) \B (-n)\\
\end{gather*}

and the result follows.

### Q25. extend the type `term`

We add

- the `| Inv t' -> inv (interp t')` case in `interp`
- the `| wf_inv: forall t:term. interp t <> 0. -> wf_term t -> wf_term (Inv t)` case in `wf_term`

### Q26-27. prove the correction and termination of both functions

- When it comes to the correction:

    nothing really fancier than before: the only new case is `Inv t'`, and `msd` (which is called only there in `compute`) yields an `m` such that $\vert \texttt{interp } t \vert > \B (-m)$ (such an `m` always exists provided $\texttt{interp } t ≠ 0$, which is what we assume).

    `msd` recursively calls itself until $\vert c \vert ≥ 2$ (where $c$ is the integer approximating $t$), thus straightforwardly ensuring the correction of the algorithm.

    In `compute`, the case where the sign is negative is easily treated, similarly to `compute_neg`, by taking the opposite.

- The termination is a bit more involved because of `msd`:

    - when `compute t n` is called:

        - either `t` is structurally smaller
        - either `t` remains the same and `compute` has been called inside `msd`

        which hints at the fact that an adequate variant would follow a lexicographic order, with the size of `t` as first component (where `size` is defined as expected).

    - `msd` stops recursively calling itself as soon as $\vert c \vert > 1$.

        - if $\texttt{interp } t > 0$:

            then if $4^n (\texttt{interp } t) > 2$, i.e. $n > \log_4 {\frac 2 {\texttt{interp } t}} = \log_4 {\frac 2 {\vert \texttt{interp } t \vert} }$, it follows that $c > 4^n (\texttt{interp } t) - 1 > 1$

        - if $\texttt{interp } t < 0$:

            then if $4^n (\texttt{interp } t) < -2$, i.e. $n > \log_4 {\frac {-2} {\texttt{interp } t}} = \log_4 {\frac 2 {\vert \texttt{interp } t \vert} }$, it follows that $c < 4^n (\texttt{interp } t) + 1 < -1$

        and each time `msd` is recursively called, $n$ is incremented (and it is originally set at $0$).

    So a good variant is $(\texttt{size } t, \left\lceil \log_4 {\frac 2 {\vert \texttt{interp } t \vert}} \right\rceil - n)$ for the lexicographic order, which we can routinely check in Why3 by asserting what was outlined before and adding axiom about the `log` being increasing as suggested at the beginning of the problem statement.

## Bonus

Here is a counter-example: with

- $x \; ≝ \; -0.6161$
- $n=2$

It comes that $\texttt{msd } (x) = 1$ with $x_0 = 0, x_1 = -2, …, x_5 = -630$.

Let's run the proposed algorithm on this instance to compute, say, $\overline{1/x_n}$.

- $n > - \texttt{msd } (x) = -1$
- as $k = n + 2 \texttt{msd } (x) + 1 = 5$ and $x_5 = -630 ≤ 1$: it comes that

    $$\overline{1/x_2} = \left\lfloor \frac{\B (k+n)}{x_k}\right\rfloor = -27$$

However:

$$(\overline{1/x_n} + 1) × \B (-n) = \frac {-27 + 1} {16} = -1.625 < \frac 1 x ≃ - 1.623$$

so the framing is not correct.


# Conclusion

I didn't find this project particularly easy (especially as I am not keen on real numbers computation usually), but it definitely was a good foray into Why3. The most difficult part was `inv_simple_simple`, due to the fact that I got bogged down in a misleading track (as explained before) by misinterpreting a cue in the problem statement.

With some of my friends, I have jotted down a handful of suggestions about axioms that I think could be good adjuncts to the standard library, and a few features that may enhance the user experience of the Why3 IDE. I will enclose them in a forthcoming email.
