# Third-party code

Code copied or adapted from the repositories below, with imports, namespaces and proofs
adjusted as needed.

- [`QiuzhenCFSG/`](QiuzhenCFSG): [Qiuzhen-CFSG/CFSG](https://github.com/Qiuzhen-CFSG/CFSG/tree/96b2a02085dc678f3e0a97b334c31ada599c55fd),
  by Tianjiao Nie and contributors. Bender–Suzuki, Gorenstein–Walter and supporting results.
  Four unused upstream statements whose proofs were `sorry` are removed, with the one theorem
  that used one of them; each changed file says so in its module docstring.
- [`BrauerInduction/`](BrauerInduction): [norbsvr/BrauerInduction](https://github.com/norbsvr/BrauerInduction/tree/a88cd7566a7c3b5d93d791a9320b9e7fa75a001a),
  by Norbert Voelker. Brauer's induction theorem for characters.
- [`OddOrder/`](OddOrder): [yawara/odd-order](https://github.com/yawara/odd-order/tree/7a412eae81e9510a684fd8c180cf1fbd47b8d00d),
  by Yawara Ishida. Results from Chapter 8 of Isaacs, *Finite Group Theory*.
- [`TauCeti/`](TauCeti): [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti).
  Algebraic groups, Hopf algebras and comodules.
- [`Mathlib/`](Mathlib): [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4).
  Group scheme smoothness and averaging idempotents.

Qiuzhen CFSG, BrauerInduction and OddOrder target older Lean versions, so we use ported
copies here rather than adding those upstream revisions directly to the lakefile.
The TauCeti copies backport results missing from our pinned revision and adapt private
helpers. The Mathlib copies expose a private smoothness lemma and adapt averaging results
to use field inverses.

All upstream sources use Apache-2.0; each folder includes its upstream license.

Qiuzhen CFSG includes a proof of Feit–Thompson, but we use our own entirely self-contained
[Feit–Thompson proof](../FeitThompson).
