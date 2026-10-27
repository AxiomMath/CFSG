module

public import Certificates.Data.L34QEight
public import Certificates.Data.Kernel.FootePk
public import Certificates.Data.Kernel.Census.CatFacts.PkWord

public section

namespace CFSG.Certificates.Kernel.L34QEightK

open CFSG.Certificates.Kernel.PkEnum CFSG.Certificates.Kernel.FootePk
open CFSG.GH74.KGroups.L34 Certificates.Data.L34QEight CFSG.KS.PK

@[expose] def prodV (w : List (VP 21)) : VP 21 := w.foldr mulV (oneV 21)

@[expose] def gV : List (VP 21) := [pa, pb].map codeV

@[expose] def n0aV : VP 21 :=
  prodV (codesW gV [1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2])

@[expose] def n0bV : VP 21 := prodV (codesW gV [1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2])

@[expose] def q1V : VP 21 := mulV n0aV n0bV

@[expose] def q2V : VP 21 := mulV (mulV n0bV n0aV) n0aV

@[expose] def qV : List (VP 21) :=
  [oneV 21, q1V, powV q1V 2, powV q1V 3, q2V, mulV q1V q2V, mulV (powV q1V 2) q2V,
    mulV (powV q1V 3) q2V]

@[expose] def fdS (x i : Nat) : Nat := (x >>> (5 * i)) &&& 31

@[expose] def mulN (s t : Nat) : Nat :=
  let g := fun i => fdS s (fdS t i)
  0 + g 0 * 2 ^ (5 * 0) + g 1 * 2 ^ (5 * 1) + g 2 * 2 ^ (5 * 2) + g 3 * 2 ^ (5 * 3) +
    g 4 * 2 ^ (5 * 4) + g 5 * 2 ^ (5 * 5) + g 6 * 2 ^ (5 * 6) + g 7 * 2 ^ (5 * 7) +
    g 8 * 2 ^ (5 * 8) + g 9 * 2 ^ (5 * 9) + g 10 * 2 ^ (5 * 10) + g 11 * 2 ^ (5 * 11) +
    g 12 * 2 ^ (5 * 12) + g 13 * 2 ^ (5 * 13) + g 14 * 2 ^ (5 * 14) + g 15 * 2 ^ (5 * 15) +
    g 16 * 2 ^ (5 * 16) + g 17 * 2 ^ (5 * 17) + g 18 * 2 ^ (5 * 18) + g 19 * 2 ^ (5 * 19) +
    g 20 * 2 ^ (5 * 20)

@[expose] def oneN : Nat := enc 5 (fun i => i) 21

@[expose] def cjK (qs : List (Nat × Nat)) (x xi k : Nat) (κ : Nat → Nat → Nat → Bool) : Bool :=
  if k = 0 then κ oneN oneN oneN else
    forceD (qs.getD ((k - 1) / 2) (oneN, oneN)).1 fun p _ =>
      forceD (qs.getD ((k - 1) / 2) (oneN, oneN)).2 fun pi _ =>
        κ p (if (k - 1) % 2 = 0 then x else xi) pi

@[expose] def ap3 (p₁ p₂ p₃ j : Nat) : Nat := fdS p₁ (fdS p₂ (fdS p₃ j))

@[expose] def yN (x a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ i : Nat) : Nat :=
  fdS x (ap3 a₁ a₂ a₃ (ap3 b₁ b₂ b₃ (ap3 c₁ c₂ c₃ i)))

@[expose] def tripN (qs : List (Nat × Nat)) (x xi : Nat) (t : Nat × Nat × Nat) : Bool :=
  cjK qs x xi t.1 fun a₁ a₂ a₃ => cjK qs x xi t.2.1 fun b₁ b₂ b₃ =>
    cjK qs x xi t.2.2 fun c₁ c₂ c₃ =>
      (List.range 21).all (fun i => yN x a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃
        (yN x a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ (yN x a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ i)) == i) &&
      !(List.range 21).all fun i => yN x a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ i == i

@[expose] def coverT : List (Nat × Nat × Nat) :=
  [(6, 4, 6), (9, 1, 13), (11, 1, 15), (4, 7, 6), (14, 9, 6), (16, 11, 6), (6, 6, 1), (14, 7, 6),
    (6, 3, 14), (4, 7, 16), (12, 3, 8), (5, 0, 16), (16, 5, 0), (0, 5, 10), (10, 0, 5),
    (15, 14, 12), (11, 14, 11), (16, 7, 16), (15, 3, 12)]

@[expose] def p5N (x i : Nat) : Nat := fdS x (fdS x (fdS x (fdS x (fdS x i))))

@[expose] def p7N (x i : Nat) : Nat := fdS x (fdS x (p5N x i))

@[expose] def testN (qs : List (Nat × Nat)) (x xi : Nat) : Bool :=
  forceD x fun x _ => forceD xi fun xi _ =>
    x == oneN || (!(List.range 21).all (fun i => p5N x i == i) &&
      !(List.range 21).all fun i => p7N x i == i) || coverT.any (tripN qs x xi)

@[expose] def stepN (a : VP 21) (r : Nat) : Nat := forceD r fun r _ => mulN a.1.1 r

@[expose] def prodN (w : List (VP 21)) : Nat := w.foldr stepN oneN

@[expose] def closureBlock (j : Nat) : Bool :=
  forceL qV fun qv => forceLL (transL QP21) fun T =>
    (blockW T j).all fun w => testN (qv.map fun q => (q.1.1, q.1.2)) (prodN w) (prodN (invW w))

@[expose] def ch642001b (j : Nat) : Bool := closureBlock j

@[expose] def qClosedV : Bool :=
  forceL qV fun qs =>
    (List.range qs.length).all (fun i => (List.range qs.length).all fun j =>
      i == j || !eqV (qs.getD i (oneV 21)) (qs.getD j (oneV 21))) &&
    (qs.all fun a => qs.all fun b => qs.any fun d => eqV (mulV a b) d) &&
    qs.all fun a => qs.any fun d => eqV (invV a) d

end CFSG.Certificates.Kernel.L34QEightK

end
