module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront13

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def R133 (D : Data G) : Prop :=
  D.sig = D.sig1 → F13.Hyp131 D →
    ∀ L ∈ calC D.M, ∀ K ∈ calC D.M, ∀ n : ℕ, (IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) →
      ∀ s : ℕ, Odd s → s ∣ n → ∀ r : ℕ, r.Prime → r ∣ 2 ^ s - 1 →
        ∀ X : Subgroup G, X ≤ L → Nat.card X = r →
          ∀ g : G, g ∉ D.M → X.map (MulAut.conj g).toMonoidHom ≤ D.M →
            (X.map (MulAut.conj g).toMonoidHom ≤ K ⊔ F13.cMStar D.M K ∨
              ((IsL2 (Bar2 K) r ∨ IsSz (Bar2 K) r) ∧ Even n)) ∧
            ¬ ∃ m : ℕ, IsU3 (Bar2 K) m

@[expose] def ThinList13 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsKGroup X → CFSG.Open.IsQuasisimple X →
    CFSG.pCore 2 X = ⊥ → (∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r X ≤ 1) →
      IsSimpleGroup X ∧
        ((∃ a : ℕ, IsL2 X a) ∨ (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsL2Odd X p) ∨
          (∃ a : ℕ, IsSz X a) ∨ IsJ1 X)

@[expose] def SigmaRankThree13 (D : Data G) : Prop :=
  (∃ p ∈ D.sig, CFSG.Open.pRank p D.M = 3) →
    ∀ r : ℕ, r.Prime → 7 ≤ r → 3 ≤ CFSG.Open.pRank r D.M → r ∈ D.sig

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
