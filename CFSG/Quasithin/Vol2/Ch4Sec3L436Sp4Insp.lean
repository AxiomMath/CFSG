module

public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.A3Structure316

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.Quasithin

@[expose] def InspFF436 : Prop :=
  ∀ (U : Type) [CommGroup U] [Finite U], (∀ u : U, u ^ 2 = 1) →
    ∀ (L K A : Subgroup (MulAut U)) (n p : ℕ), 2 ≤ n → CFSG.IsQuasisimple ↥L →
      B56QuasisimpleList ↥L → K ≤ L → IsPSL 2 2 n ↥K →
      A ≤ K → A ≠ ⊥ → IsElemAbelian2 A → Nat.card ↥A ≤ 2 ^ n →
      Nat.card U ≤ Nat.card ↥A * Nat.card ↥(fixV A) →
      p.Prime → p ≠ 2 → p ∣ 2 ^ n - 1 →
      (CFSG.Open.pRank p L ≤ 1 ∨
        (p = 3 ∧ ∃ (S : Type) (_ : Group S) (φ : ↥L →* S), Function.Surjective φ ∧
          (∀ x ∈ φ.ker, ¬ 3 ∣ orderOf x) ∧
          ∃ (s : Bool) (q : ℕ), Int.ModEq 3 (q : ℤ) (if s then 1 else -1) ∧
            IsPSLEps3q s q S)) →
      L = K

end CFSG.Quasithin.H13.Ch4
