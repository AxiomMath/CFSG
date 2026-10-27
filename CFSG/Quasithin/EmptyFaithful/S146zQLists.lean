module

public import CFSG.Quasithin.EmptyFaithful.S146A0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

@[expose] def Input14614Lists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      conjClosure (oTwoUpper H) (mcOf T) ≠ oTwoUpper H →
        ∃ K₁ : Subgroup G, K₁ ∈ cComp (mcOf T) ∧
          ((∃ s : G, s ∈ T ∧ s ∉ Subgroup.normalizer (K₁ : Set G) ∧
              conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁ ∧
              ((∃ m : ℕ, 2 ≤ m ∧ p ∣ 2 ^ m - 1 ∧
                  Nonempty (OTwoQuot K₁ ≃*
                    Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m))) ∨
                (p = 3 ∧ Nonempty (OTwoQuot K₁ ≃*
                  Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))))) ∨
            (p = 3 ∧ conjClosure (oTwoUpper H) (mcOf T) = K₁ ∧
              ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
                Nonempty (OTwoQuot (K₁ ⊔ T) ≃*
                  MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)))))

@[expose] def Input14614NoSz : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      ∀ J ∈ cComp (mcOf T), ∀ n : ℕ, 1 ≤ n → ¬ Nonempty (OTwoQuot J ≃* ↥(Sz n))

end CFSG.Quasithin
