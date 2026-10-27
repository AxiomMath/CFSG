module

public import CFSG.Quasithin.EmptyFaithful.S14612DC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

section Defs

variable {G : Type} [Group G]

@[expose] def Stage14614E9C2 (T H : Subgroup G) : Prop :=
  conjClosure (oTwoUpper H) (mcOf T) ∈ cComp (mcOf T) ∧
    Nonempty (OTwoQuot (conjClosure (oTwoUpper H) (mcOf T)) ≃*
      Matrix.symplecticGroup (Fin 2) (GaloisField 2 2)) ∧
    mcOf T = conjClosure (oTwoUpper H) (mcOf T) ⊔ T

@[expose] def Stage14614E9C3 (T H : Subgroup G) : Prop :=
  ∃ (K₁ : Subgroup G) (s : G), K₁ ∈ cComp (mcOf T) ∧ s ∈ T ∧
    s ∉ Subgroup.normalizer (K₁ : Set G) ∧
    conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁ ∧
    Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) ∧
    mcOf T = conjClosure (oTwoUpper H) (mcOf T) ⊔ T

@[expose] def Stage14614E9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p → IsE9Z4Shape T H p →
      Stage14614C1 T H p ∨ Stage14614E9C2 T H ∨ Stage14614E9C3 T H

@[expose] def Input14614ListsE9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p → IsE9Z4Shape T H p →
      conjClosure (oTwoUpper H) (mcOf T) ≠ oTwoUpper H →
        ∃ K₁ : Subgroup G, K₁ ∈ cComp (mcOf T) ∧
          ((∃ s : G, s ∈ T ∧ s ∉ Subgroup.normalizer (K₁ : Set G) ∧
              conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁ ∧
              ((∃ m : ℕ, 2 ≤ m ∧ 3 ∣ 2 ^ m - 1 ∧
                  Nonempty (OTwoQuot K₁ ≃*
                    Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m))) ∨
                Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))) ∨
            (conjClosure (oTwoUpper H) (mcOf T) = K₁ ∧
              ((∃ n : ℕ, 2 ≤ n ∧ Even n ∧
                  Nonempty (OTwoQuot K₁ ≃* Matrix.symplecticGroup (Fin 2) (GaloisField 2 n))) ∨
                ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
                  Nonempty (OTwoQuot (K₁ ⊔ T) ≃*
                    MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))))))

end Defs

section Local

variable {X : Type} [Group X]

structure E9Local (L Th Hh Eh R : Subgroup X) : Prop where
  normal_L : L.Normal
  sylow_T : IsSylowTwoOf Th ⊤
  T_le : Th ≤ Hh
  solv_H : Group.IsSolvable ↥Hh
  E_le_L : Eh ≤ L
  E_le_H : Eh ≤ Hh
  card_E : Nat.card Eh = 9
  exp_E : ∀ e ∈ Eh, e ^ 3 = 1
  comm_E : ∀ a ∈ Eh, ∀ b ∈ Eh, a * b = b * a
  dec : ∀ h ∈ Hh, ∃ e ∈ Eh, ∃ t ∈ Th, h = e * t
  R_le_T : R ≤ Th
  R_norm : Hh ≤ Subgroup.normalizer (R : Set X)
  R_max : ∀ A : Subgroup X, IsPGroup 2 ↥A → Hh ≤ Subgroup.normalizer (A : Set X) → A ≤ R
  quot4 : ∃ φ : ↥Th →* Multiplicative (ZMod 4), Function.Surjective φ ∧
    ∀ x : ↥Th, φ x = 1 ↔ (x : X) ∈ R

end Local

section Crit

structure BinCrit (L : Type) [Group L] : Prop where
  card_sylow : ∀ U : Subgroup L, IsSylowTwoOf U ⊤ → ∃ k : ℕ, Nat.card U = 4 ^ k
  gen_invol : ∀ U : Subgroup L, IsSylowTwoOf U ⊤ →
    Subgroup.closure {x : L | x ∈ U ∧ x * x = 1} = U
  no_invol : ∀ E : Subgroup L, Nat.card E = 9 → (∀ e ∈ E, e ^ 3 = 1) →
    (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      ∀ z : L, z * z = 1 → (∀ e ∈ E, z * e = e * z) → z = 1
  no_normalizer : ∀ U : Subgroup L, IsSylowTwoOf U ⊤ →
    ∀ x : L, x ∈ Subgroup.normalizer (U : Set L) → x ^ 3 = 1 → x = 1

end Crit

end CFSG.Quasithin
