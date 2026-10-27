module

public import CFSG.Quasithin.EmptyFaithful.S146F7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

section Three

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDec12.isInvU_of_mem (S : Setting146 G T M) (h5 : Stage1461Five) (h16 : Stage14616)
    {PQ : Subgroup G} (hred : IsRedCE T M H PQ p) (hmax : PMaximal T M p)
    (h : IsDec12 T M H p H₀ H₁ H₂ t) (iMod : Input14617Mod) (hF : oTwoUpper H ≤ oTwoFstarIn (mcOf T))
    {u : G} (hu : u ∈ uHi T M H H₁ ∨ u ∈ uHi T M H H₂) (huZ : u ∉ quasithinOmegaOneCenter T)
    (huT : T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ tZero T u) : IsInvU T M H u := by
  rcases hu with hu | hu
  · exact h.isInvU_of_fixed S h5 h16 hred hmax (iMod G T M S H PQ p hred H₀ H₁ H₂ t h) hF hu huZ huT
  · have huT' : T ⊓ Subgroup.normalizer (H₂ : Set G) ≤ tZero T u := by
      rw [h.inf_normalizer_eq_swap hred.isHTM.1.1]
      exact huT
    exact h.swap.isInvU_of_fixed S h5 h16 hred hmax
      (iMod G T M S H PQ p hred H₀ H₂ H₁ t⁻¹ h.swap) hF hu huZ huT'

end Three

@[expose] def Input14617Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDec12 T M H p H₀ H₁ H₂ t →
        (Case13One T M H p H₁ ∨ Case13One T M H p H₂) →
          ∀ u : G, u ∈ uK T M H → (u ∈ uHi T M H H₁ ∨ u ∈ uHi T M H H₂) →
            u ∉ quasithinOmegaOneCenter T →
            T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ tZero T u → IsInvU T M H u →
              IsI T M u (Subgroup.centralizer ({u} : Set G))

@[expose] def Input14617Five : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p → p = 3 → IsOFourPlusOn T M H →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDec12 T M H p H₀ H₁ H₂ t →
        Nat.card (conjClosure (VZ T M) (oTwoUpper H₂)) = 2 ^ 4

end CFSG.Quasithin
