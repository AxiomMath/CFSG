module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P1Dat
public import CFSG.Quasithin.EmptyFaithful.S14612DC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

section Final

variable {G : Type} [Group G] [Finite G]

@[expose] def FinalData146E9 (T M : Subgroup G) : Prop :=
  ∃ (H : Subgroup G) (u : G) (H₂ : Subgroup G),
    IsHTM T M H ∧ IsInvU T M H u ∧ IsI T M u (Subgroup.centralizer ({u} : Set G)) ∧
    2 ^ 11 < Nat.card T ∧
    4 ≤ mIdx (conjClosure (VZ T M) H) (Subgroup.centralizer (pCoreOf 2 H : Set G)) ∧
    tZero T u ≤ H₂ ∧
    H₂ ≤ centralizerMod (quasithinOmegaOneCenter T) H (Subgroup.zpowers u) ∧
    Nonempty (OTwoQuot H₂ ≃* Equiv.Perm (Fin 3)) ∧ ¬ H₂ ≤ M ∧
    Nat.card (conjClosure (VZ T M) (oTwoUpper H₂)) = 2 ^ 4

end Final

@[expose] def E9Fstar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p → IsE9Z4Shape T H p →
      oTwoUpper H ≤ oTwoFstarIn (mcOf T)

@[expose] def E9Normalizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p → IsE9Z4Shape T H p →
      ∀ (R₁ R₂ : Subgroup G) (s : G), IsE9Dat T M H PQ R₁ R₂ s →
        Subgroup.normalizer ((T ⊓ Subgroup.normalizer (R₁ : Set G) : Subgroup G) : Set G) ⊓
          mcOf T = T

end CFSG.Quasithin
