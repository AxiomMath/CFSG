module

public import CFSG.Quasithin.EmptyFaithful.S14610Q0
public import CFSG.Quasithin.EmptyFaithful.T1531InspBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1

variable {G : Type} [Group G] [Finite G]

theorem oTwoUpper_eq_sup_of_isGoldschmidtTripleIn {I I₁ I₂ : Subgroup G}
    (hT : F6.IsGoldschmidtTripleIn I I₁ I₂) : oTwoUpper I = oTwoUpper I₁ ⊔ oTwoUpper I₂ := by
  have h := F6.twoResidual_top_eq hT.subgroupOf
  have h₁ : I₁ ≤ I := hT.1 ▸ le_sup_left
  have h₂ : I₂ ≤ I := hT.1 ▸ le_sup_right
  rw [F6.twoResidual_eq_oTwoUpper, F6.twoResidual_eq_oTwoUpper, F6.twoResidual_eq_oTwoUpper] at h
  have e : oTwoUpper (⊤ : Subgroup ↥I) = (oTwoUpper I).subgroupOf I := by
    rw [← Subgroup.subgroupOf_self I]
    exact oTwoUpper_subgroupOf (le_refl I)
  rw [e, oTwoUpper_subgroupOf h₁, oTwoUpper_subgroupOf h₂] at h
  have h' := congrArg (Subgroup.map I.subtype) h
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (oTwoUpper_le I),
    Subgroup.map_subgroupOf_eq_of_le ((oTwoUpper_le I₁).trans h₁),
    Subgroup.map_subgroupOf_eq_of_le ((oTwoUpper_le I₂).trans h₂)] at h'
  exact h'

structure Concl14610Core (I K : Subgroup G) : Prop where
  shape : (IsPSL 3 2 1 (OTwoQuot K) ∧ True) ∨
    (IsBlock2 I K ∧
      ((IsHatA6Block K ∧ True) ∨ (IsG2Block K ∧ True) ∨
       (IsAlt 6 (OTwoQuot K) ∧ True ∧
         (Nat.card (wOf1469 K) = 2 ^ 4 ∨ Nat.card (wOf1469 K) = 2 ^ 5)) ∨
       (IsAlt 7 (OTwoQuot K) ∧ True ∧
         (Nat.card (wOf1469 K) = 2 ^ 4 ∨ Nat.card (wOf1469 K) = 2 ^ 6))))

theorem concl14610List_of_core {T M H : Subgroup G} {u : G} {I I₂ : Subgroup G}
    (c : Facts14610 T M H u I I₂) (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T))
    (hT : F6.IsGoldschmidtTripleIn I (i1Of1469 T M I) I₂)
    (hc : Concl14610Core I (oTwoUpper I)) : Concl14610List T M I I₂ (oTwoUpper I) where
  le := oTwoUpper_le I
  normal := le_normalizer_oTwoUpper I
  eq_residual := rfl
  eq_sup := by
    have h := sup_twoResidual_eq hsyl
    rw [F6.twoResidual_eq_oTwoUpper, sup_comm] at h
    exact h.symm
  gen := oTwoUpper_eq_sup_of_isGoldschmidtTripleIn hT
  shape := hc.shape
  v_le_w := Setting146.vz_le_wOf1469 c hsyl hLT

@[expose] def Input14610ListN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G) (I I₂ : Subgroup G),
    ASC27Statement G → Facts14610 T M H u I I₂ → IsSylowTwoOf (T ⊓ I) I →
    yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T) →
    F6.IsGoldschmidtTripleIn I (i1Of1469 T M I) I₂ →
    F6.F618ConclusionCat
      (((i1Of1469 T M I).subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
      ((I₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) →
    Concl14610Core I (oTwoUpper I)

end CFSG.Quasithin
