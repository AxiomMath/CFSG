module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4Card
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4UMod

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.S1417
open scoped commutatorElement

section Glue

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ} {R₁ R₂ : Subgroup G}
  {s : G}

theorem e9z4_card_conjClosure_H₂ (h35 : Lemma1435) (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ p) (hshape : IsE9Z4Shape T H p) (hdat : IsE9Dat T M H PQ R₁ R₂ s) :
    Nat.card (conjClosure (VZ T M)
      (oTwoUpper (R₂ ⊔ (T ⊓ Subgroup.normalizer (R₁ : Set G))))) = 2 ^ 4 := by
  have hcard := e9z4_card_conjClosure h35 S hred hshape hdat
  obtain ⟨h98, hsplit, Q₁, Q₂, hstr, hpp, hR₁, hR₂⟩ := hdat.setup h35 S hred hshape
  have hsw := inf_normalizer_HLb_swap h98.toHypF91 hred.isHTM.1.1 rfl hstr hpp
  have hBA : T ⊓ Subgroup.normalizer (R₁ : Set G) ≤ Subgroup.normalizer (R₂ : Set G) := by
    rw [hR₁, hR₂]
    intro x hx
    have hx' : x ∈ T ⊓ Subgroup.normalizer
        (HLb (resBeta (rhoH h98.toHypF91)) Q₂ : Set G) := by
      rw [hsw]
      exact hx
    exact hx'.2
  rwa [oTwoUpper_sup_eq_oTwoUpper (S.hyp.sylow.1.to_le inf_le_left) hBA]

end Glue

end CFSG.Quasithin
