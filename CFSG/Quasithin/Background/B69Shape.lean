module

public import CFSG.Quasithin.Background.B69Comp2
public import CFSG.Quasithin.Background.B69Cnt
public import CFSG.Quasithin.Background.B69Comp

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69

@[expose] def CompShape {V : Type} [CommGroup V] (T M A L : Subgroup (MulAut V)) (W : Subgroup V) :
    Prop :=
  ((∃ e : ℕ, 1 ≤ e ∧ BinaryNaturalSL L W (W ⊓ fixV L) 2 e) ∧
      CFSG.QuasithinUnique.IsSylowTwoOf A L ∧
      M ⊓ L = L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V))) ∨
    (∃ k : ℕ, 1 ≤ k ∧ ∃ π : Equiv.Perm (Fin (2 * k + 1)) →* ↥(L ⊔ A),
      Function.Surjective π ∧
      (FFModel.symDn (2 * k + 1)).RealizesVia (L ⊔ A) W ⊥ π ∧
      L = (alternatingGroup (Fin (2 * k + 1))).map ((L ⊔ A).subtype.comp π) ∧
      (∃ i j : Fin (2 * k + 1), i ≠ j ∧
        A = (Subgroup.zpowers (Equiv.swap i j)).map ((L ⊔ A).subtype.comp π)) ∧
      ((M ⊓ (L ⊔ A)).subgroupOf (L ⊔ A) =
        (MulAction.stabilizer (Equiv.Perm (Fin (2 * k + 1)))
          (⟨0, by omega⟩ : Fin (2 * k + 1))).map π))

theorem asB69Component_iff : AsB69Component ↔
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ (X T M A L : Subgroup (MulAut V)), CompHyp X T M A L →
        ∀ W : Subgroup V, W ∈ IrrPlus L (⊤ : Subgroup V) → CompShape T M A L W :=
  Iff.rfl

variable {V : Type} [CommGroup V] [Finite V]

theorem eq_sup_fixV_of_sec (hV : ∀ v : V, v ^ 2 = 1) {X A L : Subgroup (MulAut V)}
    (hA : IsFFStarMin X A) (hL : CFSG.Open.IsQuasisimple ↥L) (hLA : ⁅L, A⁆ = L) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V))
    (hS : Nat.card (autSec A W (W ⊓ fixV L)) * Nat.card (fixV (autSec A W (W ⊓ fixV L))) ≤
      Nat.card (Sec W (W ⊓ fixV L))) :
    W ⊔ fixV A = ⊤ ∧ A ⊓ centSub W = ⊥ := by
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  have hAW := a_stab_irr hV hA hL hLA hW
  have hAst : A ≤ stabSub W := B1.le_stabSub_of_invariant hAW
  have hnt : commSub W A ≠ ⊥ := commSub_ne_bot_of_irr hLA hW
  obtain ⟨hmin, hfaith⟩ := B1_5_2 hV hA hAW hnt
  refine hfaith fun hstrong => ?_
  have hr : rAV (autSub A W) < 1 := hstrong.2
  have hW2 := B1.sq_eq_one_sub hV W
  have h1 : Nat.card W < Nat.card (autSub A W) * Nat.card (fixV (autSub A W)) :=
    (rAV_lt_one_iff hW2 hmin.1.isA2).1 hr
  have hUW : W ⊓ fixV L ≤ W := inf_le_left
  have hAU : A ≤ stabSub (W ⊓ fixV L) :=
    B1.le_stabSub_of_invariant (isInv_inf hAW (B1Red.fixV_inv_of_normalizes hAn))
  have hker : A ⊓ centSec W (W ⊓ fixV L) = A ⊓ centSub W := by
    apply le_antisymm
    · rintro a ⟨haA, ha⟩
      refine ⟨haA, ?_⟩
      have := sec_triv_imp_triv hL hAn hW hAW haA fun w hw => (ha.2 w hw).2
      intro w hw
      exact this w hw
    · rintro a ⟨haA, ha⟩
      refine ⟨haA, hAst haA, fun w hw => ?_⟩
      rw [ha w hw, mul_inv_cancel]
      exact Subgroup.one_mem _
  have hcard : Nat.card (autSub A W) = Nat.card (autSec A W (W ⊓ fixV L)) := by
    have e1 := card_autSub_mul hAst
    have e2 := card_autSec_mul hAst hAU
    rw [hker] at e2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (e1.trans e2.symm)
  have hfix : Nat.card (fixV (autSub A W)) = Nat.card ↥(W ⊓ fixV A) := by
    rw [← map_subtype_fixV_autSub hAst, Subgroup.card_map_of_injective W.subtype_injective]
  have h2 := card_inf_fixV_le_autSec hUW hAst
  have h3 : Nat.card ↥((W ⊓ fixV L) ⊓ fixV A) ≤ Nat.card ↥(W ⊓ fixV L) :=
    Subgroup.card_le_of_le inf_le_left
  have h4 := card_sec_mul hUW
  rw [hcard, hfix] at h1
  set a := Nat.card (autSec A W (W ⊓ fixV L))
  set cS := Nat.card (fixV (autSec A W (W ⊓ fixV L)))
  set c := Nat.card ↥(W ⊓ fixV A)
  set cU := Nat.card ↥((W ⊓ fixV L) ⊓ fixV A)
  set u := Nat.card ↥(W ⊓ fixV L)
  set s := Nat.card (Sec W (W ⊓ fixV L))
  have h5 : a * c ≤ s * u := by
    calc a * c ≤ a * (cS * cU) := Nat.mul_le_mul_left _ h2
      _ ≤ a * (cS * u) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
      _ = (a * cS) * u := by ring
      _ ≤ s * u := Nat.mul_le_mul_right _ hS
  rw [h4] at h5
  exact absurd (lt_of_lt_of_le h1 h5) (lt_irrefl _)

theorem eq_sup_fixV_of_card_le_two (hV : ∀ v : V, v ^ 2 = 1) {X A L : Subgroup (MulAut V)}
    (hA : IsFFStarMin X A) (hL : CFSG.Open.IsQuasisimple ↥L) (hLA : ⁅L, A⁆ = L) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) (hc : Nat.card A ≤ 2) :
    W ⊔ fixV A = ⊤ ∧ A ⊓ centSub W = ⊥ := by
  have hAW := a_stab_irr hV hA hL hLA hW
  have hAst : A ≤ stabSub W := B1.le_stabSub_of_invariant hAW
  have hnt : commSub W A ≠ ⊥ := commSub_ne_bot_of_irr hLA hW
  obtain ⟨hmin, hfaith⟩ := B1_5_2 hV hA hAW hnt
  refine hfaith fun hstrong => ?_
  have hW2 := B1.sq_eq_one_sub hV W
  have hA2 : IsA2 (autSub X W) (autSub A W) := hmin.1.isA2
  have e1 := card_autSub_mul hAst
  have hle : Nat.card (autSub A W) ≤ 2 :=
    (Nat.le_of_dvd Nat.card_pos ⟨_, e1.symm⟩).trans hc
  have hne : Nat.card (autSub A W) ≠ 1 := fun h =>
    hA2.2.1 (Subgroup.card_eq_one.1 h)
  have hpos : 0 < Nat.card (autSub A W) := Nat.card_pos
  have h2 : Nat.card (autSub A W) = 2 := by omega
  exact not_rAV_lt_one_of_card_two hW2 hA2 h2 hstrong.2

end B69

end CFSG.Quasithin
