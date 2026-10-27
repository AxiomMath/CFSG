module

public import CFSG.Quasithin.EmptyFaithful.LRed13ExA
public import CFSG.Quasithin.Vol2.Ch3yChain

public section

namespace CFSG.Quasithin

namespace LRed13

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {G₁ G₂ T V M₂ : Subgroup G}

theorem exists_isMinOffender_quadratic (h : D11Hyp G₁ G₂ T V M₂)
    (hnff : ¬ IsFFInt G₁ V h.reduced.2.2.1) (hVR₂ : V ≤ pCoreOf 2 G₂)
    (hq2 : (2 : WithTop ℚ) ≤ qInt G₁ V h.reduced.2.2.1) :
    ∃ A : Subgroup G, IsMaxElemAbelian T A ∧ ¬ IsMaxElemAbelian (pCoreOf 2 G₂) A ∧
      (∀ A' : Subgroup G, IsMaxElemAbelian T A' → ¬ IsMaxElemAbelian (pCoreOf 2 G₂) A' →
        Nat.card ↥(A ⊔ pCoreOf 2 G₂) ≤ Nat.card ↥(A' ⊔ pCoreOf 2 G₂)) ∧
      ⁅⁅conjClosure V G₂, A⁆, A⁆ = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := h.reduced.2.2.1
  have hmp := h.minParabolic hnff
  set R₂ := pCoreOf 2 G₂ with hR₂def
  set U := conjClosure V G₂ with hUdef
  have hTG₁ : T ≤ G₁ := h.sylow₁.1
  have hTG₂ : T ≤ G₂ := h.sylow₂.1
  have hR₂T : R₂ ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf h.sylow₂
  have hG₂R₂ : G₂ ≤ Subgroup.normalizer (R₂ : Set G) := le_normalizer_pCoreOf 2 G₂
  have hUR₂ : U ≤ R₂ := conjClosure_le fun g hg v hv =>
    (Subgroup.mem_normalizer_iff.mp (hG₂R₂ hg) v).mp (hVR₂ hv)
  have hUT : U ≤ T := hUR₂.trans hR₂T
  have hUG₂ : U ≤ G₂ := hUT.trans hTG₂
  have hG₂U : G₂ ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure V G₂
  have hUe : IsElemAbelian 2 U := D15Proof.isElemAbelian_conjClosure h hnff hVR₂
  have hUP : ⁅U, oTwoUpper G₂⁆ ≠ ⊥ := D15Proof.commutator_ne_bot h
  have hex : ∃ A : Subgroup G, IsMaxElemAbelian T A ∧ ¬ IsMaxElemAbelian R₂ A := by
    by_contra hcon
    push Not at hcon
    apply h.not_thompsonJ_le_pCoreOf hnff
    rw [← h.thompsonJ_eq hnff]
    exact iSup₂_le fun A hA => (hcon A hA).1
  obtain ⟨A, ⟨hAT, hAn⟩, hmin⟩ := Set.exists_min_image
    {A : Subgroup G | IsMaxElemAbelian T A ∧ ¬ IsMaxElemAbelian R₂ A}
    (fun A => Nat.card ↥(A ⊔ R₂)) (Set.toFinite _) hex
  have hAnR : ¬ A ≤ R₂ := fun hle =>
    hAn ⟨hle, hAT.2.1, fun B hBR hB => hAT.2.2 B (hBR.trans hR₂T) hB⟩
  have hAG₂ : A ≤ G₂ := hAT.1.trans hTG₂
  have hAN : A ≤ Subgroup.normalizer (U : Set G) := hAG₂.trans hG₂U
  have hCAU : A ⊓ Subgroup.centralizer (U : Set G) ≤ R₂ :=
    D15Proof.inf_centralizer_le_pCoreOf hmp hG₂U hUP hAT.1
  have hAnc : ¬ A ≤ Subgroup.centralizer (U : Set G) := fun hle =>
    hAnR ((le_inf le_rfl hle).trans hCAU)
  have hAH : IsMaxElemAbelian G₂ A := isMaxElemAbelian_of_isSylowTwoOf h.sylow₂ hAT
  have hAbar : IsFFStarOffender (autI hUe G₂) (autI hUe A) :=
    offenderImages_isFFStarOffender hUe hUG₂ hG₂U ⟨A, ⟨hAH, hAnc⟩, rfl⟩
  obtain ⟨P, hPoff, hPle, hPq⟩ := exists_quadratic_ffLe IntMod.sq_eq_one hAbar
  obtain ⟨hDmax, hDaut⟩ := (offender_core hUe hUG₂ hG₂U hAH hPle.2.2.1).2 hPle.2.2.2
  obtain ⟨D, hDdef⟩ : ∃ D : Subgroup G, D = preI hUe A (hAH.1.trans hG₂U) P ⊔
      (U ⊓ Subgroup.centralizer (preI hUe A (hAH.1.trans hG₂U) P : Set G)) := ⟨_, rfl⟩
  rw [← hDdef] at hDmax hDaut
  have hDA : D ≤ A ⊔ U := by
    rw [hDdef]
    exact sup_le (le_sup_of_le_left (preI_le hUe)) (le_sup_of_le_right inf_le_left)
  have hDT : D ≤ T := hDA.trans (sup_le hAT.1 hUT)
  have hDmaxT : IsMaxElemAbelian T D :=
    ⟨hDT, hDmax.2.1, fun B hBT hB => hDmax.2.2 B (hBT.trans hTG₂) hB⟩
  have hDN : D ≤ Subgroup.normalizer (U : Set G) := hDT.trans (hTG₂.trans hG₂U)
  have hDq : ⁅⁅U, D⁆, D⁆ = ⊥ := by
    refine commutator_commutator_eq_bot_of_isQuadratic hUe hDN ?_
    rw [hDaut]
    exact hPq
  have hDnc : ¬ D ≤ Subgroup.centralizer (U : Set G) := by
    intro hle
    have h0 : autI hUe D = ⊥ := autI_eq_bot_of_le_centralizer hUe hle
    rw [hDaut] at h0
    exact hPoff.2.1 h0
  have hDnR : ¬ D ≤ R₂ := by
    intro hDR
    have hq2' : ∀ E₀ : Subgroup G, E₀ ≤ G₁ → IsElemAbelian 2 E₀ → ⁅⁅V, E₀⁆, E₀⁆ = ⊥ →
        ¬ E₀ ≤ Subgroup.centralizer (V : Set G) →
        ((Subgroup.centralizer (V : Set G)).relIndex E₀) ^ 2 ≤
          (Subgroup.centralizer (E₀ : Set G)).relIndex V :=
      fun E₀ hE hEe hquad hnc =>
        Ch3y.sq_relIndex_le_of_two_le_qInt hV h.reduced.2.1 hq2 hE hEe hquad hnc
    have hQ : ∀ k ∈ G₂, ∀ E : Subgroup G, E ≤ D →
        ¬ E ≤ Subgroup.centralizer (cjSub k V : Set G) →
        ((Subgroup.centralizer (cjSub k V : Set G)).relIndex E) ^ 2 ≤
          (Subgroup.centralizer (E : Set G)).relIndex (cjSub k V) := by
      intro k hk E hED hnc
      have hquad : ⁅⁅cjSub k V, E⁆, E⁆ = ⊥ := by
        have : ⁅⁅cjSub k V, E⁆, E⁆ ≤ ⁅⁅U, D⁆, D⁆ := Subgroup.commutator_mono
          (Subgroup.commutator_mono (D15Proof.cjSub_le_conjClosure hk) hED) hED
        rw [hDq] at this
        exact le_bot_iff.mp this
      exact Ch3y.relIndex_conj_le hq2' (hR₂T.trans hTG₁) (hG₂R₂ hk) (hED.trans hDR)
        (B2F.isElemAbelian_mono hED hDmax.2.1) hquad hnc
    have hsq := Ch3y.sq_relIndex_le_nonstrict (V := V) (H := G₂) (B := D) hQ D le_rfl
    have hoff := card_le_relIndex_mul_card hUe hUT hDmaxT
    rw [Subgroup.inf_relIndex_left] at hoff
    set x := (Subgroup.centralizer (U : Set G)).relIndex D with hx
    set y := (Subgroup.centralizer (D : Set G)).relIndex U with hy
    have e2 := Subgroup.relIndex_mul_card (Subgroup.centralizer (D : Set G)) U
    rw [inf_comm (Subgroup.centralizer (D : Set G)) U] at e2
    have hcpos : 0 < Nat.card (U ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) :=
      Nat.card_pos
    have hyx : y ≤ x := by
      refine Nat.le_of_mul_le_mul_right ?_ hcpos
      rw [← hy] at e2
      calc y * Nat.card (U ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) = Nat.card U := e2
        _ ≤ _ := hoff
    have hxpos : 0 < x := Nat.pos_of_ne_zero (D15Proof.relIndex_ne_zero _ _)
    have hx1 : x ≤ 1 := by
      have h1 : x * x ≤ x * 1 := by
        calc x * x = x ^ 2 := (pow_two x).symm
          _ ≤ y := hsq
          _ ≤ x := hyx
          _ = x * 1 := (mul_one x).symm
      exact Nat.le_of_mul_le_mul_left h1 hxpos
    exact hDnc (Subgroup.relIndex_eq_one.mp (le_antisymm hx1 hxpos))
  refine ⟨D, hDmaxT, fun hmax => hDnR hmax.1, fun A' hA'T hA'n => ?_, hDq⟩
  calc Nat.card ↥(D ⊔ R₂) ≤ Nat.card ↥(A ⊔ R₂) :=
        Subgroup.card_le_of_le (sup_le (hDA.trans (sup_le le_sup_left (hUR₂.trans le_sup_right)))
          le_sup_right)
    _ ≤ Nat.card ↥(A' ⊔ R₂) := hmin A' ⟨hA'T, hA'n⟩

end LRed13

end CFSG.Quasithin
