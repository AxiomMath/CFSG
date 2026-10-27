module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven

open Subgroup

theorem fixedBy_map_congr {J J' : Type} [Group J] [Group J'] (e : J ≃* J')
    (W : Subgroup (MulAut J)) :
    (fixedBy W).map e.toMonoidHom = fixedBy (W.map (MulAut.congr e).toMonoidHom) := by
  ext y'
  rw [Subgroup.mem_map, mem_fixedBy]
  constructor
  · rintro ⟨x, hx, rfl⟩ w' hw'
    rw [mem_fixedBy] at hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hw'
    change e (w (e.symm (e x))) = e x
    rw [e.symm_apply_apply, hx w hw]
  · intro h
    refine ⟨e.symm y', ?_, e.apply_symm_apply y'⟩
    rw [mem_fixedBy]
    intro w hw
    have hw' : MulAut.congr e w ∈ W.map (MulAut.congr e).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨w, hw, rfl⟩
    have hfix := h (MulAut.congr e w) hw'
    apply e.injective
    rw [e.apply_symm_apply]
    exact hfix

theorem stepConcl_of_mulEquiv (Good : ∀ (J : Type) [Group J], Prop)
    (hGood : ∀ (J J' : Type) [Group J] [Group J'], J ≃* J' → Good J → Good J')
    {J J' : Type} [Group J] [Group J'] (e : J ≃* J') (W : Subgroup (MulAut J)) (Z : Subgroup J)
    (h : StepConcl Good (W.map (MulAut.congr e).toMonoidHom) (Z.map e.toMonoidHom)) :
    StepConcl Good W Z := by
  unfold StepConcl at h ⊢
  rw [← fixedBy_map_congr e W] at h
  rw [← Subgroup.map_commutator] at h
  obtain ⟨hGood', hZle, hnorm⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · exact hGood ↥(⁅fixedBy W, fixedBy W⁆.map e.toMonoidHom) ↥⁅fixedBy W, fixedBy W⁆
      (e.subgroupMap ⁅fixedBy W, fixedBy W⁆).symm hGood'
  · exact (Subgroup.map_le_map_iff_of_injective e.injective).mp hZle
  · refine (Subgroup.map_injective (f := e.toMonoidHom) e.injective) ?_
    rw [Subgroup.map_sup, Subgroup.map_equiv_normalizer_eq, hnorm,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]

theorem card_facts_of_le {J : Type} [Group J] [Finite J] {F Z : Subgroup J} (hZF : Z ≤ F)
    (hZ : Nat.card Z = 3) (h9 : ¬ 9 ∣ Nat.card J) (h7 : ¬ 7 ∣ Nat.card J) :
    3 ∣ Nat.card F ∧ ¬ 9 ∣ Nat.card F ∧ ¬ 7 ∣ Nat.card F := by
  have h3F : 3 ∣ Nat.card F := by
    rw [← hZ]
    exact Subgroup.card_dvd_of_le hZF
  have hFJ : Nat.card F ∣ Nat.card J := Subgroup.card_subgroup_dvd_card F
  exact ⟨h3F, fun h9F => h9 (Nat.dvd_trans h9F hFJ),
    fun h7F => h7 (Nat.dvd_trans h7F hFJ)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven
