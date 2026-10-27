module

public import CFSG.RankThree.GF2n.Tim79a34Natural

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G] {M V Q P H : Subgroup G}

theorem memberUnique_wOf_le_normalizer (hc : MinCex M V Q P H) {g : G} (hg : g ∈ H) :
    wOf V H ≤ Subgroup.normalizer (conjSubgroup g V : Set G) := by
  intro w hw
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hc.conj_inf_wOf_ne_bot hg)
  obtain ⟨haU, haW⟩ := Subgroup.mem_inf.mp ha
  have ha1' : a ≠ 1 := fun h' => ha1 (Subtype.ext h')
  have hcomm : w * a = a * w := hc.wOf_isElemAbelian.comm hw haW
  exact Tim77.mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup hc.ti g) haU ha1' hcomm

theorem memberUnique_comm_mem (hc : MinCex M V Q P H) {g : G} (hg : g ∈ H) {w u : G}
    (hw : w ∈ wOf V H) (hu : u ∈ conjSubgroup g V) :
    w * u * w⁻¹ * u⁻¹ ∈ conjSubgroup g V ⊓ wOf V H := by
  have huH : u ∈ H := conjSubgroup_le_of_le_of_mem hc.V_le_H hg hu
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have h1 : w * u * w⁻¹ ∈ conjSubgroup g V :=
      (Subgroup.mem_normalizer_iff.mp (memberUnique_wOf_le_normalizer hc hg hw) u).mp hu
    exact (conjSubgroup g V).mul_mem h1 ((conjSubgroup g V).inv_mem hu)
  · have h2 : u * w⁻¹ * u⁻¹ ∈ wOf V H :=
      (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H huH) w⁻¹).mp
        ((wOf V H).inv_mem hw)
    have h3 : w * u * w⁻¹ * u⁻¹ = w * (u * w⁻¹ * u⁻¹) := by group
    rw [h3]
    exact (wOf V H).mul_mem hw h2

theorem memberUnique_not_conj_le_wOf (hc : MinCex M V Q P H) {g : G} (hg : g ∈ H) :
    ¬ conjSubgroup g V ≤ wOf V H := by
  intro hle
  apply hc.not_V_le_wOf
  intro v hv
  have hmem : g * v * g⁻¹ ∈ conjSubgroup g V :=
    mem_conjSubgroup.mpr (by rw [show g⁻¹ * (g * v * g⁻¹) * g = v by group]; exact hv)
  exact (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H hg) v).mpr (hle hmem)

theorem memberUnique_holds (hX : CXWStatement) : MemberUniqueStatement := by
  intro G _ _ M V Q P H hH hZ U hU U' hU' hle
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  obtain ⟨g, hg, rfl⟩ := hU
  obtain ⟨g', hg', rfl⟩ := hU'
  obtain ⟨x, hxU', hxW⟩ := SetLike.not_le_iff_exists.mp (memberUnique_not_conj_le_wOf hc hg')
  have hxU : x ∈ wOf V H ⊔ conjSubgroup g V := by
    rw [sup_comm]
    exact hle hxU'
  have hUW : conjSubgroup g V ≤ Subgroup.normalizer (wOf V H : Set G) := by
    intro u hu
    exact H_le_normalizer_wOf V H (conjSubgroup_le_of_le_of_mem hc.V_le_H hg hu)
  obtain ⟨w, hw, u, hu, hxwu⟩ := CFSG.RankThree.GF2n.exists_mul_of_mem_sup hUW hxU
  have huW : u ∉ wOf V H := fun huW => hxW (by rw [hxwu]; exact (wOf V H).mul_mem hw huW)
  have huX : u ∈ xOf V H := le_xOf (conjSubgroup_mem_omegaOf hg) hu
  obtain ⟨w', hw', hne⟩ : ∃ w' ∈ wOf V H, u * w' ≠ w' * u := by
    by_contra hcon
    push Not at hcon
    exact huW (hX G M V Q P H hH hZ u huX hcon)
  have hcU : w' * u * w'⁻¹ * u⁻¹ ∈ conjSubgroup g V ⊓ wOf V H :=
    memberUnique_comm_mem hc hg hw' hu
  have hcW : w' * u * w'⁻¹ * u⁻¹ ∈ wOf V H := (Subgroup.mem_inf.mp hcU).2
  have hcomm_ww' : w' * w = w * w' := hc.wOf_isElemAbelian.comm hw' hw
  have hwc : w * (w' * u * w'⁻¹ * u⁻¹) = (w' * u * w'⁻¹ * u⁻¹) * w :=
    hc.wOf_isElemAbelian.comm hw hcW
  have heq : w' * x * w'⁻¹ * x⁻¹ = w' * u * w'⁻¹ * u⁻¹ := by
    rw [hxwu]
    calc w' * (w * u) * w'⁻¹ * (w * u)⁻¹ = (w' * w) * u * w'⁻¹ * (u⁻¹ * w⁻¹) := by group
      _ = (w * w') * u * w'⁻¹ * (u⁻¹ * w⁻¹) := by rw [hcomm_ww']
      _ = w * (w' * u * w'⁻¹ * u⁻¹) * w⁻¹ := by group
      _ = (w' * u * w'⁻¹ * u⁻¹) * w * w⁻¹ := by rw [hwc]
      _ = w' * u * w'⁻¹ * u⁻¹ := by group
  have hcU' : w' * u * w'⁻¹ * u⁻¹ ∈ conjSubgroup g' V := by
    rw [← heq]
    exact (Subgroup.mem_inf.mp (memberUnique_comm_mem hc hg' hw' hxU')).1
  have hne1 : w' * u * w'⁻¹ * u⁻¹ ≠ 1 := by
    intro h1
    apply hne
    calc u * w' = (w' * u * w'⁻¹ * u⁻¹)⁻¹ * (w' * u) := by group
      _ = w' * u := by rw [h1, inv_one, one_mul]
  have hbot : conjSubgroup g V ⊓ conjSubgroup g' V ≠ ⊥ := by
    intro hbot
    apply hne1
    have hmem : w' * u * w'⁻¹ * u⁻¹ ∈ conjSubgroup g V ⊓ conjSubgroup g' V :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hcU).1, hcU'⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hk : conjSubgroup (g' * g⁻¹) (conjSubgroup g V) = conjSubgroup g' V := by
    rw [conjSubgroup_conjSubgroup, inv_mul_cancel_right]
  have hfin := conjSubgroup_eq_of_isTI (isTI_conjSubgroup hc.ti g) (g := g' * g⁻¹)
    (by rw [hk]; exact hbot)
  rw [hk] at hfin
  exact hfin

end CFSG.RankThree.GF2n.Tim79a
