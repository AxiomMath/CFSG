module

public import CFSG.RankThree.PartOne.TAIL.LSideSL
public import CFSG.RankThree.PartOne.S11b.Sec109SylowTransport

public section

namespace CFSG.RankThree.PartOne.TAIL

open Subgroup
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

section Pull

variable {G : Type} [Group G] {L B : Subgroup G} {M : Type} [Group M]

theorem mem_image_iff (e : ↥L ≃* M) (y : M) :
    y ∈ (B.subgroupOf L).map e.toMonoidHom ↔ ((e.symm y : ↥L) : G) ∈ B := by
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]

theorem coe_normalizer_of_equiv (hBL : B ≤ L) (e : ↥L ≃* M) {g' : M}
    (hg' : g' ∈ Subgroup.normalizer
      (((B.subgroupOf L).map e.toMonoidHom : Subgroup M) : Set M)) :
    ((e.symm g' : ↥L) : G) ∈ Subgroup.normalizer (B : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hg' ⊢
  intro x
  by_cases hxL : x ∈ L
  · set y : M := e ⟨x, hxL⟩ with hy
    have h1 := hg' y
    rw [mem_image_iff e, mem_image_iff e] at h1
    have hxy : ((e.symm y : ↥L) : G) = x := by simp [hy]
    have hgy : ((e.symm (g' * y * g'⁻¹) : ↥L) : G) =
        ((e.symm g' : ↥L) : G) * x * ((e.symm g' : ↥L) : G)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      simp [hxy]
    rw [hxy, hgy] at h1
    exact h1
  · have h1 : x ∉ B := fun hx => hxL (hBL hx)
    have h2 : ((e.symm g' : ↥L) : G) * x * ((e.symm g' : ↥L) : G)⁻¹ ∉ B := by
      intro h
      apply hxL
      have h3 := L.mul_mem (L.mul_mem (L.inv_mem (e.symm g').2) (hBL h)) (e.symm g').2
      have h4 : ((e.symm g' : ↥L) : G)⁻¹ * (((e.symm g' : ↥L) : G) * x *
          ((e.symm g' : ↥L) : G)⁻¹) * ((e.symm g' : ↥L) : G) = x := by group
      rwa [h4] at h3
    exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩

end Pull

section Main

variable {G : Type} [Group G] [Finite G]

theorem lData_of_model {L B : Subgroup G} {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hL : StatedClassicalModel ↥L .PSL n 2 1) (hBL : B ≤ L) (hB7 : IsPGroup 7 B)
    (hBc : Nat.card B = 49) : LData G L B := by
  obtain ⟨k, hk, rfl⟩ : ∃ k : ℕ, k ≤ 1 ∧ n = 6 + k := by
    rcases hn with rfl | rfl
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.Sec109.exists_mulEquiv_sl_two hL
  let B' : Subgroup (Matrix.SpecialLinearGroup (Fin (6 + k)) (ZMod 2)) :=
    (B.subgroupOf L).map e.toMonoidHom
  have hBL' : Nat.card (B.subgroupOf L) = 49 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv]
    exact hBc
  have hB'c : Nat.card B' = 49 := by
    rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
    exact hBL'
  obtain ⟨hI, hP⟩ := model_facts k hk hB'c
  refine ⟨⟨hBL, hB7, ?_⟩, ?_, ?_, ?_⟩
  ·
    intro h7
    apply not_dvd_card_sl_six k hk
    have h1 : Nat.card (B.subgroupOf L) * (B.subgroupOf L).index = Nat.card L :=
      Subgroup.card_mul_index _
    have h3 : Nat.card L = Nat.card (Matrix.SpecialLinearGroup (Fin (6 + k)) (ZMod 2)) :=
      Nat.card_congr e.toEquiv
    rw [← h3, ← h1, hBL']
    obtain ⟨c, hc⟩ := h7
    refine ⟨c, ?_⟩
    have : (B.subgroupOf L).index = B.relIndex L := rfl
    rw [this, hc]
    ring
  ·
    rintro x hx ⟨j, hj⟩
    exact sup_centralizer_of_pow_seven (by omega) e hx j hj
  ·
    intro d hd hd1
    have hdL : d ∈ L := hBL hd
    have hd' : e ⟨d, hdL⟩ ∈ B' := by
      rw [mem_image_iff e]
      simpa using hd
    have hd'1 : e ⟨d, hdL⟩ ≠ 1 := by
      intro h
      apply hd1
      have : (⟨d, hdL⟩ : ↥L) = 1 := e.injective (h.trans (map_one e).symm)
      simpa using congrArg Subtype.val this
    obtain ⟨g', hg', hng⟩ := hI _ hd' hd'1
    refine ⟨((e.symm g' : ↥L) : G), ⟨(e.symm g').2, coe_normalizer_of_equiv hBL e hg'⟩, ?_⟩
    intro hmem
    apply hng
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨m, ?_⟩
    have h1 : (⟨d, hdL⟩ : ↥L) ^ m = e.symm g' * ⟨d, hdL⟩ * (e.symm g')⁻¹ := by
      apply Subtype.ext
      simpa using hm
    have h2 := congrArg e h1
    rw [map_zpow, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h2
    exact h2
  ·
    intro x hxL hxB
    let ρ : MulAut ↥L := L.normalizerMonoidHom ⟨x, hxL⟩
    let α : MulAut (Matrix.SpecialLinearGroup (Fin (6 + k)) (ZMod 2)) := MulAut.congr e ρ
    have hρ : ∀ z : ↥L, ((ρ z : ↥L) : G) = x * z * x⁻¹ := fun z => by
      simp [ρ, Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hαc : ∀ y, ((e.symm (α y) : ↥L) : G) = x * ((e.symm y : ↥L) : G) * x⁻¹ := by
      intro y
      have : e.symm (α y) = ρ (e.symm y) := by simp [α, MulAut.congr_apply]
      rw [this, hρ]
    have hα : ∀ y, y ∈ B' ↔ α y ∈ B' := by
      intro y
      rw [mem_image_iff e, mem_image_iff e, hαc]
      exact Subgroup.mem_normalizer_iff.1 hxB _
    obtain ⟨l', hl', hcase⟩ := hP α hα
    refine ⟨((e.symm l' : ↥L) : G), ⟨(e.symm l').2, coe_normalizer_of_equiv hBL e hl'⟩, ?_⟩
    set l : G := ((e.symm l' : ↥L) : G) with hl
    have key : ∀ (z : G) (hz : z ∈ B),
        ((e.symm (l' * α (e ⟨z, hBL hz⟩) * l'⁻¹) : ↥L) : G) = l * (x * z * x⁻¹) * l⁻¹ := by
      intro z hz
      rw [map_mul, map_mul, map_inv]
      simp [hαc, hl]
    have hz' : ∀ (z : G) (hz : z ∈ B), e ⟨z, hBL hz⟩ ∈ B' := by
      intro z hz
      rw [mem_image_iff e]
      simpa using hz
    rcases hcase with h | h
    · left
      intro z hz
      have h1 : ((e.symm (l' * α (e ⟨z, hBL hz⟩) * l'⁻¹) : ↥L) : G) =
          ((e.symm (e ⟨z, hBL hz⟩) : ↥L) : G) := by rw [h _ (hz' z hz)]
      rw [key z hz] at h1
      simp only [MulEquiv.symm_apply_apply] at h1
      calc (l * x) * z * (l * x)⁻¹ = l * (x * z * x⁻¹) * l⁻¹ := by group
        _ = z := h1
    · right
      intro z hz
      have h1 : ((e.symm (l' * α (e ⟨z, hBL hz⟩) * l'⁻¹) : ↥L) : G) =
          ((e.symm (e ⟨z, hBL hz⟩)⁻¹ : ↥L) : G) := by rw [h _ (hz' z hz)]
      rw [key z hz] at h1
      simp only [map_inv, MulEquiv.symm_apply_apply, Subgroup.coe_inv] at h1
      calc (l * x) * z * (l * x)⁻¹ = l * (x * z * x⁻¹) * l⁻¹ := by group
        _ = z⁻¹ := h1

end Main

end CFSG.RankThree.PartOne.TAIL
