module

public import CFSG.RankThree.PartTwo.Sec21.FF81Sec32

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}

theorem FF81Hyp.isElemAb_B4 (h : FF81Hyp b L)
    {b₁ b₂ b₃ : G} (hb₁ : b₁ ∈ L) (hb₂ : b₂ ∈ L) (hb₃ : b₃ ∈ L)
    (hE : IsElemAb 3 3 (Subgroup.closure ({b₁, b₂, b₃} : Set G)))
    (hbB : b ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G)) :
    IsElemAb 3 4 (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)) :=
  h.isElemAb_B hE ((Subgroup.closure_le L).mpr (by
    rintro x (rfl | rfl | rfl)
    exacts [hb₁, hb₂, hb₃]))

theorem fix_tau'_le_of_conj
    {B : Subgroup G} {b : G} (hbB : b ∈ B) (hb3 : orderOf b = 3)
    {τX : MulAut ↥B}
    (hτXfix : ∀ x : ↥B, τX x = x ↔ x ∈ Subgroup.zpowers (⟨b, hbB⟩ : ↥B))
    {σ : MulAut ↥B}
    (hσb : (σ * τX * σ⁻¹) ⟨b, hbB⟩ = ⟨b, hbB⟩)
    {x : ↥B} (hx : (σ * τX * σ⁻¹) x = x) :
    x ∈ Subgroup.zpowers (⟨b, hbB⟩ : ↥B) := by
  let bB : ↥B := ⟨b, hbB⟩
  have hord : orderOf bB = 3 := by
    rw [← Subgroup.orderOf_coe bB]
    simpa [bB] using hb3
  have hbB_ne : bB ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    norm_num at hord
  have hmem : σ⁻¹ x ∈ Subgroup.zpowers bB := by
    apply (hτXfix (σ⁻¹ x)).mp
    have h := congrArg (fun z => σ⁻¹ z) hx
    simpa only [MulAut.mul_apply, MulAut.inv_apply_self] using h
  have hzmem : σ⁻¹ bB ∈ Subgroup.zpowers bB := by
    apply (hτXfix (σ⁻¹ bB)).mp
    have h := congrArg (fun z => σ⁻¹ z) hσb
    simpa only [MulAut.mul_apply, MulAut.inv_apply_self] using h
  have hz_ne : σ⁻¹ bB ≠ 1 := by
    intro h1
    apply hbB_ne
    have h := congrArg (fun z => σ z) h1
    simpa using h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp hzmem
  rcases eq_or_eq_inv_of_mem_zpowers (b := bB) hord hzmem hz_ne with hz | hz
  ·
    have hσb' : σ bB = bB := by
      have h := congrArg σ hz
      simpa using h.symm
    have hxeq : x = bB ^ k := by
      calc x = σ (σ⁻¹ x) := (MulAut.apply_inv_self (M := ↥B) σ x).symm
        _ = σ (bB ^ k) := by rw [← hk]
        _ = (σ bB) ^ k := map_zpow σ bB k
        _ = bB ^ k := by rw [hσb']
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, hxeq.symm⟩
  ·
    have hσb' : σ bB = bB⁻¹ := by
      have h := congrArg σ hz
      have h2 : bB = (σ bB)⁻¹ := by simpa using h
      simpa [← h2] using (inv_inv (σ bB)).symm
    have hxeq : x = bB ^ (-k) := by
      calc x = σ (σ⁻¹ x) := (MulAut.apply_inv_self (M := ↥B) σ x).symm
        _ = σ (bB ^ k) := by rw [← hk]
        _ = (σ bB) ^ k := map_zpow σ bB k
        _ = (bB⁻¹) ^ k := by rw [hσb']
        _ = bB ^ (-k) := by rw [inv_zpow, zpow_neg]
    exact Subgroup.mem_zpowers_iff.mpr ⟨-k, hxeq.symm⟩
end CFSG.RankThree.PartTwo.Sec21.FF81