module

public import CFSG.LocalAnalysis.StandardType.A8LiftBlocks
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.StandardType

namespace A8LiftHom

open scoped commutatorElement

variable {S G : Type*} [Group S] [Group G]

lemma commutatorElement_mul_central_left {z a b : S} (hz : z ∈ Subgroup.center S) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have h : ⁅z, b⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz b).symm
  rw [commutatorElement_mul_left_eq_conj_mul, h]
  simp

lemma commutatorElement_mul_central_right {z a b : S} (hz : z ∈ Subgroup.center S) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have h : ⁅a, z⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz a)
  rw [commutatorElement_mul_right_eq_mul_conj, h]
  simp

theorem exists_perfect_subgroup_map_eq (ψ : S →* G) (hker : ψ.ker ≤ Subgroup.center S)
    {J : Subgroup G} (hJ : J ≤ ψ.range) (hperf : commutator ↥J = ⊤) :
    ∃ Γ : Subgroup S, commutator ↥Γ = ⊤ ∧ Γ.map ψ = J := by
  let T : Subgroup S := J.comap ψ
  let Γ : Subgroup S := ⁅T, T⁆
  have hJeq : ⁅J, J⁆ = J := by
    rw [← Subgroup.map_subtype_commutator J, hperf, Subgroup.map_top, Subgroup.range_subtype]
  have hmap : Γ.map ψ = J := by
    dsimp only [Γ]
    rw [Subgroup.map_commutator]
    have hT : T.map ψ = J := by
      dsimp only [T]
      exact Subgroup.map_comap_eq_self hJ
    rw [hT, hJeq]
  have hgen : ∀ t ∈ T, ∃ γ ∈ Γ, γ⁻¹ * t ∈ ψ.ker := by
    intro t ht
    have hψ : ψ t ∈ Γ.map ψ := by rw [hmap]; exact ht
    rw [Subgroup.mem_map] at hψ
    obtain ⟨γ, hγ, hγt⟩ := hψ
    exact ⟨γ, hγ, by rw [MonoidHom.mem_ker, map_mul, map_inv, hγt, inv_mul_cancel]⟩
  have hle : Γ ≤ ⁅Γ, Γ⁆ := by
    change ⁅T, T⁆ ≤ ⁅Γ, Γ⁆
    rw [Subgroup.commutator_def T T, Subgroup.closure_le]
    rintro g ⟨t₁, ht₁, t₂, ht₂, rfl⟩
    obtain ⟨γ₁, hγ₁, hz₁⟩ := hgen t₁ ht₁
    obtain ⟨γ₂, hγ₂, hz₂⟩ := hgen t₂ ht₂
    rw [← mul_inv_cancel_left γ₁ t₁, ← mul_inv_cancel_left γ₂ t₂,
      commutatorElement_mul_central_left (hker hz₁),
      commutatorElement_mul_central_right (hker hz₂)]
    exact Subgroup.commutator_mem_commutator hγ₁ hγ₂
  refine ⟨Γ, ?_, hmap⟩
  rw [← Group.isPerfect_def, Subgroup.isPerfect_iff]
  exact le_antisymm (Subgroup.commutator_le_self Γ) hle

theorem hasOrderSevenData_of_map_eq [Finite S] [Finite G] (ψ : S →* G)
    (hker : ψ.ker ≤ Subgroup.center S) {J : Subgroup G} (hJ : IsAlternatingEightCover ↥J)
    {Γ : Subgroup S} (hperf : commutator ↥Γ = ⊤) (hmap : Γ.map ψ = J)
    (h7 : ∀ z ∈ ψ.ker, z ^ 7 = 1 → z = 1) : HasOrderSevenData ↥Γ := by
  let π : ↥Γ →* ↥J :=
    (ψ.domRestrict Γ).codRestrict J (fun γ => hmap ▸ Subgroup.mem_map.mpr ⟨γ, γ.2, rfl⟩)
  have mem_ker : ∀ z : ↥Γ, z ∈ π.ker → (z : S) ∈ ψ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    rw [MonoidHom.mem_ker]
    have h := congrArg Subtype.val hz
    simpa [π] using h
  have hsurj : Function.Surjective π := by
    intro j
    have hj : (j : G) ∈ Γ.map ψ := by rw [hmap]; exact j.2
    rw [Subgroup.mem_map] at hj
    obtain ⟨γ, hγ, hγj⟩ := hj
    exact ⟨⟨γ, hγ⟩, by apply Subtype.ext; simpa [π] using hγj⟩
  have hcen : π.ker ≤ Subgroup.center ↥Γ := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hker (mem_ker z hz)) (w : S)
  have hkill : ∀ z ∈ π.ker, z ^ 7 = 1 → z = 1 := by
    intro z hz hz7
    apply Subtype.ext
    have hzψ := mem_ker z hz
    have hz7' : (z : S) ^ 7 = 1 := by
      have h := congrArg Subtype.val hz7
      simpa using h
    exact h7 (z : S) hzψ hz7'
  exact hasOrderSevenData_of_central_ext hJ π hsurj hcen hperf hkill

theorem hasOrderFiveData_of_map_eq [Finite S] [Finite G] (ψ : S →* G)
    (hker : ψ.ker ≤ Subgroup.center S) {J : Subgroup G} (hJ : IsAlternatingEightCover ↥J)
    {Γ : Subgroup S} (hperf : commutator ↥Γ = ⊤) (hmap : Γ.map ψ = J)
    (h5 : ∀ z ∈ ψ.ker, z ^ 5 = 1 → z = 1) : HasOrderFiveData ↥Γ := by
  let π : ↥Γ →* ↥J :=
    (ψ.domRestrict Γ).codRestrict J (fun γ => hmap ▸ Subgroup.mem_map.mpr ⟨γ, γ.2, rfl⟩)
  have mem_ker : ∀ z : ↥Γ, z ∈ π.ker → (z : S) ∈ ψ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    rw [MonoidHom.mem_ker]
    have h := congrArg Subtype.val hz
    simpa [π] using h
  have hsurj : Function.Surjective π := by
    intro j
    have hj : (j : G) ∈ Γ.map ψ := by rw [hmap]; exact j.2
    rw [Subgroup.mem_map] at hj
    obtain ⟨γ, hγ, hγj⟩ := hj
    exact ⟨⟨γ, hγ⟩, by apply Subtype.ext; simpa [π] using hγj⟩
  have hcen : π.ker ≤ Subgroup.center ↥Γ := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hker (mem_ker z hz)) (w : S)
  have hkill : ∀ z ∈ π.ker, z ^ 5 = 1 → z = 1 := by
    intro z hz hz5
    apply Subtype.ext
    have hzψ := mem_ker z hz
    have hz5' : (z : S) ^ 5 = 1 := by
      have h := congrArg Subtype.val hz5
      simpa using h
    exact h5 (z : S) hzψ hz5'
  exact hasOrderFiveData_of_central_ext hJ π hsurj hcen hperf hkill

theorem ne_bot_of_isAlternatingEightCover [Finite G] {J : Subgroup G}
    (hJ : IsAlternatingEightCover ↥J) : J ≠ ⊥ := by
  intro hbot
  obtain ⟨x, -, hx, -⟩ := hJ.exists_orderOf_five_conj_sq
  have hx1 : x = 1 := by
    apply Subtype.ext
    exact Subgroup.mem_bot.mp (hbot ▸ x.2)
  rw [hx1, orderOf_one] at hx
  exact absurd hx (by norm_num)

end A8LiftHom

end CFSG.StandardType
