module

public import CFSG.RankThree.GroupTheory.SteinbergBYQD32Extraspecial
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne.Sec9Excl

open Subgroup CFSG CFSG.RankThree.GroupTheory

variable {G : Type*} [Group G]

theorem card_isPGroup_of_qd32 {R : Subgroup G} (e : R ≃* QD32) :
    Nat.card R = 32 ∧ IsPGroup 2 R := by
  have hcard : Nat.card R = 32 := by
    rw [Nat.card_congr e.toEquiv]
    exact SteinbergBY.quaternion_dihedral_extraspecial_involution_generation.1
  exact ⟨hcard, IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)⟩

theorem exists_central_involution {R : Subgroup G} (e : R ≃* QD32) :
    ∃ z ∈ R, z ≠ 1 ∧ z ∈ inSubgroup Subgroup.center R ∧ orderOf z = 2 := by
  have hord : orderOf (e.symm SteinbergBY.qd32Z) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact SteinbergBY.orderOf_qd32Z
  refine ⟨((e.symm SteinbergBY.qd32Z : R) : G),
    (e.symm SteinbergBY.qd32Z).2, ?_, ?_, ?_⟩
  · intro h1
    have h1' : e.symm SteinbergBY.qd32Z = 1 := Subtype.ext h1
    rw [h1', orderOf_one] at hord
    omega
  · refine Subgroup.mem_map.mpr ⟨e.symm SteinbergBY.qd32Z, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro w
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact (Subgroup.mem_center_iff.mp SteinbergBY.qd32Z_mem_center) (e w)
  · rw [Subgroup.orderOf_coe]
    exact hord

theorem exists_noncentral_involution {R : Subgroup G} (e : R ≃* QD32) :
    ∃ r ∈ R, orderOf r = 2 ∧ r ∉ inSubgroup Subgroup.center R := by
  obtain ⟨hcard, hgen, hcenter, hzord⟩ :
      Nat.card QD32 = 32 ∧ Subgroup.closure {g : QD32 | orderOf g = 2} = ⊤ ∧
        Subgroup.center QD32 = Subgroup.zpowers SteinbergBY.qd32Z ∧
        orderOf SteinbergBY.qd32Z = 2 := by
    obtain ⟨h1, -, h3, -, -, -, h7, h8, -⟩ :=
      SteinbergBY.quaternion_dihedral_extraspecial_involution_generation
    exact ⟨h1, h3, h8, h7⟩
  have hex : ∃ g : QD32, orderOf g = 2 ∧ g ∉ Subgroup.center QD32 := by
    by_contra hcon
    push Not at hcon
    have hle : Subgroup.closure {g : QD32 | orderOf g = 2} ≤ Subgroup.center QD32 :=
      (Subgroup.closure_le _).mpr fun g hg => hcon g hg
    rw [hgen, top_le_iff] at hle
    have h2 : Nat.card (Subgroup.center QD32) = 32 := by
      rw [hle, Subgroup.card_top, hcard]
    rw [hcenter, Nat.card_zpowers, hzord] at h2
    omega
  obtain ⟨g, hg2, hgc⟩ := hex
  refine ⟨((e.symm g : R) : G), (e.symm g).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hg2
  · intro hmem
    obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.mp hmem
    have hw' : w = e.symm g := Subtype.ext hwe
    rw [hw', Subgroup.mem_center_iff] at hw
    apply hgc
    rw [Subgroup.mem_center_iff]
    intro x
    have := hw (e.symm x)
    have h2 := congrArg e this
    simpa [map_mul] using h2

end CFSG.RankThree.PartOne.Sec9Excl
