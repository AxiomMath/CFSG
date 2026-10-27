module

import CFSG.RankThree.PartTwo.Sec21.FF84S23Sub
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base
import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFIdCyc
public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {H : Type} [Group H] [Finite H]

theorem e34_comm_of_pGroup (hS : ∃ S : Subgroup H, IsSylowOf 3 S ⊤ ∧ IsMulCommutative S)
    {P : Subgroup H} (hP : IsPGroup 3 P) : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hSyl, hSc⟩ := hS
  obtain ⟨k, -, hk⟩ := L41.exists_conj_le_sylowOf_p (p := 3) hSyl (le_top : P ≤ ⊤) hP
  intro x hx y hy
  have h := congrArg Subtype.val
    (hSc.is_comm.comm ⟨k * x * k⁻¹, hk x hx⟩ ⟨k * y * k⁻¹, hk y hy⟩)
  simp only [Subgroup.coe_mul] at h
  have h2 : k * (x * y) * k⁻¹ = k * (y * x) * k⁻¹ := by
    calc k * (x * y) * k⁻¹ = (k * x * k⁻¹) * (k * y * k⁻¹) := by group
      _ = (k * y * k⁻¹) * (k * x * k⁻¹) := h
      _ = k * (y * x) * k⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h2)


theorem e34_pGroup_zpowers {G : Type*} [Group G] {p : ℕ} {x : G} {k : ℕ} (h : x ^ (p ^ k) = 1) :
    IsPGroup p (Subgroup.zpowers x) := by
  rw [isPGroup_iff_orderOf_dvd_pow]
  intro g
  exact ⟨k, by
    rw [← Subgroup.orderOf_coe]
    exact (orderOf_dvd_of_mem_zpowers g.2).trans (orderOf_dvd_of_pow_eq_one h)⟩

theorem e34_comp_center_trivial (hO : pPrimeCore 3 H = ⊥)
    (hS : ∃ S : Subgroup H, IsSylowOf 3 S ⊤ ∧ IsMulCommutative S) {C : Subgroup H}
    (hC : IsComponent C) {z : H} (hz : z ∈ C) (hcen : ∀ w ∈ C, w * z = z * w) : z = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzl : z ∈ layer H := LocalCores.component_le_layer hC hz
  have hzc := WholeGroup.mem_centralizer_layer_of_mem_component hC hz hcen
  have hzm : z ∈ ((Subgroup.center (layer H)).map (layer H).subtype) :=
    (LocalCores.mem_map_center_iff _).mpr ⟨hzl, hzc⟩
  have hzp : z ∈ pCore 3 H := WholeGroup.center_layer_le_pCore_of_pPrimeCore_eq_bot 3 hO hzm
  obtain ⟨k, hk⟩ := pCore_isPGroup (p := 3) (G := H) ⟨z, hzp⟩
  have hk' : z ^ (3 ^ k) = 1 := congrArg Subtype.val hk
  let z' : ↥C := ⟨z, hz⟩
  have hz'k : z' ^ (3 ^ k) = 1 := Subtype.ext hk'
  obtain ⟨Q, hQ⟩ := (e34_pGroup_zpowers hz'k).exists_le_sylow
  have hcomm : IsMulCommutative (Q : Subgroup ↥C) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    have hP : IsPGroup 3 ((Q : Subgroup ↥C).map C.subtype) := Q.isPGroup'.map _
    have := e34_comm_of_pGroup hS hP (a : H) ⟨a, a.2, rfl⟩ (b : H) ⟨b, b.2, rfl⟩
    exact Subtype.ext (Subtype.ext this)
  haveI : Group.IsPerfect ↥C := hC.1.1
  have hmeet := Quasithin.SBd19F.sylow_inf_center_eq_bot Q
  have hz'c : z' ∈ Subgroup.center ↥C := Subgroup.mem_center_iff.mpr fun w =>
    Subtype.ext (hcen w w.2)
  have hmem : z' ∈ (Q : Subgroup ↥C) ⊓ Subgroup.center ↥C :=
    ⟨hQ (Subgroup.mem_zpowers z'), hz'c⟩
  rw [hmeet, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem e34_comp_simple (hO : pPrimeCore 3 H = ⊥)
    (hS : ∃ S : Subgroup H, IsSylowOf 3 S ⊤ ∧ IsMulCommutative S) {C : Subgroup H}
    (hC : IsComponent C) : IsSimpleGroup ↥C := by
  have hcen : Subgroup.center ↥C = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun z hz => ?_
    exact Subtype.ext (e34_comp_center_trivial hO hS hC z.2 fun w hw =>
      congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨w, hw⟩))
  have h1 := hC.1.2.1
  exact (((QuotientGroup.quotientMulEquivOfEq hcen).trans
    (QuotientGroup.quotientBot (G := ↥C))).isSimpleGroup_congr).mp h1

theorem e34_comp_three_dvd (hO : pPrimeCore 3 H = ⊥) {C : Subgroup H} (hC : IsComponent C)
    (hne : C ≠ ⊥) : 3 ∣ Nat.card C :=
  FF84.dvd_card_of_isSubnormal' Nat.prime_three hO hC.2 hne

end CFSG.RankThree.PartTwo.Sec21.FF79
