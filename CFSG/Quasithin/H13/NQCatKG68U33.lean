module

public import CFSG.Quasithin.H13.KGFact68CSLin
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineSylow

public section

namespace CFSG.Quasithin.H13.KG68

open CFSG.Assembly.LowTwoRank CFSG.LinearGroups.UnitaryThreeOverNine

theorem mem_zpowers_of_mem_center {G : Type*} [Group G] {s t w : G} (hst : s * t = t * s)
    (hs : s ≠ 1) (hinf : Subgroup.zpowers s ⊓ Subgroup.zpowers t = ⊥) (hw : w ^ 2 = 1)
    (hws : w⁻¹ * s * w = t) (hwt : w⁻¹ * t * w = s) {z : G}
    (hz : z ∈ Subgroup.closure {s, t, w})
    (hzc : ∀ g ∈ Subgroup.closure {s, t, w}, g * z = z * g) : z ∈ Subgroup.zpowers (s * t) := by
  have hc : Commute s t := hst
  have hww : w⁻¹ = w := inv_eq_of_mul_eq_one_right (by rw [← sq, hw])
  obtain ⟨i, j, e, he, rfl⟩ := CFSG.LieType.Steinberg.exists_zpow_mul_zpow_mul_pow hc hws.symm hw hz
  have hsmem : s ∈ Subgroup.closure ({s, t, w} : Set G) := Subgroup.subset_closure (by simp)
  have hwmem : w ∈ Subgroup.closure ({s, t, w} : Set G) := Subgroup.subset_closure (by simp)
  interval_cases e
  ·
    rw [pow_zero, mul_one] at hzc ⊢
    have h1 := hzc w hwmem
    have hconj : ∀ (x : G) (n : ℤ), w⁻¹ * x ^ n * w = (w⁻¹ * x * w) ^ n := fun x n => by
      have := map_zpow (MulAut.conj w⁻¹) x n
      simpa [MulAut.conj_apply] using this
    have h2 : w⁻¹ * (s ^ i * t ^ j) * w = t ^ i * s ^ j := by
      rw [show w⁻¹ * (s ^ i * t ^ j) * w = (w⁻¹ * s ^ i * w) * (w⁻¹ * t ^ j * w) by group,
        hconj, hconj, hws, hwt]
    have h3 : s ^ i * t ^ j = s ^ j * t ^ i := by
      rw [(hc.zpow_zpow j i).eq, ← h2, mul_assoc, ← h1, ← mul_assoc, inv_mul_cancel, one_mul]
    have h4 : s ^ (i - j) = t ^ (i - j) := by
      have h5 : s ^ (i - j) * (s ^ j * t ^ j) = t ^ (i - j) * (s ^ j * t ^ j) := by
        calc s ^ (i - j) * (s ^ j * t ^ j) = s ^ i * t ^ j := by
              rw [← mul_assoc, ← zpow_add, sub_add_cancel]
          _ = s ^ j * t ^ i := h3
          _ = t ^ (i - j) * (s ^ j * t ^ j) := by
              rw [← mul_assoc, ← (hc.zpow_zpow j (i - j)).eq, mul_assoc, ← zpow_add,
                sub_add_cancel]
      exact mul_right_cancel h5
    have h5 : s ^ (i - j) = 1 := by
      have : s ^ (i - j) ∈ Subgroup.zpowers s ⊓ Subgroup.zpowers t :=
        ⟨⟨i - j, rfl⟩, ⟨i - j, h4.symm⟩⟩
      rwa [hinf, Subgroup.mem_bot] at this
    refine ⟨j, ?_⟩
    change (s * t) ^ j = s ^ i * t ^ j
    rw [hc.mul_zpow, show s ^ i = s ^ (i - j) * s ^ j by rw [← zpow_add, sub_add_cancel], h5,
      one_mul]
  ·
    exfalso
    rw [pow_one] at hzc
    have h1 := hzc s hsmem
    have h2 : w * s = s * w := by
      have h3 : s ^ i * t ^ j * (w * s) = s ^ i * t ^ j * (s * w) := by
        calc s ^ i * t ^ j * (w * s) = s ^ i * t ^ j * w * s := by group
          _ = s * (s ^ i * t ^ j * w) := h1.symm
          _ = s ^ i * t ^ j * (s * w) := by
              have hsi : s * s ^ i = s ^ i * s := (Commute.self_zpow s i).eq
              have hsj : s * t ^ j = t ^ j * s := (hc.zpow_right j).eq
              calc s * (s ^ i * t ^ j * w) = (s * s ^ i) * t ^ j * w := by group
                _ = s ^ i * (s * t ^ j) * w := by rw [hsi]; group
                _ = s ^ i * t ^ j * (s * w) := by rw [hsj]; group
      exact mul_left_cancel h3
    have h3 : s = t := by
      rw [← hws, hww, mul_assoc, ← h2, ← mul_assoc, ← sq, hw, one_mul]
    have h4 : s ∈ Subgroup.zpowers s ⊓ Subgroup.zpowers t :=
      ⟨Subgroup.mem_zpowers s, h3 ▸ Subgroup.mem_zpowers t⟩
    rw [hinf, Subgroup.mem_bot] at h4
    exact hs h4

theorem isCyclic_center_sylow_of_isCyclic {S : Type} [Group S] [Finite S] (U : Sylow 2 S)
    (hU : IsCyclic (Subgroup.center ↥(U : Subgroup S))) (T : Sylow 2 S) :
    IsCyclic (Subgroup.center ↥(T : Subgroup S)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S T U
  let e : ↥(T : Subgroup S) ≃* ↥(U : Subgroup S) :=
    (T.equivSMul g).trans (MulEquiv.subgroupCongr (by rw [hg]))
  let hc := ((Subgroup.center ↥(T : Subgroup S)).equivMapOfInjective e.toMonoidHom
    e.injective).trans (MulEquiv.subgroupCongr (Subgroup.map_center_eq e))
  exact isCyclic_of_surjective hc.symm.toMonoidHom hc.symm.surjective

theorem isCyclic_center_sylow_psu33 {X : Type} [Group X] [Finite X]
    (hX : StatedClassicalModel X .PSU 3 3 1) (T : Sylow 2 X) :
    IsCyclic (Subgroup.center ↥(T : Subgroup X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have hK9 : Nat.card K = 9 := by rw [hK]; norm_num
  let e' : X ≃* ↥(StatedSU 3 3 K) := e.trans ((QuotientGroup.quotientMulEquivOfEq
    (statedScalars_subgroupOf_statedSU_eq_bot hK9)).trans QuotientGroup.quotientBot)
  have : Finite ↥(StatedSU 3 3 K) := Finite.of_equiv X e'.toEquiv
  refine isCyclic_center_sylow_of_mulEquiv e' (fun T' => ?_) T
  obtain ⟨i, hi⟩ := exists_units_orderOf_eq_four hK9
  obtain ⟨⟨s, t, w, hs, ht, hw⟩, hall⟩ := wreath_sylow_model hK9 i hi
  obtain ⟨hst, hs4, -, hinf, hw2, -, hws, hwt, -, ⟨P, hP⟩, -⟩ := hall s t w hs ht hw
  have hs1 : s ≠ 1 := fun h => by rw [h, orderOf_one] at hs4; norm_num at hs4
  have hw2' : w ^ 2 = 1 := by rw [← hw2]; exact pow_orderOf_eq_one w
  refine isCyclic_center_sylow_of_isCyclic P ?_ T'
  set C := (Subgroup.center ↥(P : Subgroup ↥(StatedSU 3 3 K))).map
    (P : Subgroup ↥(StatedSU 3 3 K)).subtype with hC
  have hCle : C ≤ Subgroup.zpowers (s * t) := by
    rintro _ ⟨z, hz, rfl⟩
    have hzP : (z : ↥(StatedSU 3 3 K)) ∈ Subgroup.closure {s, t, w} := hP ▸ z.2
    refine mem_zpowers_of_mem_center hst hs1 hinf hw2' hws hwt hzP fun g hg => ?_
    rw [← hP] at hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)
  have : IsCyclic ↥C := by
    have h1 : IsCyclic ↥(C.subgroupOf (Subgroup.zpowers (s * t))) := inferInstance
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hCle).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hCle).surjective
  exact isCyclic_of_surjective
    ((Subgroup.center ↥(P : Subgroup ↥(StatedSU 3 3 K))).equivMapOfInjective _
      (P : Subgroup ↥(StatedSU 3 3 K)).subtype_injective).symm.toMonoidHom
    (MulEquiv.surjective _)

theorem cartanSingerCover_psu33 {X : Type} [Group X] [Finite X]
    (hX : StatedClassicalModel X .PSU 3 3 1) : CartanSingerCover X :=
  cartanSingerCover_of_isCyclic (isCyclic_center_sylow_psu33 hX)

end CFSG.Quasithin.H13.KG68
