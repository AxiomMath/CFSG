module

public import CFSG.Quasithin.H13.GoldschmidtU43EQSylow
public import CFSG.CharacterTheory.Semidihedral.Local.QuaternionNormalForm
public import CFSG.Quasithin.H13.GoldschmidtU43EQCoset

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

theorem u43_card_quaternion_two : Nat.card (QuaternionGroup 2) = 8 := by
  simp [Nat.card_eq_fintype_card, QuaternionGroup.card]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)

omit [Finite G] in
theorem exists_quaternion_closure :
    Nonempty (↥(Subgroup.closure ({((S.a₂ : ↥(Hz z)) : G), ((S.b₂ : ↥(Hz z)) : G)} : Set G)) ≃*
      QuaternionGroup 2) := by
  set x : G := ((S.a₂ : ↥(Hz z)) : G) with hx
  set y : G := ((S.b₂ : ↥(Hz z)) : G) with hy
  set K := Subgroup.closure ({x, y} : Set G) with hK
  have hxK : x ∈ K := Subgroup.subset_closure (by simp)
  have hyK : y ∈ K := Subgroup.subset_closure (by simp)
  have hgen : Subgroup.closure ({⟨x, hxK⟩, ⟨y, hyK⟩} : Set K) = ⊤ := by
    convert Subgroup.closure_closure_coe_preimage (k := ({x, y} : Set G)) using 2
    ext g
    simp [Subtype.ext_iff]
  have h4 : orderOf x = 4 := (Subgroup.orderOf_coe S.a₂).trans S.orderOf_a₂
  have hord : orderOf (⟨x, hxK⟩ : K) = 2 * 2 := by
    have h := Subgroup.orderOf_mk x hxK
    omega
  have hnot : (⟨y, hyK⟩ : K) ∉ Subgroup.zpowers (⟨x, hxK⟩ : K) := by
    intro hmem
    apply S.b₂_not_mem_zpowers
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  have hxz : x * x = z := congrArg Subtype.val S.a₂_sq
  have hyz : y * y = z := congrArg Subtype.val S.b₂_sq
  have hy2 : (⟨y, hyK⟩ : K) ^ 2 = (⟨x, hxK⟩ : K) ^ 2 := Subtype.ext (by
    show y ^ 2 = x ^ 2
    rw [pow_two, pow_two, hxz, hyz])
  have hyx : (⟨y, hyK⟩ : K) * ⟨x, hxK⟩ * (⟨y, hyK⟩ : K)⁻¹ = (⟨x, hxK⟩ : K)⁻¹ :=
    Subtype.ext (by simpa using congrArg Subtype.val S.b₂_conj_a₂)
  obtain ⟨⟨e, -⟩, -⟩ := CFSG.Semidihedral.Local.quaternion_normal_form_isomorphism (m := 2)
    (by norm_num) hgen hord hnot hy2 hyx
  exact ⟨e.symm⟩

theorem Yg_eq_closure (hAU : (S.A : G) ∈ Uz z) :
    S.Yg = Subgroup.closure ({((S.a₂ : ↥(Hz z)) : G), ((S.b₂ : ↥(Hz z)) : G)} : Set G) := by
  have hle : Subgroup.closure
      ({((S.a₂ : ↥(Hz z)) : G), ((S.b₂ : ↥(Hz z)) : G)} : Set G) ≤ S.Yg := by
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact ⟨S.a₂_mem_U hAU, S.a₂_mem_Cg1⟩
    · exact ⟨S.b₂_mem_U hAU, S.b₂_mem_Cg1⟩
  obtain ⟨e⟩ := S.exists_quaternion_closure
  have hcard : Nat.card (Subgroup.closure
      ({((S.a₂ : ↥(Hz z)) : G), ((S.b₂ : ↥(Hz z)) : G)} : Set G)) = 8 := by
    rw [Nat.card_congr e.toEquiv, u43_card_quaternion_two]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard]; exact S.card_Yg_le)).symm

theorem card_Yg_eq (hAU : (S.A : G) ∈ Uz z) : Nat.card S.Yg = 8 := by
  obtain ⟨e⟩ := S.exists_quaternion_closure
  rw [S.Yg_eq_closure hAU, Nat.card_congr e.toEquiv, u43_card_quaternion_two]

theorem equiv_Yg (hAU : (S.A : G) ∈ Uz z) : Nonempty (↥S.Yg ≃* QuaternionGroup 2) := by
  obtain ⟨e⟩ := S.exists_quaternion_closure
  exact ⟨(MulEquiv.subgroupCongr (S.Yg_eq_closure hAU)).trans e⟩

omit [Finite G] in
theorem z_mem_Yg : z ∈ S.Yg :=
  ⟨S.hyp.z_mem, Subgroup.mem_centralizer_singleton_iff.mpr (z_comm_H S.σ₁).symm⟩

omit [Finite G] in
theorem z_mem_Cg1 : z ∈ S.Cg1 := S.z_mem_Yg.2

theorem Yg_eq_z_of_sq (hAU : (S.A : G) ∈ Uz z) {y : G} (hy : y ∈ S.Yg) (hy2 : y * y = 1)
    (hy1 : y ≠ 1) : y = z := by
  obtain ⟨e⟩ := S.equiv_Yg hAU
  have hzY : z ∈ S.Yg := S.z_mem_Yg
  have hy' : orderOf (⟨y, hy⟩ : ↥S.Yg) = 2 :=
    orderOf_eq_prime (by rw [← pow_two] at hy2; exact Subtype.ext hy2)
      (fun h => hy1 (congrArg Subtype.val h))
  have hz' : orderOf (⟨z, hzY⟩ : ↥S.Yg) = 2 :=
    orderOf_eq_prime (Subtype.ext (by simpa [pow_two] using S.hyp.sq_z))
      (fun h => S.hyp.z_ne_one (congrArg Subtype.val h))
  exact congrArg Subtype.val
    (CFSG.BrauerSuzuki.Helpers.unique_order_two_of_mulEquiv_quaternion e hy' hz')

theorem exists_sylow_Yg (hAU : (S.A : G) ∈ Uz z) :
    ∃ P : Sylow 2 ↥S.Cg1, (P : Subgroup ↥S.Cg1) = S.Yg.subgroupOf S.Cg1 := by
  have hle : S.Yg ≤ S.Cg1 := inf_le_right
  have hY2 : IsPGroup 2 (S.Yg.subgroupOf S.Cg1) := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    simp [S.card_Yg_eq hAU]
  refine u43_exists_sylow_eq hY2 ?_
  intro x hxN hxP
  have hzC : (⟨z, S.z_mem_Cg1⟩ : ↥S.Cg1) ∈ S.Yg.subgroupOf S.Cg1 := S.z_mem_Yg
  have hconj : (x : G) * z * (x : G)⁻¹ ∈ S.Yg :=
    (Subgroup.mem_normalizer_iff.mp hxN ⟨z, S.z_mem_Cg1⟩).mp hzC
  have hw2 : ((x : G) * z * (x : G)⁻¹) * ((x : G) * z * (x : G)⁻¹) = 1 := by
    calc ((x : G) * z * (x : G)⁻¹) * ((x : G) * z * (x : G)⁻¹) = (x : G) * (z * z) * (x : G)⁻¹ := by
          group
      _ = 1 := by rw [S.hyp.sq_z]; group
  have hw1 : (x : G) * z * (x : G)⁻¹ ≠ 1 := by
    intro h
    apply S.hyp.z_ne_one
    calc z = (x : G)⁻¹ * ((x : G) * z * (x : G)⁻¹) * x := by group
      _ = 1 := by rw [h]; group
  have hwz := S.Yg_eq_z_of_sq hAU hconj hw2 hw1
  have hxH : (x : G) ∈ Hz z := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (x : G) * z = ((x : G) * z * (x : G)⁻¹) * x := by group
      _ = z * x := by rw [hwz]
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hxP) ⟨x, Subgroup.mem_zpowers x⟩
  rw [Subgroup.orderOf_mk] at hm
  have hxm : x ^ (2 ^ m) = 1 := by
    rw [← hm]
    exact pow_orderOf_eq_one x
  have hxmG : (x : G) ^ (2 ^ m) = 1 := by
    have := congrArg Subtype.val hxm
    simpa using this
  exact S.mem_Yg_of_pow_G hxH x.2 hxmG

theorem frattini_Cg1 (hAU : (S.A : G) ∈ Uz z) (g : ↥S.Cg1) :
    ∃ c ∈ Subgroup.centralizer ({(⟨z, S.z_mem_Cg1⟩ : ↥S.Cg1)} : Set ↥S.Cg1),
      ∃ k ∈ CFSG.oddCore ↥S.Cg1, g = c * k := by
  obtain ⟨P, hP⟩ := S.exists_sylow_Yg hAU
  have hle : S.Yg ≤ S.Cg1 := inf_le_right
  have hquat : Nonempty ((P : Subgroup ↥S.Cg1) ≃* QuaternionGroup 2) := by
    obtain ⟨e⟩ := S.equiv_Yg hAU
    rw [hP]
    exact ⟨(Subgroup.subgroupOfEquivOfLe hle).trans e⟩
  have hzP : (⟨z, S.z_mem_Cg1⟩ : ↥S.Cg1) ∈ (P : Subgroup ↥S.Cg1) := by
    rw [hP]
    exact S.z_mem_Yg
  have hz : orderOf (⟨z, S.z_mem_Cg1⟩ : ↥S.Cg1) = 2 :=
    orderOf_eq_prime (Subtype.ext (by simpa [pow_two] using S.hyp.sq_z))
      (fun h => S.hyp.z_ne_one (congrArg Subtype.val h))
  exact u43_frattini_quaternion P hquat hzP hz g

end JWSetup

end CFSG.Quasithin.H13.U43
