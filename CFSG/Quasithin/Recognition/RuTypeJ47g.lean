module

public import CFSG.Quasithin.Recognition.RuTypeJ47e
public import CFSG.Quasithin.Recognition.RuTypeJ47Mat

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin

theorem quaternion_comm_eq' : ((QuaternionGroup.xa 0 : QuaternionGroup 2) * .a 1)⁻¹ *
    (.a 1 * .xa 0) = .a 2 := by decide

theorem quaternion_a_two_ne : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by decide

theorem quaternion_a_two_sq : (QuaternionGroup.a 2 : QuaternionGroup 2) ^ 2 = 1 := by decide

namespace RuDataM

variable {G : Type} [Group G] [Finite G] {M : RuDataM G}

namespace Conf47

variable (C : Conf47 M)

theorem z_inv_of_gen {i x : G} (hiz : i * M.z = M.z * i)
    (hib : i * C.b * i⁻¹ = C.b⁻¹) (hxP : x ∈ P5 C.b) (hxi : x * i = i * x) (hx5 : x ^ 5 = 1)
    (hx1 : x ≠ 1) (hgen : ∀ y ∈ P5 C.b, y * i = i * y → ∃ n : ℕ, x ^ n = y) :
    M.z * x * M.z⁻¹ = x⁻¹ := by
  refine inv_of_normalizes_zpowers M.z_mul_self hx5 ?_ ?_
  · have hzP : M.z * x * M.z⁻¹ ∈ P5 C.b := conj_mem_P5 (z_mem_G5 C.b_mem_H) hxP
    have hzi : M.z * x * M.z⁻¹ * i = i * (M.z * x * M.z⁻¹) := by
      have hzi' : M.z⁻¹ * i = i * M.z⁻¹ := by
        rw [M.z_inv47]; exact hiz.symm
      calc M.z * x * M.z⁻¹ * i = M.z * x * (M.z⁻¹ * i) := by group
        _ = M.z * (x * i) * M.z⁻¹ := by rw [hzi']; group
        _ = M.z * (i * x) * M.z⁻¹ := by rw [hxi]
        _ = (M.z * i) * x * M.z⁻¹ := by group
        _ = i * (M.z * x * M.z⁻¹) := by rw [← hiz]; group
    obtain ⟨n, hn⟩ := hgen _ hzP hzi
    exact ⟨n, hn.symm⟩
  · intro hzx
    have hxb : x ∈ Subgroup.zpowers C.b :=
      mem_zpowers_of_P5_comm_z C.b_mem_H C.orderOf_b hxP hzx.symm
    exact hx1 (eq_one_of_zpowers_comm_inv C.orderOf_b hib hxb hxi.symm)

theorem exists_bu :
    ∃ bu ∈ P5 C.b, bu * C.u = C.u * bu ∧ bu ^ 5 = 1 ∧ bu ≠ 1 ∧
      (∀ y ∈ P5 C.b, y * C.u = C.u * y → ∃ n : ℕ, bu ^ n = y) ∧ M.z * bu * M.z⁻¹ = bu⁻¹ := by
  have hK := card_P5_inf_centralizer C.b_mem_H C.orderOf_b C.isConj_u C.u_mul_self C.u_inv_b
  obtain ⟨x, hxK, hx5, hx1, hgen⟩ := exists_gen_of_card_five hK
  have hxP : x ∈ P5 C.b := (Subgroup.mem_inf.mp hxK).1
  have hxu : x * C.u = C.u * x :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hxK).2
  have hgen' : ∀ y ∈ P5 C.b, y * C.u = C.u * y → ∃ n : ℕ, x ^ n = y := fun y hy hyu =>
    hgen y (Subgroup.mem_inf.mpr ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr hyu⟩)
  exact ⟨x, hxP, hxu, hx5, hx1, hgen',
    C.z_inv_of_gen C.u_comm_z C.u_inv_b hxP hxu hx5 hx1 hgen'⟩

omit [Finite G] in
theorem conj_mem_T5 {τ : G} (hτ : τ ∈ M.T5 C.b) :
    C.u * τ * C.u⁻¹ ∈ M.T5 C.b := by
  obtain ⟨hτQ, hτb⟩ := hτ
  have hτb' : τ * C.b = C.b * τ := mem_G5.mp hτb
  refine ⟨M.conj_mem_Q C.u_mem_H hτQ, mem_G5.mpr ?_⟩
  have hub' : C.u * C.b⁻¹ = C.b * C.u := by
    calc C.u * C.b⁻¹ = (C.u * C.b * C.u⁻¹)⁻¹ * C.u := by group
      _ = C.b * C.u := by rw [C.u_inv_b, inv_inv]
  have hτb'' : τ * C.b⁻¹ = C.b⁻¹ * τ := (Commute.inv_right hτb').eq
  have hu1 : C.u⁻¹ * C.b * C.u = C.b⁻¹ := by
    rw [C.u_inv]
    calc C.u * C.b * C.u = C.u * C.b * C.u⁻¹ := by rw [C.u_inv]
      _ = C.b⁻¹ := C.u_inv_b
  calc C.u * τ * C.u⁻¹ * C.b = C.u * τ * (C.u⁻¹ * C.b * C.u) * C.u⁻¹ := by group
    _ = C.u * (τ * C.b⁻¹) * C.u⁻¹ := by rw [hu1]; group
    _ = C.u * (C.b⁻¹ * τ) * C.u⁻¹ := by rw [hτb'']
    _ = (C.u * C.b⁻¹) * τ * C.u⁻¹ := by group
    _ = C.b * (C.u * τ * C.u⁻¹) := by rw [hub']; group

theorem not_comm_T5 :
    ∃ τ ∈ M.T5 C.b, τ * C.u ≠ C.u * τ := by
  by_contra hall
  push Not at hall
  obtain ⟨bu, hbuP, hbuu, hbu5, hbu1, hgen, hzbu⟩ := C.exists_bu
  have hnorm : ∀ τ ∈ M.T5 C.b, ∃ n : ℕ, τ * bu * τ⁻¹ = bu ^ n := by
    intro τ hτ
    have hP : τ * bu * τ⁻¹ ∈ P5 C.b := conj_mem_P5 (M.T5_le_G5 hτ) hbuP
    have hτu := hall τ hτ
    have hu : τ * bu * τ⁻¹ * C.u = C.u * (τ * bu * τ⁻¹) := by
      have hτu' : τ⁻¹ * C.u = C.u * τ⁻¹ := by
        calc τ⁻¹ * C.u = τ⁻¹ * (C.u * τ) * τ⁻¹ := by group
          _ = τ⁻¹ * (τ * C.u) * τ⁻¹ := by rw [hτu]
          _ = C.u * τ⁻¹ := by group
      calc τ * bu * τ⁻¹ * C.u = τ * bu * (τ⁻¹ * C.u) := by group
        _ = τ * (bu * C.u) * τ⁻¹ := by rw [hτu']; group
        _ = τ * (C.u * bu) * τ⁻¹ := by rw [hbuu]
        _ = (τ * C.u) * bu * τ⁻¹ := by group
        _ = C.u * (τ * bu * τ⁻¹) := by rw [hτu]; group
    obtain ⟨n, hn⟩ := hgen _ hP hu
    exact ⟨n, hn.symm⟩
  obtain ⟨e⟩ := T5_quaternion C.b_mem_H C.orderOf_b
  set q1 : M.T5 C.b := e.symm (.a 1) with hq1
  set q2 : M.T5 C.b := e.symm (.xa 0) with hq2
  have hz2 : ((e.symm (.a 2) : M.T5 C.b) : G) = M.z := by
    refine eq_z_of_T5 C.b_mem_H C.orderOf_b (e.symm (.a 2)).2 ?_ ?_
    · have h2 := congrArg Subtype.val (congrArg e.symm quaternion_a_two_sq)
      rwa [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one] at h2
    · intro h0
      apply quaternion_a_two_ne
      have h3 : e.symm (.a 2) = 1 := Subtype.ext (by rw [Subgroup.coe_one]; exact h0)
      rw [← map_one e.symm] at h3
      exact e.symm.injective h3
  have hq : (q2 * q1)⁻¹ * (q1 * q2) = e.symm (.a 2) := by
    apply e.injective
    rw [map_mul, map_inv, map_mul, map_mul, hq1, hq2, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact quaternion_comm_eq'
  have hzc : ((q2 : G) * q1)⁻¹ * ((q1 : G) * q2) = M.z := by
    rw [← hz2, ← hq]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  obtain ⟨n1, hn1⟩ := hnorm q1 q1.2
  obtain ⟨n2, hn2⟩ := hnorm q2 q2.2
  have hX : ((q1 : G) * q2) * bu * ((q1 : G) * q2)⁻¹ = bu ^ (n1 * n2) := by
    calc ((q1 : G) * q2) * bu * ((q1 : G) * q2)⁻¹ = (q1 : G) * ((q2 : G) * bu * (q2 : G)⁻¹) *
          (q1 : G)⁻¹ := by group
      _ = (q1 : G) * bu ^ n2 * (q1 : G)⁻¹ := by rw [hn2]
      _ = ((q1 : G) * bu * (q1 : G)⁻¹) ^ n2 := conj_pow.symm
      _ = bu ^ (n1 * n2) := by rw [hn1, ← pow_mul]
  have hY : ((q2 : G) * q1) * bu * ((q2 : G) * q1)⁻¹ = bu ^ (n1 * n2) := by
    calc ((q2 : G) * q1) * bu * ((q2 : G) * q1)⁻¹ = (q2 : G) * ((q1 : G) * bu * (q1 : G)⁻¹) *
          (q2 : G)⁻¹ := by group
      _ = (q2 : G) * bu ^ n1 * (q2 : G)⁻¹ := by rw [hn1]
      _ = ((q2 : G) * bu * (q2 : G)⁻¹) ^ n1 := conj_pow.symm
      _ = bu ^ (n1 * n2) := by rw [hn2, ← pow_mul, mul_comm]
  have hzbu' : M.z * bu * M.z⁻¹ = bu := by
    rw [← hzc]
    calc ((q2 : G) * q1)⁻¹ * ((q1 : G) * q2) * bu * (((q2 : G) * q1)⁻¹ * ((q1 : G) * q2))⁻¹
        = ((q2 : G) * q1)⁻¹ * (((q1 : G) * q2) * bu * ((q1 : G) * q2)⁻¹) * ((q2 : G) * q1) := by
          group
      _ = ((q2 : G) * q1)⁻¹ * (((q2 : G) * q1) * bu * ((q2 : G) * q1)⁻¹) * ((q2 : G) * q1) := by
          rw [hX, hY]
      _ = bu := by group
  rw [hzbu] at hzbu'
  have h2 : bu ^ 2 = 1 := by
    rw [pow_two]
    calc bu * bu = bu * bu⁻¹ := by rw [hzbu']
      _ = 1 := mul_inv_cancel _
  apply hbu1
  have := (pow_gcd_eq_one (a := bu)).mpr ⟨h2, hbu5⟩
  rwa [show Nat.gcd 2 5 = 1 by norm_num, pow_one] at this

theorem exists_tau :
    ∃ τ ∈ M.T5 C.b, τ * C.u * τ⁻¹ = C.u * M.z := by
  obtain ⟨τ0, hτ0, hne⟩ := C.not_comm_T5
  set x := C.u * τ0 * C.u⁻¹ * τ0⁻¹ with hx
  have hxT : x ∈ M.T5 C.b := mul_mem (C.conj_mem_T5 hτ0) (inv_mem hτ0)
  have hx1 : x ≠ 1 := by
    intro h
    apply hne
    have h' : C.u * τ0 * C.u⁻¹ = τ0 := by
      calc C.u * τ0 * C.u⁻¹ = x * τ0 := by rw [hx]; group
        _ = τ0 := by rw [h, one_mul]
    calc τ0 * C.u = (C.u * τ0 * C.u⁻¹) * C.u := by rw [h']
      _ = C.u * τ0 := by group
  have huxu : C.u * x * C.u⁻¹ = x⁻¹ := by
    rw [hx]
    calc C.u * (C.u * τ0 * C.u⁻¹ * τ0⁻¹) * C.u⁻¹ = (C.u * C.u) * τ0 * C.u⁻¹ * τ0⁻¹ * C.u⁻¹ := by
          group
      _ = τ0 * C.u * τ0⁻¹ * C.u := by rw [C.u_mul_self, one_mul, C.u_inv]
      _ = (C.u * τ0 * C.u⁻¹ * τ0⁻¹)⁻¹ := by simp only [mul_inv_rev, inv_inv, C.u_inv, mul_assoc]
  have hw : ∃ w ∈ M.T5 C.b, C.u * w * C.u⁻¹ = w * M.z := by
    by_cases hxz : x = M.z
    · refine ⟨τ0, hτ0, ?_⟩
      have hzc : M.z * τ0 = τ0 * M.z :=
        M.mem_H_iff_comm.mp (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hτ0.1)
      calc C.u * τ0 * C.u⁻¹ = x * τ0 := by rw [hx]; group
        _ = τ0 * M.z := by rw [hxz, hzc]
    · have hx4 : x ^ 4 = 1 := pow_four_T5 C.b_mem_H C.orderOf_b hxT
      have hx2 : x ^ 2 ≠ 1 := fun h => hxz (eq_z_of_T5 C.b_mem_H C.orderOf_b hxT h hx1)
      have hx2z : x ^ 2 = M.z := by
        refine eq_z_of_T5 C.b_mem_H C.orderOf_b (pow_mem hxT 2) ?_ hx2
        rw [← pow_mul]
        exact hx4
      refine ⟨x, hxT, ?_⟩
      rw [huxu, ← hx2z]
      calc x⁻¹ = x ^ 4 * x⁻¹ := by rw [hx4, one_mul]
        _ = x * x ^ 2 := by group
  obtain ⟨w, hwT, hwz⟩ := hw
  refine ⟨w⁻¹, inv_mem hwT, ?_⟩
  have hzw : M.z * w = w * M.z :=
    M.mem_H_iff_comm.mp (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hwT.1)
  calc w⁻¹ * C.u * w⁻¹⁻¹ = w⁻¹ * (C.u * w * C.u⁻¹) * C.u := by group
    _ = w⁻¹ * (w * M.z) * C.u := by rw [hwz]
    _ = M.z * C.u := by group
    _ = C.u * M.z := C.u_comm_z.symm

theorem isConj_t :
    IsConj M.z C.t := by
  obtain ⟨τ, -, hτ⟩ := C.exists_tau
  exact C.isConj_u.trans (isConj_iff.mpr ⟨τ, hτ⟩)

theorem t_comm_z : C.t * M.z = M.z * C.t := by
  show C.u * M.z * M.z = M.z * (C.u * M.z)
  rw [← mul_assoc, ← C.u_comm_z]

theorem exists_bt :
    ∃ bt ∈ P5 C.b, bt * C.t = C.t * bt ∧ bt ^ 5 = 1 ∧ bt ≠ 1 ∧
      (∀ y ∈ P5 C.b, y * C.t = C.t * y → ∃ n : ℕ, bt ^ n = y) ∧ M.z * bt * M.z⁻¹ = bt⁻¹ ∧
      C.u * bt * C.u⁻¹ = bt⁻¹ := by
  have hK := card_P5_inf_centralizer C.b_mem_H C.orderOf_b C.isConj_t C.t_mul_self C.t_inv_b
  obtain ⟨x, hxK, hx5, hx1, hgen⟩ := exists_gen_of_card_five hK
  have hxP : x ∈ P5 C.b := (Subgroup.mem_inf.mp hxK).1
  have hxt : x * C.t = C.t * x :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hxK).2
  have hgen' : ∀ y ∈ P5 C.b, y * C.t = C.t * y → ∃ n : ℕ, x ^ n = y := fun y hy hyt =>
    hgen y (Subgroup.mem_inf.mpr ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr hyt⟩)
  have hzx := C.z_inv_of_gen C.t_comm_z C.t_inv_b hxP hxt hx5 hx1 hgen'
  refine ⟨x, hxP, hxt, hx5, hx1, hgen', hzx, ?_⟩
  have hu : C.u = C.t * M.z := by
    show C.u = C.u * M.z * M.z
    rw [mul_assoc, M.z_mul_self, mul_one]
  rw [hu]
  calc C.t * M.z * x * (C.t * M.z)⁻¹ = C.t * (M.z * x * M.z⁻¹) * C.t⁻¹ := by group
    _ = C.t * x⁻¹ * C.t⁻¹ := by rw [hzx]
    _ = (C.t * x * C.t⁻¹)⁻¹ := by group
    _ = x⁻¹ := by rw [← hxt]; group

theorem comm_bu_bt
    {bu bt : G} (hbuP : bu ∈ P5 C.b) (hbuu : bu * C.u = C.u * bu) (hbu5 : bu ^ 5 = 1)
    (hbu1 : bu ≠ 1) (hbtP : bt ∈ P5 C.b) (hbtt : bt * C.t = C.t * bt) (hbt5 : bt ^ 5 = 1)
    (hbt1 : bt ≠ 1) (hubt : C.u * bt * C.u⁻¹ = bt⁻¹) :
    bu * bt * bu⁻¹ * bt⁻¹ ∈ Subgroup.zpowers C.b ∧ bu * bt * bu⁻¹ * bt⁻¹ ≠ 1 := by
  refine ⟨comm_mem_zpowers_P5 C.b_mem_H C.orderOf_b hbuP hbtP, fun h1 => ?_⟩
  have hcomm : Commute bt bu := by
    have h : bu * bt = bt * bu := by
      calc bu * bt = (bu * bt * bu⁻¹ * bt⁻¹) * (bt * bu) := by group
        _ = bt * bu := by rw [h1, one_mul]
    exact h.symm
  have hb1 : C.b ≠ 1 := fun h => by
    have := C.orderOf_b
    rw [h, orderOf_one] at this
    norm_num at this
  exact false_of_signs (card_P5_eq_125 C.b_mem_H C.orderOf_b) (not_comm_P5 C.b_mem_H C.orderOf_b)
    (b_mem_P5 C.orderOf_b) hbtP hbuP C.b_pow_five hbt5 hbu5 hb1 hbt1 hbu1
    ((comm_b_P5 hbtP).symm) ((comm_b_P5 hbuP).symm) hcomm C.u_inv_b hubt
    (by rw [← hbuu]; group) C.t_inv_b (by rw [← hbtt]; group)

end Conf47

end RuDataM

end CFSG.Quasithin.RuType
