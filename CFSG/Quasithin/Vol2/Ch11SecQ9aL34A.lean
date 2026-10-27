module

public import CFSG.Fischer.F4
public import CFSG.Assembly.OrderReductions.LinearOrders
import all CFSG.Fischer.F4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open CFSG.Fischer Matrix

@[expose] def s0Mat : Matrix (Fin 3) (Fin 3) F4 := !![0, 0, 1; 1, 0, F4.ω ^ 2; 0, 1, F4.ω ^ 2]

theorem s0Mat_det : s0Mat.det = 1 := by
  rw [Matrix.det_fin_three]
  decide

theorem s0Mat_pow_five : s0Mat ^ 5 = 1 := by
  decide

theorem s0Mat_ne_one : s0Mat ≠ 1 := by
  decide

theorem poly_check : ∀ a b c : F4,
    (a • (1 : Matrix (Fin 3) (Fin 3) F4) + b • s0Mat + c • s0Mat ^ 2) ^ 9 = 1 →
    (a • (1 : Matrix (Fin 3) (Fin 3) F4) + b • s0Mat + c • s0Mat ^ 2).det = 1 →
      b = 0 ∧ c = 0 := by
  simp only [Matrix.det_fin_three]
  decide

theorem poly_of_rel : ∀ a b c : F4,
    !![a, c, b + F4.ω ^ 2 * c; b, a + F4.ω ^ 2 * c, c + F4.ω ^ 2 * (b + F4.ω ^ 2 * c);
      c, b + F4.ω ^ 2 * c, a + F4.ω ^ 2 * c + F4.ω ^ 2 * (b + F4.ω ^ 2 * c)] =
        a • (1 : Matrix (Fin 3) (Fin 3) F4) + b • s0Mat + c • s0Mat ^ 2 := by
  decide

theorem eq_poly_of_commute {M : Matrix (Fin 3) (Fin 3) F4} (h : M * s0Mat = s0Mat * M) :
    M = M 0 0 • (1 : Matrix (Fin 3) (Fin 3) F4) + M 1 0 • s0Mat + M 2 0 • s0Mat ^ 2 := by
  have e : ∀ i j, (M * s0Mat) i j = (s0Mat * M) i j := fun i j => by rw [h]
  have e00 := e 0 0
  have e10 := e 1 0
  have e20 := e 2 0
  have e01 := e 0 1
  have e11 := e 1 1
  have e21 := e 2 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, s0Mat] at e00 e10 e20 e01 e11 e21
  conv_lhs => rw [Matrix.eta_fin_three M, e21, e11, e01, e20, e10, e00]
  exact poly_of_rel _ _ _

@[expose] def s0 : SpecialLinearGroup (Fin 3) F4 := ⟨s0Mat, s0Mat_det⟩

theorem s0_pow_five : s0 ^ 5 = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow]
  exact congrFun (congrFun s0Mat_pow_five i) j

theorem mem_center_of_commute_s0 {t : SpecialLinearGroup (Fin 3) F4} (hc : Commute s0 t)
    (ht : t ^ 9 = 1) : t ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F4) := by
  have hM : (t : Matrix (Fin 3) (Fin 3) F4) * s0Mat = s0Mat * t := by
    have := congrArg (fun g : SpecialLinearGroup (Fin 3) F4 => (g : Matrix (Fin 3) (Fin 3) F4))
      hc.eq
    exact this.symm
  have heq := eq_poly_of_commute hM
  have h9 : (t : Matrix (Fin 3) (Fin 3) F4) ^ 9 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, ht, Matrix.SpecialLinearGroup.coe_one]
  have hdet : (t : Matrix (Fin 3) (Fin 3) F4).det = 1 := t.2
  rw [heq] at h9 hdet
  obtain ⟨hb, hc0⟩ := poly_check _ _ _ h9 hdet
  rw [hb, hc0, zero_smul, zero_smul, add_zero, add_zero] at heq hdet
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨(t : Matrix (Fin 3) (Fin 3) F4) 0 0, ?_, ?_⟩
  · rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
    rw [Fintype.card_fin]
    exact hdet
  · conv_rhs => rw [heq]
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem s0_ne_one : s0 ≠ 1 := fun h =>
  s0Mat_ne_one (congrArg (fun g : SpecialLinearGroup (Fin 3) F4 =>
    (g : Matrix (Fin 3) (Fin 3) F4)) h)

theorem card_SL3F4 : Nat.card (SpecialLinearGroup (Fin 3) F4) = 60480 := by
  rw [CFSG.OrderReductions.LinearOrders.card_specialLinear F4 3 (by norm_num),
    Nat.card_eq_fintype_card, F4.card]
  decide

theorem eq_zpowers_of_sylow {u : SpecialLinearGroup (Fin 3) F4} (hu5 : u ^ 5 = 1) (hu1 : u ≠ 1)
    (P : Sylow 5 (SpecialLinearGroup (Fin 3) F4)) (hP : Subgroup.zpowers u ≤ P) :
    (P : Subgroup (SpecialLinearGroup (Fin 3) F4)) = Subgroup.zpowers u := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have ho : orderOf u = 5 := orderOf_eq_prime hu5 hu1
  have hzc : Nat.card (Subgroup.zpowers u) = 5 := by rw [Nat.card_zpowers, ho]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hdvd : Nat.card P ∣ 60480 := card_SL3F4 ▸ Subgroup.card_subgroup_dvd_card _
  have hk1 : k ≤ 1 := by
    by_contra hk2
    have h25 : 5 ^ 2 ∣ 60480 := (pow_dvd_pow 5 (by omega)).trans (hk ▸ hdvd)
    norm_num at h25
  have hle : Nat.card P ≤ Nat.card (Subgroup.zpowers u) := by
    rw [hk, hzc]
    calc 5 ^ k ≤ 5 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 5 := by norm_num
  exact (Subgroup.eq_of_le_of_card_ge hP hle).symm

theorem mem_center_of_commute {u t : SpecialLinearGroup (Fin 3) F4} (hu5 : u ^ 5 = 1)
    (hu1 : u ≠ 1) (hc : Commute u t) (ht : t ^ 9 = 1) :
    t ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F4) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hpg : ∀ v : SpecialLinearGroup (Fin 3) F4, v ^ 5 = 1 →
      IsPGroup 5 (Subgroup.zpowers v) := by
    rintro v hv ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, pow_one, Subgroup.coe_one, ← zpow_natCast, ← _root_.zpow_mul, mul_comm,
      _root_.zpow_mul, zpow_natCast, hv, _root_.one_zpow]
  obtain ⟨P, hP⟩ := (hpg u hu5).exists_le_sylow
  obtain ⟨Q, hQ⟩ := (hpg s0 s0_pow_five).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 3) F4) P Q
  have hPu := eq_zpowers_of_sylow hu5 hu1 P hP
  have hQs := eq_zpowers_of_sylow s0_pow_five s0_ne_one Q hQ
  have hs0Q : s0 ∈ (Q : Subgroup (SpecialLinearGroup (Fin 3) F4)) :=
    hQs ▸ Subgroup.mem_zpowers s0
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hPu] at hs0Q
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs0Q
  have hk' : s0 = g * u ^ k * g⁻¹ := by
    rw [hk, MulAut.smul_def, MulAut.conj_inv_apply]
    group
  have hs0 : Commute s0 (g * t * g⁻¹) := by
    rw [hk']
    change g * u ^ k * g⁻¹ * (g * t * g⁻¹) = g * t * g⁻¹ * (g * u ^ k * g⁻¹)
    calc g * u ^ k * g⁻¹ * (g * t * g⁻¹) = g * (u ^ k * t) * g⁻¹ := by group
      _ = g * (t * u ^ k) * g⁻¹ := by rw [(hc.zpow_left k).eq]
      _ = g * t * g⁻¹ * (g * u ^ k * g⁻¹) := by group
  have ht' : (g * t * g⁻¹) ^ 9 = 1 := by rw [conj_pow, ht, mul_one, mul_inv_cancel]
  have hz := mem_center_of_commute_s0 hs0 ht'
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro z
  have h1 := hz (g * z * g⁻¹)
  calc z * t = g⁻¹ * (g * z * g⁻¹ * (g * t * g⁻¹)) * g := by group
    _ = g⁻¹ * (g * t * g⁻¹ * (g * z * g⁻¹)) * g := by rw [h1]
    _ = t * z := by group

@[expose] noncomputable def slMapEquiv (n : ℕ) {K F : Type*} [Field K] [Field F] (e : K ≃+* F) :
    SpecialLinearGroup (Fin n) K ≃* SpecialLinearGroup (Fin n) F where
  toFun := SpecialLinearGroup.map e.toRingHom
  invFun := SpecialLinearGroup.map e.symm.toRingHom
  left_inv g := by
    ext i j
    simp [SpecialLinearGroup.map_apply_coe]
  right_inv g := by
    ext i j
    simp [SpecialLinearGroup.map_apply_coe]
  map_mul' := map_mul _

theorem mem_center_of_commute_of_card {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 4)
    {u t : SpecialLinearGroup (Fin 3) K} (hu5 : u ^ 5 = 1) (hu1 : u ≠ 1) (hc : Commute u t)
    (ht : t ^ 9 = 1) : t ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card F4 := by rw [F4.card, ← Nat.card_eq_fintype_card, hK]
  set e := slMapEquiv 3 (FiniteField.ringEquivOfCardEq hcard) with he
  have hz := mem_center_of_commute (u := e u) (t := e t) (by rw [← map_pow, hu5, map_one])
    (fun h1 => hu1 (e.injective (h1.trans (map_one e).symm))) (hc.map e)
    (by rw [← map_pow, ht, map_one])
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro z
  apply e.injective
  rw [map_mul, map_mul]
  exact hz (e z)

theorem orderOf_ne_fifteen {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 4)
    (x : ProjectiveSpecialLinearGroup (Fin 3) K) : orderOf x ≠ 15 := by
  intro hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hmk : ∀ k : ℕ, (QuotientGroup.mk g : ProjectiveSpecialLinearGroup (Fin 3) K) ^ k =
      QuotientGroup.mk (g ^ k) := fun k =>
    (map_pow (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 3) K))) g k).symm
  have h15 : g ^ 15 ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
    rw [← QuotientGroup.eq_one_iff, ← hmk, ← hx, pow_orderOf_eq_one]
  obtain ⟨r, hr, hgr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h15
  rw [Fintype.card_fin] at hr
  have h45 : g ^ 45 = 1 := by
    have h3 : (g ^ 15) ^ 3 = 1 := by
      ext i j
      rw [Matrix.SpecialLinearGroup.coe_pow, ← hgr, ← map_pow, hr, map_one]
      rfl
    rwa [← pow_mul] at h3
  have hu5 : (g ^ 9) ^ 5 = 1 := by rw [← pow_mul]; exact h45
  have ht9 : (g ^ 10) ^ 9 = 1 := by
    rw [← pow_mul, show 10 * 9 = 45 * 2 by norm_num, pow_mul, h45, one_pow]
  have hu1 : g ^ 9 ≠ 1 := by
    intro h1
    have h2 : (QuotientGroup.mk g : ProjectiveSpecialLinearGroup (Fin 3) K) ^ 9 = 1 := by
      rw [hmk, h1, QuotientGroup.mk_one]
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hx] at this
    norm_num at this
  have hz := mem_center_of_commute_of_card hK hu5 hu1 (Commute.pow_pow_self g 9 10) ht9
  have h2 : (QuotientGroup.mk g : ProjectiveSpecialLinearGroup (Fin 3) K) ^ 10 = 1 := by
    rw [hmk, QuotientGroup.eq_one_iff]
    exact hz
  have := orderOf_dvd_of_pow_eq_one h2
  rw [hx] at this
  norm_num at this

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
