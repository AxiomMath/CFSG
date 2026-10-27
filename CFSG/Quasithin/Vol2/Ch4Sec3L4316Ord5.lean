module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aL34A
import all CFSG.Fischer.F4

public section

namespace CFSG.Quasithin.H13.Ch4.L4316

open CFSG.Fischer Matrix CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

theorem poly_check_two : ∀ a b c : F4,
    (a • (1 : Matrix (Fin 3) (Fin 3) F4) + b • s0Mat + c • s0Mat ^ 2) ^ 2 = 1 →
    (a • (1 : Matrix (Fin 3) (Fin 3) F4) + b • s0Mat + c • s0Mat ^ 2).det = 1 →
      a = 1 ∧ b = 0 ∧ c = 0 := by
  simp only [Matrix.det_fin_three]
  decide

theorem eq_one_of_commute_s0 {t : SpecialLinearGroup (Fin 3) F4} (hc : Commute s0 t)
    (ht : t ^ 2 = 1) : t = 1 := by
  have hM : (t : Matrix (Fin 3) (Fin 3) F4) * s0Mat = s0Mat * t := by
    have := congrArg (fun g : SpecialLinearGroup (Fin 3) F4 => (g : Matrix (Fin 3) (Fin 3) F4))
      hc.eq
    exact this.symm
  have heq := eq_poly_of_commute hM
  have h2 : (t : Matrix (Fin 3) (Fin 3) F4) ^ 2 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, ht, Matrix.SpecialLinearGroup.coe_one]
  have hdet : (t : Matrix (Fin 3) (Fin 3) F4).det = 1 := t.2
  rw [heq] at h2 hdet
  obtain ⟨ha, hb, hc0⟩ := poly_check_two _ _ _ h2 hdet
  refine Subtype.ext ?_
  rw [heq, ha, hb, hc0, zero_smul, zero_smul, add_zero, add_zero, one_smul,
    Matrix.SpecialLinearGroup.coe_one]

theorem eq_one_of_commute_ord5 {u t : SpecialLinearGroup (Fin 3) F4} (hu5 : u ^ 5 = 1)
    (hu1 : u ≠ 1) (hc : Commute u t) (ht : t ^ 2 = 1) : t = 1 := by
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
  have ht' : (g * t * g⁻¹) ^ 2 = 1 := by rw [conj_pow, ht, mul_one, mul_inv_cancel]
  have h1 := eq_one_of_commute_s0 hs0 ht'
  calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
    _ = 1 := by rw [h1, mul_one, inv_mul_cancel]

theorem eq_one_of_commute_ord5_of_card {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 4)
    {u t : SpecialLinearGroup (Fin 3) K} (hu5 : u ^ 5 = 1) (hu1 : u ≠ 1) (hc : Commute u t)
    (ht : t ^ 2 = 1) : t = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card F4 := by rw [F4.card, ← Nat.card_eq_fintype_card, hK]
  set e := slMapEquiv 3 (FiniteField.ringEquivOfCardEq hcard) with he
  have h1 := eq_one_of_commute_ord5 (u := e u) (t := e t) (by rw [← map_pow, hu5, map_one])
    (fun h1 => hu1 (e.injective (h1.trans (map_one e).symm))) (hc.map e)
    (by rw [← map_pow, ht, map_one])
  exact e.injective (h1.trans (map_one e).symm)

theorem units_pow_three {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 4) (x : Kˣ) :
    x ^ 3 = 1 := by
  have : Fintype K := Fintype.ofFinite K
  classical
  have h3 : Fintype.card Kˣ = 3 := by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  rw [← h3]
  exact pow_card_eq_one

theorem exists_lift_pow_eq_one {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 4)
    {n : ℕ} (hn : n % 3 = 1 ∨ n % 3 = 2) {g : GL (Fin 3) K}
    (hg : g ^ n ∈ Subgroup.center (GL (Fin 3) K)) :
    ∃ g' : GL (Fin 3) K, (QuotientGroup.mk g' : GL (Fin 3) K ⧸ Subgroup.center (GL (Fin 3) K)) =
      QuotientGroup.mk g ∧ g' ^ n = 1 ∧ GeneralLinearGroup.det g' = 1 := by
  rw [GeneralLinearGroup.center_eq_range_scalar] at hg
  obtain ⟨c, hc⟩ := hg
  have hc3 := units_pow_three hK c
  obtain ⟨ν, hν⟩ : ∃ ν : Kˣ, ν ^ n * c = 1 := by
    rcases hn with h | h
    · refine ⟨c⁻¹, ?_⟩
      obtain ⟨q, hq⟩ : ∃ q, n = 3 * q + 1 := ⟨n / 3, by omega⟩
      rw [hq, pow_succ, pow_mul, inv_pow, hc3, inv_one, one_pow, one_mul, inv_mul_cancel]
    · refine ⟨c, ?_⟩
      obtain ⟨q, hq⟩ : ∃ q, n = 3 * q + 2 := ⟨n / 3, by omega⟩
      rw [hq, pow_add, pow_mul, hc3, one_pow, one_mul, ← pow_succ, hc3]
  have hsc : GeneralLinearGroup.scalar (Fin 3) ν ∈ Subgroup.center (GL (Fin 3) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨ν, rfl⟩
  set g' := GeneralLinearGroup.scalar (Fin 3) ν * g with hg'
  have hcomm : ∀ k : ℕ, g' ^ k = GeneralLinearGroup.scalar (Fin 3) ν ^ k * g ^ k := fun k =>
    (Commute.mul_pow ((Subgroup.mem_center_iff.mp hsc g).symm) k)
  have hpow : g' ^ n = 1 := by
    rw [hcomm, ← hc, ← map_pow, ← map_mul, hν, map_one]
  refine ⟨g', ?_, hpow, ?_⟩
  · rw [QuotientGroup.eq]
    have : g'⁻¹ * g = (GeneralLinearGroup.scalar (Fin 3) ν)⁻¹ := by
      rw [hg', _root_.mul_inv_rev, mul_assoc,
        ← Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hsc) g, inv_mul_cancel_left]
    rw [this]
    exact Subgroup.inv_mem _ hsc
  ·
    have h1 : GeneralLinearGroup.det g' ^ n = 1 := by rw [← map_pow, hpow, map_one]
    have h2 := units_pow_three hK (GeneralLinearGroup.det g')
    set d := GeneralLinearGroup.det g'
    rcases hn with h | h
    · obtain ⟨q, hq⟩ : ∃ q, n = 3 * q + 1 := ⟨n / 3, by omega⟩
      rw [hq, pow_succ, pow_mul, h2, one_pow, one_mul] at h1
      exact h1
    · obtain ⟨q, hq⟩ : ∃ q, n = 3 * q + 2 := ⟨n / 3, by omega⟩
      rw [hq, pow_add, pow_mul, h2, one_pow, one_mul] at h1
      calc d = d ^ 3 * (d ^ 2)⁻¹ := by group
        _ = 1 := by rw [h2, h1, inv_one, mul_one]

theorem pgl_eq_one_of_commute_ord5 {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 4)
    {t z : GL (Fin 3) K ⧸ Subgroup.center (GL (Fin 3) K)} (hc : t * z = z * t) (ht : t ^ 2 = 1)
    (hz5 : z ^ 5 = 1) (hz1 : z ≠ 1) : t = 1 := by
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective t
  obtain ⟨h₀, rfl⟩ := QuotientGroup.mk_surjective z
  have hg₀ : g₀ ^ 2 ∈ Subgroup.center (GL (Fin 3) K) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ht]
  have hh₀ : h₀ ^ 5 ∈ Subgroup.center (GL (Fin 3) K) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hz5]
  obtain ⟨g, hgm, hg2, hgd⟩ := exists_lift_pow_eq_one hK (Or.inr rfl) hg₀
  obtain ⟨h, hhm, hh5, hhd⟩ := exists_lift_pow_eq_one hK (Or.inr rfl) hh₀
  rw [← hgm, ← hhm] at hc
  rw [← hhm] at hz1
  rw [← hgm]
  have hcm : (g * h)⁻¹ * (h * g) ∈ Subgroup.center (GL (Fin 3) K) := by
    rw [← QuotientGroup.eq, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact hc
  set s := (g * h)⁻¹ * (h * g) with hs
  have hsc := Subgroup.mem_center_iff.mp hcm
  have e1 : h * g = g * h * s := by rw [hs]; group
  have hss : s * s = 1 := by
    have e2 : h * g * h⁻¹ = g * s := by
      rw [e1, mul_assoc g h s, hsc h, ← mul_assoc]
      group
    have e3 : h * (g * g) * h⁻¹ = g * s * (g * s) := by
      calc h * (g * g) * h⁻¹ = (h * g * h⁻¹) * (h * g * h⁻¹) := by group
        _ = g * s * (g * s) := by rw [e2]
    have hgg : g * g = 1 := by rw [← pow_two, hg2]
    rw [hgg, mul_one, mul_inv_cancel, mul_assoc g s (g * s), ← mul_assoc s g s, (hsc g).symm,
      mul_assoc, ← mul_assoc g g, hgg, one_mul] at e3
    exact e3.symm
  have hs1 : s = 1 := by
    have hs3 : s ^ 3 = 1 := by
      rw [GeneralLinearGroup.center_eq_range_scalar] at hcm
      obtain ⟨c, hc'⟩ := hcm
      rw [← hc', ← map_pow, units_pow_three hK c, map_one]
    calc s = s ^ 3 * (s * s)⁻¹ := by group
      _ = 1 := by rw [hs3, hss, inv_one, mul_one]
  have hgh : h * g = g * h := by rw [e1, hs1, mul_one]
  let g' : SpecialLinearGroup (Fin 3) K :=
    ⟨g, by rw [← GeneralLinearGroup.val_det_apply, hgd, Units.val_one]⟩
  let h' : SpecialLinearGroup (Fin 3) K :=
    ⟨h, by rw [← GeneralLinearGroup.val_det_apply, hhd, Units.val_one]⟩
  have hcomm : Commute h' g' := by
    refine Subtype.ext ?_
    have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hgh
    simpa using this
  have hh'5 : h' ^ 5 = 1 := by
    refine Subtype.ext ?_
    have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hh5
    simpa [Matrix.SpecialLinearGroup.coe_pow] using this
  have hh'1 : h' ≠ 1 := by
    intro h1
    apply hz1
    have : h = 1 := by
      refine Units.ext ?_
      rw [Units.val_one]
      exact (congrArg (fun x : SpecialLinearGroup (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K))
        h1).trans Matrix.SpecialLinearGroup.coe_one
    rw [this, QuotientGroup.mk_one]
  have hg'2 : g' ^ 2 = 1 := by
    refine Subtype.ext ?_
    have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hg2
    simpa [Matrix.SpecialLinearGroup.coe_pow] using this
  have hg'1 := eq_one_of_commute_ord5_of_card hK hh'5 hh'1 hcomm hg'2
  have hg1 : g = 1 := by
    refine Units.ext ?_
    rw [Units.val_one]
    exact (congrArg (fun x : SpecialLinearGroup (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K))
      hg'1).trans Matrix.SpecialLinearGroup.coe_one
  rw [hg1, QuotientGroup.mk_one]

theorem pgl_eq_one_of_commute_ord5_of_two_pow {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 4) {t z : GL (Fin 3) K ⧸ Subgroup.center (GL (Fin 3) K)}
    (hc : t * z = z * t) {e : ℕ} (ht : t ^ (2 ^ e) = 1) (hz5 : z ^ 5 = 1) (hz1 : z ≠ 1) :
    t = 1 := by
  induction e generalizing t with
  | zero => simpa using ht
  | succ e ih =>
    have hc2 : t ^ 2 * z = z * t ^ 2 := by
      rw [pow_two, mul_assoc, hc, ← mul_assoc, hc, mul_assoc]
    have ht2 : (t ^ 2) ^ (2 ^ e) = 1 := by rw [← pow_mul, ← pow_succ']; exact ht
    exact pgl_eq_one_of_commute_ord5 hK hc (ih hc2 ht2) hz5 hz1

end CFSG.Quasithin.H13.Ch4.L4316
