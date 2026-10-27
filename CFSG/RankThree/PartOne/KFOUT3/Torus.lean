module

public import CFSG.RankThree.PartOne.KFOUT3.Root
public import CFSG.RankThree.PartOne.KF.UnitaryTorus
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG.RankThree.PartOne.KFU (torusSU diagU torusElt prod_torusElt torusElt_mem mem_torusSU_iff
  diagU_val diagU_injective)

variable {K : Type} [Field K]

@[expose] def diagSL (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1) : SL3 K :=
  ⟨Matrix.diagonal fun i => (v i : K), by
    rw [Matrix.det_diagonal, ← Units.coe_prod, hv, Units.val_one]⟩

theorem coe_diagSL (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1) :
    ((diagSL v hv : SL3 K) : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal fun i => (v i : K) :=
  rfl

theorem diagSL_apply (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1) (a b : Fin 3) :
    ent (diagSL v hv) a b = if a = b then (v a : K) else 0 := by
  simp [diagSL, ent, Matrix.diagonal_apply]

theorem ent_diagSL_mul (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1) (x : SL3 K) (a b : Fin 3) :
    ent (diagSL v hv * x) a b = (v a : K) * ent x a b := by
  simp only [ent, Matrix.SpecialLinearGroup.coe_mul, coe_diagSL, Matrix.diagonal_mul]

theorem ent_mul_diagSL (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1) (x : SL3 K) (a b : Fin 3) :
    ent (x * diagSL v hv) a b = ent x a b * (v b : K) := by
  simp only [ent, Matrix.SpecialLinearGroup.coe_mul, coe_diagSL, Matrix.mul_diagonal]

theorem diagSL_conj_ent (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1) (x : SL3 K) (a b : Fin 3) :
    ent (diagSL v hv * x * (diagSL v hv)⁻¹) a b = (v a : K) * ((v b)⁻¹ : Kˣ) * ent x a b := by
  have h1 : (diagSL v hv * x * (diagSL v hv)⁻¹) * diagSL v hv = diagSL v hv * x := by
    rw [mul_assoc, inv_mul_cancel, mul_one]
  have h2 := congrArg (fun y : SL3 K => ent y a b) h1
  simp only [ent_mul_diagSL, ent_diagSL_mul] at h2
  have h3 : (v b : K) ≠ 0 := (v b).ne_zero
  rw [Units.val_inv_eq_inv_val]
  field_simp
  linear_combination h2

theorem diagSL_conj_rt (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1) {i j : Fin 3} (h : i ≠ j) (s : K) :
    diagSL v hv * rt h s * (diagSL v hv)⁻¹ = rt h ((v i : K) * ((v j)⁻¹ : Kˣ) * s) := by
  apply Subtype.ext
  ext a b
  have h1 := diagSL_conj_ent v hv (rt h s) a b
  change ent (diagSL v hv * rt h s * (diagSL v hv)⁻¹) a b = ent (rt h _) a b
  rw [h1, ent, ent, rt_apply, rt_apply]
  by_cases hab : a = b
  · subst hab
    by_cases hc : i = a ∧ j = a
    · exact absurd (hc.1.trans hc.2.symm) h
    · simp [hc]
  · by_cases hc : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := hc
      simp [hab]
    · simp [hab, hc]

@[expose] def Tor (p : ℕ) (K : Type) [Field K] : Subgroup (SL3 K) :=
  (torusSU p 3 K).comap Matrix.SpecialLinearGroup.toGL

theorem mem_Tor_iff {p : ℕ} {t : SL3 K} :
    t ∈ Tor p K ↔ ∃ v : Fin 3 → Kˣ, (∀ i, v i ^ p = 1) ∧ ∃ hv : ∏ i, v i = 1, t = diagSL v hv := by
  constructor
  · intro ht
    obtain ⟨v, hv1, hv2, hv⟩ := mem_torusSU_iff.mp ht
    refine ⟨v, hv1, hv2, ?_⟩
    apply Subtype.ext
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hv
    simp only [diagU_val, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at this
    rw [coe_diagSL]
    exact this.symm
  · rintro ⟨v, hv1, hv2, rfl⟩
    refine mem_torusSU_iff.mpr ⟨v, hv1, hv2, ?_⟩
    apply Units.ext
    rfl

theorem diagSL_mem_Tor {p : ℕ} (v : Fin 3 → Kˣ) (h1 : ∀ i, v i ^ p = 1) (hv : ∏ i, v i = 1) :
    diagSL v hv ∈ Tor p K :=
  mem_Tor_iff.mpr ⟨v, h1, hv, rfl⟩

@[expose] def Tbar (p : ℕ) (K : Type) [Field K] : Subgroup (PSL3 K) :=
  (Tor p K).map (QuotientGroup.mk' (Subgroup.center (SL3 K)))

theorem mem_Tbar_iff {p : ℕ} {u : PSL3 K} :
    u ∈ Tbar p K ↔ ∃ t ∈ Tor p K, (QuotientGroup.mk t : PSL3 K) = u := by
  simp [Tbar, Subgroup.mem_map]

theorem diagSL_mem_center_of_const (v : Fin 3 → Kˣ) (hv : ∏ i, v i = 1)
    (hc : ∀ a, v a = v 0) : diagSL v hv ∈ Subgroup.center (SL3 K) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨(v 0 : K), ?_, ?_⟩
  · have h3 : ∏ i, v i = v 0 ^ 3 := by
      simp [Fin.prod_univ_three, hc 1, hc 2, pow_succ, mul_assoc]
    have := congrArg (fun u : Kˣ => (u : K)) (h3.symm.trans hv)
    simpa using this
  · ext a b
    simp only [diagSL, Matrix.scalar_apply, Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab
      simp [hc a]
    · simp [hab]

theorem const_of_diagSL_mem_center {v : Fin 3 → Kˣ} {hv : ∏ i, v i = 1}
    (hz : diagSL v hv ∈ Subgroup.center (SL3 K)) (a b : Fin 3) : v a = v b := by
  obtain ⟨r, -, hr⟩ := exists_scalar_of_mem_center hz
  have h1 : ∀ c, ((v c : Kˣ) : K) = r := by
    intro c
    have := congrFun (congrFun hr c) c
    simpa [diagSL] using this
  exact Units.ext ((h1 a).trans (h1 b).symm)

structure IsZeta (p : ℕ) (ζ : Kˣ) : Prop where
  pow : ζ ^ p = 1
  sq : ζ ^ 2 ≠ 1
  cube : ζ ^ 3 ≠ 1

theorem IsZeta.of_orderOf {p : ℕ} (h5 : 5 ≤ p) {ζ : Kˣ} (h : orderOf ζ = p) :
    IsZeta p ζ := by
  refine ⟨h ▸ pow_orderOf_eq_one ζ, fun h2 => ?_, fun h3 => ?_⟩
  · have := orderOf_dvd_of_pow_eq_one h2
    rw [h] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  · have := orderOf_dvd_of_pow_eq_one h3
    rw [h] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega

@[expose] def nonreg (ζ : Kˣ) (c : Fin 3) : Fin 3 → Kˣ := fun i => if i = c then (ζ ^ 2)⁻¹ else ζ

theorem prod_nonreg (ζ : Kˣ) (c : Fin 3) : ∏ i, nonreg ζ c i = 1 := by
  fin_cases c <;> simp [nonreg, Fin.prod_univ_three] <;> group

theorem nonreg_pow {p : ℕ} {ζ : Kˣ} (hζ : ζ ^ p = 1) (c i : Fin 3) : nonreg ζ c i ^ p = 1 := by
  unfold nonreg
  split_ifs
  · rw [inv_pow, ← pow_mul, mul_comm, pow_mul, hζ, one_pow, inv_one]
  · exact hζ

@[expose] def tNon (ζ : Kˣ) (c : Fin 3) : SL3 K := diagSL (nonreg ζ c) (prod_nonreg ζ c)

theorem tNon_mem {p : ℕ} {ζ : Kˣ} (hζ : IsZeta p ζ) (c : Fin 3) : (tNon ζ c : SL3 K) ∈ Tor p K :=
  diagSL_mem_Tor _ (nonreg_pow hζ.pow c) _

theorem nonreg_self (ζ : Kˣ) (c : Fin 3) : nonreg ζ c c = (ζ ^ 2)⁻¹ := by
  simp [nonreg]

theorem nonreg_of_ne (ζ : Kˣ) {c a : Fin 3} (ha : a ≠ c) : nonreg ζ c a = ζ := by
  simp [nonreg, ha]

theorem nonreg_ne {p : ℕ} {ζ : Kˣ} (hζ : IsZeta p ζ) {c a : Fin 3} (ha : a ≠ c) :
    nonreg ζ c c ≠ nonreg ζ c a := by
  rw [nonreg_self, nonreg_of_ne ζ ha]
  intro h
  apply hζ.cube
  calc ζ ^ 3 = ζ ^ 2 * ζ := by rw [pow_succ]
    _ = ζ ^ 2 * (ζ ^ 2)⁻¹ := by rw [h]
    _ = 1 := mul_inv_cancel _

theorem tNon_not_center {p : ℕ} {ζ : Kˣ} (hζ : IsZeta p ζ) (c : Fin 3) :
    (tNon ζ c : SL3 K) ∉ Subgroup.center (SL3 K) := by
  intro hz
  have h1 : c + 1 ≠ c := by fin_cases c <;> decide
  exact nonreg_ne hζ h1 (const_of_diagSL_mem_center hz c (c + 1))

@[expose] def tSep (ζ : Kˣ) (a b : Fin 3) : Fin 3 → Kˣ := torusElt a b ζ

theorem tSep_mem {p : ℕ} {ζ : Kˣ} (hζ : IsZeta p ζ) {a b : Fin 3} (hab : a ≠ b) :
    diagSL (tSep ζ a b) (prod_torusElt a b ζ) ∈ Tor p K :=
  diagSL_mem_Tor _ (fun k => (torusElt_mem hab hζ.pow : torusElt a b ζ ∈ KFU.torusVec p 3 K).1 k)
    _

theorem tSep_ne {p : ℕ} {ζ : Kˣ} (hζ : IsZeta p ζ) {a b : Fin 3} (hab : a ≠ b) :
    tSep ζ a b a ≠ tSep ζ a b b := by
  unfold tSep
  rw [KFU.torusElt_apply_left hab, KFU.torusElt_apply_right hab]
  intro h
  apply hζ.sq
  calc ζ ^ 2 = ζ * ζ := sq ζ
    _ = ζ * ζ⁻¹ := by rw [← h]
    _ = 1 := mul_inv_cancel _

end CFSG.RankThree.PartOne.KFOUT3
