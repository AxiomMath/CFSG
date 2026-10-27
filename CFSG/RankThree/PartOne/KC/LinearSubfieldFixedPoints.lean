module

public import CFSG.RankThree.PartOne.KC.LinearSubfieldInclusion

public section

namespace CFSG.RankThree.PartOne

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace KCLinearSubfield

variable {n : ℕ} {K : Type*} [Field K]

theorem apply_prod_pow_eq {σ : K ≃+* K} {p : ℕ} (hσp : σ ^ p = 1) {u : K} (hu : u ≠ 0) :
    σ (∏ i ∈ Finset.range p, (σ ^ i) u) = ∏ i ∈ Finset.range p, (σ ^ i) u := by
  rw [map_prod]
  have h1 : ∀ i : ℕ, σ ((σ ^ i) u) = (σ ^ (i + 1)) u := fun i => by rw [pow_succ']; rfl
  simp_rw [h1]
  rcases p with _ | p
  · simp
  · have e1 := Finset.prod_range_succ (fun i => (σ ^ i) u) (p + 1)
    have e2 := Finset.prod_range_succ' (fun i => (σ ^ i) u) (p + 1)
    have hlast : (σ ^ (p + 1)) u = u := by rw [hσp]; rfl
    have hfirst : (σ ^ 0) u = u := rfl
    rw [e1, hlast] at e2
    rw [hfirst] at e2
    exact (mul_right_cancel₀ hu e2).symm

theorem exists_fixed_unit_pow_eq_pow {σ : K ≃+* K} {p : ℕ} (hσp : σ ^ p = 1) {a u : Kˣ}
    (hσa : σ (a : K) = a) (hu : u ^ n = a) :
    ∃ w : Kˣ, σ (w : K) = w ∧ w ^ n = a ^ p := by
  have hne : ∏ i ∈ Finset.range p, (σ ^ i) (u : K) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => by
      rw [Ne, EmbeddingLike.map_eq_zero_iff]
      exact u.ne_zero
  refine ⟨Units.mk0 _ hne, ?_, ?_⟩
  · exact apply_prod_pow_eq hσp u.ne_zero
  · apply Units.ext
    have hua : (u : K) ^ n = a := by rw [← Units.val_pow_eq_pow_val, hu]
    have hfix : ∀ i : ℕ, (σ ^ i) (a : K) = a := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih => rw [pow_succ', RingAut.mul_apply, ih, hσa]
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [← Finset.prod_pow]
    calc ∏ i ∈ Finset.range p, ((σ ^ i) (u : K)) ^ n
        = ∏ i ∈ Finset.range p, (σ ^ i) ((u : K) ^ n) := by simp only [map_pow]
      _ = ∏ i ∈ Finset.range p, (a : K) := by simp only [hua, hfix]
      _ = (a : K) ^ p := by rw [Finset.prod_const, Finset.card_range]

theorem zpow_mul_zpow_pow_eq_of_coprime {G : Type*} [CommGroup G] {a w : G} {n p : ℕ}
    (hwn : w ^ n = a ^ p) {s t : ℤ} (hst : s * n + t * p = 1) : (a ^ s * w ^ t) ^ n = a := by
  have e1 : (a ^ s) ^ n = a ^ (s * (n : ℤ)) := by rw [← zpow_natCast (a ^ s) n, ← _root_.zpow_mul]
  have e2 : (w ^ t) ^ n = (w ^ n) ^ t := by
    rw [← zpow_natCast (w ^ t) n, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast]
  have e3 : (a ^ p) ^ t = a ^ (t * (p : ℤ)) := by rw [mul_comm, _root_.zpow_mul, zpow_natCast]
  calc (a ^ s * w ^ t) ^ n = (a ^ s) ^ n * (w ^ t) ^ n := mul_pow _ _ _
    _ = a ^ (s * (n : ℤ)) * (a ^ p) ^ t := by rw [e1, e2, hwn]
    _ = a ^ (s * (n : ℤ) + t * p) := by rw [e3, _root_.zpow_add]
    _ = a := by rw [hst, zpow_one]

theorem zpow_pow_eq_of_pow_eq_one {G : Type*} [CommGroup G] {a w : G} {n p m : ℕ}
    (hwn : w ^ n = a ^ p) (ham : a ^ m = 1) {s t : ℤ} (hst : s * p + t * m = 1) :
    (w ^ s) ^ n = a := by
  have e1 : (w ^ s) ^ n = (w ^ n) ^ s := by
    rw [← zpow_natCast (w ^ s) n, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast]
  have e2 : (a ^ p) ^ s = a ^ (s * (p : ℤ)) := by rw [mul_comm, _root_.zpow_mul, zpow_natCast]
  have e3 : a ^ (t * (m : ℤ)) = 1 := by
    rw [mul_comm, _root_.zpow_mul, zpow_natCast, ham, _root_.one_zpow]
  calc (w ^ s) ^ n = (w ^ n) ^ s := e1
    _ = a ^ (s * (p : ℤ)) := by rw [hwn, e2]
    _ = a ^ (s * (p : ℤ) + t * m) := by rw [_root_.zpow_add, e3, mul_one]
    _ = a := by rw [hst, zpow_one]

theorem apply_zpow_unit_eq {σ : K ≃+* K} {v : Kˣ} (hv : σ (v : K) = v) (m : ℤ) :
    σ ((v ^ m : Kˣ) : K) = (v ^ m : Kˣ) := by
  have hmap : (Units.map (σ : K ≃+* K).toMonoidHom) v = v := Units.ext hv
  calc σ ((v ^ m : Kˣ) : K) = (((Units.map (σ : K ≃+* K).toMonoidHom) (v ^ m) : Kˣ) : K) := rfl
    _ = (v ^ m : Kˣ) := by rw [map_zpow, hmap]

theorem exists_fixed_root_of_coprime {σ : K ≃+* K} {p : ℕ} (hσp : σ ^ p = 1)
    (hnp : Nat.Coprime n p) {a u : Kˣ} (hσa : σ (a : K) = a) (hu : u ^ n = a) :
    ∃ w : Kˣ, σ (w : K) = w ∧ w ^ n = a := by
  obtain ⟨w, hw, hwn⟩ := exists_fixed_unit_pow_eq_pow hσp hσa hu
  obtain ⟨s, t, hst⟩ := Nat.isCoprime_iff_coprime.mpr hnp
  refine ⟨a ^ s * w ^ t, ?_, zpow_mul_zpow_pow_eq_of_coprime hwn hst⟩
  rw [Units.val_mul, map_mul, apply_zpow_unit_eq hσa s, apply_zpow_unit_eq hw t]

theorem exists_fixed_root_of_not_dvd [Finite K] {σ : K ≃+* K} {p : ℕ} (hp : p.Prime)
    (hσp : σ ^ p = 1) (hpK : ¬ p ∣ Nat.card Kˣ) {a u : Kˣ} (hσa : σ (a : K) = a)
    (hu : u ^ n = a) : ∃ w : Kˣ, σ (w : K) = w ∧ w ^ n = a := by
  obtain ⟨w, hw, hwn⟩ := exists_fixed_unit_pow_eq_pow hσp hσa hu
  obtain ⟨s, t, hst⟩ := Nat.isCoprime_iff_coprime.mpr
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpK)
  exact ⟨w ^ s, apply_zpow_unit_eq hw s, zpow_pow_eq_of_pow_eq_one hwn pow_card_eq_one' hst⟩

theorem exists_ne_zero_entry (hn : 0 < n) (g : SpecialLinearGroup (Fin n) K) :
    ∃ i j : Fin n, (g : Matrix (Fin n) (Fin n) K) i j ≠ 0 := by
  by_contra h
  push Not at h
  have hz : (g : Matrix (Fin n) (Fin n) K) = 0 := by
    ext i j
    exact h i j
  have h1 := g.2
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [hz, Matrix.det_zero] at h1
  exact zero_ne_one h1

theorem exists_scalar_of_fieldAut_proj_eq {σ : K ≃+* K} {g : SpecialLinearGroup (Fin n) K}
    (hx : fieldAut n K σ (proj n K g) = proj n K g) :
    ∃ c : Kˣ, c ^ n = 1 ∧ ∀ a b : Fin n,
      σ ((g : Matrix (Fin n) (Fin n) K) a b) = (g : Matrix (Fin n) (Fin n) K) a b * c := by
  rw [fieldAut_proj] at hx
  obtain ⟨c, hcn, hc⟩ := mem_scalars.mp (proj_eq_proj_iff.mp hx.symm)
  refine ⟨c, hcn, fun a b => ?_⟩
  have h1 : SpecialLinearGroup.map σ.toRingHom g =
      g * (g⁻¹ * SpecialLinearGroup.map σ.toRingHom g) := (mul_inv_cancel_left _ _).symm
  have h2 := congrArg (fun y : SpecialLinearGroup (Fin n) K =>
    (y : Matrix (Fin n) (Fin n) K) a b) h1
  simp only [Matrix.SpecialLinearGroup.coe_mul, hc, SpecialLinearGroup.map_apply_coe, scalar_apply,
    Matrix.mul_diagonal, RingHom.mapMatrix_apply, Matrix.map_apply] at h2
  exact h2

theorem fixed_point_mem_range {k : Subfield K} {σ : K ≃+* K} (hk : ∀ x, x ∈ k ↔ σ x = x)
    (hn : 0 < n)
    (hdesc : ∀ a : Kˣ, (a : K) ∈ k → (∃ u : Kˣ, u ^ n = a) → ∃ w : Kˣ, (w : K) ∈ k ∧ w ^ n = a)
    {x : projectiveSL n K} (hx : fieldAut n K σ x = x) :
    x ∈ (linearSubfieldInclusion n k).range := by
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  obtain ⟨c, hcn, hent⟩ := exists_scalar_of_fieldAut_proj_eq hx
  obtain ⟨i₀, j₀, hne⟩ := exists_ne_zero_entry hn g
  set G : Matrix (Fin n) (Fin n) K := (g : Matrix (Fin n) (Fin n) K) with hG
  set u : Kˣ := Units.mk0 (G i₀ j₀)⁻¹ (inv_ne_zero hne) with hu
  have hcc : (c : K) * ((c⁻¹ : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hσu : σ (u : K) = (u : K) * ((c⁻¹ : Kˣ) : K) := by
    rw [hu, Units.val_mk0, map_inv₀, hent i₀ j₀, mul_inv, Units.val_inv_eq_inv_val]
  have hσun : σ ((u ^ n : Kˣ) : K) = ((u ^ n : Kˣ) : K) := by
    have hcn' : ((c⁻¹ : Kˣ) : K) ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, inv_pow, hcn, inv_one, Units.val_one]
    rw [Units.val_pow_eq_pow_val, map_pow, hσu, mul_pow, hcn', mul_one]
  have hentk : ∀ a b : Fin n, G a b * (u : K) ∈ k := by
    intro a b
    rw [hk, map_mul, hent a b, hσu]
    calc G a b * c * ((u : K) * ((c⁻¹ : Kˣ) : K))
        = G a b * (u : K) * ((c : K) * ((c⁻¹ : Kˣ) : K)) := by ring
      _ = G a b * (u : K) := by rw [hcc, mul_one]
  obtain ⟨w, hwk, hwn⟩ := hdesc (u ^ n) ((hk _).mpr hσun) ⟨u, rfl⟩
  set v : Kˣ := w⁻¹ * u with hv
  have hvn : v ^ n = 1 := by rw [hv, mul_pow, inv_pow, hwn, inv_mul_cancel]
  have hwinv : ((w⁻¹ : Kˣ) : K) ∈ k := by
    rw [Units.val_inv_eq_inv_val]
    exact k.inv_mem hwk
  obtain ⟨Y, hY⟩ : ∃ Y : SpecialLinearGroup (Fin n) K,
      (Y : Matrix (Fin n) (Fin n) K) = (v : K) • G :=
    ⟨⟨(v : K) • G, by
      rw [Matrix.det_smul, hG, g.2, mul_one, Fintype.card_fin, ← Units.val_pow_eq_pow_val, hvn,
        Units.val_one]⟩, rfl⟩
  refine mem_range_linearSubfieldInclusion.mpr ⟨Y, fun a b => ?_, ?_⟩
  · rw [hY, Matrix.smul_apply, smul_eq_mul, hv, Units.val_mul]
    have := k.mul_mem hwinv (hentk a b)
    convert this using 1
    ring
  · symm
    rw [proj_eq_proj_iff]
    refine mem_scalars.mpr ⟨v, hvn, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, hY, Matrix.mul_smul, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, scalar_apply, ← smul_one_eq_diagonal]

theorem fixed_points_eq_range {k : Subfield K} {σ : K ≃+* K} (hk : ∀ x, x ∈ k ↔ σ x = x)
    (hn : 0 < n)
    (hdesc : ∀ a : Kˣ, (a : K) ∈ k → (∃ u : Kˣ, u ^ n = a) → ∃ w : Kˣ, (w : K) ∈ k ∧ w ^ n = a) :
    {x : projectiveSL n K | fieldAut n K σ x = x} =
      ((linearSubfieldInclusion n k).range : Set (projectiveSL n K)) := by
  ext x
  constructor
  · exact fixed_point_mem_range hk hn hdesc
  · rintro ⟨y, rfl⟩
    exact fieldAut_linearSubfieldInclusion (fun c hc => (hk c).mp hc) y

theorem root_descent_of_coprime {k : Subfield K} {σ : K ≃+* K} {p : ℕ}
    (hk : ∀ x, x ∈ k ↔ σ x = x) (hσp : σ ^ p = 1) (hnp : Nat.Coprime n p) :
    ∀ a : Kˣ, (a : K) ∈ k → (∃ u : Kˣ, u ^ n = a) → ∃ w : Kˣ, (w : K) ∈ k ∧ w ^ n = a := by
  rintro a ha ⟨u, hu⟩
  obtain ⟨w, hw, hwn⟩ := exists_fixed_root_of_coprime hσp hnp ((hk _).mp ha) hu
  exact ⟨w, (hk _).mpr hw, hwn⟩

theorem root_descent_of_not_dvd [Finite K] {k : Subfield K} {σ : K ≃+* K} {p : ℕ}
    (hp : p.Prime) (hk : ∀ x, x ∈ k ↔ σ x = x) (hσp : σ ^ p = 1) (hpK : ¬ p ∣ Nat.card Kˣ) :
    ∀ a : Kˣ, (a : K) ∈ k → (∃ u : Kˣ, u ^ n = a) → ∃ w : Kˣ, (w : K) ∈ k ∧ w ^ n = a := by
  rintro a ha ⟨u, hu⟩
  obtain ⟨w, hw, hwn⟩ := exists_fixed_root_of_not_dvd hp hσp hpK ((hk _).mp ha) hu
  exact ⟨w, (hk _).mpr hw, hwn⟩

end KCLinearSubfield

end CFSG.RankThree.PartOne
