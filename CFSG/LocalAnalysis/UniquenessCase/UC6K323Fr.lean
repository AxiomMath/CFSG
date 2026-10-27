module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6.K323Fr

open Matrix

variable {p : ℕ} [Fact p.Prime]

theorem mulVec_pow_succ (g : GL (Fin 3) (ZMod p)) (k : ℕ) (w : Fin 3 → ZMod p) :
    ((g ^ (k + 1) : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w =
      (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ
        (((g ^ k : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w) := by
  rw [pow_succ', Units.val_mul, ← Matrix.mulVec_mulVec]

theorem coord_of_linearIndependent {z v u : Fin 3 → ZMod p}
    (hli : LinearIndependent (ZMod p) ![z, v, u]) (w : Fin 3 → ZMod p) :
    ∃ s t r : ZMod p, w = s • z + t • v + r • u := by
  have hspan : Submodule.span (ZMod p) (Set.range ![z, v, u]) = ⊤ :=
    LinearIndependent.span_eq_top_of_card_eq_finrank hli (by simp)
  have hw : w ∈ Submodule.span (ZMod p) (Set.range ![z, v, u]) := hspan ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).1 hw
  exact ⟨c 0, c 1, c 2, by rw [← hc]; simp [Fin.sum_univ_three]⟩

theorem pow_pred_eq_one {g : GL (Fin 3) (ZMod p)} {n : ℕ} (hn : 0 < n) (hpn : ¬ p ∣ n)
    (hgn : g ^ n = 1) {z v u : Fin 3 → ZMod p}
    (hli : LinearIndependent (ZMod p) ![z, v, u])
    (hz : (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ z = z) {a b : ZMod p}
    (hv : (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v = a • z + b • v) :
    g ^ (p - 1) = 1 := by
  classical
  have hind : ∀ s t r : ZMod p, s • z + t • v + r • u = 0 → s = 0 ∧ t = 0 ∧ r = 0 := by
    intro s t r h
    have := Fintype.linearIndependent_iff.1 hli ![s, t, r] (by simpa [Fin.sum_univ_three] using h)
    exact ⟨this 0, this 1, this 2⟩
  have hspan : Submodule.span (ZMod p) (Set.range ![z, v, u]) = ⊤ :=
    LinearIndependent.span_eq_top_of_card_eq_finrank hli (by simp)
  have hcoord : ∀ w : Fin 3 → ZMod p, ∃ s t r : ZMod p, w = s • z + t • v + r • u := by
    intro w
    have hw : w ∈ Submodule.span (ZMod p) (Set.range ![z, v, u]) := hspan ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).1 hw
    exact ⟨c 0, c 1, c 2, by rw [← hc]; simp [Fin.sum_univ_three]⟩
  have hz0 : z ≠ 0 := fun h => one_ne_zero (hind 1 0 0 (by simp [h])).1
  obtain ⟨α, β, c, hu⟩ := hcoord ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ u)
  have hpowv : ∀ k : ℕ, ∃ ak : ZMod p,
      ((g ^ k : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v =
        ak • z + b ^ k • v := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨ak, hak⟩ := ih
      refine ⟨ak + b ^ k * a, ?_⟩
      rw [mulVec_pow_succ, hak, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hz, hv]
      module
  have hpowu : ∀ k : ℕ, ∃ ak bk : ZMod p,
      ((g ^ k : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ u =
        ak • z + bk • v + c ^ k • u := by
    intro k
    induction k with
    | zero => exact ⟨0, 0, by simp⟩
    | succ k ih =>
      obtain ⟨ak, bk, hak⟩ := ih
      refine ⟨ak + bk * a + c ^ k * α, bk * b + c ^ k * β, ?_⟩
      rw [mulVec_pow_succ, hak, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul,
        Matrix.mulVec_smul, Matrix.mulVec_smul, hz, hv, hu]
      module
  have hpowz : ∀ k : ℕ, ((g ^ k : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ z = z := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [mulVec_pow_succ, ih, hz]
  have hbn : b ^ n = 1 := by
    obtain ⟨an, han⟩ := hpowv n
    rw [hgn, Units.val_one, Matrix.one_mulVec] at han
    have := hind (-an) (1 - b ^ n) 0 (by
      have h2 : (-an) • z + (1 - b ^ n) • v + (0 : ZMod p) • u = v - (an • z + b ^ n • v) := by
        module
      rw [h2, ← han, sub_self])
    exact (sub_eq_zero.1 this.2.1).symm
  have hcn : c ^ n = 1 := by
    obtain ⟨an, bn, han⟩ := hpowu n
    rw [hgn, Units.val_one, Matrix.one_mulVec] at han
    have := hind (-an) (-bn) (1 - c ^ n) (by
      have h2 : (-an) • z + (-bn) • v + (1 - c ^ n) • u = u - (an • z + bn • v + c ^ n • u) := by
        module
      rw [h2, ← han, sub_self])
    exact (sub_eq_zero.1 this.2.2).symm
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hbn
    exact zero_ne_one hbn
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hcn
    exact zero_ne_one hcn
  have hbp : b ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hb0
  have hcp : c ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hc0
  set M : Matrix (Fin 3) (Fin 3) (ZMod p) := ((g ^ (p - 1) : GL (Fin 3) (ZMod p)) :
    Matrix (Fin 3) (Fin 3) (ZMod p)) with hM
  obtain ⟨a1, ha1⟩ := hpowv (p - 1)
  obtain ⟨A, B, hAB⟩ := hpowu (p - 1)
  rw [hbp, one_smul] at ha1
  rw [hcp, one_smul] at hAB
  set N : Matrix (Fin 3) (Fin 3) (ZMod p) := M - 1 with hN
  have hNz : N *ᵥ z = 0 := by
    rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec, hM, hpowz, sub_self]
  have hNv : N *ᵥ v = a1 • z := by
    rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec, hM, ha1]; module
  have hNu : N *ᵥ u = A • z + B • v := by
    rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec, hM, hAB]; module
  have hN2v : N *ᵥ (N *ᵥ v) = 0 := by
    rw [hNv, Matrix.mulVec_smul, hNz, smul_zero]
  have hN2u : N *ᵥ (N *ᵥ u) = (B * a1) • z := by
    rw [hNu, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hNz, hNv, smul_zero,
      zero_add, smul_smul]
  have hN3 : ∀ w : Fin 3 → ZMod p, N *ᵥ (N *ᵥ (N *ᵥ w)) = 0 := by
    intro w
    obtain ⟨s, t, r, rfl⟩ := hcoord w
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hNz, hNv, hNu, hN2v, hN2u, smul_zero,
      zero_add, add_zero]
  have hMk : ∀ (k : ℕ) (w : Fin 3 → ZMod p), (M ^ k) *ᵥ w =
      w + (k : ZMod p) • (N *ᵥ w) + ((k.choose 2 : ℕ) : ZMod p) • (N *ᵥ (N *ᵥ w)) := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      have hMN : M = 1 + N := by rw [hN]; abel
      have hc : (k + 1).choose 2 = k + k.choose 2 := by
        have := Nat.choose_succ_succ' k 1
        simpa [Nat.choose_one_right, add_comm] using this
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, hMN, Matrix.add_mulVec, Matrix.one_mulVec]
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hN3 w, smul_zero, add_zero]
      rw [hc]
      push_cast
      module
  have hMn : M ^ n = 1 := by
    rw [hM, ← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, hgn, one_pow, Units.val_one]
  have hn0 : (n : ZMod p) ≠ 0 := fun h => hpn ((ZMod.natCast_eq_zero_iff n p).1 h)
  have hrel : ∀ w : Fin 3 → ZMod p, (n : ZMod p) • (N *ᵥ w) +
      ((n.choose 2 : ℕ) : ZMod p) • (N *ᵥ (N *ᵥ w)) = 0 := by
    intro w
    have h := hMk n w
    rw [hMn, Matrix.one_mulVec] at h
    have h2 : w + ((n : ZMod p) • (N *ᵥ w) + ((n.choose 2 : ℕ) : ZMod p) • (N *ᵥ (N *ᵥ w))) =
        w + 0 := by rw [add_zero, ← add_assoc]; exact h.symm
    exact add_left_cancel h2
  have ha1 : a1 = 0 := by
    have h := hrel v
    rw [hN2v, hNv, smul_zero, add_zero, smul_smul] at h
    exact (mul_eq_zero.1 ((smul_eq_zero.1 h).resolve_right hz0)).resolve_left hn0
  have hNv0 : N *ᵥ v = 0 := by rw [hNv, ha1, zero_smul]
  have hAB0 : A = 0 ∧ B = 0 := by
    have h := hrel u
    rw [hN2u, ha1, mul_zero, zero_smul, smul_zero, add_zero, hNu] at h
    have h2 := hind (n * A) (n * B) 0 (by rw [← h]; module)
    exact ⟨(mul_eq_zero.1 h2.1).resolve_left hn0, (mul_eq_zero.1 h2.2.1).resolve_left hn0⟩
  have hNu0 : N *ᵥ u = 0 := by rw [hNu, hAB0.1, hAB0.2]; simp
  have hM1 : M = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun w => ?_
    obtain ⟨s, t, r, rfl⟩ := hcoord w
    have hNw : N *ᵥ (s • z + t • v + r • u) = 0 := by
      rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        Matrix.mulVec_smul, hNz, hNv0, hNu0]
      simp
    have hMw : M *ᵥ (s • z + t • v + r • u) = s • z + t • v + r • u := by
      have h1 : M = N + 1 := by rw [hN]; abel
      rw [h1, Matrix.add_mulVec, hNw, Matrix.one_mulVec, zero_add]
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hMw, Matrix.one_mulVec]
  exact Units.ext hM1

theorem false_of_fixed_outside {g y : GL (Fin 3) (ZMod p)} {n : ℕ} (horder : orderOf g = n)
    (hn : p - 1 < n) (hpn : ¬ p ∣ n) (hcomm : g * y = y * g) {z v : Fin 3 → ZMod p}
    (hz0 : z ≠ 0) (hgz : (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ z = z)
    (hyz : (y : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ z = z)
    (hyv : (y : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v = v) (hv : ∀ c : ZMod p, v ≠ c • z)
    (hy : ∃ u : Fin 3 → ZMod p, (y : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ u ≠ u) : False := by
  classical
  obtain ⟨u, hu⟩ := hy
  set Y : Matrix (Fin 3) (Fin 3) (ZMod p) := (y : Matrix (Fin 3) (Fin 3) (ZMod p)) with hY
  have hyu : Y *ᵥ u - u ≠ 0 := sub_ne_zero.2 hu
  have hr0 : ∀ s t r : ZMod p, s • z + t • v + r • u = 0 → r = 0 := by
    intro s t r h
    have h1 : Y *ᵥ (s • z + t • v + r • u) = 0 := by rw [h, Matrix.mulVec_zero]
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_smul, hyz, hyv] at h1
    have h2 : r • (Y *ᵥ u - u) = 0 := by
      have : r • (Y *ᵥ u - u) = (s • z + t • v + r • Y *ᵥ u) - (s • z + t • v + r • u) := by
        module
      rw [this, h1, h, sub_zero]
    exact (smul_eq_zero.1 h2).resolve_right hyu
  have hli : LinearIndependent (ZMod p) ![z, v, u] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hc
    have hc2 : c 2 = 0 := hr0 (c 0) (c 1) (c 2) hc
    rw [hc2, zero_smul, add_zero] at hc
    have hc1 : c 1 = 0 := by
      by_contra h1
      apply hv (-(c 1)⁻¹ * c 0)
      have : c 1 • v = -(c 0 • z) := eq_neg_of_add_eq_zero_right hc
      calc v = (c 1)⁻¹ • (c 1 • v) := by rw [smul_smul, inv_mul_cancel₀ h1, one_smul]
        _ = (-(c 1)⁻¹ * c 0) • z := by rw [this]; module
    rw [hc1, zero_smul, add_zero] at hc
    have hc0 : c 0 = 0 := (smul_eq_zero.1 hc).resolve_right hz0
    intro i
    fin_cases i <;> simp [hc0, hc1, hc2]
  obtain ⟨a, b, c, hgv⟩ := coord_of_linearIndependent hli
    ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v)
  have hyg : Y *ᵥ ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v) =
      (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v := by
    rw [Matrix.mulVec_mulVec, hY, ← Units.val_mul, ← hcomm, Units.val_mul, ← Matrix.mulVec_mulVec,
      hyv]
  have hc0 : c = 0 := by
    have h1 : c • (Y *ᵥ u - u) = 0 := by
      have h2 := hyg
      rw [hgv, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        Matrix.mulVec_smul, hyz, hyv] at h2
      have : c • (Y *ᵥ u - u) = (a • z + b • v + c • Y *ᵥ u) - (a • z + b • v + c • u) := by
        module
      rw [this, h2, sub_self]
    exact (smul_eq_zero.1 h1).resolve_right hyu
  rw [hc0, zero_smul, add_zero] at hgv
  have hg1 : g ^ (p - 1) = 1 := pow_pred_eq_one (by omega) hpn (by rw [← horder]; exact pow_orderOf_eq_one g)
    hli hgz hgv
  have hdvd : n ∣ p - 1 := horder ▸ orderOf_dvd_of_pow_eq_one hg1
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have := Nat.le_of_dvd (by omega) hdvd
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC6.K323Fr
