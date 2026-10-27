module

public import CFSG.LocalAnalysis.StandardType.GGResIBasic
public import CFSG.LocalAnalysis.StandardType.GGResIDefs
public import CFSG.LocalAnalysis.StandardType.GGResIISmall

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Lattice

variable {m : ℕ} {Q : Matrix (Fin m) (Fin m) ℤ}

theorem ggResI_dot_symm (hQ : GGLatForm Q) (v w : Fin m → ℤ) :
    dotProduct w (Q.mulVec v) = dotProduct v (Q.mulVec w) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hQ.1, dotProduct_comm]

theorem ggResI_dot_sq_le (hQ : GGLatForm Q) (v w : Fin m → ℤ) :
    (dotProduct v (Q.mulVec w)) ^ 2 ≤ dotProduct v (Q.mulVec v) * dotProduct w (Q.mulVec w) := by
  set B := dotProduct v (Q.mulVec w)
  set Nv := dotProduct v (Q.mulVec v)
  set Nw := dotProduct w (Q.mulVec w)
  have hpos : ∀ z : Fin m → ℤ, 0 ≤ dotProduct z (Q.mulVec z) := by
    intro z
    by_cases hz : z = 0
    · simp [hz]
    · exact (hQ.2 z hz).le
  have hBw : dotProduct w (Q.mulVec v) = B := ggResI_dot_symm hQ v w
  have hz : dotProduct (Nw • v - B • w) (Q.mulVec (Nw • v - B • w)) = Nw * (Nw * Nv - B ^ 2) := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [hBw]
    ring
  have h0 := hpos (Nw • v - B • w)
  rw [hz] at h0
  by_cases hw : w = 0
  · have hB : B = 0 := by simp [B, hw]
    rw [hB]
    have := hpos v
    have := hpos w
    nlinarith
  · have hNw : 0 < Nw := hQ.2 w hw
    nlinarith

theorem ggResI_gram_det_nonneg (hQ : GGLatForm Q) (v : Fin 3 → Fin m → ℤ) (hv : v 0 ≠ 0) :
    0 ≤ dotProduct (v 0) (Q.mulVec (v 0)) * dotProduct (v 1) (Q.mulVec (v 1)) *
          dotProduct (v 2) (Q.mulVec (v 2)) -
        dotProduct (v 2) (Q.mulVec (v 2)) * dotProduct (v 0) (Q.mulVec (v 1)) ^ 2 -
        dotProduct (v 1) (Q.mulVec (v 1)) * dotProduct (v 0) (Q.mulVec (v 2)) ^ 2 -
        dotProduct (v 0) (Q.mulVec (v 0)) * dotProduct (v 1) (Q.mulVec (v 2)) ^ 2 +
        2 * dotProduct (v 0) (Q.mulVec (v 1)) * dotProduct (v 0) (Q.mulVec (v 2)) *
          dotProduct (v 1) (Q.mulVec (v 2)) := by
  set n0 := dotProduct (v 0) (Q.mulVec (v 0))
  set n1 := dotProduct (v 1) (Q.mulVec (v 1))
  set n2 := dotProduct (v 2) (Q.mulVec (v 2))
  set g01 := dotProduct (v 0) (Q.mulVec (v 1))
  set g02 := dotProduct (v 0) (Q.mulVec (v 2))
  set g12 := dotProduct (v 1) (Q.mulVec (v 2))
  have s10 : dotProduct (v 1) (Q.mulVec (v 0)) = g01 := ggResI_dot_symm hQ _ _
  have s20 : dotProduct (v 2) (Q.mulVec (v 0)) = g02 := ggResI_dot_symm hQ _ _
  have s21 : dotProduct (v 2) (Q.mulVec (v 1)) = g12 := ggResI_dot_symm hQ _ _
  have hn0 : 0 < n0 := hQ.2 _ hv
  have e11 : dotProduct (n0 • v 1 - g01 • v 0) (Q.mulVec (n0 • v 1 - g01 • v 0)) =
      n0 * (n0 * n1 - g01 ^ 2) := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [s10]
    ring
  have e22 : dotProduct (n0 • v 2 - g02 • v 0) (Q.mulVec (n0 • v 2 - g02 • v 0)) =
      n0 * (n0 * n2 - g02 ^ 2) := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [s20]
    ring
  have e12 : dotProduct (n0 • v 1 - g01 • v 0) (Q.mulVec (n0 • v 2 - g02 • v 0)) =
      n0 * (n0 * g12 - g01 * g02) := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [s10]
    ring
  have hCS := ggResI_dot_sq_le hQ (n0 • v 1 - g01 • v 0) (n0 • v 2 - g02 • v 0)
  rw [e11, e22, e12] at hCS
  have h1 : n0 ^ 2 * (n0 * g12 - g01 * g02) ^ 2 ≤
      n0 ^ 2 * ((n0 * n1 - g01 ^ 2) * (n0 * n2 - g02 ^ 2)) := by nlinarith
  have h2 : (n0 * g12 - g01 * g02) ^ 2 ≤ (n0 * n1 - g01 ^ 2) * (n0 * n2 - g02 ^ 2) :=
    le_of_mul_le_mul_left h1 (by positivity)
  have h3 : 0 ≤ n0 * (n0 * n1 * n2 - n2 * g01 ^ 2 - n1 * g02 ^ 2 - n0 * g12 ^ 2 +
      2 * g01 * g02 * g12) := by nlinarith
  exact (mul_nonneg_iff_of_pos_left hn0).mp h3

theorem ggResI_triLift {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hQ : GGLatForm Q)
    {v : Fin 3 → Fin m → ℤ}
    (hroot : ∀ k, GGLatRoot Q (v k)) {μ : Fin 3 → ZMod p} (hμ : ∀ k, μ k ≠ 0)
    {a : Fin 3 → Fin 3 → ZMod p}
    (ha : ∀ i k : Fin 3, a i k * μ k = μ i * (ggLatCartan Q (v k) (v i) : ZMod p)) :
    GGTriLift p a := by
  set N : Fin 3 → Fin 3 → ℤ := fun k i => ggLatCartan Q (v k) (v i) with hN
  have ha' : ∀ i k, a i k = μ i * (N k i : ZMod p) * (μ k)⁻¹ := by
    intro i k
    rw [← ha i k, mul_assoc, mul_inv_cancel₀ (hμ k), mul_one]
  have hNn : ∀ k i, N k i * dotProduct (v i) (Q.mulVec (v i)) =
      2 * dotProduct (v k) (Q.mulVec (v i)) := fun k i => Int.ediv_mul_cancel ((hroot i).2 (v k))
  have hpos : ∀ i, 0 < dotProduct (v i) (Q.mulVec (v i)) := fun i => hQ.2 _ (hroot i).1
  have hP : ∀ i k, 0 ≤ N i k * N k i ∧ N i k * N k i ≤ 4 := fun i k =>
    ggResII_latCartan_mul_mem hQ (hroot i) (hroot k)
  set n0 := dotProduct (v 0) (Q.mulVec (v 0))
  set n1 := dotProduct (v 1) (Q.mulVec (v 1))
  set n2 := dotProduct (v 2) (Q.mulVec (v 2))
  set g01 := dotProduct (v 0) (Q.mulVec (v 1))
  set g02 := dotProduct (v 0) (Q.mulVec (v 2))
  set g12 := dotProduct (v 1) (Q.mulVec (v 2))
  have s10 : dotProduct (v 1) (Q.mulVec (v 0)) = g01 := ggResI_dot_symm hQ _ _
  have s20 : dotProduct (v 2) (Q.mulVec (v 0)) = g02 := ggResI_dot_symm hQ _ _
  have s21 : dotProduct (v 2) (Q.mulVec (v 1)) = g12 := ggResI_dot_symm hQ _ _
  have e10 : N 1 0 * n0 = 2 * g01 := by rw [hNn 1 0, s10]
  have e01 : N 0 1 * n1 = 2 * g01 := hNn 0 1
  have e20 : N 2 0 * n0 = 2 * g02 := by rw [hNn 2 0, s20]
  have e02 : N 0 2 * n2 = 2 * g02 := hNn 0 2
  have e21 : N 2 1 * n1 = 2 * g12 := by rw [hNn 2 1, s21]
  have e12 : N 1 2 * n2 = 2 * g12 := hNn 1 2
  have hn0 := hpos 0
  have hn1 := hpos 1
  have hn2 := hpos 2
  have hn : 0 < n0 * n1 * n2 := by positivity
  have hτ : N 1 0 * N 2 1 * N 0 2 = N 2 0 * N 1 2 * N 0 1 := by
    have h1 : N 1 0 * N 2 1 * N 0 2 * (n0 * n1 * n2) = (N 1 0 * n0) * (N 2 1 * n1) * (N 0 2 * n2) := by
      ring
    have h2 : N 2 0 * N 1 2 * N 0 1 * (n0 * n1 * n2) = (N 2 0 * n0) * (N 1 2 * n2) * (N 0 1 * n1) := by
      ring
    have h3 : N 1 0 * N 2 1 * N 0 2 * (n0 * n1 * n2) = N 2 0 * N 1 2 * N 0 1 * (n0 * n1 * n2) := by
      rw [h1, h2, e10, e21, e02, e20, e12, e01]
      ring
    exact mul_right_cancel₀ hn.ne' h3
  have hgram : 0 ≤ 4 - N 0 1 * N 1 0 - N 0 2 * N 2 0 - N 1 2 * N 2 1 + N 1 0 * N 2 1 * N 0 2 := by
    have hdet := ggResI_gram_det_nonneg hQ v (hroot 0).1
    have hG : (4 - N 0 1 * N 1 0 - N 0 2 * N 2 0 - N 1 2 * N 2 1 + N 1 0 * N 2 1 * N 0 2) *
        (n0 * n1 * n2) = 4 * n0 * n1 * n2 - (N 1 0 * n0) * (N 0 1 * n1) * n2 -
          (N 2 0 * n0) * (N 0 2 * n2) * n1 - (N 2 1 * n1) * (N 1 2 * n2) * n0 +
          (N 1 0 * n0) * (N 2 1 * n1) * (N 0 2 * n2) := by ring
    rw [e10, e01, e20, e02, e21, e12] at hG
    have hG' : (4 - N 0 1 * N 1 0 - N 0 2 * N 2 0 - N 1 2 * N 2 1 + N 1 0 * N 2 1 * N 0 2) *
        (n0 * n1 * n2) = 4 * (n0 * n1 * n2 - n2 * g01 ^ 2 - n1 * g02 ^ 2 - n0 * g12 ^ 2 +
          2 * g01 * g02 * g12) := by rw [hG]; ring
    have h4 : 0 ≤ (4 - N 0 1 * N 1 0 - N 0 2 * N 2 0 - N 1 2 * N 2 1 + N 1 0 * N 2 1 * N 0 2) *
        (n0 * n1 * n2) := by rw [hG']; linarith
    exact (mul_nonneg_iff_of_pos_right hn).mp h4
  have hzN : ∀ i k, N k i = 0 ↔ N i k = 0 := by
    intro i k
    have h1 := hNn k i
    have h2 := hNn i k
    have hs : dotProduct (v k) (Q.mulVec (v i)) = dotProduct (v i) (Q.mulVec (v k)) :=
      ggResI_dot_symm hQ (v i) (v k)
    constructor
    · intro h0
      rw [h0, zero_mul] at h1
      have hg : dotProduct (v i) (Q.mulVec (v k)) = 0 := by rw [← hs]; linarith
      rw [hg, mul_zero] at h2
      exact (mul_eq_zero.mp h2).resolve_right (hpos k).ne'
    · intro h0
      rw [h0, zero_mul] at h2
      have hg : dotProduct (v k) (Q.mulVec (v i)) = 0 := by rw [hs]; linarith
      rw [hg, mul_zero] at h1
      exact (mul_eq_zero.mp h1).resolve_right (hpos i).ne'
  have hmod : ∀ i k, (N k i : ZMod p) = 0 → N k i = 0 := by
    intro i k h0
    by_contra hne
    have hne' : N i k ≠ 0 := fun h => hne ((hzN i k).mpr h)
    have hb : |N k i| ≤ 4 := by
      have hpk := hP i k
      have h1 : 1 ≤ |N i k| := Int.one_le_abs hne'
      have h2 : |N i k * N k i| ≤ 4 := by rw [abs_le]; constructor <;> linarith [hpk.1, hpk.2]
      rw [abs_mul] at h2
      nlinarith [abs_nonneg (N k i)]
    have hdvd : (p : ℤ) ∣ N k i := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
    have hlt : (N k i).natAbs < p := by
      have h4 : ((N k i).natAbs : ℤ) ≤ 4 := by rw [← Int.abs_eq_natAbs]; exact hb
      omega
    exact hne (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by simpa using hlt))
  have hzA : ∀ i k, a i k = 0 ↔ (N k i : ZMod p) = 0 := by
    intro i k
    rw [ha' i k]
    constructor
    · intro h0
      rcases mul_eq_zero.mp h0 with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · exact absurd h2 (hμ i)
        · exact h2
      · exact absurd h1 (inv_ne_zero (hμ k))
    · intro h0
      rw [h0, mul_zero, zero_mul]
  have hzero : ∀ i k : Fin 3, a i k = 0 ↔ a k i = 0 := by
    intro i k
    rw [hzA i k, hzA k i]
    constructor
    · intro h0
      rw [(hzN i k).mp (hmod i k h0)]
      simp
    · intro h0
      rw [(hzN k i).mp (hmod k i h0)]
      simp
  refine ⟨N 0 1 * N 1 0, N 0 2 * N 2 0, N 1 2 * N 2 1, N 1 0 * N 2 1 * N 0 2,
    (hP 0 1).1, (hP 0 1).2, (hP 0 2).1, (hP 0 2).2, (hP 1 2).1, (hP 1 2).2, ?_, ?_, ?_, ?_, ?_,
    ?_, hgram, hzero⟩
  · rw [ha' 0 1, ha' 1 0]
    have h0 := hμ 0
    have h1 := hμ 1
    push_cast
    field_simp
  · rw [ha' 0 2, ha' 2 0]
    have h0 := hμ 0
    have h2 := hμ 2
    push_cast
    field_simp
  · rw [ha' 1 2, ha' 2 1]
    have h1 := hμ 1
    have h2 := hμ 2
    push_cast
    field_simp
  · rw [ha' 0 1, ha' 1 2, ha' 2 0]
    have h0 := hμ 0
    have h1 := hμ 1
    have h2 := hμ 2
    push_cast
    field_simp
  · rw [hτ, ha' 0 2, ha' 2 1, ha' 1 0]
    have h0 := hμ 0
    have h1 := hμ 1
    have h2 := hμ 2
    push_cast
    field_simp
  · have : N 1 0 * N 2 1 * N 0 2 * (N 1 0 * N 2 1 * N 0 2) =
        N 1 0 * N 2 1 * N 0 2 * (N 2 0 * N 1 2 * N 0 1) := by rw [← hτ]
    rw [this]
    ring

end Lattice

section Refl

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

theorem ggResI_tri_of_comm {s t : V ≃ₗ[ZMod p] V} {h₁ h₂ : V}
    {α₁ α₂ : Module.Dual (ZMod p) V} (hsw : ∀ w, s w = w - α₁ w • h₁)
    (htw : ∀ w, t w = w - α₂ w • h₂) (hc : t * s = s * t) (α₀ : Module.Dual (ZMod p) V)
    (h₀ : V) : α₁ h₀ * α₂ h₁ * α₀ h₂ = α₂ h₀ * α₁ h₂ * α₀ h₁ := by
  have key : ∀ w, (α₁ w * α₂ h₁) • h₂ = (α₂ w * α₁ h₂) • h₁ := by
    intro w
    have h := congrArg (fun f : V ≃ₗ[ZMod p] V => f w) hc
    simp only [LinearEquiv.mul_apply] at h
    rw [hsw, htw, htw, hsw, map_sub, map_sub, map_smul, map_smul] at h
    simp only [smul_eq_mul] at h
    linear_combination (norm := module) h
  have k := congrArg α₀ (key h₀)
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at k
  exact k

theorem ggResI_not_comm (hp2 : p ≠ 2) {s t : V ≃ₗ[ZMod p] V} {h₀ h₁ h₂ : V}
    {α₀ α₁ α₂ : Module.Dual (ZMod p) V} (hsw : ∀ w, s w = w - α₁ w • h₁)
    (htw : ∀ w, t w = w - α₂ w • h₂) (h2s : α₁ h₁ = 2) (h2t : α₂ h₂ = 2)
    (hbad : (ggTriMat α₀ α₁ α₂ h₀ h₁ h₂ 1 2 * ggTriMat α₀ α₁ α₂ h₀ h₁ h₂ 2 1 ≠ 0 ∧
        ggTriMat α₀ α₁ α₂ h₀ h₁ h₂ 1 2 * ggTriMat α₀ α₁ α₂ h₀ h₁ h₂ 2 1 ≠ 4) ∨
      ggTriMat α₀ α₁ α₂ h₀ h₁ h₂ 0 1 * ggTriMat α₀ α₁ α₂ h₀ h₁ h₂ 1 2 *
          ggTriMat α₀ α₁ α₂ h₀ h₁ h₂ 2 0 ≠
        ggTriMat α₀ α₁ α₂ h₀ h₁ h₂ 0 2 * ggTriMat α₀ α₁ α₂ h₀ h₁ h₂ 2 1 *
          ggTriMat α₀ α₁ α₂ h₀ h₁ h₂ 1 0 ∨
      (ggTriMat α₀ α₁ α₂ h₀ h₁ h₂ 1 2 = 0 ∧ ggTriMat α₀ α₁ α₂ h₀ h₁ h₂ 2 1 ≠ 0) ∨
      (ggTriMat α₀ α₁ α₂ h₀ h₁ h₂ 1 2 ≠ 0 ∧ ggTriMat α₀ α₁ α₂ h₀ h₁ h₂ 2 1 = 0)) :
    t * s ≠ s * t := by
  intro hc
  simp only [ggTriMat, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hbad
  have h20 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have key : ∀ w, (α₁ w * α₂ h₁) • h₂ = (α₂ w * α₁ h₂) • h₁ := by
    intro w
    have h := congrArg (fun f : V ≃ₗ[ZMod p] V => f w) hc
    simp only [LinearEquiv.mul_apply] at h
    rw [hsw, htw, htw, hsw, map_sub, map_sub, map_smul, map_smul] at h
    simp only [smul_eq_mul] at h
    linear_combination (norm := module) h
  have hh₁ : h₁ ≠ 0 := by rintro rfl; rw [map_zero] at h2s; exact h20 h2s.symm
  have hh₂ : h₂ ≠ 0 := by rintro rfl; rw [map_zero] at h2t; exact h20 h2t.symm
  rcases hbad with ⟨h0, h4⟩ | hτ | ⟨h12, h21⟩ | ⟨h12, h21⟩
  · rcases ggResII_pair_of_comm hp2 hsw htw h2s h2t hc with h | h
    · exact h0 h
    · exact h4 h
  · apply hτ
    have := ggResI_tri_of_comm hsw htw hc α₀ h₀
    linear_combination -this
  · have k := key h₁
    rw [h2s, h12, mul_zero, zero_smul] at k
    exact hh₂ ((smul_eq_zero.mp k).resolve_left (mul_ne_zero h20 h21))
  · have k := key h₂
    rw [h2t, h21, mul_zero, zero_smul] at k
    exact hh₁ ((smul_eq_zero.mp k.symm).resolve_left (mul_ne_zero h20 h12))

end Refl

theorem ggResI_false_of_triBad (hJr : GGForkJr) (hPump : GGForkPumpOr) (hLB : GGLBalanceInput)
    (hSP : GGStdSubPrimeInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Option Λ → MulAut ↥Bs} {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o) (hα2 : ∀ o, α o (h o) = 2)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none}))
    (hJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ≠ b} => φ (some j)))
    {ψ : V ≃ₗ[ZMod p] V}
    (hψ : ψ ∈ Subgroup.closure (Set.range fun o => ggLin (p := p) ι (φ o))) {j j' : Λ}
    (hj : j ≠ b) (hj' : j' ≠ b)
    (hbad : GGTriBad p (ggTriMat (α (some j)) (α (some j'))
      ((α (some j)).comp (ψ⁻¹ : V ≃ₗ[ZMod p] V).toLinearMap) (h (some j)) (h (some j'))
      (ψ (h (some j))))) : False := by
  have hp2 : p ≠ 2 := by omega
  have hA := ggResI_sup_eq_closure hAL hAK
  rw [← ggResI_map_sup ι hA, hA] at hψ
  obtain ⟨ψ₀, hψ₀, rfl⟩ := Subgroup.mem_map.mp hψ
  set ht : V := ggLin (p := p) ι ψ₀ (h (some j)) with hht
  set αt : Module.Dual (ZMod p) V :=
    (α (some j)).comp ((ggLin (p := p) ι ψ₀)⁻¹ : V ≃ₗ[ZMod p] V).toLinearMap with hαt'
  have hαt : αt ht = 2 := by
    change α (some j) ((ggLin (p := p) ι ψ₀)⁻¹ (ggLin (p := p) ι ψ₀ (h (some j)))) = 2
    rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    exact hα2 (some j)
  have htl : ∀ w, ggLin (p := p) ι (ψ₀ * φ (some j) * ψ₀⁻¹) w = w - αt w • ht := by
    intro w
    rw [map_mul, map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hφ, map_sub,
      map_smul, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
    rfl
  have hnc : ψ₀ * φ (some j) * ψ₀⁻¹ * φ (some j') ≠ φ (some j') * (ψ₀ * φ (some j) * ψ₀⁻¹) := by
    intro hc
    have hc' : ggLin (p := p) ι (ψ₀ * φ (some j) * ψ₀⁻¹) * ggLin (p := p) ι (φ (some j')) =
        ggLin (p := p) ι (φ (some j')) * ggLin (p := p) ι (ψ₀ * φ (some j) * ψ₀⁻¹) := by
      rw [← map_mul, ← map_mul, hc]
    exact ggResI_not_comm hp2 (hφ (some j')) htl (hα2 (some j')) hαt hbad.1 hc'
  obtain ⟨m, Q, v, μ, hQ, hroot, hμ, hcongr⟩ := ggRC_lattice_triple hJr hPump hLB hSP hp5 hH
    hφ (hα2 (some j)) (hα2 (some j')) hAL hAK hJ hj hj' hψ₀ hαt htl hnc
  exact hbad.2 (ggResI_triLift hp5 hQ hroot hμ hcongr)

end CFSG.StandardType
