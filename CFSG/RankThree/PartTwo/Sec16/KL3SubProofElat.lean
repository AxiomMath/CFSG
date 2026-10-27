module

public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.RankThree.PartTwo.Sec16

namespace KL3SubProof

open Matrix

variable {K : Type} [Field K]

@[expose] def IsElat (g : GL (Fin 3) K) (a φ : Fin 3 → K) : Prop :=
  a ≠ 0 ∧ φ ≠ 0 ∧ φ ⬝ᵥ a = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) = 1 + vecMulVec a φ

theorem vecMulVec_mul_self {a φ : Fin 3 → K} (h : φ ⬝ᵥ a = 0) :
    vecMulVec a φ * vecMulVec a φ = 0 := by
  rw [vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero]

theorem det_one_add_vecMulVec (a φ : Fin 3 → K) :
    (1 + vecMulVec a φ : Matrix (Fin 3) (Fin 3) K).det = 1 + φ ⬝ᵥ a := by
  simp only [Matrix.det_fin_three, Matrix.add_apply, Matrix.one_apply, vecMulVec_apply,
    dotProduct, Fin.sum_univ_three]
  simp
  ring

theorem IsElat.det_eq_one {g : GL (Fin 3) K} {a φ : Fin 3 → K} (h : IsElat g a φ) :
    (g : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [h.2.2.2, det_one_add_vecMulVec, h.2.2.1, add_zero]

theorem IsElat.ne_one {g : GL (Fin 3) K} {a φ : Fin 3 → K} (h : IsElat g a φ) : g ≠ 1 := by
  intro hg
  have h1 := h.2.2.2
  rw [hg, Units.val_one, left_eq_add, vecMulVec_eq_zero] at h1
  exact h1.elim h.1 h.2.1

theorem IsElat.mul_self [CharP K 2] {g : GL (Fin 3) K} {a φ : Fin 3 → K} (h : IsElat g a φ) :
    g * g = 1 := by
  apply Units.ext
  have h0 := vecMulVec_mul_self h.2.2.1
  have h2 : vecMulVec a φ + vecMulVec a φ = 0 := by
    rw [← two_smul K, show (2 : K) = 0 from CharTwo.two_eq_zero, zero_smul]
  rw [Units.val_mul, Units.val_one, h.2.2.2]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, h0, add_zero]
  rw [add_assoc, h2, add_zero]

theorem exists_eq_vecMulVec_of_mul_self {N : Matrix (Fin 3) (Fin 3) K} (hN : N * N = 0)
    (h0 : N ≠ 0) : ∃ a φ : Fin 3 → K, a ≠ 0 ∧ φ ≠ 0 ∧ N = vecMulVec a φ := by
  set L := Matrix.toLin' N with hL
  have hLL : LinearMap.range L ≤ LinearMap.ker L := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker, hL, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
      hN, Matrix.zero_mulVec]
  have hrn := LinearMap.finrank_range_add_finrank_ker L
  rw [Module.finrank_fin_fun] at hrn
  have hle := Submodule.finrank_mono hLL
  have hne : LinearMap.range L ≠ ⊥ := by
    intro hb
    apply h0
    have hL0 : L = 0 := LinearMap.range_eq_bot.mp hb
    have : N = LinearMap.toMatrix' L := by rw [hL, LinearMap.toMatrix'_toLin']
    rw [this, hL0, map_zero]
  have hpos : Module.finrank K (LinearMap.range L) ≠ 0 := fun h =>
    hne (Submodule.finrank_eq_zero.mp h)
  have h1 : Module.finrank K (LinearMap.range L) = 1 := by omega
  obtain ⟨a, ha, hspan⟩ := finrank_eq_one_iff'.mp h1
  have hcol : ∀ j : Fin 3, ∃ c : K, c • (a : Fin 3 → K) = N *ᵥ Pi.single j 1 := by
    intro j
    obtain ⟨c, hc⟩ := hspan ⟨N *ᵥ Pi.single j 1, ⟨Pi.single j 1, rfl⟩⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  choose φ hφ using hcol
  have hNeq : N = vecMulVec (a : Fin 3 → K) φ := by
    ext i j
    have h := congrFun (hφ j) i
    rw [Matrix.mulVec_single_one] at h
    have h' : φ j * (a : Fin 3 → K) i = N i j := h
    rw [vecMulVec_apply, ← h', mul_comm]
  have ha0 : (a : Fin 3 → K) ≠ 0 := fun h => ha (Subtype.ext h)
  refine ⟨a, φ, ha0, ?_, hNeq⟩
  rintro rfl
  apply h0
  rw [hNeq, vecMulVec_zero]

theorem exists_isElat_of_mul_self [CharP K 2] {g : GL (Fin 3) K} (hg : g * g = 1) (h1 : g ≠ 1) :
    ∃ a φ : Fin 3 → K, IsElat g a φ := by
  set N := (g : Matrix (Fin 3) (Fin 3) K) - 1 with hNdef
  have hgg : (g : Matrix (Fin 3) (Fin 3) K) * g = 1 := by
    rw [← Units.val_mul, hg, Units.val_one]
  have hN : N * N = 0 := by
    rw [hNdef, sub_mul, mul_sub, mul_sub, hgg, Matrix.mul_one, Matrix.one_mul, Matrix.one_mul]
    have h2 : (1 : Matrix (Fin 3) (Fin 3) K) - g - (g - 1) = (2 : K) • (1 - g) := by
      rw [two_smul]
      abel
    rw [h2, show (2 : K) = 0 from CharTwo.two_eq_zero, zero_smul]
  have hN0 : N ≠ 0 := by
    intro h
    apply h1
    apply Units.ext
    rw [Units.val_one]
    exact sub_eq_zero.mp h
  obtain ⟨a, φ, ha, hφ, hNa⟩ := exists_eq_vecMulVec_of_mul_self hN hN0
  have hdot : φ ⬝ᵥ a = 0 := by
    have h2 : vecMulVec a ((φ ⬝ᵥ a) • φ) = 0 := by
      rw [← vecMulVec_mul_vecMulVec, ← hNa, hN]
    rcases vecMulVec_eq_zero.mp h2 with h | h
    · exact absurd h ha
    · exact (smul_eq_zero.mp h).resolve_right hφ
  refine ⟨a, φ, ha, hφ, hdot, ?_⟩
  rw [← hNa, hNdef, add_sub_cancel]

theorem IsElat.conj {g : GL (Fin 3) K} {a φ : Fin 3 → K} (h : IsElat g a φ) (x : GL (Fin 3) K) :
    IsElat (x * g * x⁻¹) ((x : Matrix (Fin 3) (Fin 3) K) *ᵥ a)
      (φ ᵥ* ((x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  obtain ⟨ha, hφ, hdot, hg⟩ := h
  have hxx : ((x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * x = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hxx' : (x : Matrix (Fin 3) (Fin 3) K) * ((x⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h0
    apply ha
    have := congrArg (fun v => ((x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) h0
    simpa [Matrix.mulVec_mulVec, hxx] using this
  · intro h0
    apply hφ
    have := congrArg (fun v => v ᵥ* (x : Matrix (Fin 3) (Fin 3) K)) h0
    simpa [Matrix.vecMul_vecMul, hxx] using this
  · rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hxx, Matrix.vecMul_one, hdot]
  · rw [Units.val_mul, Units.val_mul, hg, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hxx',
      mul_vecMulVec, vecMulVec_mul]

theorem exists_eq_smul_of_vecMulVec_eq {a φ b ψ : Fin 3 → K} (ha : a ≠ 0) (hφ : φ ≠ 0)
    (h : vecMulVec a φ = vecMulVec b ψ) : ∃ c : K, b = c • a := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hφ
  have hcol : ∀ i, a i * φ j = b i * ψ j := fun i => by
    have := congrFun (congrFun h i) j
    simpa [vecMulVec_apply] using this
  have hψj : ψ j ≠ 0 := by
    intro h0
    apply ha
    funext i
    have := hcol i
    rw [h0, mul_zero, mul_eq_zero] at this
    exact this.resolve_right hj
  refine ⟨φ j / ψ j, funext fun i => ?_⟩
  have := hcol i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj ⊢
  field_simp
  linear_combination -this

theorem exists_eq_smul_of_vecMulVec_eq' {a φ b ψ : Fin 3 → K} (ha : a ≠ 0) (hφ : φ ≠ 0)
    (h : vecMulVec a φ = vecMulVec b ψ) : ∃ c : K, ψ = c • φ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  have hrow : ∀ j, a i * φ j = b i * ψ j := fun j => by
    have := congrFun (congrFun h i) j
    simpa [vecMulVec_apply] using this
  have hbi : b i ≠ 0 := by
    intro h0
    apply hφ
    funext j
    have := hrow j
    rw [h0, zero_mul, mul_eq_zero] at this
    exact this.resolve_left hi
  refine ⟨a i / b i, funext fun j => ?_⟩
  have := hrow j
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
  field_simp
  linear_combination -this

theorem exists_eq_smul_of_dotProduct_eq_zero {u v x y : Fin 3 → K}
    (huv : LinearIndependent K ![u, v]) (hxu : u ⬝ᵥ x = 0) (hxv : v ⬝ᵥ x = 0)
    (hyu : u ⬝ᵥ y = 0) (hyv : v ⬝ᵥ y = 0) (hx : x ≠ 0) : ∃ c : K, y = c • x := by
  set w := crossProduct u v with hw
  have hw0 : w ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.mpr huv
  have hmul : ∀ z : Fin 3 → K, u ⬝ᵥ z = 0 → v ⬝ᵥ z = 0 → ∃ c : K, z = c • w := by
    intro z hzu hzv
    have hzw : crossProduct z w = 0 := by
      rw [hw, cross_cross_eq_smul_sub_smul', dotProduct_comm z v, hzv, hzu, zero_smul, zero_smul,
        sub_zero]
    by_contra hne
    push Not at hne
    have hli : LinearIndependent K ![w, z] := by
      rw [LinearIndependent.pair_iff' hw0]
      intro c hc
      exact hne c hc.symm
    have := crossProduct_ne_zero_iff_linearIndependent.mpr hli
    rw [← cross_anticomm, hzw, neg_zero] at this
    exact this rfl
  obtain ⟨c, rfl⟩ := hmul x hxu hxv
  obtain ⟨d, rfl⟩ := hmul y hyu hyv
  have hc : c ≠ 0 := by
    rintro rfl
    exact hx (zero_smul K w)
  exact ⟨d / c, by rw [smul_smul, div_mul_cancel₀ d hc]⟩

theorem IsElat.center_or_axis_of_commute {g h : GL (Fin 3) K} {a φ b ψ : Fin 3 → K}
    (hg : IsElat g a φ) (hh : IsElat h b ψ) (hc : g * h = h * g) :
    (∃ c : K, b = c • a) ∨ (∃ c : K, ψ = c • φ) := by
  obtain ⟨ha, hφ, hφa, hgm⟩ := hg
  obtain ⟨hb, hψ, hψb, hhm⟩ := hh
  have hm : vecMulVec a φ * vecMulVec b ψ = vecMulVec b ψ * vecMulVec a φ := by
    have h1 := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hc
    simp only [Units.val_mul, hgm, hhm] at h1
    have e1 : ((1 : Matrix (Fin 3) (Fin 3) K) + vecMulVec a φ) * (1 + vecMulVec b ψ) =
        1 + vecMulVec a φ + vecMulVec b ψ + vecMulVec a φ * vecMulVec b ψ := by noncomm_ring
    have e2 : ((1 : Matrix (Fin 3) (Fin 3) K) + vecMulVec b ψ) * (1 + vecMulVec a φ) =
        1 + vecMulVec a φ + vecMulVec b ψ + vecMulVec b ψ * vecMulVec a φ := by noncomm_ring
    rw [e1, e2] at h1
    exact add_left_cancel h1
  rw [vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec] at hm
  by_cases h1 : φ ⬝ᵥ b = 0
  · by_cases h2 : ψ ⬝ᵥ a = 0
    ·
      by_cases hli : LinearIndependent K ![φ, ψ]
      · left
        exact exists_eq_smul_of_dotProduct_eq_zero hli hφa h2 h1 hψb ha
      · right
        rw [LinearIndependent.pair_iff' hφ] at hli
        push Not at hli
        obtain ⟨c, hc⟩ := hli
        exact ⟨c, hc.symm⟩
    ·
      exfalso
      rw [h1, zero_smul, vecMulVec_zero] at hm
      have := vecMulVec_eq_zero.mp hm.symm
      rcases this with h | h
      · exact hb h
      · exact (smul_eq_zero.mp h).elim h2 hφ
  · left
    have hm' : vecMulVec b ((ψ ⬝ᵥ a) • φ) = vecMulVec ((φ ⬝ᵥ b) • a) ψ := by
      rw [hm.symm]
      ext i j
      simp [vecMulVec_apply, mul_comm, mul_left_comm]
    have hne : (ψ ⬝ᵥ a) • φ ≠ 0 := by
      intro h0
      rw [h0, vecMulVec_zero] at hm'
      rcases vecMulVec_eq_zero.mp hm'.symm with h | h
      · exact (smul_eq_zero.mp h).elim h1 ha
      · exact hψ h
    obtain ⟨c, hc⟩ := exists_eq_smul_of_vecMulVec_eq hb hne hm'
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul, smul_eq_zero] at hc
      exact hc.elim h1 ha
    refine ⟨(φ ⬝ᵥ b) / c, ?_⟩
    calc b = c⁻¹ • (c • b) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • ((φ ⬝ᵥ b) • a) := by rw [hc]
      _ = ((φ ⬝ᵥ b) / c) • a := by rw [smul_smul, div_eq_inv_mul]

theorem sq_mul_of_dotProduct_eq_zero [CharP K 2] {a φ b ψ : Fin 3 → K} (hφa : φ ⬝ᵥ a = 0)
    (hψb : ψ ⬝ᵥ b = 0) (hφb : φ ⬝ᵥ b = 0) :
    ((1 + vecMulVec a φ) * (1 + vecMulVec b ψ)) * ((1 + vecMulVec a φ) * (1 + vecMulVec b ψ)) =
      (1 + vecMulVec b ((ψ ⬝ᵥ a) • φ) : Matrix (Fin 3) (Fin 3) K) := by
  have hprod : (1 + vecMulVec a φ) * (1 + vecMulVec b ψ) =
      (1 + (vecMulVec a φ + vecMulVec b ψ) : Matrix (Fin 3) (Fin 3) K) := by
    have e : ((1 : Matrix (Fin 3) (Fin 3) K) + vecMulVec a φ) * (1 + vecMulVec b ψ) =
        1 + (vecMulVec a φ + vecMulVec b ψ) + vecMulVec a φ * vecMulVec b ψ := by noncomm_ring
    rw [e, vecMulVec_mul_vecMulVec, hφb, zero_smul, vecMulVec_zero, add_zero]
  rw [hprod]
  set N := vecMulVec a φ + vecMulVec b ψ with hN
  have hNN : N * N = vecMulVec b ((ψ ⬝ᵥ a) • φ) := by
    rw [hN]
    simp only [Matrix.add_mul, Matrix.mul_add, vecMulVec_mul_vecMulVec, hφa, hφb, hψb, zero_smul,
      vecMulVec_zero, zero_add, add_zero]
  have e : ((1 : Matrix (Fin 3) (Fin 3) K) + N) * (1 + N) = 1 + (N + N) + N * N := by
    noncomm_ring
  rw [e, hNN, ← two_smul K N, show (2 : K) = 0 from CharTwo.two_eq_zero, zero_smul, add_zero]

end KL3SubProof

end CFSG.RankThree.PartTwo.Sec16
