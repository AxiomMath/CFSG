module

public import CFSG.Milestones.ASVolI.F48.Core
public import CFSG.Milestones.ASVolI.F4L3
public import CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open

section L3Core

variable {K : Type} [Field K]

def burnsideF48_nMat (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0; 0, 0, -1; 0, 1, 0]

def burnsideF48_wMat (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 1; 1, 0, 0; 0, 1, 0]

def burnsideF48_dMat (a b c : K) : Matrix (Fin 3) (Fin 3) K :=
  !![a, 0, 0; 0, b, 0; 0, 0, c]

open Matrix in
theorem burnsideF48_det_nMat : (burnsideF48_nMat K).det = 1 := by
  simp [burnsideF48_nMat, Matrix.det_fin_three]

open Matrix in
theorem burnsideF48_det_wMat : (burnsideF48_wMat K).det = 1 := by
  simp [burnsideF48_wMat, Matrix.det_fin_three]

open Matrix in
theorem burnsideF48_det_dMat {a b c : K} (h : a * b * c = 1) : (burnsideF48_dMat a b c).det = 1 := by
  simp [burnsideF48_dMat, Matrix.det_fin_three, h]

def burnsideF48_nSL (K : Type) [Field K] : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨burnsideF48_nMat K, burnsideF48_det_nMat⟩

def burnsideF48_wSL (K : Type) [Field K] : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨burnsideF48_wMat K, burnsideF48_det_wMat⟩

def burnsideF48_dSL (a b c : K) (h : a * b * c = 1) : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨burnsideF48_dMat a b c, burnsideF48_det_dMat h⟩


open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem burnsideF48_mem_stabilizer_iff {n : ℕ} {K : Type} [Field K]
    (W : Submodule K (Fin n → K)) (A : Matrix.SpecialLinearGroup (Fin n) K) :
    A ∈ stabilizer W ↔
      ∀ v : Fin n → K, (A : Matrix (Fin n) (Fin n) K).mulVec v ∈ W ↔ v ∈ W := by
  have hinv : ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (A : Matrix (Fin n) (Fin n) K) = 1 := coe_inv_mul_coe A
  have hmul : (A : Matrix (Fin n) (Fin n) K) *
      ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [mem_stabilizer]
  constructor
  · intro h v
    constructor
    · intro hv
      rw [← h] at hv
      obtain ⟨w, hw, hwv⟩ := hv
      have h2 : (A : Matrix (Fin n) (Fin n) K).mulVec w = (A : Matrix (Fin n) (Fin n) K).mulVec v :=
        hwv
      have : w = v := by
        calc w = ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec
              ((A : Matrix (Fin n) (Fin n) K).mulVec w) := by
              rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
          _ = ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec
              ((A : Matrix (Fin n) (Fin n) K).mulVec v) := by rw [h2]
          _ = v := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      rw [this] at hw
      exact hw
    · intro hv
      rw [← h]
      exact ⟨v, hv, rfl⟩
  · intro h
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (h w).2 hw
    · intro hx
      have hv : ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x
          ∈ W := by
        refine (h _).1 ?_
        rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
        exact hx
      refine ⟨_, hv, ?_⟩
      show (A : Matrix (Fin n) (Fin n) K).mulVec
        (((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x) = x
      rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem burnsideF48_mem_flag_one {K : Type} [Field K] (v : Fin 3 → K) :
    v ∈ flagSpace 3 K 1 ↔ v 1 = 0 ∧ v 2 = 0 := by
  rw [mem_flagSpace]
  constructor
  · intro h
    exact ⟨h 1 (by decide), h 2 (by decide)⟩
  · rintro ⟨h1, h2⟩ j hj
    fin_cases j
    · exact absurd hj (by decide)
    · exact h1
    · exact h2

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem burnsideF48_mem_flag_two {K : Type} [Field K] (v : Fin 3 → K) :
    v ∈ flagSpace 3 K 2 ↔ v 2 = 0 := by
  rw [mem_flagSpace]
  constructor
  · intro h
    exact h 2 (by decide)
  · intro h2 j hj
    fin_cases j
    · exact absurd hj (by decide)
    · exact absurd hj (by decide)
    · exact h2

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem burnsideF48_mem_stab_one {K : Type} [Field K] (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    A ∈ stabilizer (flagSpace 3 K 1) ↔ ∀ v : Fin 3 → K,
      ((A : Matrix (Fin 3) (Fin 3) K).mulVec v 1 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) K).mulVec v 2 = 0) ↔
        (v 1 = 0 ∧ v 2 = 0) := by
  rw [burnsideF48_mem_stabilizer_iff]
  simp only [burnsideF48_mem_flag_one]

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem burnsideF48_mem_stab_two {K : Type} [Field K] (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    A ∈ stabilizer (flagSpace 3 K 2) ↔ ∀ v : Fin 3 → K,
      (A : Matrix (Fin 3) (Fin 3) K).mulVec v 2 = 0 ↔ v 2 = 0 := by
  rw [burnsideF48_mem_stabilizer_iff]
  simp only [burnsideF48_mem_flag_two]

theorem burnsideF48_nMat_mulVec (v : Fin 3 → K) :
    (burnsideF48_nMat K).mulVec v = ![v 0, -v 2, v 1] := by
  ext i
  fin_cases i <;> simp [burnsideF48_nMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem burnsideF48_wMat_mulVec (v : Fin 3 → K) :
    (burnsideF48_wMat K).mulVec v = ![v 2, v 0, v 1] := by
  ext i
  fin_cases i <;> simp [burnsideF48_wMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem burnsideF48_dMat_mulVec (a b c : K) (v : Fin 3 → K) :
    (burnsideF48_dMat a b c).mulVec v = ![a * v 0, b * v 1, c * v 2] := by
  ext i
  fin_cases i <;> simp [burnsideF48_dMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem burnsideF48_nSL_mem_stab_one :
    burnsideF48_nSL K ∈ stabilizer (flagSpace 3 K 1) := by
  rw [burnsideF48_mem_stab_one]
  intro v
  simp [burnsideF48_nSL, burnsideF48_nMat_mulVec, and_comm]

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem burnsideF48_nSL_not_mem_stab_two :
    burnsideF48_nSL K ∉ stabilizer (flagSpace 3 K 2) := by
  intro h
  rw [burnsideF48_mem_stab_two] at h
  have h1 := (h ![0, 1, 0]).2 (by simp)
  rw [show ((burnsideF48_nSL K : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    burnsideF48_nMat K from rfl, burnsideF48_nMat_mulVec] at h1
  simp at h1

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem burnsideF48_dSL_mem_stab_one {a b c : K} (h : a * b * c = 1) (hb : b ≠ 0) (hc : c ≠ 0) :
    burnsideF48_dSL a b c h ∈ stabilizer (flagSpace 3 K 1) := by
  rw [burnsideF48_mem_stab_one]
  intro v
  simp [burnsideF48_dSL, burnsideF48_dMat_mulVec, hb, hc]

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem burnsideF48_dSL_mem_stab_two {a b c : K} (h : a * b * c = 1) (hc : c ≠ 0) :
    burnsideF48_dSL a b c h ∈ stabilizer (flagSpace 3 K 2) := by
  rw [burnsideF48_mem_stab_two]
  intro v
  simp [burnsideF48_dSL, burnsideF48_dMat_mulVec, hc]

theorem burnsideF48_dSL_mul_nSL {a b c : K} (h : a * b * c = 1) (h' : a * c * b = 1) :
    burnsideF48_dSL a b c h * burnsideF48_nSL K = burnsideF48_nSL K * burnsideF48_dSL a c b h' := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  change burnsideF48_dMat a b c * burnsideF48_nMat K = burnsideF48_nMat K * burnsideF48_dMat a c b
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideF48_dMat, burnsideF48_nMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem burnsideF48_dSL_mul_wSL {a b c : K} (h : a * b * c = 1) (h' : b * c * a = 1) :
    burnsideF48_dSL a b c h * burnsideF48_wSL K = burnsideF48_wSL K * burnsideF48_dSL b c a h' := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  change burnsideF48_dMat a b c * burnsideF48_wMat K = burnsideF48_wMat K * burnsideF48_dMat b c a
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideF48_dMat, burnsideF48_wMat, Matrix.mul_apply, Fin.sum_univ_three]

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem burnsideF48_wSL_ne_mul {k l : Matrix.SpecialLinearGroup (Fin 3) K}
    (hk : k ∈ stabilizer (flagSpace 3 K 1)) (hl : l ∈ stabilizer (flagSpace 3 K 2)) :
    burnsideF48_wSL K ≠ k * l := by
  intro hwkl
  have hk' : k⁻¹ ∈ stabilizer (flagSpace 3 K 1) := (stabilizer _).inv_mem hk
  have hlk : l = k⁻¹ * burnsideF48_wSL K := by
    rw [hwkl, inv_mul_cancel_left]
  have h1 : (l : Matrix (Fin 3) (Fin 3) K).mulVec ![0, 0, 1] =
      (k⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K).1.mulVec ![1, 0, 0] := by
    rw [hlk, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
    congr 1
    rw [show ((burnsideF48_wSL K : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      burnsideF48_wMat K from rfl, burnsideF48_wMat_mulVec]
    simp
  have h2 := (burnsideF48_mem_stab_one _).1 hk' ![1, 0, 0]
  have h3 : (l : Matrix (Fin 3) (Fin 3) K).mulVec ![0, 0, 1] 2 = 0 := by
    rw [h1]
    exact (h2.2 (by simp)).2
  have h4 := ((burnsideF48_mem_stab_two _).1 hl ![0, 0, 1]).1 h3
  simp at h4

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem burnsideF48_proj_eq_mat {A B : Matrix.SpecialLinearGroup (Fin 3) K}
    (h : proj 3 K A = proj 3 K B) :
    ∃ c : K, (B : Matrix (Fin 3) (Fin 3) K) = (A : Matrix (Fin 3) (Fin 3) K) * Matrix.scalar (Fin 3) c := by
  obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_proj_iff.1 h)
  refine ⟨(c : K), ?_⟩
  have hB : B = A * (A⁻¹ * B) := (mul_inv_cancel_left A B).symm
  rw [hB, Matrix.SpecialLinearGroup.coe_mul, hc]

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem burnsideF48_unitri_cent {u : Kˣ} (hu : u ≠ 1) {q : projectiveSL 3 K}
    (hq : q ∈ projUnitriangular 3 K)
    (hnq : (proj 3 K (burnsideF48_nSL K))⁻¹ * q * proj 3 K (burnsideF48_nSL K) ∈
      projUnitriangular 3 K)
    (hc : proj 3 K (burnsideF48_dSL (1 : K) (u : K) ((u⁻¹ : Kˣ) : K) (by simp)) * q *
      (proj 3 K (burnsideF48_dSL (1 : K) (u : K) ((u⁻¹ : Kˣ) : K) (by simp)))⁻¹ = q) :
    q = 1 := by
  obtain ⟨Q, hQ, rfl⟩ := hq
  obtain ⟨R, hR, hRQ⟩ := hnq
  set n : Matrix.SpecialLinearGroup (Fin 3) K := burnsideF48_nSL K with hn
  set H : Matrix.SpecialLinearGroup (Fin 3) K :=
    burnsideF48_dSL (1 : K) (u : K) ((u⁻¹ : Kˣ) : K) (by simp) with hH
  have hQ12 : (Q : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by
    have hRQ' : proj 3 K R = proj 3 K (n⁻¹ * Q * n) := by
      rw [hRQ]
      simp [map_mul, map_inv]
    obtain ⟨c, hc'⟩ := burnsideF48_proj_eq_mat hRQ'
    have hmat : (Q : Matrix (Fin 3) (Fin 3) K) * (n : Matrix (Fin 3) (Fin 3) K) =
        (n : Matrix (Fin 3) (Fin 3) K) * ((R : Matrix (Fin 3) (Fin 3) K) *
          Matrix.scalar (Fin 3) c) := by
      have h1 : Q * n = n * (n⁻¹ * Q * n) := by group
      have h2 := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 3) K =>
        (X : Matrix (Fin 3) (Fin 3) K)) h1
      simp only [Matrix.SpecialLinearGroup.coe_mul] at h2 hc'
      rw [h2, hc']
    have h3 := congrFun (congrFun hmat 1) 1
    have hR21 : (R : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := hR.1 2 1 (by decide)
    simp [hn, burnsideF48_nSL, burnsideF48_nMat, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.scalar_apply, Matrix.diagonal_apply, hR21, hQ.1 1 0 (by decide), hQ.2 1] at h3
    exact h3
  have hQ01 : (Q : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 ∧ (Q : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 := by
    have hc1 : proj 3 K (H * Q) = proj 3 K (Q * H) := by
      rw [map_mul, map_mul]
      exact (mul_inv_eq_iff_eq_mul.1 hc)
    obtain ⟨c, hc'⟩ := burnsideF48_proj_eq_mat hc1
    simp only [Matrix.SpecialLinearGroup.coe_mul] at hc'
    have e00 := congrFun (congrFun hc' 0) 0
    have e01 := congrFun (congrFun hc' 0) 1
    have e02 := congrFun (congrFun hc' 0) 2
    have hu0 : (u : K) ≠ 0 := u.ne_zero
    simp [hH, burnsideF48_dSL, burnsideF48_dMat, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.vecMul, dotProduct,
      hQ.1 1 0 (by decide), hQ.1 2 0 (by decide),
      hQ.1 2 1 (by decide), hQ.2 0, hQ.2 1, hQ.2 2] at e00 e01 e02
    rw [← e00] at e01 e02
    exact ⟨e01.resolve_left fun h => hu (Units.ext h),
      e02.resolve_left fun h => hu (Units.ext (inv_eq_one.1 h))⟩
  obtain ⟨h01, h02⟩ := hQ01
  have hQ1 : Q = 1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [h01, h02, hQ12, hQ.1 1 0 (by decide), hQ.1 2 0 (by decide), hQ.1 2 1 (by decide),
        hQ.2 0, hQ.2 1, hQ.2 2]
  rw [hQ1, map_one]


open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem burnsideF48_proj_mem_projStabilizer {n : ℕ} (W : Submodule K (Fin n → K))
    (x : Matrix.SpecialLinearGroup (Fin n) K) :
    proj n K x ∈ projStabilizer W ↔ x ∈ stabilizer W := by
  rw [← comap_projStabilizer W]
  rfl

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem burnsideF48_L3_cartan_proj [Finite K] (hK : 3 ≤ Nat.card K) :
    ∃ n w h : projectiveSL 3 K,
      n ∈ projStabilizer (flagSpace 3 K 1) ∧ n ∉ projStabilizer (flagSpace 3 K 2) ∧
      h ∈ projStabilizer (flagSpace 3 K 1) ∧ h ∈ projStabilizer (flagSpace 3 K 2) ∧
      n⁻¹ * h * n ∈ projStabilizer (flagSpace 3 K 2) ∧
      w⁻¹ * h * w ∈ projStabilizer (flagSpace 3 K 2) ∧
      (¬ ∃ k ∈ projStabilizer (flagSpace 3 K 1), ∃ l ∈ projStabilizer (flagSpace 3 K 2),
        w = k * l) ∧
      ∀ q ∈ projUnitriangular 3 K, n⁻¹ * q * n ∈ projUnitriangular 3 K → h * q * h⁻¹ = q → q = 1 := by
  obtain ⟨u, hu⟩ : ∃ u : Kˣ, u ≠ 1 := by
    have h : 1 < Nat.card Kˣ := by rw [Nat.card_units K]; omega
    have := Finite.one_lt_card_iff_nontrivial.mp h
    exact exists_ne 1
  have hu0 : (u : K) ≠ 0 := u.ne_zero
  have hv0 : ((u⁻¹ : Kˣ) : K) ≠ 0 := (u⁻¹).ne_zero
  have hprod : (1 : K) * (u : K) * ((u⁻¹ : Kˣ) : K) = 1 := by simp
  have hprod' : (1 : K) * ((u⁻¹ : Kˣ) : K) * (u : K) = 1 := by simp
  have hprod'' : (u : K) * ((u⁻¹ : Kˣ) : K) * 1 = 1 := by simp
  set H : Matrix.SpecialLinearGroup (Fin 3) K := burnsideF48_dSL (1 : K) (u : K) ((u⁻¹ : Kˣ) : K) hprod
    with hH
  refine ⟨proj 3 K (burnsideF48_nSL K), proj 3 K (burnsideF48_wSL K), proj 3 K H, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [burnsideF48_proj_mem_projStabilizer]
    exact burnsideF48_nSL_mem_stab_one
  · rw [burnsideF48_proj_mem_projStabilizer]
    exact burnsideF48_nSL_not_mem_stab_two
  · rw [burnsideF48_proj_mem_projStabilizer]
    exact burnsideF48_dSL_mem_stab_one hprod hu0 hv0
  · rw [burnsideF48_proj_mem_projStabilizer]
    exact burnsideF48_dSL_mem_stab_two hprod hv0
  · rw [← map_inv, ← map_mul, ← map_mul, burnsideF48_proj_mem_projStabilizer]
    have h1 := burnsideF48_dSL_mul_nSL hprod hprod'
    have h2 : (burnsideF48_nSL K)⁻¹ * H * burnsideF48_nSL K =
        burnsideF48_dSL (1 : K) ((u⁻¹ : Kˣ) : K) (u : K) hprod' := by
      rw [mul_assoc, inv_mul_eq_iff_eq_mul]
      exact h1
    rw [h2]
    exact burnsideF48_dSL_mem_stab_two hprod' hu0
  · rw [← map_inv, ← map_mul, ← map_mul, burnsideF48_proj_mem_projStabilizer]
    have h1 := burnsideF48_dSL_mul_wSL hprod hprod''
    have h2 : (burnsideF48_wSL K)⁻¹ * H * burnsideF48_wSL K =
        burnsideF48_dSL (u : K) ((u⁻¹ : Kˣ) : K) (1 : K) hprod'' := by
      rw [mul_assoc, inv_mul_eq_iff_eq_mul]
      exact h1
    rw [h2]
    exact burnsideF48_dSL_mem_stab_two hprod'' one_ne_zero
  · rintro ⟨k, ⟨k₀, hk₀, rfl⟩, l, ⟨l₀, hl₀, rfl⟩, hkl⟩
    have hz := proj_eq_proj_iff.1 (hkl.trans (map_mul _ _ _).symm).symm
    have hz' : (k₀ * l₀)⁻¹ * burnsideF48_wSL K ∈ stabilizer (flagSpace 3 K 2) :=
      scalars_le_stabilizer _ hz
    refine burnsideF48_wSL_ne_mul hk₀ ((stabilizer (flagSpace 3 K 2)).mul_mem hl₀ hz') ?_
    group
  · intro q hq hnq hc
    exact burnsideF48_unitri_cent hu hq hnq hc

end L3Core


theorem burnsideF48_pCoreOf_le_self {E : Type} [Group E] (p : ℕ) (H : Subgroup E) :
    pCoreOf p H ≤ H :=
  Subgroup.map_subtype_le _

theorem burnsideF48_pCoreOf_conj {E : Type} [Group E] {p : ℕ} {H : Subgroup E} {g q : E}
    (hg : g ∈ H) (hq : q ∈ pCoreOf p H) : g * q * g⁻¹ ∈ pCoreOf p H := by
  obtain ⟨q₀, hq₀, rfl⟩ := hq
  haveI : (CFSG.pCore p ↥H).Normal := CFSG.LieType.BorelTits.pCore_normal p
  exact ⟨⟨g, hg⟩ * q₀ * ⟨g, hg⟩⁻¹, (inferInstance : (CFSG.pCore p ↥H).Normal).conj_mem q₀ hq₀ ⟨g, hg⟩,
    by simp⟩

theorem burnsideF48_mem_map_map {G' E : Type} [Group G'] [Group E] {Gp : Subgroup E}
    (ε : G' ≃* ↥Gp) (U : Subgroup G') (g : G') :
    ((ε g : ↥Gp) : E) ∈ (U.map ε.toMonoidHom).map Gp.subtype ↔ g ∈ U := by
  constructor
  · rintro ⟨x, ⟨u, hu, rfl⟩, hx⟩
    have : ε u = ε g := Subtype.ext hx
    rwa [ε.injective this] at hu
  · intro hg
    exact ⟨ε g, ⟨g, hg, rfl⟩, rfl⟩

theorem burnsideF48_split_two {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M₁ ⊓ M₂, e = n * h) {g : E} (hg : g ∈ Gp)
    (hkl : ∃ k ∈ M₁, ∃ l ∈ M₂, g = k * l) :
    ∃ k ∈ Gp ⊓ M₁, ∃ l ∈ Gp ⊓ M₂, g = k * l := by
  obtain ⟨k, hk, l, hl, rfl⟩ := hkl
  obtain ⟨n₁, hn₁, h₁, hh₁, hkn⟩ := hsplit k
  have hh₁1 : h₁ ∈ M₁ := (Subgroup.mem_inf.1 hh₁).1
  have hh₁2 : h₁ ∈ M₂ := (Subgroup.mem_inf.1 hh₁).2
  have hn₁M : n₁ ∈ M₁ := by
    have : n₁ = k * h₁⁻¹ := by rw [hkn]; group
    rw [this]
    exact M₁.mul_mem hk (M₁.inv_mem hh₁1)
  refine ⟨n₁, Subgroup.mem_inf.2 ⟨hn₁, hn₁M⟩, h₁ * l, Subgroup.mem_inf.2 ⟨?_, M₂.mul_mem hh₁2 hl⟩, ?_⟩
  · have : h₁ * l = n₁⁻¹ * (k * l) := by rw [hkn]; group
    rw [this]
    exact Gp.mul_mem (Gp.inv_mem hn₁) hg
  · rw [hkn]; group

theorem burnsideF48_split_three {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M₁ ⊓ M₂, e = n * h) {g : E} (hg : g ∈ Gp)
    (hkl : ∃ k ∈ M₁, ∃ l ∈ M₂, ∃ k' ∈ M₁, g = k * l * k') :
    ∃ k ∈ Gp ⊓ M₁, ∃ l ∈ Gp ⊓ M₂, ∃ k' ∈ Gp ⊓ M₁, g = k * l * k' := by
  obtain ⟨k, hk, l, hl, k', hk', rfl⟩ := hkl
  obtain ⟨n₁, hn₁, h₁, hh₁, hkn⟩ := hsplit k
  obtain ⟨n₂, hn₂, h₂, hh₂, hkn'⟩ := hsplit k'⁻¹
  have hh₁1 : h₁ ∈ M₁ := (Subgroup.mem_inf.1 hh₁).1
  have hh₁2 : h₁ ∈ M₂ := (Subgroup.mem_inf.1 hh₁).2
  have hh₂1 : h₂ ∈ M₁ := (Subgroup.mem_inf.1 hh₂).1
  have hh₂2 : h₂ ∈ M₂ := (Subgroup.mem_inf.1 hh₂).2
  have hn₁M : n₁ ∈ M₁ := by
    have : n₁ = k * h₁⁻¹ := by rw [hkn]; group
    rw [this]
    exact M₁.mul_mem hk (M₁.inv_mem hh₁1)
  have hk'eq : k' = h₂⁻¹ * n₂⁻¹ := by
    have : k' = (k'⁻¹)⁻¹ := (inv_inv k').symm
    rw [this, hkn']; group
  have hn₂M : n₂⁻¹ ∈ M₁ := by
    have : n₂⁻¹ = h₂ * k' := by rw [hk'eq]; group
    rw [this]
    exact M₁.mul_mem hh₂1 hk'
  refine ⟨n₁, Subgroup.mem_inf.2 ⟨hn₁, hn₁M⟩, h₁ * l * h₂⁻¹,
    Subgroup.mem_inf.2 ⟨?_, M₂.mul_mem (M₂.mul_mem hh₁2 hl) (M₂.inv_mem hh₂2)⟩, n₂⁻¹,
    Subgroup.mem_inf.2 ⟨Gp.inv_mem hn₂, hn₂M⟩, ?_⟩
  · have : h₁ * l * h₂⁻¹ = n₁⁻¹ * (k * l * k') * n₂ := by
      rw [hkn, hk'eq]; group
    rw [this]
    exact Gp.mul_mem (Gp.mul_mem (Gp.inv_mem hn₁) hg) hn₂
  · rw [hkn, hk'eq]; group


open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_cartanFPF_of_data_three {κ : ChF.GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ κ.m)
    (hκ : κ.m = 3) (hpoly : IsGenPolygon (burnsideF48_setting hyp hp hm).ι.graph 3)
    {G' : Type} [Group G'] (ε : G' ≃* ↥Gp) (P₁ P₂ U : Subgroup G')
    (hP₁ : ∀ g : G', ((ε g : ↥Gp) : E) ∈ M₁ ↔ g ∈ P₁)
    (hP₂ : ∀ g : G', ((ε g : ↥Gp) : E) ∈ M₂ ↔ g ∈ P₂)
    (hU : ChF.IsSylowOf p ((U.map ε.toMonoidHom).map Gp.subtype) Gp) (hUP : U ≤ P₁)
    (n w h : G') (hn1 : n ∈ P₁) (hn2 : n ∉ P₂) (hh1 : h ∈ P₁) (hh2 : h ∈ P₂)
    (hh3 : n⁻¹ * h * n ∈ P₂) (hh4 : w⁻¹ * h * w ∈ P₂)
    (hw : ¬ ∃ k ∈ P₁, ∃ l ∈ P₂, w = k * l)
    (hQ : ∀ q ∈ U, n⁻¹ * q * n ∈ U → h * q * h⁻¹ = q → q = 1) :
    (burnsideF48_setting hyp hp hm).CartanFPF := by
  haveI : Finite E := hyp.finite
  set ι : G' → E := fun g => ((ε g : ↥Gp) : E) with hι
  have hmul : ∀ a b, ι (a * b) = ι a * ι b := fun a b => by simp [hι]
  have hinv : ∀ a, ι a⁻¹ = (ι a)⁻¹ := fun a => by simp [hι]
  have hinj : Function.Injective ι := fun a b hab => ε.injective (Subtype.ext hab)
  have hmemGp : ∀ a, ι a ∈ Gp := fun a => (ε a).2
  have hconj : ∀ a b c : G', ι (a⁻¹ * b * c) = (ι a)⁻¹ * ι b * ι c := fun a b c => by
    rw [hmul, hmul, hinv]
  refine burnsideF48_cartanFPF_three hyp hp hm hκ hpoly (ι n) (ι w) (ι h) ((hP₁ n).2 hn1)
    (fun hc => hn2 ((hP₂ n).1 hc)) ((hP₁ h).2 hh1) ((hP₂ h).2 hh2) ?_ ?_ ?_ ?_
  · rw [← hconj]
    exact (hP₂ _).2 hh3
  · rw [← hconj]
    exact (hP₂ _).2 hh4
  · intro hkl
    obtain ⟨k, hk, l, hl, hwkl⟩ := burnsideF48_split_two hyp.split (hmemGp w) hkl
    have ha : ι (ε.symm ⟨k, (Subgroup.mem_inf.1 hk).1⟩) = k := by simp [hι]
    have hb : ι (ε.symm ⟨l, (Subgroup.mem_inf.1 hl).1⟩) = l := by simp [hι]
    refine hw ⟨ε.symm ⟨k, (Subgroup.mem_inf.1 hk).1⟩, (hP₁ _).1 (by show ι _ ∈ M₁; rw [ha]; exact (Subgroup.mem_inf.1 hk).2),
      ε.symm ⟨l, (Subgroup.mem_inf.1 hl).1⟩, (hP₂ _).1 (by show ι _ ∈ M₂; rw [hb]; exact (Subgroup.mem_inf.1 hl).2),
      hinj ?_⟩
    rw [hmul, ha, hb, hwkl]
  · intro q hq hcomm
    have hSP : (U.map ε.toMonoidHom).map Gp.subtype ≤ Gp ⊓ M₁ := by
      rintro _ ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      exact Subgroup.mem_inf.2 ⟨(ε u).2, (hP₁ u).2 (hUP hu)⟩
    have hcore := burnsideF48_pCoreOf_le_sylow hp hU hSP (inf_le_left : Gp ⊓ M₁ ≤ Gp)
    have hqGp : q ∈ Gp := (Subgroup.mem_inf.1 (burnsideF48_pCoreOf_le_self p _ hq)).1
    set q₀ : G' := ε.symm ⟨q, hqGp⟩ with hq₀
    have hιq₀ : ι q₀ = q := by simp [hι, hq₀]
    have hq₀U : q₀ ∈ U := by
      have := hcore hq
      rw [← hιq₀] at this
      exact (burnsideF48_mem_map_map ε U q₀).1 this
    have hnM : (ι n)⁻¹ ∈ Gp ⊓ M₁ :=
      (Gp ⊓ M₁).inv_mem (Subgroup.mem_inf.2 ⟨hmemGp n, (hP₁ n).2 hn1⟩)
    have hnqU : n⁻¹ * q₀ * n ∈ U := by
      have h1 : (ι n)⁻¹ * q * ι n ∈ pCoreOf p (Gp ⊓ M₁) := by
        simpa [inv_inv] using burnsideF48_pCoreOf_conj hnM hq
      have h2 := hcore h1
      rw [← hιq₀, ← hconj] at h2
      exact (burnsideF48_mem_map_map ε U _).1 h2
    have hcomm' : h * q₀ * h⁻¹ = q₀ := by
      apply hinj
      rw [hmul, hmul, hinv, hιq₀]
      exact hcomm
    have := hQ q₀ hq₀U hnqU hcomm'
    rw [← hιq₀, this]
    simp [hι]


open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_cartanFPF_of_data_four {κ : ChF.GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ κ.m)
    (hκ : κ.m = 4) (hpoly : IsGenPolygon (burnsideF48_setting hyp hp hm).ι.graph 4)
    {G' : Type} [Group G'] (ε : G' ≃* ↥Gp) (P₁ P₂ U : Subgroup G')
    (hP₁ : ∀ g : G', ((ε g : ↥Gp) : E) ∈ M₁ ↔ g ∈ P₁)
    (hP₂ : ∀ g : G', ((ε g : ↥Gp) : E) ∈ M₂ ↔ g ∈ P₂)
    (hU : ChF.IsSylowOf p ((U.map ε.toMonoidHom).map Gp.subtype) Gp) (hUP : U ≤ P₁)
    (n w h : G') (hn1 : n ∈ P₁) (hn2 : n ∉ P₂) (hh1 : h ∈ P₁) (hh2 : h ∈ P₂)
    (hh3 : n⁻¹ * h * n ∈ P₂) (hh4 : w⁻¹ * h * w ∈ P₁)
    (hw : ¬ ∃ k ∈ P₁, ∃ l ∈ P₂, ∃ k' ∈ P₁, w = k * l * k')
    (hQ : ∀ q ∈ U, n⁻¹ * q * n ∈ U → h * q * h⁻¹ = q → q = 1) :
    (burnsideF48_setting hyp hp hm).CartanFPF := by
  haveI : Finite E := hyp.finite
  set ι : G' → E := fun g => ((ε g : ↥Gp) : E) with hι
  have hmul : ∀ a b, ι (a * b) = ι a * ι b := fun a b => by simp [hι]
  have hinv : ∀ a, ι a⁻¹ = (ι a)⁻¹ := fun a => by simp [hι]
  have hinj : Function.Injective ι := fun a b hab => ε.injective (Subtype.ext hab)
  have hmemGp : ∀ a, ι a ∈ Gp := fun a => (ε a).2
  have hconj : ∀ a b c : G', ι (a⁻¹ * b * c) = (ι a)⁻¹ * ι b * ι c := fun a b c => by
    rw [hmul, hmul, hinv]
  refine burnsideF48_cartanFPF_four hyp hp hm hκ hpoly (ι n) (ι w) (ι h) ((hP₁ n).2 hn1)
    (fun hc => hn2 ((hP₂ n).1 hc)) ((hP₁ h).2 hh1) ((hP₂ h).2 hh2) ?_ ?_ ?_ ?_
  · rw [← hconj]
    exact (hP₂ _).2 hh3
  · rw [← hconj]
    exact (hP₁ _).2 hh4
  · intro hkl
    obtain ⟨k, hk, l, hl, k', hk', hwkl⟩ := burnsideF48_split_three hyp.split (hmemGp w) hkl
    have ha : ι (ε.symm ⟨k, (Subgroup.mem_inf.1 hk).1⟩) = k := by simp [hι]
    have hb : ι (ε.symm ⟨l, (Subgroup.mem_inf.1 hl).1⟩) = l := by simp [hι]
    have hc : ι (ε.symm ⟨k', (Subgroup.mem_inf.1 hk').1⟩) = k' := by simp [hι]
    refine hw ⟨ε.symm ⟨k, (Subgroup.mem_inf.1 hk).1⟩,
      (hP₁ _).1 (by show ι _ ∈ M₁; rw [ha]; exact (Subgroup.mem_inf.1 hk).2),
      ε.symm ⟨l, (Subgroup.mem_inf.1 hl).1⟩,
      (hP₂ _).1 (by show ι _ ∈ M₂; rw [hb]; exact (Subgroup.mem_inf.1 hl).2),
      ε.symm ⟨k', (Subgroup.mem_inf.1 hk').1⟩,
      (hP₁ _).1 (by show ι _ ∈ M₁; rw [hc]; exact (Subgroup.mem_inf.1 hk').2), hinj ?_⟩
    rw [hmul, hmul, ha, hb, hc, hwkl]
  · intro q hq hcomm
    have hSP : (U.map ε.toMonoidHom).map Gp.subtype ≤ Gp ⊓ M₁ := by
      rintro _ ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      exact Subgroup.mem_inf.2 ⟨(ε u).2, (hP₁ u).2 (hUP hu)⟩
    have hcore := burnsideF48_pCoreOf_le_sylow hp hU hSP (inf_le_left : Gp ⊓ M₁ ≤ Gp)
    have hqGp : q ∈ Gp := (Subgroup.mem_inf.1 (burnsideF48_pCoreOf_le_self p _ hq)).1
    set q₀ : G' := ε.symm ⟨q, hqGp⟩ with hq₀
    have hιq₀ : ι q₀ = q := by simp [hι, hq₀]
    have hq₀U : q₀ ∈ U := by
      have := hcore hq
      rw [← hιq₀] at this
      exact (burnsideF48_mem_map_map ε U q₀).1 this
    have hnM : (ι n)⁻¹ ∈ Gp ⊓ M₁ :=
      (Gp ⊓ M₁).inv_mem (Subgroup.mem_inf.2 ⟨hmemGp n, (hP₁ n).2 hn1⟩)
    have hnqU : n⁻¹ * q₀ * n ∈ U := by
      have h1 : (ι n)⁻¹ * q * ι n ∈ pCoreOf p (Gp ⊓ M₁) := by
        simpa [inv_inv] using burnsideF48_pCoreOf_conj hnM hq
      have h2 := hcore h1
      rw [← hιq₀, ← hconj] at h2
      exact (burnsideF48_mem_map_map ε U _).1 h2
    have hcomm' : h * q₀ * h⁻¹ = q₀ := by
      apply hinj
      rw [hmul, hmul, hinv, hιq₀]
      exact hcomm
    have := hQ q₀ hq₀U hnqU hcomm'
    rw [← hιq₀, this]
    simp [hι]


theorem burnsideF48_isSylowOf_of_equiv {p : ℕ} [Fact p.Prime] {E : Type} [Group E]
    {Gp : Subgroup E} {G' : Type} [Group G'] [Finite G'] (ε : G' ≃* ↥Gp) {U : Subgroup G'}
    (hU : ∃ P : Sylow p G', (P : Subgroup G') = U) :
    ChF.IsSylowOf p ((U.map ε.toMonoidHom).map Gp.subtype) Gp := by
  obtain ⟨P, rfl⟩ := hU
  refine ⟨Subgroup.map_subtype_le _, (P.isPGroup'.map ε.toMonoidHom).map Gp.subtype, ?_⟩
  have h1 : ((P.map ε.toMonoidHom).map Gp.subtype).subgroupOf Gp = P.map ε.toMonoidHom :=
    Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
  rw [Subgroup.relIndex, h1]
  change ¬ p ∣ ((P : Subgroup G').map (ε : G' →* ↥Gp)).index
  rw [Subgroup.index_map_equiv]
  exact P.not_dvd_index

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
noncomputable def burnsideF48_psi {p f : ℕ} {H : Type} [Group H]
    (marking : ChF.ClassicalRoots.Marking .L3 p f H) : H ≃* projectiveSL 3 marking.field :=
  marking.identification.symm.trans
    (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 marking.field).symm

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
private theorem burnsideF48_psi_transport {p f : ℕ} {H : Type} [Group H]
    (marking : ChF.ClassicalRoots.Marking .L3 p f H)
    (A : Matrix.SpecialLinearGroup (Fin 3) marking.field) :
    burnsideF48_psi marking (marking.transport
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 marking.field A)) =
      proj 3 marking.field A := by
  have h1 : CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 marking.field
      (proj 3 marking.field A) =
      (QuotientGroup.mk
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 marking.field A) :
        StatedProj (StatedSL 3 marking.field)) := rfl
  show (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 marking.field).symm
      (marking.identification.symm (marking.identification (QuotientGroup.mk _))) = _
  rw [MulEquiv.symm_apply_apply]
  exact (MulEquiv.symm_apply_eq _).2 h1.symm

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
private theorem burnsideF48_L3_comap_nativeParabolic (q : ℕ) (K : Type) [Field K]
    (basis : GL (Fin 3) K) (hb : basis = 1) (b : Bool) :
    (ChF.ClassicalRoots.nativeParabolic .L3 q K basis b).comap
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).toMonoidHom =
      stabilizer (flagSpace 3 K (if b then 2 else 1)) := by
  subst hb
  ext A
  have h1 : A ∈ (ChF.ClassicalRoots.nativeParabolic .L3 q K 1 b).comap
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).toMonoidHom ↔
      ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K A : GL (Fin 3) K)) ∈
        ChF.ClassicalRoots.rawStabilizer ((fun vector =>
            ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec vector) ''
          ChF.ClassicalRoots.coordinateSpace
            (if b then ChF.ClassicalRoots.flagTwo .L3 else ChF.ClassicalRoots.flagOne .L3 :
              Set (Fin 3))) :=
    Iff.rfl
  refine h1.trans ?_
  rw [burnsideF4d_Y1_mem_rawStabilizer, burnsideF4d_Y1_image_one,
    burnsideF4d_Y1_mem_stabilizer_iff]
  have key : ∀ (S : Set (Fin 3)) (i : ℕ), S = {p : Fin 3 | (p : ℕ) < i} →
      ((∀ v : Fin 3 → K, (A : Matrix (Fin 3) (Fin 3) K).mulVec v ∈
            ChF.ClassicalRoots.coordinateSpace S ↔ v ∈ ChF.ClassicalRoots.coordinateSpace S) ↔
        ∀ v : Fin 3 → K, (A : Matrix (Fin 3) (Fin 3) K).mulVec v ∈ flagSpace 3 K i ↔
          v ∈ flagSpace 3 K i) := by
    intro S i hS
    subst hS
    simp only [burnsideF4d_Y1_coordinateSpace_flag]
  cases b
  · exact key _ 1 (by ext p; simp [ChF.ClassicalRoots.flagOne] <;> omega)
  · exact key _ 2 (by ext p; simp [ChF.ClassicalRoots.flagTwo] <;> omega)

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem burnsideF48_psi_map_parabolic {p f : ℕ} {H : Type} [Group H]
    (marking : ChF.ClassicalRoots.Marking .L3 p f H) (b : Bool) :
    (marking.parabolic b).map (burnsideF48_psi marking).toMonoidHom =
      projStabilizer (flagSpace 3 marking.field (if b then 2 else 1)) := by
  have hbasis : marking.basis = 1 := marking.basis_compatible
  have key := burnsideF48_L3_comap_nativeParabolic (p ^ f) marking.field marking.basis hbasis b
  have hsurj := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3
    marking.field).surjective
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨A, rfl⟩ := hsurj z
    refine ⟨A, ?_, (burnsideF48_psi_transport marking A).symm⟩
    rw [← key]
    exact hz
  · rintro ⟨A, hA, rfl⟩
    rw [← key] at hA
    exact ⟨marking.transport (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3
      marking.field A), ⟨_, hA, rfl⟩, burnsideF48_psi_transport marking A⟩

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem burnsideF48_psi_mem_iff {p f : ℕ} {H : Type} [Group H]
    (marking : ChF.ClassicalRoots.Marking .L3 p f H) (b : Bool) (g : projectiveSL 3 marking.field) :
    (burnsideF48_psi marking).symm g ∈ marking.parabolic b ↔
      g ∈ projStabilizer (flagSpace 3 marking.field (if b then 2 else 1)) := by
  rw [← burnsideF48_psi_map_parabolic marking b]
  exact Subgroup.mem_map_equiv.symm


open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_cartanFPF_L3 {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .L3 p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ ChF.GLKind.L3.m)
    (hq : 3 ≤ p ^ f) (hpoly : IsGenPolygon (burnsideF48_setting hyp hp hm).ι.graph 3) :
    (burnsideF48_setting hyp hp hm).CartanFPF := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨marking, h1, h2⟩ := burnsideF48_marking (c := .L3) hyp.toHypF_4_4g
  have hK : Nat.card marking.field = p ^ f := by simpa using marking.field_card
  haveI : CharP marking.field p := by
    have := Fintype.ofFinite marking.field
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hK)
  obtain ⟨n, w, h, hn1, hn2, hh1, hh2, hh3, hh4, hw, hQ⟩ :=
    burnsideF48_L3_cartan_proj (K := marking.field) (by rw [hK]; exact hq)
  obtain ⟨SU, hSU⟩ := exists_sylow_projUnitriangular (K := marking.field) p (n := 3) (by norm_num)
  refine burnsideF48_cartanFPF_of_data_three hyp hp hm rfl hpoly (burnsideF48_psi marking).symm
    (projStabilizer (flagSpace 3 marking.field 1)) (projStabilizer (flagSpace 3 marking.field 2))
    (projUnitriangular 3 marking.field) ?_ ?_ (burnsideF48_isSylowOf_of_equiv _ ⟨SU, hSU⟩) ?_
    n w h hn1 hn2 hh1 hh2 hh3 hh4 hw hQ
  · intro g
    have := burnsideF48_psi_mem_iff marking false g
    simp only [Bool.false_eq_true, if_false] at this
    rw [← this, ← h1]
    exact Subgroup.mem_subgroupOf.symm
  · intro g
    have := burnsideF48_psi_mem_iff marking true g
    simp only [if_true] at this
    rw [← this, ← h2]
    exact Subgroup.mem_subgroupOf.symm
  · exact Subgroup.map_mono ((unitriangular_le_upperTriangular 3 marking.field).trans
      (upperTriangular_le_stabilizer_flagSpace 1))


theorem burnsideF48_simple_L3 {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .L3 p f Gp M₁ M₂) : IsSimpleGroup ↥Gp := by
  obtain ⟨-, -, K, hK, hKfin, -, ⟨e⟩⟩ := hyp.model
  haveI : IsSimpleGroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K) :=
    CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (n := 3) (K := K) le_rfl
  exact (e.trans (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 K).symm).isSimpleGroup

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_concl_L3 (hF : F_4_5) (hcompat : ChF.NativeChartCompatibilityGoal)
    {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .L3 p f Gp M₁ M₂) (hq : 3 ≤ p ^ f) : ChF.F48Concl .L3 p f Gp M₁ M₂ := by
  have hP := burnsideF48_parabolics_of_compat hcompat hyp
  have hp := ChF.burnsideF4a_prime_of_isGenLie hyp.model
  have hm := burnsideF48_three_le_m .L3
  have hL : ChF.GLKind.L3.IsLie :=
    show ChF.GLKind.L3 ≠ ChF.GLKind.G2d ∧ ChF.GLKind.L3 ≠ ChF.GLKind.Tits from
      ⟨by decide, by decide⟩
  refine burnsideF48_concl_of_F45_cartan hF hyp hL (burnsideF48_simple_L3 hyp) hP ?_
  exact burnsideF48_cartanFPF_L3 hyp hp hm hq (burnsideF48_facts45L_of_F45 hF hyp hL hp hm hP).poly

end CFSG.ASVolI
