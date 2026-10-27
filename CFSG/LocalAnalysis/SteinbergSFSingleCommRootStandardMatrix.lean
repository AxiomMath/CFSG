module

public import CFSG.LocalAnalysis.SteinbergSFFullCenterTorusComplementBase

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace RootStandard

open Subgroup Matrix
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis GomiFusion FullCenterTorus
open scoped commutatorElement

variable {K : Type} [Field K]

@[expose] def rootMat : Axis → Matrix (Fin 2) (Fin 2) K → Matrix (Fin 4) (Fin 4) K
  | .one => fun A =>
    !![A 0 0, 0, A 0 1, 0; 0, A 0 0, 0, A 0 1; A 1 0, 0, A 1 1, 0; 0, A 1 0, 0, A 1 1]
  | .two => fun A => !![A 0 0, 0, 0, A 0 1; 0, 1, 0, 0; 0, 0, 1, 0; A 1 0, 0, 0, A 1 1]

theorem rootMat_mul (k : Axis) (A B : Matrix (Fin 2) (Fin 2) K) :
    rootMat k A * rootMat k B = rootMat k (A * B) := by
  cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMat, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem rootMat_one (k : Axis) : rootMat k (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [rootMat]

variable [CharP K 2]

theorem rootMat_mem (k : Axis) {A : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1) :
    (rootMat k A)ᵀ * minorJ K * rootMat k A = minorJ K := by
  rw [Matrix.det_fin_two] at hA
  cases k <;> ext i j <;> rw [transpose_mul_minorJ_mul_apply, minorJ_apply] <;>
    fin_cases i <;> fin_cases j <;> simp [rootMat] <;> grind

@[expose] def rootElt (k : Axis) (A : SL₂ K) : antiSp K :=
  ⟨⟨rootMat k (A : Matrix (Fin 2) (Fin 2) K), rootMat k ((A⁻¹ : SL₂ K) : Matrix (Fin 2) (Fin 2) K),
    by rw [rootMat_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, rootMat_one],
    by rw [rootMat_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, rootMat_one]⟩, rootMat_mem k A.2⟩

theorem glMat_rootElt (k : Axis) (A : SL₂ K) :
    glMat (rootElt k A : GL (Fin 4) K) = rootMat k (A : Matrix (Fin 2) (Fin 2) K) :=
  rfl

variable (K) in
@[expose] def rootSLHom (k : Axis) : SL₂ K →* antiSp K where
  toFun := rootElt k
  map_one' := antiSp_ext (by
    rw [glMat_rootElt, Matrix.SpecialLinearGroup.coe_one, rootMat_one]
    rfl)
  map_mul' A B := antiSp_ext (by
    change _ = glMat (rootElt k A : GL (Fin 4) K) * glMat (rootElt k B : GL (Fin 4) K)
    rw [glMat_rootElt, glMat_rootElt, glMat_rootElt, Matrix.SpecialLinearGroup.coe_mul,
      rootMat_mul])

theorem glMat_rootSLHom (k : Axis) (A : SL₂ K) :
    glMat (rootSLHom K k A : GL (Fin 4) K) = rootMat k (A : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem rootSLHom_injective (k : Axis) : Function.Injective (rootSLHom K k) := by
  intro A B h
  have h1 := congrArg (fun g : antiSp K => glMat (g : GL (Fin 4) K)) h
  simp only [glMat_rootSLHom] at h1
  ext i j
  cases k
  · fin_cases i <;> fin_cases j
    · simpa [rootMat] using congrFun (congrFun h1 0) 0
    · simpa [rootMat] using congrFun (congrFun h1 0) 2
    · simpa [rootMat] using congrFun (congrFun h1 2) 0
    · simpa [rootMat] using congrFun (congrFun h1 2) 2
  · fin_cases i <;> fin_cases j
    · simpa [rootMat] using congrFun (congrFun h1 0) 0
    · simpa [rootMat] using congrFun (congrFun h1 0) 3
    · simpa [rootMat] using congrFun (congrFun h1 3) 0
    · simpa [rootMat] using congrFun (congrFun h1 3) 3

@[expose] def upperSL (x : K) : SL₂ K :=
  ⟨!![1, x; 0, 1], by rw [Matrix.det_fin_two]; simp⟩

theorem rootCoord_eq_rootSLHom (k : Axis) (x : K) :
    rootCoord K k x = rootSLHom K k (upperSL x) := by
  apply antiSp_ext
  rw [glMat_rootSLHom]
  cases k
  · change uMat 0 x 0 0 = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uMat, rootMat, upperSL]
  · change uMat 0 0 x 0 = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uMat, rootMat, upperSL]

theorem rootU_le_range (k : Axis) : rootU K k ≤ (rootSLHom K k).range := by
  intro a ha
  obtain ⟨x, rfl⟩ := RootAxisTwoCore.exists_rootCoord_eq k ha
  exact ⟨upperSL x, (rootCoord_eq_rootSLHom k x).symm⟩

omit [CharP K 2] in
theorem diagMat_mul_rootMat_one (r : K) (A : Matrix (Fin 2) (Fin 2) K) :
    diagMat r r⁻¹ * rootMat .one A = rootMat .one A * diagMat r r⁻¹ := by
  ext i j
  rw [diagMat, diagonal_mul, mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [rootMat] <;> ring

omit [CharP K 2] in
theorem diagMat_mul_rootMat_two (s : K) (A : Matrix (Fin 2) (Fin 2) K) :
    diagMat 1 s * rootMat .two A = rootMat .two A * diagMat 1 s := by
  ext i j
  rw [diagMat, diagonal_mul, mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [rootMat]

theorem axisTorus_comm_rootSL (k : Axis) {δ : antiSp K} (hδ : δ ∈ axisTorus K k) (A : SL₂ K) :
    δ * rootSLHom K k A = rootSLHom K k A * δ := by
  apply antiSp_ext
  change glMat (δ : GL (Fin 4) K) * glMat (rootSLHom K k A : GL (Fin 4) K) =
    glMat (rootSLHom K k A : GL (Fin 4) K) * glMat (δ : GL (Fin 4) K)
  rw [glMat_rootSLHom]
  cases k
  · obtain ⟨r, -, hr⟩ := hδ
    rw [hr, diagMat_mul_rootMat_one]
  · obtain ⟨s, -, hs⟩ := hδ
    rw [hs, diagMat_mul_rootMat_two]

theorem eq_one_of_sq_eq_one {r : K} (h : r ^ 2 = 1) : r = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h5 : (r - 1) ^ 2 = 0 := by linear_combination h + (1 - r) * h2
  exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h5)

omit [CharP K 2] in
theorem eq_zero_of_mul_eq {x u v : K} (h : x * u = v * x) (huv : u ≠ v) : x = 0 := by
  have h1 : x * (u - v) = 0 := by linear_combination h
  exact (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr huv)

theorem exists_eq_two_of_comm {g : antiSp K} {s₀ : K} (hs₀ : s₀ ≠ 0) (hs₁ : s₀ ≠ 1)
    (hc : glMat (g : GL (Fin 4) K) * diagMat 1 s₀ = diagMat 1 s₀ * glMat (g : GL (Fin 4) K)) :
    ∃ δ ∈ axisTorus K .two, ∃ A : SL₂ K, g = δ * rootSLHom K .two A := by
  set X := glMat (g : GL (Fin 4) K) with hX
  have hent : ∀ a b : Fin 4, X a b * (![1, s₀⁻¹, s₀, 1] : Fin 4 → K) b =
      (![1, s₀⁻¹, s₀, 1] : Fin 4 → K) a * X a b := by
    intro a b
    have h1 := congrFun (congrFun hc a) b
    rw [diagMat, mul_diagonal, diagonal_mul] at h1
    simpa using h1
  have hi1 : s₀⁻¹ ≠ 1 := fun h => hs₁ (by rw [← inv_inv s₀, h, inv_one])
  have hii : s₀⁻¹ ≠ s₀ := by
    intro h
    refine hs₁ (eq_one_of_sq_eq_one ?_)
    calc s₀ ^ 2 = s₀⁻¹ * s₀ := by rw [h, sq]
      _ = 1 := inv_mul_cancel₀ hs₀
  have z01 : X 0 1 = 0 := eq_zero_of_mul_eq (by simpa using hent 0 1) hi1
  have z02 : X 0 2 = 0 := eq_zero_of_mul_eq (by simpa using hent 0 2) hs₁
  have z10 : X 1 0 = 0 := eq_zero_of_mul_eq (by simpa using hent 1 0) hi1.symm
  have z12 : X 1 2 = 0 := eq_zero_of_mul_eq (by simpa using hent 1 2) hii.symm
  have z13 : X 1 3 = 0 := eq_zero_of_mul_eq (by simpa using hent 1 3) hi1.symm
  have z20 : X 2 0 = 0 := eq_zero_of_mul_eq (by simpa using hent 2 0) hs₁.symm
  have z21 : X 2 1 = 0 := eq_zero_of_mul_eq (by simpa using hent 2 1) hii
  have z23 : X 2 3 = 0 := eq_zero_of_mul_eq (by simpa using hent 2 3) hs₁.symm
  have z31 : X 3 1 = 0 := eq_zero_of_mul_eq (by simpa using hent 3 1) hi1
  have z32 : X 3 2 = 0 := eq_zero_of_mul_eq (by simpa using hent 3 2) hs₁
  have hf : Xᵀ * minorJ K * X = minorJ K := g.2
  have f03 := congrFun (congrFun hf 0) 3
  have f12 := congrFun (congrFun hf 1) 2
  rw [transpose_mul_minorJ_mul_apply, minorJ_apply] at f03 f12
  simp only [z10, z20, z23, z13, z01, z02, z31, z32, z21, z12, mul_zero, add_zero,
    zero_add] at f03 f12
  norm_num at f03 f12
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hs : X 2 2 ≠ 0 := right_ne_zero_of_mul_eq_one f12
  have hX11 : X 1 1 = (X 2 2)⁻¹ := eq_inv_of_mul_eq_one_left f12
  obtain ⟨δ, -, hδ⟩ := exists_diagTorus (K := K) one_ne_zero hs
  refine ⟨δ, ⟨X 2 2, hs, hδ⟩, ⟨!![X 0 0, X 0 3; X 3 0, X 3 3], ?_⟩, antiSp_ext ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination f03 - X 0 3 * X 3 0 * h2
  · change X = glMat (δ : GL (Fin 4) K) * rootMat .two !![X 0 0, X 0 3; X 3 0, X 3 3]
    rw [hδ]
    ext a b
    rw [diagMat, diagonal_mul]
    fin_cases a <;> fin_cases b <;> simp [rootMat, z01, z02, z10, z12, z13, z20, z21, z23, z31,
      z32, hX11]

theorem exists_eq_one_of_comm [Finite K] {g : antiSp K} {r₀ : K} (hr₀ : r₀ ≠ 0) (hr₁ : r₀ ≠ 1)
    (hc : glMat (g : GL (Fin 4) K) * diagMat r₀ r₀⁻¹ =
      diagMat r₀ r₀⁻¹ * glMat (g : GL (Fin 4) K)) :
    ∃ δ ∈ axisTorus K .one, ∃ A : SL₂ K, g = δ * rootSLHom K .one A := by
  set X := glMat (g : GL (Fin 4) K) with hX
  have hent : ∀ a b : Fin 4, X a b * (![r₀⁻¹, r₀, r₀⁻¹, r₀] : Fin 4 → K) b =
      (![r₀⁻¹, r₀, r₀⁻¹, r₀] : Fin 4 → K) a * X a b := by
    intro a b
    have h1 := congrFun (congrFun hc a) b
    rw [diagMat, mul_diagonal, diagonal_mul] at h1
    simpa using h1
  have hii : r₀⁻¹ ≠ r₀ := by
    intro h
    refine hr₁ (eq_one_of_sq_eq_one ?_)
    calc r₀ ^ 2 = r₀⁻¹ * r₀ := by rw [h, sq]
      _ = 1 := inv_mul_cancel₀ hr₀
  have z01 : X 0 1 = 0 := eq_zero_of_mul_eq (by simpa using hent 0 1) hii.symm
  have z03 : X 0 3 = 0 := eq_zero_of_mul_eq (by simpa using hent 0 3) hii.symm
  have z10 : X 1 0 = 0 := eq_zero_of_mul_eq (by simpa using hent 1 0) hii
  have z12 : X 1 2 = 0 := eq_zero_of_mul_eq (by simpa using hent 1 2) hii
  have z21 : X 2 1 = 0 := eq_zero_of_mul_eq (by simpa using hent 2 1) hii.symm
  have z23 : X 2 3 = 0 := eq_zero_of_mul_eq (by simpa using hent 2 3) hii.symm
  have z30 : X 3 0 = 0 := eq_zero_of_mul_eq (by simpa using hent 3 0) hii
  have z32 : X 3 2 = 0 := eq_zero_of_mul_eq (by simpa using hent 3 2) hii
  have hf : Xᵀ * minorJ K * X = minorJ K := g.2
  have f03 := congrFun (congrFun hf 0) 3
  have f01 := congrFun (congrFun hf 0) 1
  have f23 := congrFun (congrFun hf 2) 3
  have f21 := congrFun (congrFun hf 2) 1
  rw [transpose_mul_minorJ_mul_apply, minorJ_apply] at f03 f01 f23 f21
  simp only [z01, z03, z10, z12, z21, z23, z30, z32, mul_zero, add_zero] at f03 f01 f23 f21
  norm_num at f03 f01 f23 f21
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set Δ := X 0 0 * X 2 2 - X 0 2 * X 2 0 with hΔ
  have e11 : Δ * X 1 1 = X 0 0 := by linear_combination X 0 0 * f21 - X 0 2 * f01
  have e13 : Δ * X 1 3 = X 0 2 := by
    linear_combination X 0 0 * f23 - X 0 2 * f03 - X 0 2 * h2
  have e31 : Δ * X 3 1 = X 2 0 := by
    linear_combination X 2 2 * f01 - X 2 0 * f21 - X 2 0 * h2
  have e33 : Δ * X 3 3 = X 2 2 := by linear_combination X 2 2 * f03 - X 2 0 * f23
  have hΔ0 : Δ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at e11 e13 e31 e33
    rw [← e11, ← e31] at f03
    simp at f03
  obtain ⟨ρ, hρ⟩ := exists_sq_eq Δ
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    exact hΔ0 (by rw [← hρ]; ring)
  obtain ⟨δ, -, hδ⟩ := exists_diagTorus (K := K) (inv_ne_zero hρ0) (inv_ne_zero (inv_ne_zero hρ0))
  refine ⟨δ, ⟨ρ⁻¹, inv_ne_zero hρ0, hδ⟩,
    ⟨!![ρ⁻¹ * X 0 0, ρ⁻¹ * X 0 2; ρ⁻¹ * X 2 0, ρ⁻¹ * X 2 2], ?_⟩, antiSp_ext ?_⟩
  · rw [Matrix.det_fin_two_of]
    have : ρ⁻¹ * X 0 0 * (ρ⁻¹ * X 2 2) - ρ⁻¹ * X 0 2 * (ρ⁻¹ * X 2 0) = (ρ ^ 2)⁻¹ * Δ := by
      rw [hΔ]
      field_simp
    rw [this, hρ, inv_mul_cancel₀ hΔ0]
  · change X = glMat (δ : GL (Fin 4) K) *
      rootMat .one !![ρ⁻¹ * X 0 0, ρ⁻¹ * X 0 2; ρ⁻¹ * X 2 0, ρ⁻¹ * X 2 2]
    rw [hδ]
    have hX11 : X 1 1 = (ρ ^ 2)⁻¹ * X 0 0 := by
      rw [hρ, ← e11]
      field_simp
    have hX13 : X 1 3 = (ρ ^ 2)⁻¹ * X 0 2 := by
      rw [hρ, ← e13]
      field_simp
    have hX31 : X 3 1 = (ρ ^ 2)⁻¹ * X 2 0 := by
      rw [hρ, ← e31]
      field_simp
    have hX33 : X 3 3 = (ρ ^ 2)⁻¹ * X 2 2 := by
      rw [hρ, ← e33]
      field_simp
    ext a b
    rw [diagMat, diagonal_mul]
    fin_cases a <;> fin_cases b <;>
      simp [rootMat, z01, z03, z10, z12, z21, z23, z30, z32, hX11, hX13, hX31, hX33] <;>
      field_simp

omit [CharP K 2] in
theorem axisTorus_comm (k : Axis) {δ δ' : antiSp K} (hδ : δ ∈ axisTorus K k)
    (hδ' : δ' ∈ axisTorus K k) : δ * δ' = δ' * δ := by
  obtain ⟨r, s, -, -, h1⟩ := axisTorus_le k hδ
  obtain ⟨r', s', -, -, h2⟩ := axisTorus_le k hδ'
  apply antiSp_ext
  change glMat (δ : GL (Fin 4) K) * glMat (δ' : GL (Fin 4) K) =
    glMat (δ' : GL (Fin 4) K) * glMat (δ : GL (Fin 4) K)
  rw [h1, h2, diagMat_mul_diagMat, diagMat_mul_diagMat, mul_comm r, mul_comm s]

theorem mem_centralizer_axisTorus_iff [Finite K] (hK : 2 < Nat.card K) (k : Axis)
    {g : antiSp K} : g ∈ centralizer (axisTorus K k : Set (antiSp K)) ↔
      ∃ δ ∈ axisTorus K k, ∃ A : SL₂ K, g = δ * rootSLHom K k A := by
  constructor
  · intro hg
    obtain ⟨r₀, hr₀, hr₁⟩ := exists_ne_zero_ne hK (1 : K)
    cases k
    · obtain ⟨δ₀, -, hδ₀⟩ := exists_diagTorus (K := K) hr₀ (inv_ne_zero hr₀)
      have hc := congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K))
        (mem_centralizer_iff.mp hg δ₀ ⟨r₀, hr₀, hδ₀⟩)
      refine exists_eq_one_of_comm hr₀ (Ne.symm hr₁) ?_
      change glMat (δ₀ : GL (Fin 4) K) * glMat (g : GL (Fin 4) K) =
        glMat (g : GL (Fin 4) K) * glMat (δ₀ : GL (Fin 4) K) at hc
      rw [hδ₀] at hc
      exact hc.symm
    · obtain ⟨δ₀, -, hδ₀⟩ := exists_diagTorus (K := K) one_ne_zero hr₀
      have hc := congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K))
        (mem_centralizer_iff.mp hg δ₀ ⟨r₀, hr₀, hδ₀⟩)
      refine exists_eq_two_of_comm hr₀ (Ne.symm hr₁) ?_
      change glMat (δ₀ : GL (Fin 4) K) * glMat (g : GL (Fin 4) K) =
        glMat (g : GL (Fin 4) K) * glMat (δ₀ : GL (Fin 4) K) at hc
      rw [hδ₀] at hc
      exact hc.symm
  · rintro ⟨δ, hδ, A, rfl⟩
    refine mem_centralizer_iff.mpr fun δ' hδ' => ?_
    rw [← mul_assoc, axisTorus_comm k hδ' hδ, mul_assoc, axisTorus_comm_rootSL k hδ' A,
      mul_assoc]

omit [CharP K 2] in
theorem axisTorus_le_centralizer (k : Axis) :
    axisTorus K k ≤ centralizer (axisTorus K k : Set (antiSp K)) := fun _ hδ =>
  mem_centralizer_iff.mpr fun _ hδ' => axisTorus_comm k hδ' hδ

theorem range_le_centralizer (k : Axis) :
    (rootSLHom K k).range ≤ centralizer (axisTorus K k : Set (antiSp K)) := by
  rintro _ ⟨A, rfl⟩
  exact mem_centralizer_iff.mpr fun _ hδ => axisTorus_comm_rootSL k hδ A

theorem centralizer_axisTorus_eq [Finite K] (hK : 2 < Nat.card K) (k : Axis) :
    centralizer (axisTorus K k : Set (antiSp K)) = axisTorus K k ⊔ (rootSLHom K k).range := by
  refine le_antisymm (fun g hg => ?_) (sup_le (axisTorus_le_centralizer k) (range_le_centralizer k))
  obtain ⟨δ, hδ, A, rfl⟩ := (mem_centralizer_axisTorus_iff hK k).mp hg
  exact mul_mem (mem_sup_left hδ) (mem_sup_right ⟨A, rfl⟩)

theorem commutatorElement_mul_left_of_comm {Y : Type*} [Group Y] {C : Subgroup Y} {z a b : Y}
    (hz : ∀ c ∈ C, z * c = c * z) (ha : a ∈ C) (hb : b ∈ C) : ⁅z * a, b⁆ = ⁅a, b⁆ := by
  have h1 := hz _ (mul_mem (mul_mem ha hb) (inv_mem ha))
  rw [commutatorElement_def, commutatorElement_def,
    show z * a * b * (z * a)⁻¹ * b⁻¹ = (z * (a * b * a⁻¹)) * z⁻¹ * b⁻¹ by group, h1]
  group

theorem commutatorElement_mul_right_of_comm {Y : Type*} [Group Y] {C : Subgroup Y} {z a b : Y}
    (hz : ∀ c ∈ C, z * c = c * z) (ha : a ∈ C) (hb : b ∈ C) : ⁅a, z * b⁆ = ⁅a, b⁆ := by
  have h1 := hz _ ha
  have h2 := hz _ (mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb))
  rw [commutatorElement_def, commutatorElement_def,
    show a * (z * b) * a⁻¹ * (z * b)⁻¹ = a * z * b * a⁻¹ * b⁻¹ * z⁻¹ by group,
    ← h1, show z * a * b * a⁻¹ * b⁻¹ * z⁻¹ = z * (a * b * a⁻¹ * b⁻¹) * z⁻¹ by group, h2]
  group

theorem commutator_centralizer_axisTorus [Finite K] (hK : 4 ≤ Nat.card K) (k : Axis) :
    ⁅centralizer (axisTorus K k : Set (antiSp K)), centralizer (axisTorus K k : Set (antiSp K))⁆ =
      (rootSLHom K k).range := by
  apply le_antisymm
  · rw [commutator_le]
    intro x hx y hy
    obtain ⟨δ, hδ, A, rfl⟩ := (mem_centralizer_axisTorus_iff (by omega) k).mp hx
    obtain ⟨δ', hδ', B, rfl⟩ := (mem_centralizer_axisTorus_iff (by omega) k).mp hy
    have hc : ∀ δ₀ ∈ axisTorus K k, ∀ c ∈ centralizer (axisTorus K k : Set (antiSp K)),
        δ₀ * c = c * δ₀ := fun δ₀ hδ₀ c hc => (mem_centralizer_iff.mp hc δ₀ hδ₀)
    rw [commutatorElement_mul_left_of_comm (hc δ hδ) (range_le_centralizer k ⟨A, rfl⟩) hy,
      commutatorElement_mul_right_of_comm (hc δ' hδ') (range_le_centralizer k ⟨A, rfl⟩)
        (range_le_centralizer k ⟨B, rfl⟩)]
    exact ⟨⁅A, B⁆, map_commutatorElement _ _ _⟩
  · have : Group.IsPerfect (SL₂ K) := sl2_isPerfect hK
    have : Group.IsPerfect (rootSLHom K k).range := Group.IsPerfect.range _
    calc (rootSLHom K k).range = ⁅(rootSLHom K k).range, (rootSLHom K k).range⁆ :=
          (Subgroup.commutator_eq_self).symm
      _ ≤ _ := commutator_mono (range_le_centralizer k) (range_le_centralizer k)

end RootStandard

end CFSG.LocalAnalysis.SymplecticFourStandard
