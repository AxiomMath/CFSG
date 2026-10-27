module

public import CFSG.LocalAnalysis.StandardType.GGTwE6FixedA2Type
public import CFSG.RankThree.PartOne.TCX.E.E6A2Sigma
public import CFSG.Mathlib.FieldTheory.InfiniteUnitPowers
public import CFSG.Mathlib.GroupTheory.CentralProductQuotient
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusSL3Algebraic
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusPSL3Two
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResL3ThreeFix

public noncomputable section

namespace CFSG.StandardType.TwE6FixedA2SL3

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableBExc.Three
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.TwE6HyperplaneTypes
  CFSG.StandardType.TwE6FixedA2Type CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.E6 (chain13 support13 chainRoot)

open CFSG.RankThree.PartOne.TCX.E (A2Std a2Std₁)

open scoped MatrixGroups

local instance tableBE6FixA2SL3NeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section WeightMatrix

open CFSG.LocalAnalysis.ComponentInitial

theorem eq_zero_of_forall_zpow_eq_one {Ω : Type} [Field Ω] [IsAlgClosed Ω] {k : ℤ}
    (h : ∀ u : Ωˣ, u ^ k = 1) : k = 0 := by
  by_contra hk
  obtain ⟨ζ, hζ⟩ :=
    CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_units_zpow_ne_one (L := Ω) hk
  exact hζ (h ζ)

theorem exists_weightMatrix_of_conj_rootDiagUnit {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (d : Ωˣ → Ωˣ → Fin Tag.E6.rank → Ωˣ) (w₁ w₂ : Label Tag.E6 → ℤ)
    (hd : ∀ s u ℓ, rootChar (d s u) (labelWt Tag.E6 ℓ) = s ^ w₁ ℓ * u ^ w₂ ℓ)
    (R : ModGL Tag.E6 Ω) (θ₁ θ₂ : Ωˣ → Ωˣ → Ωˣ)
    (h : ∀ s u, R * rootDiagUnit Tag.E6 (d s u) * R⁻¹ =
      rootDiagUnit Tag.E6 (d (θ₁ s u) (θ₂ s u)))
    {ℓ₁ ℓ₂ : Label Tag.E6} (h₁ : w₁ ℓ₁ = 1 ∧ w₂ ℓ₁ = 0) (h₂ : w₁ ℓ₂ = 0 ∧ w₂ ℓ₂ = 1) :
    ∃ b₁ b₂ : Label Tag.E6,
      (∀ s u, θ₁ s u = s ^ w₁ b₁ * u ^ w₂ b₁ ∧ θ₂ s u = s ^ w₁ b₂ * u ^ w₂ b₂) ∧
      (∀ a, ∃ b, w₁ b = w₁ b₁ * w₁ a + w₁ b₂ * w₂ a ∧ w₂ b = w₂ b₁ * w₁ a + w₂ b₂ * w₂ a) ∧
      (∀ b, ∃ a, w₁ b = w₁ b₁ * w₁ a + w₁ b₂ * w₂ a ∧ w₂ b = w₂ b₁ * w₁ a + w₂ b₂ * w₂ a) := by
  classical
  set R' : Module.End Ω (RootModule Tag.E6 Ω) := (R : Module.End Ω (RootModule Tag.E6 Ω))
  have key : ∀ (s u : Ωˣ) (a b : Label Tag.E6),
      ((s ^ w₁ b * u ^ w₂ b : Ωˣ) : Ω) * R' (Finsupp.single b 1) a =
        ((θ₁ s u ^ w₁ a * θ₂ s u ^ w₂ a : Ωˣ) : Ω) * R' (Finsupp.single b 1) a := by
    intro s u a b
    have e := congrArg (fun X : ModGL Tag.E6 Ω =>
      (X : Module.End Ω (RootModule Tag.E6 Ω)) (Finsupp.single b 1) a)
      (eq_mul_of_mul_inv_eq (h s u))
    simp only [Units.val_mul, Module.End.mul_apply] at e
    change R' (rootDiag (d s u) (Finsupp.single b 1)) a =
      rootDiag (d (θ₁ s u) (θ₂ s u)) (R' (Finsupp.single b 1)) a at e
    rw [rootDiag_single, map_smul, Finsupp.smul_apply, smul_eq_mul,
      CFSG.SeitzReduction.F4Pilot.rootDiag_apply, hd s u b, hd (θ₁ s u) (θ₂ s u) a] at e
    exact e
  have hrow : ∀ a : Label Tag.E6, ∃ b, R' (Finsupp.single b 1) a ≠ 0 := by
    intro a
    by_contra hcon
    push Not at hcon
    have hall : ∀ v : RootModule Tag.E6 Ω, R' v a = 0 := by
      intro v
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add f g hf hg => rw [map_add, Finsupp.add_apply, hf, hg, add_zero]
      | single b r =>
        rw [← mul_one r, ← smul_eq_mul, ← Finsupp.smul_single, map_smul, Finsupp.smul_apply,
          hcon b, smul_zero]
    have h1 := hall ((↑R⁻¹ : Module.End Ω (RootModule Tag.E6 Ω)) (Finsupp.single a 1))
    change ((R * R⁻¹ : ModGL Tag.E6 Ω) : Module.End Ω (RootModule Tag.E6 Ω))
      (Finsupp.single a 1) a = 0 at h1
    rw [mul_inv_cancel, Units.val_one, Module.End.one_apply, Finsupp.single_eq_same] at h1
    exact one_ne_zero h1
  have hcol : ∀ b : Label Tag.E6, ∃ a, R' (Finsupp.single b 1) a ≠ 0 := by
    intro b
    by_contra hcon
    push Not at hcon
    have h0 : R' (Finsupp.single b 1) = 0 := Finsupp.ext hcon
    have h1 := congrArg (↑R⁻¹ : Module.End Ω (RootModule Tag.E6 Ω)) h0
    change ((R⁻¹ * R : ModGL Tag.E6 Ω) : Module.End Ω (RootModule Tag.E6 Ω))
      (Finsupp.single b 1) = _ at h1
    rw [inv_mul_cancel, Units.val_one, Module.End.one_apply, map_zero] at h1
    have h2 := congrArg (fun v : RootModule Tag.E6 Ω => v b) h1
    simp only [Finsupp.single_eq_same, Finsupp.coe_zero, Pi.zero_apply] at h2
    exact one_ne_zero h2
  obtain ⟨b₁, hb₁⟩ := hrow ℓ₁
  obtain ⟨b₂, hb₂⟩ := hrow ℓ₂
  have hθ₁ : ∀ s u, θ₁ s u = s ^ w₁ b₁ * u ^ w₂ b₁ := by
    intro s u
    have e := mul_right_cancel₀ hb₁ (key s u ℓ₁ b₁)
    rw [h₁.1, h₁.2, zpow_one, zpow_zero, mul_one] at e
    exact (Units.ext e).symm
  have hθ₂ : ∀ s u, θ₂ s u = s ^ w₁ b₂ * u ^ w₂ b₂ := by
    intro s u
    have e := mul_right_cancel₀ hb₂ (key s u ℓ₂ b₂)
    rw [h₂.1, h₂.2, zpow_zero, zpow_one, one_mul] at e
    exact (Units.ext e).symm
  have hM : ∀ (a b : Label Tag.E6), R' (Finsupp.single b 1) a ≠ 0 →
      ∀ s u : Ωˣ, s ^ w₁ b * u ^ w₂ b =
        (s ^ w₁ b₁ * u ^ w₂ b₁) ^ w₁ a * (s ^ w₁ b₂ * u ^ w₂ b₂) ^ w₂ a := by
    intro a b hb s u
    have e : s ^ w₁ b * u ^ w₂ b = θ₁ s u ^ w₁ a * θ₂ s u ^ w₂ a :=
      Units.ext (mul_right_cancel₀ hb (key s u a b))
    rw [e, hθ₁ s u, hθ₂ s u]
  have hA : ∀ (a b : Label Tag.E6), R' (Finsupp.single b 1) a ≠ 0 →
      ∀ s : Ωˣ, s ^ w₁ b = s ^ (w₁ b₁ * w₁ a + w₁ b₂ * w₂ a) := by
    intro a b hb s
    have h := hM a b hb s 1
    simp only [one_zpow, mul_one] at h
    rw [← zpow_mul, ← zpow_mul, ← zpow_add] at h
    exact h
  have hB : ∀ (a b : Label Tag.E6), R' (Finsupp.single b 1) a ≠ 0 →
      ∀ u : Ωˣ, u ^ w₂ b = u ^ (w₂ b₁ * w₁ a + w₂ b₂ * w₂ a) := by
    intro a b hb u
    have h := hM a b hb 1 u
    simp only [one_zpow, one_mul] at h
    rw [← zpow_mul, ← zpow_mul, ← zpow_add] at h
    exact h
  have hw₁ : ∀ (a b : Label Tag.E6), R' (Finsupp.single b 1) a ≠ 0 →
      w₁ b = w₁ b₁ * w₁ a + w₁ b₂ * w₂ a := by
    intro a b hb
    have hk : w₁ b - (w₁ b₁ * w₁ a + w₁ b₂ * w₂ a) = 0 := by
      apply eq_zero_of_forall_zpow_eq_one (Ω := Ω)
      intro s
      rw [zpow_sub, hA a b hb s, mul_inv_cancel]
    exact sub_eq_zero.1 hk
  have hw₂ : ∀ (a b : Label Tag.E6), R' (Finsupp.single b 1) a ≠ 0 →
      w₂ b = w₂ b₁ * w₁ a + w₂ b₂ * w₂ a := by
    intro a b hb
    have hk : w₂ b - (w₂ b₁ * w₁ a + w₂ b₂ * w₂ a) = 0 := by
      apply eq_zero_of_forall_zpow_eq_one (Ω := Ω)
      intro u
      rw [zpow_sub, hB a b hb u, mul_inv_cancel]
    exact sub_eq_zero.1 hk
  refine ⟨b₁, b₂, fun s u => ⟨hθ₁ s u, hθ₂ s u⟩, ?_, ?_⟩
  · intro a
    obtain ⟨b, hb⟩ := hrow a
    exact ⟨b, hw₁ a b hb, hw₂ a b hb⟩
  · intro b
    obtain ⟨a, ha⟩ := hcol b
    exact ⟨a, hw₁ a b ha, hw₂ a b ha⟩

end WeightMatrix

@[expose] def fixedA2Word : List (Fin Tag.E6.rank) := ([2, 3, 4, 0, 2, 1, 3] : List (Fin 6))

@[expose] def fixedA2V : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd fixedA2Word

@[expose] def wtVec (k : Fin Tag.E6.rank) (μ : Fin Tag.E6.rank → ℤ) : ℤ :=
  ∑ j, (fixedA2Word.reverse.foldr (reflect Tag.E6) μ) j * Tag.E6.cartan k j

@[expose] def diagWtList : List (ℤ × ℤ) :=
  [(0, 0), (2, -1), (-2, 1), (-1, 2), (1, -2), (1, 1), (-1, -1), (1, 0), (-1, 0), (-1, 1),
    (1, -1), (0, -1), (0, 1)]

@[expose] def weylMatList : List ((ℤ × ℤ) × (ℤ × ℤ)) :=
  [((1, 0), (0, 1)), ((-1, 1), (0, 1)), ((1, 0), (1, -1)), ((0, -1), (-1, 0)),
    ((-1, 1), (-1, 0)), ((0, -1), (1, -1)),
    ((-1, 0), (0, -1)), ((1, -1), (0, -1)), ((-1, 0), (-1, 1)), ((0, 1), (1, 0)),
    ((1, -1), (1, 0)), ((0, 1), (-1, 1))]

set_option maxRecDepth 100000 in
theorem wtVec_mem_diagWtList : ∀ δ ∈ rootFinset .E6, (wtVec 0 δ, wtVec 2 δ) ∈ diagWtList := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem exists_wtVec_eq : ∀ μ ∈ diagWtList, μ = (0, 0) ∨
    ∃ δ ∈ rootFinset .E6, (wtVec 0 δ, wtVec 2 δ) = μ := by
  decide +kernel

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 100000 in
theorem weightMatrix_mem_weylMatList : ∀ μ ∈ diagWtList, ∀ ν ∈ diagWtList,
    (∀ α ∈ diagWtList, (μ.1 * α.1 + ν.1 * α.2, μ.2 * α.1 + ν.2 * α.2) ∈ diagWtList) →
    (∀ β ∈ diagWtList, ∃ α ∈ diagWtList, (μ.1 * α.1 + ν.1 * α.2, μ.2 * α.1 + ν.2 * α.2) = β) →
    (μ, ν) ∈ weylMatList := by
  decide +kernel

section DiagShape

variable {L : Type} [Field L]

@[expose] def diagSL3 {L : Type} [Field L] (s u : Lˣ) : SL(3, L) :=
  ⟨Matrix.diagonal ![(s : L), ((s⁻¹ * u : Lˣ) : L), ((u⁻¹ : Lˣ) : L)], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp⟩

@[expose] def permGL3 (P Q : Matrix (Fin 3) (Fin 3) L) (h₁ : P * Q = 1) (h₂ : Q * P = 1) :
    GL (Fin 3) L :=
  ⟨P, Q, h₁, h₂⟩

theorem invTransposeSL_diagSL3 (s u : Lˣ) :
    CFSG.RankThree.Classical2.invTransposeSL (diagSL3 s u) = diagSL3 s⁻¹ u⁻¹ := by
  have hinv : (diagSL3 s u)⁻¹ = diagSL3 s⁻¹ u⁻¹ := by
    rw [inv_eq_iff_mul_eq_one]
    ext i j
    change ((Matrix.diagonal ![(s : L), ((s⁻¹ * u : Lˣ) : L), ((u⁻¹ : Lˣ) : L)]) *
      (Matrix.diagonal ![((s⁻¹ : Lˣ) : L), ((s⁻¹⁻¹ * u⁻¹ : Lˣ) : L), ((u⁻¹⁻¹ : Lˣ) : L)])) i j =
        (1 : Matrix (Fin 3) (Fin 3) L) i j
    rw [Matrix.diagonal_mul_diagonal]
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply, Matrix.one_apply] <;> field_simp
  ext i j
  rw [CFSG.RankThree.Classical2.coe_invTransposeSL, hinv]
  change (Matrix.diagonal ![((s⁻¹ : Lˣ) : L), ((s⁻¹⁻¹ * u⁻¹ : Lˣ) : L),
      ((u⁻¹⁻¹ : Lˣ) : L)]).transpose i j =
    (Matrix.diagonal ![((s⁻¹ : Lˣ) : L), ((s⁻¹⁻¹ * u⁻¹ : Lˣ) : L), ((u⁻¹⁻¹ : Lˣ) : L)]) i j
  rw [Matrix.diagonal_transpose]

@[expose] def permGL3_12 : GL (Fin 3) L :=
  permGL3 !![0, 1, 0; 1, 0, 0; 0, 0, 1] !![0, 1, 0; 1, 0, 0; 0, 0, 1]
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three])
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three])

theorem diagSL3_perm_12 (s u : Lˣ) :
    diagSL3 (s⁻¹ * u) (u) = CFSG.RankThree.Classical2.conjSLn permGL3_12 (diagSL3 s u) := by
  ext i j
  rw [CFSG.RankThree.Classical2.coe_conjSLn]
  fin_cases i <;> fin_cases j <;>
    simp [permGL3_12, permGL3, diagSL3, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.diagonal_apply, Matrix.vecMul_diagonal] <;> ring

@[expose] def permGL3_23 : GL (Fin 3) L :=
  permGL3 !![1, 0, 0; 0, 0, 1; 0, 1, 0] !![1, 0, 0; 0, 0, 1; 0, 1, 0]
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three])
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three])

theorem diagSL3_perm_23 (s u : Lˣ) :
    diagSL3 (s) (s * u⁻¹) = CFSG.RankThree.Classical2.conjSLn permGL3_23 (diagSL3 s u) := by
  ext i j
  rw [CFSG.RankThree.Classical2.coe_conjSLn]
  fin_cases i <;> fin_cases j <;>
    simp [permGL3_23, permGL3, diagSL3, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.diagonal_apply, Matrix.vecMul_diagonal] <;> ring

@[expose] def permGL3_13 : GL (Fin 3) L :=
  permGL3 !![0, 0, 1; 0, 1, 0; 1, 0, 0] !![0, 0, 1; 0, 1, 0; 1, 0, 0]
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three])
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three])

theorem diagSL3_perm_13 (s u : Lˣ) :
    diagSL3 (u⁻¹) (s⁻¹) = CFSG.RankThree.Classical2.conjSLn permGL3_13 (diagSL3 s u) := by
  ext i j
  rw [CFSG.RankThree.Classical2.coe_conjSLn]
  fin_cases i <;> fin_cases j <;>
    simp [permGL3_13, permGL3, diagSL3, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.diagonal_apply, Matrix.vecMul_diagonal] <;> ring

@[expose] def permGL3_123 : GL (Fin 3) L :=
  permGL3 !![0, 1, 0; 0, 0, 1; 1, 0, 0] !![0, 0, 1; 1, 0, 0; 0, 1, 0]
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three])
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three])

theorem diagSL3_perm_123 (s u : Lˣ) :
    diagSL3 (s⁻¹ * u) (s⁻¹) = CFSG.RankThree.Classical2.conjSLn permGL3_123 (diagSL3 s u) := by
  ext i j
  rw [CFSG.RankThree.Classical2.coe_conjSLn]
  fin_cases i <;> fin_cases j <;>
    simp [permGL3_123, permGL3, diagSL3, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.diagonal_apply, Matrix.vecMul_diagonal] <;> ring

@[expose] def permGL3_132 : GL (Fin 3) L :=
  permGL3 !![0, 0, 1; 1, 0, 0; 0, 1, 0] !![0, 1, 0; 0, 0, 1; 1, 0, 0]
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three])
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three])

theorem diagSL3_perm_132 (s u : Lˣ) :
    diagSL3 (u⁻¹) (s * u⁻¹) = CFSG.RankThree.Classical2.conjSLn permGL3_132 (diagSL3 s u) := by
  ext i j
  rw [CFSG.RankThree.Classical2.coe_conjSLn]
  fin_cases i <;> fin_cases j <;>
    simp [permGL3_132, permGL3, diagSL3, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.diagonal_apply, Matrix.vecMul_diagonal] <;> ring

theorem exists_conj_diagSL3_perm (μ ν : ℤ × ℤ)
    (h : (μ, ν) ∈ [((1, 0), (0, 1)), ((-1, 1), (0, 1)), ((1, 0), (1, -1)), ((0, -1), (-1, 0)),
      ((-1, 1), (-1, 0)), ((0, -1), (1, -1))]) :
    ∃ A₀ : GL (Fin 3) L, ∀ s u : Lˣ, diagSL3 (s ^ μ.1 * u ^ μ.2) (s ^ ν.1 * u ^ ν.2) =
      CFSG.RankThree.Classical2.conjSLn A₀ (diagSL3 s u) := by
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨1, fun s u => ?_⟩
    ext i j
    simp [CFSG.RankThree.Classical2.coe_conjSLn]
  · exact ⟨permGL3_12, fun s u => by simpa using diagSL3_perm_12 s u⟩
  · exact ⟨permGL3_23, fun s u => by simpa using diagSL3_perm_23 s u⟩
  · exact ⟨permGL3_13, fun s u => by simpa using diagSL3_perm_13 s u⟩
  · exact ⟨permGL3_123, fun s u => by simpa using diagSL3_perm_123 s u⟩
  · exact ⟨permGL3_132, fun s u => by simpa using diagSL3_perm_132 s u⟩

theorem diagSL3_neg_of_conj (μ ν : ℤ × ℤ) (A₀ : GL (Fin 3) L)
    (hA : ∀ s u : Lˣ, diagSL3 (s ^ μ.1 * u ^ μ.2) (s ^ ν.1 * u ^ ν.2) =
      CFSG.RankThree.Classical2.conjSLn A₀ (diagSL3 s u)) (s u : Lˣ) :
    diagSL3 (s ^ (-μ.1) * u ^ (-μ.2)) (s ^ (-ν.1) * u ^ (-ν.2)) =
      CFSG.RankThree.Classical2.conjSLn A₀
        (CFSG.RankThree.Classical2.invTransposeSL (diagSL3 s u)) := by
  rw [invTransposeSL_diagSL3, ← hA s⁻¹ u⁻¹]
  simp only [inv_zpow', zpow_neg]

theorem exists_conj_diagSL3_of_mem_weylMatList (μ ν : ℤ × ℤ) (h : (μ, ν) ∈ weylMatList) :
    ∃ A₀ : GL (Fin 3) L,
      (∀ s u : Lˣ, diagSL3 (s ^ μ.1 * u ^ μ.2) (s ^ ν.1 * u ^ ν.2) =
        CFSG.RankThree.Classical2.conjSLn A₀ (diagSL3 s u)) ∨
      (∀ s u : Lˣ, diagSL3 (s ^ μ.1 * u ^ μ.2) (s ^ ν.1 * u ^ ν.2) =
        CFSG.RankThree.Classical2.conjSLn A₀
          (CFSG.RankThree.Classical2.invTransposeSL (diagSL3 s u))) := by
  have pos : ∀ μ' ν' : ℤ × ℤ, (μ', ν') ∈ [((1, 0), (0, 1)), ((-1, 1), (0, 1)), ((1, 0), (1, -1)),
      ((0, -1), (-1, 0)), ((-1, 1), (-1, 0)), ((0, -1), (1, -1))] →
      ∃ A₀ : GL (Fin 3) L, ∀ s u : Lˣ, diagSL3 (s ^ μ'.1 * u ^ μ'.2) (s ^ ν'.1 * u ^ ν'.2) =
        CFSG.RankThree.Classical2.conjSLn A₀ (diagSL3 s u) := exists_conj_diagSL3_perm (L := L)
  have neg : ∀ μ' ν' : ℤ × ℤ, (μ', ν') ∈ [((1, 0), (0, 1)), ((-1, 1), (0, 1)), ((1, 0), (1, -1)),
      ((0, -1), (-1, 0)), ((-1, 1), (-1, 0)), ((0, -1), (1, -1))] →
      ∃ A₀ : GL (Fin 3) L, ∀ s u : Lˣ,
        diagSL3 (s ^ (-μ'.1) * u ^ (-μ'.2)) (s ^ (-ν'.1) * u ^ (-ν'.2)) =
          CFSG.RankThree.Classical2.conjSLn A₀
            (CFSG.RankThree.Classical2.invTransposeSL (diagSL3 s u)) := fun μ' ν' h' => by
    obtain ⟨A₀, hA⟩ := exists_conj_diagSL3_perm (L := L) μ' ν' h'
    exact ⟨A₀, diagSL3_neg_of_conj μ' ν' A₀ hA⟩
  simp only [weylMatList, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (pos _ _ (by simp)).imp fun _ h => Or.inl h
  · exact (pos _ _ (by simp)).imp fun _ h => Or.inl h
  · exact (pos _ _ (by simp)).imp fun _ h => Or.inl h
  · exact (pos _ _ (by simp)).imp fun _ h => Or.inl h
  · exact (pos _ _ (by simp)).imp fun _ h => Or.inl h
  · exact (pos _ _ (by simp)).imp fun _ h => Or.inl h
  · obtain ⟨A₀, hA⟩ := neg ((1, 0)) ((0, 1)) (by simp)
    exact ⟨A₀, Or.inr fun s u => by simpa using hA s u⟩
  · obtain ⟨A₀, hA⟩ := neg ((-1, 1)) ((0, 1)) (by simp)
    exact ⟨A₀, Or.inr fun s u => by simpa using hA s u⟩
  · obtain ⟨A₀, hA⟩ := neg ((1, 0)) ((1, -1)) (by simp)
    exact ⟨A₀, Or.inr fun s u => by simpa using hA s u⟩
  · obtain ⟨A₀, hA⟩ := neg ((0, -1)) ((-1, 0)) (by simp)
    exact ⟨A₀, Or.inr fun s u => by simpa using hA s u⟩
  · obtain ⟨A₀, hA⟩ := neg ((-1, 1)) ((-1, 0)) (by simp)
    exact ⟨A₀, Or.inr fun s u => by simpa using hA s u⟩
  · obtain ⟨A₀, hA⟩ := neg ((0, -1)) ((1, -1)) (by simp)
    exact ⟨A₀, Or.inr fun s u => by simpa using hA s u⟩

end DiagShape

section Embedding


theorem fixedA2V_smul (u : Fin Tag.E6.rank → ℤ) :
    fixedA2V • u = fixedA2Word.foldr (reflect Tag.E6) u :=
  CFSG.LieType.Chevalley.wordProd_smul fixedA2Word u

set_option maxRecDepth 100000 in
theorem fixedA2V_smul_chainRoot :
    (∀ i j : Fin 3, i ≠ j → fixedA2V • chainRoot chain13 i j ∈ fixedA2E6) ∧
      ∀ α ∈ fixedA2E6, ∃ i j : Fin 3, i ≠ j ∧ α = fixedA2V • chainRoot chain13 i j := by
  simp only [fixedA2V_smul]
  decide +kernel

theorem fixedA2V_smul_chainRoot_01 : fixedA2V • chainRoot chain13 0 1 = gamma1 := by
  rw [fixedA2V_smul]
  decide +kernel

theorem fixedA2V_smul_chainRoot_12 : fixedA2V • chainRoot chain13 1 2 = gamma2 := by
  rw [fixedA2V_smul]
  decide +kernel

theorem fixedA2V_smul_chainRoot_02 : fixedA2V • chainRoot chain13 0 2 = gamma3 := by
  rw [fixedA2V_smul]
  decide +kernel

@[expose] def fixedA2Rho (L : Type) [Field L] : SL(3, L) →* ModGL Tag.E6 L :=
  a2Std₁.rhoV L fixedA2V

theorem fixedA2Rho_injective (L : Type) [Field L] : Function.Injective (fixedA2Rho L) :=
  (a2Std₁.embedding fixedA2V).inj L

theorem range_fixedA2Rho (L : Type) [Field L] :
    (fixedA2Rho L).range = rootSpan Tag.E6 L {α | α ∈ fixedA2E6} := by
  have h : (fixedA2Rho L).range =
      rootSpan Tag.E6 L ((fun γ => fixedA2V • γ) '' parabolicRoots Tag.E6 support13) :=
    (a2Std₁.embedding fixedA2V).range L
  have hS : (fun γ => fixedA2V • γ) '' parabolicRoots Tag.E6 support13 =
      {α | α ∈ fixedA2E6} := by
    ext α
    constructor
    · rintro ⟨β, hβ, rfl⟩
      obtain ⟨i, j, hij, rfl⟩ := (a2Std₁.roots β).1 hβ
      exact fixedA2V_smul_chainRoot.1 i j hij
    · intro hα
      obtain ⟨i, j, hij, rfl⟩ := fixedA2V_smul_chainRoot.2 α hα
      exact ⟨chainRoot chain13 i j, (a2Std₁.roots _).2 ⟨i, j, hij, rfl⟩, rfl⟩
  rw [h, hS]

theorem fixedA2Rho_transvection (L : Type) [Field L] {i j : Fin 3} (hij : i ≠ j) :
    ∃ ε : Lˣ, ∀ t : L, fixedA2Rho L (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.E6 L (fixedA2V • chainRoot chain13 i j) ((ε : L) * t) := by
  exact a2Std₁.rhoV_transvection L fixedA2V hij

theorem rootDiagUnit_conj_fixedA2Rho (L : Type) [Field L] (b : Fin Tag.E6.rank → Lˣ)
    (A : SL(3, L)) :
    rootDiagUnit Tag.E6 b * fixedA2Rho L A * (rootDiagUnit Tag.E6 b)⁻¹ =
      fixedA2Rho L (CFSG.RankThree.PartOne.KE.conjDiagn (fun i : Fin 3 =>
        rootChar b (fixedA2V • CFSG.RankThree.PartOne.TCX.E.chainWeight chain13 i)) A) := by
  exact a2Std₁.rhoV_torus L fixedA2V b A

theorem fixedA2Rho_diag_mem_torusGroup (L : Type) [Field L] (A : SL(3, L))
    (hA : ∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) :
    fixedA2Rho L A ∈ torusGroup Tag.E6 L := by
  exact (a2Std₁.embedding fixedA2V).diag L A hA

theorem fixedA2Rho_mem_closedIdentityComponent {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {Hh : Subgroup (ModGL Tag.E6 Ω)}
    (hU : rootSpan Tag.E6 Ω {α | α ∈ fixedA2E6} ≤
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) (A : SL(3, Ω)) :
    fixedA2Rho Ω A ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) := by
  have hZ : ∀ B, fixedA2Rho Ω B ∈
      adjointGroup Tag.E6 Ω ⊓ Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω)) := by
    intro B
    have hB : fixedA2Rho Ω B ∈ rootSpan Tag.E6 Ω {α | α ∈ fixedA2E6} := by
      rw [← range_fixedA2Rho]
      exact ⟨B, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, hU hB⟩
    exact (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α :
      rootSpan Tag.E6 Ω {α | α ∈ fixedA2E6} ≤ adjointGroup Tag.E6 Ω) hB
  have htv : ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
      fixedA2Rho Ω (Matrix.SpecialLinearGroup.transvection hij t) ∈
        closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
          Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) := by
    intro i j hij
    obtain ⟨ε, hε⟩ := fixedA2Rho_transvection Ω hij
    have hcurve : IsPolynomialCurve fun t : Ω =>
        fixedA2Rho Ω (Matrix.SpecialLinearGroup.transvection hij t) := by
      have h : (fun t : Ω => fixedA2Rho Ω (Matrix.SpecialLinearGroup.transvection hij t)) =
          fun t => pinnedX Tag.E6 Ω (fixedA2V • chainRoot chain13 i j)
            ((Polynomial.C (ε : Ω) * Polynomial.X).eval t) := by
        funext t
        rw [hε, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      rw [h]
      exact isPolynomialCurve_pinnedX _ _
    intro t
    refine mem_closedIdentityComponent_of_isPolynomialCurve hcurve (fun t => hZ _) (t₀ := 0) ?_ t
    rw [show Matrix.SpecialLinearGroup.transvection hij (0 : Ω) = 1 by
      ext a b
      simp [Matrix.SpecialLinearGroup.transvection, Matrix.transvection], map_one]
  have hA : A ∈ Subgroup.closure (CFSG.LinearGroups.elementarySet 3 Ω) := by
    rw [CFSG.LinearGroups.special_linear_elementary_generation]
    exact Subgroup.mem_top A
  induction hA using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, j, hij, t, rfl⟩ := hx
    exact htv i j hij t
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx

@[expose] def diagTuple {L : Type} [Field L] (s u : Lˣ) : Fin Tag.E6.rank → Lˣ :=
  weylTuple fixedA2V (fun j => s ^ Tag.E6.cartan 0 j * u ^ Tag.E6.cartan 2 j)

theorem fixedA2Rho_diagSL3 (L : Type) [Field L] (s u : Lˣ) :
    fixedA2Rho L (diagSL3 s u) = rootDiagUnit Tag.E6 (diagTuple s u) := by
  have hsymm : (CFSG.RankThree.E6.a2Equiv₁ L).symm (diagSL3 s u) =
      ⟨CFSG.RankThree.E6.e6TorusPair (CFSG.RankThree.E6.e6Index 0) (CFSG.RankThree.E6.e6Index 2)
        s u, CFSG.RankThree.E6.e6TorusPair_mem_subsystemGroup _ _ s u⟩ := by
    rw [MulEquiv.symm_apply_eq, CFSG.RankThree.E6.a2Equiv₁_apply]
    apply Subtype.ext
    rw [CFSG.RankThree.E6.coe_a2Rep₁]
    change _ = CFSG.RankThree.E6.a2Mat₁ (CFSG.RankThree.E6.e6TorusPair (K := L)
      (CFSG.RankThree.E6.e6Index 0) (CFSG.RankThree.E6.e6Index 2) s u)
    rw [CFSG.RankThree.E6.a2Mat₁_torus]
    rfl
  have hρ : fixedA2Rho L (diagSL3 s u) = canonicalRep (coxeterSystem Tag.E6) L fixedA2V *
      (torusElt Tag.E6 L 0 s * torusElt Tag.E6 L 2 u) *
        (canonicalRep (coxeterSystem Tag.E6) L fixedA2V)⁻¹ := by
    simp only [fixedA2Rho, A2Std.rhoV, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    change canonicalRep (coxeterSystem Tag.E6) L fixedA2V *
      CFSG.RankThree.PartOne.TCX.E.e6rhoA2₁ L (diagSL3 s u) * _ = _
    simp only [CFSG.RankThree.PartOne.TCX.E.e6rhoA2₁, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
    rw [hsymm]
    rfl
  rw [hρ, torusElt_eq_rootDiagUnit (τ := Tag.E6) (K := L) 0 s,
    torusElt_eq_rootDiagUnit (τ := Tag.E6) (K := L) 2 u, ← CFSG.LieType.Chevalley.rootDiagUnit_mul]
  have hc := conj_rootDiagUnit_of_mem_monoHat
    (x := ⟨canonicalRep (coxeterSystem Tag.E6) L fixedA2V,
      monomial_le_monoHat (canonicalRep_mem_monomialSubgroup L fixedA2V)⟩)
    ((fun j => s ^ Tag.E6.cartan 0 j) * fun j => u ^ Tag.E6.cartan 2 j)
  rw [psiHat_of_mem_monomial (canonicalRep_mem_monomialSubgroup L fixedA2V),
    weylQuotientHom_eq (mapsRootLines_canonicalRep fixedA2V)] at hc
  exact hc

@[expose] def diagWt (k : Fin Tag.E6.rank) (ℓ : Label Tag.E6) : ℤ :=
  ∑ j, (fixedA2Word.reverse.foldr (reflect Tag.E6) (labelWt Tag.E6 ℓ)) j * Tag.E6.cartan k j

theorem rootChar_diagTuple {L : Type} [Field L] (s u : Lˣ) (ℓ : Label Tag.E6) :
    rootChar (diagTuple s u) (labelWt Tag.E6 ℓ) = s ^ diagWt 0 ℓ * u ^ diagWt 2 ℓ := by
  rw [diagTuple, rootChar_weylTuple, fixedA2V, ← CoxeterSystem.wordProd_reverse,
    CFSG.LieType.Chevalley.wordProd_smul]
  simp only [rootChar, diagWt, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, ← zpow_mul]
  rw [Finset.prod_zpow_eq_zpow_sum, Finset.prod_zpow_eq_zpow_sum]
  simp only [mul_comm]

theorem exists_diag_mul_eq_conjDiagn_mul {L : Type} [Field L] [IsAlgClosed L] (d : Fin 3 → Lˣ) :
    ∃ D₀ : SL(3, L), (∀ i j, i ≠ j → (D₀ : Matrix (Fin 3) (Fin 3) L) i j = 0) ∧
      ∀ A : SL(3, L), D₀ * A = CFSG.RankThree.PartOne.KE.conjDiagn d A * D₀ := by
  obtain ⟨c₀, hc₀⟩ := IsAlgClosed.exists_pow_nat_eq ((d 0 * d 1 * d 2 : Lˣ) : L)
    (show 0 < 3 by norm_num)
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    exact (d 0 * d 1 * d 2).ne_zero (by rw [← hc₀]; ring)
  set c : Lˣ := Units.mk0 c₀ hc₀0 with hc
  have hdet : (Matrix.diagonal fun i => ((d i * c⁻¹ : Lˣ) : L)).det = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    have h3 : ((c : L)) ^ 3 = (d 0 : L) * d 1 * d 2 := by
      rw [hc, Units.val_mk0, hc₀]
      simp
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
    linear_combination -h3
  refine ⟨⟨Matrix.diagonal fun i => ((d i * c⁻¹ : Lˣ) : L), hdet⟩, fun i j hij => ?_, fun A => ?_⟩
  · exact Matrix.diagonal_apply_ne _ hij
  · ext i j
    change ((Matrix.diagonal fun i => ((d i * c⁻¹ : Lˣ) : L)) * (A : Matrix (Fin 3) (Fin 3) L)) i j =
      (((CFSG.RankThree.PartOne.KE.conjDiagn d A : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) *
        Matrix.diagonal fun i => ((d i * c⁻¹ : Lˣ) : L)) i j
    rw [CFSG.RankThree.PartOne.KE.coe_conjDiagn]
    have h1 : ((CFSG.RankThree.PartOne.KE.diagGLn d : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
        Matrix.diagonal fun i => (d i : L) := rfl
    have h2 : (((CFSG.RankThree.PartOne.KE.diagGLn d)⁻¹ : GL (Fin 3) L) :
        Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal fun i => (((d i)⁻¹ : Lˣ) : L) := rfl
    rw [h1, h2, Matrix.mul_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_mul]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp

theorem exists_central_mul_fixedA2Rho {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {K : Subgroup (ModGL Tag.E6 Ω)} (hιK : ∀ A, fixedA2Rho Ω A ∈ K)
    (hKS : ∀ z ∈ K, z ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω {α | α ∈ fixedA2E6})
    {z : ModGL Tag.E6 Ω} (hz : z ∈ K) :
    ∃ w ∈ K, w ∈ torusGroup Tag.E6 Ω ∧ (∀ y ∈ K, w * y = y * w) ∧
      ∃ B : SL(3, Ω), z = w * fixedA2Rho Ω B := by
  set ι := fixedA2Rho Ω with hιdef
  have hTU : torusGroup Tag.E6 Ω ≤
      Subgroup.normalizer (rootSpan Tag.E6 Ω {α | α ∈ fixedA2E6} : Set (ModGL Tag.E6 Ω)) :=
    CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootSpan
      (fun α hα => isRoot_of_mem_fixedA2E6 hα)
  have hdecomp : ∀ y ∈ K, ∃ b : Fin Tag.E6.rank → Ωˣ, ∃ B : SL(3, Ω),
      y = rootDiagUnit Tag.E6 b * ι B := by
    intro y hy
    have h := hKS y hy
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTU,
      ← range_fixedA2Rho] at h
    obtain ⟨t', ht', r, ⟨B, rfl⟩, rfl⟩ := h
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht'
    exact ⟨b, B, rfl⟩
  have hTc : ∀ a a' : Fin Tag.E6.rank → Ωˣ,
      rootDiagUnit Tag.E6 a * rootDiagUnit Tag.E6 a' =
        rootDiagUnit Tag.E6 a' * rootDiagUnit Tag.E6 a := fun a a' => by
    rw [← CFSG.LieType.Chevalley.rootDiagUnit_mul, ← CFSG.LieType.Chevalley.rootDiagUnit_mul,
      mul_comm]
  obtain ⟨b, B₁, rfl⟩ := hdecomp z hz
  obtain ⟨D₀, hD₀d, hD₀⟩ := exists_diag_mul_eq_conjDiagn_mul (fun i : Fin 3 =>
    rootChar b (fixedA2V • CFSG.RankThree.PartOne.TCX.E.chainWeight chain13 i))
  have hD₀T : ι D₀ ∈ torusGroup Tag.E6 Ω := fixedA2Rho_diag_mem_torusGroup Ω D₀ hD₀d
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hD₀T
  set t := rootDiagUnit Tag.E6 b with ht
  set P := ι D₀ with hP
  have hc : ∀ A, (t⁻¹ * P) * ι A = ι A * (t⁻¹ * P) := by
    intro A
    have h1 := rootDiagUnit_conj_fixedA2Rho Ω b A
    have h2 : P * ι A * P⁻¹ = ι (CFSG.RankThree.PartOne.KE.conjDiagn (fun i : Fin 3 =>
        rootChar b (fixedA2V • CFSG.RankThree.PartOne.TCX.E.chainWeight chain13 i)) A) := by
      rw [hP, ← map_mul, hD₀ A, map_mul, mul_inv_cancel_right]
    have e : P * ι A * P⁻¹ = t * ι A * t⁻¹ := by rw [h2, ht, h1]
    calc (t⁻¹ * P) * ι A = t⁻¹ * (P * ι A * P⁻¹) * P := by group
      _ = t⁻¹ * (t * ι A * t⁻¹) * P := by rw [e]
      _ = ι A * (t⁻¹ * P) := by group
  have htP : t * P = P * t := by
    have k := hTc b l
    rw [← hl] at k
    exact k
  have hw : t * P⁻¹ = (t⁻¹ * P)⁻¹ := by
    rw [mul_inv_rev, inv_inv]
    calc t * P⁻¹ = P⁻¹ * (P * t) * P⁻¹ := by group
      _ = P⁻¹ * (t * P) * P⁻¹ := by rw [htP]
      _ = P⁻¹ * t := by group
  have hwι : ∀ A, (t * P⁻¹) * ι A = ι A * (t * P⁻¹) := fun A => by
    rw [hw]
    exact (Commute.inv_left (hc A : Commute (t⁻¹ * P) (ι A))).eq
  have hwT : t * P⁻¹ ∈ torusGroup Tag.E6 Ω :=
    Subgroup.mul_mem _ (rootDiagUnit_mem_torusGroup b) (Subgroup.inv_mem _ hD₀T)
  have htK : t ∈ K := by
    have h := Subgroup.mul_mem _ hz (Subgroup.inv_mem _ (hιK B₁))
    rwa [mul_inv_cancel_right] at h
  refine ⟨t * P⁻¹, Subgroup.mul_mem _ htK (Subgroup.inv_mem _ (hιK D₀)), hwT, ?_, D₀ * B₁, ?_⟩
  · intro y hy
    obtain ⟨b', B', rfl⟩ := hdecomp y hy
    obtain ⟨l', hl'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hwT
    have k : (t * P⁻¹) * rootDiagUnit Tag.E6 b' = rootDiagUnit Tag.E6 b' * (t * P⁻¹) := by
      rw [hl', hTc]
    calc (t * P⁻¹) * (rootDiagUnit Tag.E6 b' * ι B')
        = ((t * P⁻¹) * rootDiagUnit Tag.E6 b') * ι B' := by group
      _ = rootDiagUnit Tag.E6 b' * ((t * P⁻¹) * ι B') := by rw [k]; group
      _ = rootDiagUnit Tag.E6 b' * ι B' * (t * P⁻¹) := by rw [hwι]; group
  · rw [map_mul, ← hP]
    group

open Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem exists_fixedA2Torus_projective_quotient (Ω : Type) [Field Ω] [IsAlgClosed Ω] :
    let W := torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω {α | α ∈ fixedA2E6}
    ∃ π : W →* projectiveSL 3 Ω, Function.Surjective π ∧ π.ker = center W ∧
      ∀ B : SL(3, Ω), ∀ hB : fixedA2Rho Ω B ∈ W, π ⟨fixedA2Rho Ω B, hB⟩ = proj 3 Ω B := by
  classical
  dsimp only
  let W := torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω {α | α ∈ fixedA2E6}
  have hιW : ∀ B, fixedA2Rho Ω B ∈ W := by
    intro B
    exact (le_sup_right : rootSpan Tag.E6 Ω {α | α ∈ fixedA2E6} ≤ W)
      (by rw [← range_fixedA2Rho]; exact ⟨B, rfl⟩)
  let ι : SL(3, Ω) →* W := (fixedA2Rho Ω).codRestrict W hιW
  have hι : Function.Injective ι := fun a b h =>
    fixedA2Rho_injective Ω (congrArg Subtype.val h)
  have hdec : ∀ g : W, ∃ z ∈ center W, ∃ B : SL(3, Ω), g = z * ι B := by
    intro g
    obtain ⟨z, hzW, -, hzc, B, hB⟩ :=
      exists_central_mul_fixedA2Rho hιW (fun _ h => h) g.2
    refine ⟨⟨z, hzW⟩, ?_, B, Subtype.ext hB⟩
    rw [mem_center_iff]
    intro w
    exact Subtype.ext (hzc w w.2).symm
  obtain ⟨e, he⟩ := CFSG.GroupTheory.exists_centerQuotient_equiv_of_central_product ι hι hdec
  let eP : projectiveSL 3 Ω ≃* W ⧸ center W :=
    (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center (n := 3) (K := Ω))).trans e
  let π : W →* projectiveSL 3 Ω :=
    eP.symm.toMonoidHom.comp (QuotientGroup.mk' (center W))
  refine ⟨π, eP.symm.surjective.comp (QuotientGroup.mk'_surjective _), ?_, ?_⟩
  · ext g
    change eP.symm (QuotientGroup.mk g) = 1 ↔ g ∈ center W
    constructor
    · intro h
      apply (QuotientGroup.eq_one_iff g).mp
      have h' := congrArg eP h
      simpa only [MulEquiv.apply_symm_apply, map_one] using h'
    · intro h
      rw [(QuotientGroup.eq_one_iff g).mpr h, map_one]
  · intro B hB
    apply eP.injective
    change eP (eP.symm (QuotientGroup.mk (⟨fixedA2Rho Ω B, hB⟩ : W))) = eP (proj 3 Ω B)
    rw [MulEquiv.apply_symm_apply]
    change QuotientGroup.mk (ι B) = e ((QuotientGroup.quotientMulEquivOfEq
      (scalars_eq_center (n := 3) (K := Ω))) (QuotientGroup.mk B))
    rw [QuotientGroup.quotientMulEquivOfEq_mk, he]


section MonomialFixedA2

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification.CatalogueBHigherLinearAction

theorem exists_fixedA2_monomial_diagonal_action {Ω : Type} [Field Ω]
    (a : ModGL .E6 Ω) (haM : a ∈ monomialSubgroup .E6 Ω)
    (hw : ∀ γ ∈ fixedA2E6, weylQuotientHom .E6 Ω ⟨a, haM⟩ • γ = γ) :
    ∃ d : Fin 3 → Ωˣ, ∀ B : SL(3, Ω), a * fixedA2Rho Ω B * a⁻¹ =
      fixedA2Rho Ω (slConjugation 3 Ω (CFSG.SectionRank.OddCover.diagHom 3 d) B) := by
  classical
  choose! ε hε using fun (i j : Fin 3) (hij : i ≠ j) => fixedA2Rho_transvection Ω hij
  have hconj : ∀ i j : Fin 3, i ≠ j → ∃ b : Ωˣ, ∀ c : Ω,
      a * pinnedX .E6 Ω (fixedA2V • chainRoot chain13 i j) c * a⁻¹ =
        pinnedX .E6 Ω (fixedA2V • chainRoot chain13 i j) ((b : Ω) * c) := by
    intro i j hij
    have hr := fixedA2V_smul_chainRoot.1 i j hij
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX haM (isRoot_of_mem_fixedA2E6 hr)
    exact ⟨μ, fun c => (hμ c).trans (by rw [hw _ hr])⟩
  obtain ⟨Φ, hΦ, b, hshape⟩ := CFSG.RankThree.PartOne.KE.exists_aut_of_rootData
    (τ := .E6) (fixedA2Rho Ω) (fixedA2Rho_injective Ω)
    (fun i j => fixedA2V • chainRoot chain13 i j) ε hε (RingHom.id Ω)
    Function.bijective_id a (fun i j => (i, j)) (fun i j hij => hij)
    (fun i j hij => ⟨i, j, hij, rfl⟩) hconj
  have hroot : ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
      Φ (SpecialLinearGroup.transvection hij t) =
        SpecialLinearGroup.transvection hij ((b i j : Ω) * (RingHom.id Ω) t) := by
    intro i j hij t
    apply Subtype.ext
    simpa only [SpecialLinearGroup.transvection_coe] using hshape i j hij t
  obtain ⟨d, hd⟩ := CFSG.RankThree.Classical2.exists_diag_eq_conj_map_of_root_hom
    (by decide) (RingHom.id Ω) Φ.toMonoidHom b hroot
  refine ⟨d, fun B => ?_⟩
  have hdiag : Φ B = slConjugation 3 Ω (CFSG.SectionRank.OddCover.diagHom 3 d) B := by
    apply Subtype.ext
    rw [coe_slConjugation]
    simpa using hd B
  have hid : Units.map (entrywiseHom (RingHom.id Ω)) (fixedA2Rho Ω B) = fixedA2Rho Ω B := by
    exact Units.ext (entrywise_id _)
  simpa only [hid, hdiag] using hΦ B


theorem mem_normalizer_fixedA2Torus_of_monomial_root_fixed {Ω : Type} [Field Ω]
    (a : ModGL .E6 Ω) (haM : a ∈ monomialSubgroup .E6 Ω)
    (hw : ∀ γ ∈ fixedA2E6, weylQuotientHom .E6 Ω ⟨a, haM⟩ • γ = γ) :
    a ∈ Subgroup.normalizer (((torusGroup .E6 Ω ⊔ rootSpan .E6 Ω
      {γ | γ ∈ fixedA2E6}) : Subgroup (ModGL .E6 Ω)) : Set (ModGL .E6 Ω)) := by
  obtain ⟨d, hd⟩ := exists_fixedA2_monomial_diagonal_action a haM hw
  let φ := slConjugation 3 Ω (CFSG.SectionRank.OddCover.diagHom 3 d)
  have hcomp : (MulAut.conj a).toMonoidHom.comp (fixedA2Rho Ω) =
      (fixedA2Rho Ω).comp φ.toMonoidHom := by
    apply MonoidHom.ext
    intro B
    exact hd B
  have hmap : ((fixedA2Rho Ω).range).map (MulAut.conj a).toMonoidHom =
      (fixedA2Rho Ω).range := by
    rw [← MonoidHom.range_comp, hcomp, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr φ.surjective, Subgroup.map_top]
  have hT := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (mem_normalizer_torusGroup_of_mem_monomialSubgroup haM)
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  rw [Subgroup.map_sup, hT, ← range_fixedA2Rho]
  change torusGroup .E6 Ω ⊔ ((fixedA2Rho Ω).range).map (MulAut.conj a).toMonoidHom =
    torusGroup .E6 Ω ⊔ (fixedA2Rho Ω).range
  exact congrArg (fun H : Subgroup (ModGL .E6 Ω) => torusGroup .E6 Ω ⊔ H) hmap

theorem exists_scalar_cube_of_fixedA2_action {Ω : Type} [Field Ω]
    (a : ModGL .E6 Ω) (ha3 : a ^ 3 = 1) (A : GL (Fin 3) Ω)
    (hact : ∀ B : SL(3, Ω), a * fixedA2Rho Ω B * a⁻¹ =
      fixedA2Rho Ω (slConjugation 3 Ω A B)) :
    ∃ c : Ω, (A : Matrix (Fin 3) (Fin 3) Ω) ^ 3 = c • 1 := by
  let φ := slConjugation 3 Ω A
  have hφ3 : ∀ B : SL(3, Ω), φ (φ (φ B)) = B := by
    intro B
    apply fixedA2Rho_injective Ω
    rw [← hact, ← hact, ← hact]
    calc a * (a * (a * fixedA2Rho Ω B * a⁻¹) * a⁻¹) * a⁻¹ =
        a ^ 3 * fixedA2Rho Ω B * (a ^ 3)⁻¹ := by
          simp only [pow_succ, pow_zero]
          group
      _ = fixedA2Rho Ω B := by rw [ha3]; simp
  have hpow : ∀ B : SL(3, Ω), slConjugation 3 Ω (A ^ 3) B = B := by
    intro B
    simpa [map_pow, pow_succ, MulAut.mul_apply, φ] using hφ3 B
  have hcomm : ∀ t : Matrix.TransvectionStruct (Fin 3) Ω,
      Commute t.toMatrix ((A ^ 3 : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) := by
    intro t
    let B := t.toSpecialLinearGroup
    have heq : A ^ 3 * SpecialLinearGroup.toGL B * (A ^ 3)⁻¹ = SpecialLinearGroup.toGL B := by
      rw [← toGL_slConjugation, hpow]
    have hc : A ^ 3 * SpecialLinearGroup.toGL B = SpecialLinearGroup.toGL B * A ^ 3 :=
      (mul_inv_eq_iff_eq_mul).mp heq
    exact (congrArg Units.val hc).symm
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct hcomm
  refine ⟨c, ?_⟩
  have hM : (A : Matrix (Fin 3) (Fin 3) Ω) ^ 3 = Matrix.scalar (Fin 3) c := by
    simpa using hc.symm
  rw [hM]
  ext i j
  by_cases hij : i = j
  · subst j; simp [Matrix.scalar]
  · simp [Matrix.scalar, Matrix.one_apply_ne hij, hij]

end MonomialFixedA2

section FiniteFixedA2

open Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification.CatalogueBHigherLinearAction

variable {K Ω : Type} [Field K] [Finite K] [Field Ω] [Algebra K Ω]
  [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω]

local notation "W" => ((torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω
  (fun α => α ∈ fixedA2E6)) : Subgroup (ModGL Tag.E6 Ω))

theorem exists_fixedA2Torus_equivariant_projective_quotient
    (a : ModGL Tag.E6 Ω) (haW : a ∈ normalizer (W : Set _)) (A : GL (Fin 3) Ω)
    (hact : ∀ B : SL(3, Ω), a * fixedA2Rho Ω B * a⁻¹ =
      fixedA2Rho Ω (slConjugation 3 Ω A B)) :
    ∃ π : ↥W →* projectiveSL 3 Ω, Function.Surjective π ∧ π.ker = center ↥W ∧
      (∀ B : SL(3, Ω), ∀ hB : fixedA2Rho Ω B ∈ W, π ⟨fixedA2Rho Ω B, hB⟩ = proj 3 Ω B) ∧
      ∀ w : ↥W, π ((normalizerMonoidHom W ⟨a, haW⟩) w) = conjAut 3 Ω A (π w) := by
  classical
  obtain ⟨π, hs, hker, hπ⟩ := exists_fixedA2Torus_projective_quotient Ω
  have hιW : ∀ B, fixedA2Rho Ω B ∈ W := by
    intro B
    exact (le_sup_right : rootSpan Tag.E6 Ω {α | α ∈ fixedA2E6} ≤ W)
      (by rw [← range_fixedA2Rho]; exact ⟨B, rfl⟩)
  let ι : SL(3, Ω) →* ↥W := (fixedA2Rho Ω).codRestrict W hιW
  have hdec : ∀ w : ↥W, ∃ z ∈ center ↥W, ∃ B : SL(3, Ω), w = z * ι B := by
    intro w
    obtain ⟨z, hzW, _, hzc, B, hB⟩ :=
      exists_central_mul_fixedA2Rho hιW (fun _ h => h) w.2
    refine ⟨⟨z, hzW⟩, ?_, B, Subtype.ext hB⟩
    rw [mem_center_iff]
    intro v
    exact Subtype.ext (hzc v v.2).symm
  let α : MulAut ↥W := normalizerMonoidHom W ⟨a, haW⟩
  have hα : ∀ w : ↥W, (α w : ModGL Tag.E6 Ω) = a * w * a⁻¹ :=
    fun w => normalizerMonoidHom_apply_apply_coe W ⟨a, haW⟩ w
  have hfactor : ∀ B : SL(3, Ω), π (α (ι B)) = conjAut 3 Ω A (π (ι B)) := by
    intro B
    have hB : α (ι B) = ι (slConjugation 3 Ω A B) := by
      apply Subtype.ext
      rw [hα]
      exact hact B
    have hπι : ∀ B : SL(3, Ω), π (ι B) = proj 3 Ω B := fun B => hπ B (hιW B)
    rw [hB, hπι, hπι, conjAut_proj]
  have heq : ∀ w : ↥W, π (α w) = conjAut 3 Ω A (π w) :=
    CFSG.GroupTheory.equivariant_of_central_product ι hdec π hker.ge α
      (conjAut 3 Ω A) hfactor
  exact ⟨π, hs, hker, hπ, heq⟩

include K in
theorem isSolvable_fixedA2Torus_of_cube_scalar_action
    (h3 : (3 : Ω) ≠ 0) {C : Subgroup (ModGL Tag.E6 Ω)} [Finite C]
    (hCW : C ≤ W) {a : ModGL Tag.E6 Ω} (haW : a ∈ normalizer (W : Set _))
    {A : GL (Fin 3) Ω} {c : Ω}
    (hA3 : (A : Matrix (Fin 3) (Fin 3) Ω) ^ 3 = c • 1)
    (hns : ∀ d : Ω, (A : Matrix (Fin 3) (Fin 3) Ω) ≠ d • 1)
    (hact : ∀ B : SL(3, Ω), a * fixedA2Rho Ω B * a⁻¹ =
      fixedA2Rho Ω (slConjugation 3 Ω A B))
    (hCa : C ≤ centralizer ({a} : Set _))
    (hNPC : CFSG.HasNormalPComplement 3 ↥(_root_.commutator C)) :
    Group.IsSolvable C := by
  classical
  obtain ⟨π, _, hker, _, heq⟩ := exists_fixedA2Torus_equivariant_projective_quotient a haW A hact
  let α : MulAut ↥W := normalizerMonoidHom W ⟨a, haW⟩
  have hα : ∀ w : ↥W, (α w : ModGL Tag.E6 Ω) = a * w * a⁻¹ :=
    fun w => normalizerMonoidHom_apply_apply_coe W ⟨a, haW⟩ w
  let ρ : C →* projectiveSL 3 Ω := π.comp (inclusion hCW)
  have hkerC : ρ.ker ≤ center C := by
    intro g hg
    have hgc : inclusion hCW g ∈ center ↥W := hker.le hg
    rw [mem_center_iff] at hgc ⊢
    intro v
    apply Subtype.ext
    exact congrArg (fun w : ↥W => (w : ModGL Tag.E6 Ω)) (hgc (inclusion hCW v))
  have hfix : ∀ g : C, conjAut 3 Ω A (ρ g) = ρ g := by
    intro g
    have hαg : α (inclusion hCW g) = inclusion hCW g := by
      apply Subtype.ext
      rw [hα]
      exact mul_inv_eq_of_eq_mul (mem_centralizer_singleton_iff.mp (hCa g.2)).symm
    exact (heq (inclusion hCW g)).symm.trans (congrArg π hαg)
  exact CFSG.RankThree.PartTwo.Sec6.BThreeCensus.isSolvable_of_projective_cube_scalar_over_algebraic
    (K := K) h3 ρ hkerC hA3 hns hfix hNPC


theorem isSolvable_fixedA2Torus_of_regular_action
    {C : Subgroup (ModGL Tag.E6 Ω)} (hCW : C ≤ W)
    {a : ModGL Tag.E6 Ω} (haW : a ∈ normalizer (W : Set _)) {A : GL (Fin 3) Ω}
    (hA : CFSG.StandardType.L3Three.IsReg (A : Matrix (Fin 3) (Fin 3) Ω))
    (hact : ∀ B : SL(3, Ω), a * fixedA2Rho Ω B * a⁻¹ =
      fixedA2Rho Ω (slConjugation 3 Ω A B))
    (hCa : C ≤ centralizer ({a} : Set _)) : Group.IsSolvable C := by
  classical
  obtain ⟨π, _, hker, _, heq⟩ := exists_fixedA2Torus_equivariant_projective_quotient a haW A hact
  let α : MulAut ↥W := normalizerMonoidHom W ⟨a, haW⟩
  have hα : ∀ w : ↥W, (α w : ModGL Tag.E6 Ω) = a * w * a⁻¹ :=
    fun w => normalizerMonoidHom_apply_apply_coe W ⟨a, haW⟩ w
  let ρ : C →* projectiveSL 3 Ω := π.comp (inclusion hCW)
  have hfix : ∀ g : C, conjAut 3 Ω A (ρ g) = ρ g := by
    intro g
    have hαg : α (inclusion hCW g) = inclusion hCW g := by
      apply Subtype.ext
      rw [hα]
      exact mul_inv_eq_of_eq_mul (mem_centralizer_singleton_iff.mp (hCa g.2)).symm
    exact (heq (inclusion hCW g)).symm.trans (congrArg π hαg)
  let f : C →* CFSG.StandardType.ggFix (conjAut 3 Ω A) :=
    ρ.codRestrict _ (fun g => hfix g)
  have hkerC : f.ker ≤ center C := by
    intro g hg
    have hπg : π (inclusion hCW g) = 1 := congrArg Subtype.val hg
    have hgc : inclusion hCW g ∈ center ↥W := hker.le hπg
    rw [mem_center_iff] at hgc ⊢
    intro v
    apply Subtype.ext
    exact congrArg (fun w : ↥W => (w : ModGL Tag.E6 Ω)) (hgc (inclusion hCW v))
  have : Group.IsSolvable (CFSG.StandardType.ggFix (conjAut 3 Ω A)) :=
    CFSG.StandardType.L3Three.isSolvable_ggFix_conjAut hA
  exact Group.isSolvable_of_ker_le_range (center C).subtype f
    (by rw [Subgroup.range_subtype]; exact hkerC)


include K in
theorem isSolvable_fixedA2Torus_of_monomial_order_three
    (h3 : (3 : Ω) ≠ 0) {C : Subgroup (ModGL .E6 Ω)} [Finite C]
    (hCW : C ≤ ((torusGroup .E6 Ω ⊔ rootSpan .E6 Ω {γ | γ ∈ fixedA2E6}) :
      Subgroup (ModGL .E6 Ω)))
    (a : ModGL .E6 Ω) (haM : a ∈ monomialSubgroup .E6 Ω) (ha3 : a ^ 3 = 1)
    (hwc : weylQuotientHom .E6 Ω ⟨a, haM⟩ ∈ Subgroup.zpowers cE6)
    (hntriv : ∃ B : SL(3, Ω), a * fixedA2Rho Ω B ≠ fixedA2Rho Ω B * a)
    (hCa : C ≤ Subgroup.centralizer ({a} : Set (ModGL .E6 Ω)))
    (hNPC : CFSG.HasNormalPComplement 3 ↥(_root_.commutator C)) :
    Group.IsSolvable C := by
  have hw : ∀ γ ∈ fixedA2E6, weylQuotientHom .E6 Ω ⟨a, haM⟩ • γ = γ := by
    intro γ hγ
    have hc : cE6 • γ = γ := by
      rw [cE6_smul]
      exact cAct_fixedA2E6 γ hγ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwc
    rw [← hk]
    exact MulAction.mem_fixedBy_zpow hc k
  obtain ⟨d, hact⟩ := exists_fixedA2_monomial_diagonal_action a haM hw
  let A := CFSG.SectionRank.OddCover.diagHom 3 d
  obtain ⟨c, hc⟩ := exists_scalar_cube_of_fixedA2_action a ha3 A hact
  have hns : ∀ e : Ω, (A : Matrix (Fin 3) (Fin 3) Ω) ≠ e • 1 := by
    intro e he
    have h0 : (d 0 : Ω) = e := by
      simpa [A, CFSG.SectionRank.OddCover.coe_diagHom] using congrFun (congrFun he 0) 0
    have hscalar : A = Matrix.GeneralLinearGroup.scalar (Fin 3) (d 0) := by
      apply Units.ext
      change (A : Matrix (Fin 3) (Fin 3) Ω) = Matrix.scalar (Fin 3) (d 0 : Ω)
      rw [he]
      ext i j
      by_cases hij : i = j
      · subst j; simp [Matrix.scalar, h0]
      · simp [Matrix.scalar, Matrix.one_apply_ne hij, hij]
    obtain ⟨B, hB⟩ := hntriv
    apply hB
    have h := hact B
    change a * fixedA2Rho Ω B * a⁻¹ = fixedA2Rho Ω (slConjugation 3 Ω A B) at h
    rw [hscalar, slConjugation_scalar] at h
    exact (mul_inv_eq_iff_eq_mul).mp h
  exact CFSG.StandardType.TwE6FixedA2SL3.isSolvable_fixedA2Torus_of_cube_scalar_action
    (K := K) h3 hCW (mem_normalizer_fixedA2Torus_of_monomial_root_fixed a haM hw)
    hc hns hact hCa hNPC

section PerfectFiniteFixedA2


include K in
theorem isSolvable_fixedA2Torus_of_complement_derived [CharP Ω 2]
    (C : Subgroup (ModGL .E6 Ω)) [Finite C] (hCW : C ≤ W)
    (hNPC : CFSG.HasNormalPComplement 3 ↥(_root_.commutator C)) : Group.IsSolvable C := by
  obtain ⟨π, _, hker, _⟩ := exists_fixedA2Torus_projective_quotient Ω
  let ρ : C →* projectiveSL 3 Ω := π.comp (inclusion hCW)
  have hρker : ρ.ker ≤ center C := by
    intro g hg
    have hgc : inclusion hCW g ∈ center ↥W := hker.le hg
    rw [mem_center_iff] at hgc ⊢
    intro v
    apply Subtype.ext
    exact congrArg (fun w : ↥W => (w : ModGL .E6 Ω)) (hgc (inclusion hCW v))
  exact CFSG.RankThree.PartTwo.Sec6.BThreeCensus.isSolvable_of_projectiveSL_three_two_algebraic_and_complement_derived
    (K := K) ρ hρker hNPC

end PerfectFiniteFixedA2

end FiniteFixedA2

theorem diag_of_commute_fixedA2Rho {L : Type} [Field L] (b : Fin Tag.E6.rank → Lˣ)
    (hb : ∀ γ ∈ fixedA2E6, rootChar b γ ≠ 1) {B : SL(3, L)}
    (h : rootDiagUnit Tag.E6 b * fixedA2Rho L B = fixedA2Rho L B * rootDiagUnit Tag.E6 b) :
    ∀ i j, i ≠ j → (B : Matrix (Fin 3) (Fin 3) L) i j = 0 := by
  intro i j hij
  set d : Fin 3 → Lˣ := fun i =>
    rootChar b (fixedA2V • CFSG.RankThree.PartOne.TCX.E.chainWeight chain13 i) with hd
  have hconj := rootDiagUnit_conj_fixedA2Rho L b B
  rw [h, mul_inv_cancel_right] at hconj
  have hB : (B : Matrix (Fin 3) (Fin 3) L) i j =
      ((CFSG.RankThree.PartOne.KE.conjDiagn d B : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) i j :=
    congrArg (fun X : SL(3, L) => (X : Matrix (Fin 3) (Fin 3) L) i j)
      (fixedA2Rho_injective L hconj)
  rw [CFSG.RankThree.PartOne.KE.coe_conjDiagn] at hB
  have h1 : ((CFSG.RankThree.PartOne.KE.diagGLn d : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal fun i => (d i : L) := rfl
  have h2 : (((CFSG.RankThree.PartOne.KE.diagGLn d)⁻¹ : GL (Fin 3) L) :
      Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal fun i => (((d i)⁻¹ : Lˣ) : L) := rfl
  rw [h1, h2, Matrix.mul_diagonal, Matrix.diagonal_mul] at hB
  have hratio : d i * (d j)⁻¹ = rootChar b (fixedA2V • chainRoot chain13 i j) := by
    rw [CFSG.RankThree.PartOne.TCX.E.chainRoot_eq_weight_sub, smul_sub, rootChar_sub]
  have hne : ((d i : L)) * (((d j)⁻¹ : Lˣ) : L) ≠ 1 := by
    intro h1'
    apply hb _ (fixedA2V_smul_chainRoot.1 i j hij)
    rw [← hratio]
    exact Units.ext (by simpa using h1')
  have e : (B : Matrix (Fin 3) (Fin 3) L) i j * ((d i : L) * (((d j)⁻¹ : Lˣ) : L) - 1) = 0 := by
    linear_combination -hB
  exact (mul_eq_zero.1 e).resolve_right (sub_ne_zero.2 hne)

set_option maxRecDepth 100000 in
theorem dotZ3_fixedA2E6_combC_ne : ∀ y : Fin 3 → ZMod 3, y 0 ≠ 0 →
    ∀ γ ∈ fixedA2E6, dotZ3 γ (combC y) ≠ 0 := by
  decide +kernel

end Embedding

section DiagFacts

theorem exists_eq_diagSL3 {L : Type} [Field L] (D : SL(3, L))
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin 3) (Fin 3) L) i j = 0) :
    ∃ s u : Lˣ, D = diagSL3 s u := by
  have hdiag : (D : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal fun i => (D : Matrix (Fin 3) (Fin 3) L) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hD i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : (D : Matrix (Fin 3) (Fin 3) L).det = 1 := D.2
  rw [hdiag, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
  have h0 : (D : Matrix (Fin 3) (Fin 3) L) 0 0 ≠ 0 := fun h => by
    rw [h, zero_mul, zero_mul] at hdet
    exact zero_ne_one hdet
  have h2 : (D : Matrix (Fin 3) (Fin 3) L) 2 2 ≠ 0 := fun h => by
    rw [h, mul_zero] at hdet
    exact zero_ne_one hdet
  refine ⟨Units.mk0 _ h0, (Units.mk0 _ h2)⁻¹, ?_⟩
  ext i j
  change (D : Matrix (Fin 3) (Fin 3) L) i j = Matrix.diagonal ![_, _, _] i j
  conv_lhs => rw [hdiag]
  by_cases hij : i = j
  · subst hij
    fin_cases i <;> simp
    field_simp
    linear_combination hdet
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij]

theorem map_diagSL3 {L : Type} [Field L] (Fr : L →+* L) {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (s u : Lˣ) : Matrix.SpecialLinearGroup.map Fr (diagSL3 s u) = diagSL3 (s ^ q) (u ^ q) := by
  ext i j
  change Fr (Matrix.diagonal ![(s : L), ((s⁻¹ * u : Lˣ) : L), ((u⁻¹ : Lˣ) : L)] i j) =
    Matrix.diagonal ![((s ^ q : Lˣ) : L), (((s ^ q)⁻¹ * u ^ q : Lˣ) : L),
      (((u ^ q)⁻¹ : Lˣ) : L)] i j
  by_cases hij : i = j
  · subst hij
    fin_cases i <;> simp [hFr, mul_pow, inv_pow]
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij, map_zero]

theorem diagTuple_pow {L : Type} [Field L] (s u : Lˣ) (q : ℕ) :
    diagTuple s u ^ q = diagTuple (s ^ q) (u ^ q) := by
  funext i
  simp only [diagTuple, weylTuple, Pi.pow_apply, rootChar, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← zpow_natCast _ q, ← zpow_natCast s q, ← zpow_natCast u q]
  simp only [mul_zpow, ← zpow_mul]
  first
  | (congr 1 <;> congr 1 <;> ring)
  | (rw [mul_comm]; congr 1 <;> congr 1 <;> ring)

theorem diagSL3_apply_ne {L : Type} [Field L] (s u : Lˣ) {i j : Fin 3} (hij : i ≠ j) :
    (diagSL3 s u : Matrix (Fin 3) (Fin 3) L) i j = 0 :=
  Matrix.diagonal_apply_ne _ hij

theorem foldr_reflect_zero :
    fixedA2Word.reverse.foldr (reflect Tag.E6) (0 : Fin Tag.E6.rank → ℤ) = 0 := by
  decide +kernel

theorem diagWt_inl (k i : Fin Tag.E6.rank) : diagWt k (Sum.inl i) = 0 := by
  simp only [diagWt, labelWt, foldr_reflect_zero, Pi.zero_apply, zero_mul, Finset.sum_const_zero]


theorem diagWt_mem_diagWtList (ℓ : Label Tag.E6) : (diagWt 0 ℓ, diagWt 2 ℓ) ∈ diagWtList := by
  rcases ℓ with i | ⟨δ, hδ⟩
  · rw [diagWt_inl, diagWt_inl]
    decide
  · exact wtVec_mem_diagWtList δ (mem_rootFinset.mpr hδ)

theorem exists_diagWt_eq {μ : ℤ × ℤ} (hμ : μ ∈ diagWtList) :
    ∃ ℓ : Label Tag.E6, (diagWt 0 ℓ, diagWt 2 ℓ) = μ := by
  rcases exists_wtVec_eq μ hμ with rfl | ⟨δ, hδ, h⟩
  · exact ⟨Sum.inl 0, by rw [diagWt_inl, diagWt_inl]⟩
  · exact ⟨Sum.inr ⟨δ, mem_rootFinset.mp hδ⟩, h⟩

end DiagFacts

section Recognition

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Lang.E6Descent CFSG.ComponentClassification.CatalogueBPrimeJoin
  CFSG.HardMathSupport.Timmesfeld.Torality

variable
  {Ω : Type} [Field Ω]

theorem isQuasisimple_jgeom_of_centralizes_fixedA2 {Fr : Ω →+* Ω}
    {Hh : Subgroup (ModGL Tag.E6 Ω)}
    [Finite ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)]
    {n : ℕ} (hn : 3 ≤ n) {k : Type} [Field k] [Finite k] [Algebra k Ω] [IsAlgClosure k Ω]
    (hk : Nat.card k = (2 ^ n) ^ 2) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (hHF : Hh ≤ TwistedDiag.Rgrp Ω Fr)
    {y₀ : ModGL Tag.E6 Ω} (hy₀ : y₀ ∈ adjointGroup Tag.E6 Ω) {x : ModGL Tag.E6 Ω}
    {ζ : Ωˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    (hHgen : Hh.map (MulAut.conj y₀).toMonoidHom = Subgroup.closure
      ((fun v => rootDiagUnit Tag.E6 (zetaVec ζ hζ v)) ''
        {v | ∃ x', x' 0 = 0 ∧ v = combC x'} ∪ {x}))
    (hxU : rootSpan Tag.E6 Ω {α | α ∈ fixedA2E6} ≤ Subgroup.centralizer {x})
    {e g : ModGL Tag.E6 Ω}
    (heK : e ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (heF : e ∈ TwistedDiag.Rgrp Ω Fr) (he1 : e ≠ 1) (he3 : e ^ 3 = 1)
    (hgK : g ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (hgF : g ∈ TwistedDiag.Rgrp Ω Fr) {t : ℕ} (hg2 : g ^ (2 ^ t) = 1)
    (hinv : g * e * g⁻¹ = e⁻¹) {y : Fin 3 → ZMod 3} (hy0 : y 0 ≠ 0)
    (hey : y₀ * e * y₀⁻¹ = rootDiagUnit Tag.E6 (zetaVec ζ hζ (combC y))) :
    CFSG.IsQuasisimple ((primeResidual 2 ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)).map
        (closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
          Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr).subtype) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype k := Fintype.ofFinite k
  have : CharP k 2 := charP_of_card_eq_prime_pow (f := 2 * n)
    (by rw [← Nat.card_eq_fintype_card, hk, ← pow_mul, mul_comm])
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap k Ω).injective 2
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  set K := closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
    Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) with hKdef
  set H' := Hh.map (MulAut.conj y₀).toMonoidHom with hH'
  set K' := closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
    Subgroup.centralizer (H' : Set (ModGL Tag.E6 Ω))) with hK'def
  have hconj : ∀ z, y₀ * z * y₀⁻¹ ∈ K' ↔ z ∈ K :=
    TwE6FixedComponent.conj_mem_closedIdentityComponent_iff hy₀
  set Hs : Set (Fin Tag.E6.rank → ZMod 3) := {v | ∃ x', x' 0 = 0 ∧ v = combC x'} with hHs
  have ha : ∀ v ∈ Hs, rootDiagUnit Tag.E6 (zetaVec ζ hζ v) ∈ H' := fun v hv => by
    rw [hHgen]
    exact Subgroup.subset_closure (Set.mem_union_left _ ⟨v, hv, rfl⟩)
  set ι := fixedA2Rho Ω with hιdef
  have hU : rootSpan Tag.E6 Ω {α | α ∈ fixedA2E6} ≤
      Subgroup.centralizer (H' : Set (ModGL Tag.E6 Ω)) := by
    rw [hHgen, Subgroup.centralizer_closure]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    rintro h (⟨v, hv, rfl⟩ | hh)
    · have hc : ∀ γ ∈ fixedA2E6, ∀ A, rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * rootSL2 .E6 Ω γ A =
          rootSL2 .E6 Ω γ A * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) := by
        intro γ hγ A
        have h1 := CFSG.RankThree.Chevalley.rootDiagUnit_conj_rootSL2 (zetaVec ζ hζ v)
          (isRoot_of_mem_fixedA2E6 hγ) A
        rw [((isRoot_and_rootChar_zetaVec_iff hζo hζ γ).2 hγ).2 v hv,
          CFSG.RankThree.Chevalley.diagUnitOne_one, CFSG.RankThree.Classical.conjSL_one] at h1
        calc rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * rootSL2 .E6 Ω γ A =
            (rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * rootSL2 .E6 Ω γ A *
              (rootDiagUnit Tag.E6 (zetaVec ζ hζ v))⁻¹) * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) := by
              group
          _ = rootSL2 .E6 Ω γ A * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) := by rw [h1]
      have hz' := rootSpan_fixedA2_le_centralizer (hc _ (mem_fixedA2E6.2 (Or.inl rfl)))
        (hc _ (mem_fixedA2E6.2 (Or.inr (Or.inl rfl))))
        (hc _ (mem_fixedA2E6.2 (Or.inr (Or.inr (Or.inl rfl))))) hz
      exact (Subgroup.mem_centralizer_singleton_iff.1 hz').symm
    · rw [Set.mem_singleton_iff.1 hh]
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hxU hz)).symm
  have hιK' : ∀ A, ι A ∈ K' := fixedA2Rho_mem_closedIdentityComponent hU
  have hKS : ∀ z ∈ K', z ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω {α | α ∈ fixedA2E6} :=
    fun z hz => mem_torus_sup_fixedA2_of_mem_closedIdentityComponent hζo hζ ha hz
  set ιa : SL(3, Ω) →* ModGL Tag.E6 Ω := (MulAut.conj y₀⁻¹).toMonoidHom.comp ι with hιa
  have hιa_apply : ∀ B, ιa B = y₀⁻¹ * ι B * y₀ := fun B => by
    simp only [hιa, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hιainj : Function.Injective ιa := by
    intro A B h
    rw [hιa_apply, hιa_apply] at h
    apply fixedA2Rho_injective Ω
    have h' := congrArg (fun v => y₀ * v * y₀⁻¹) h
    rwa [show y₀ * (y₀⁻¹ * ι A * y₀) * y₀⁻¹ = ι A by group,
      show y₀ * (y₀⁻¹ * ι B * y₀) * y₀⁻¹ = ι B by group] at h'
  have hιaK : ∀ B, ιa B ∈ K := by
    intro B
    rw [← hconj, hιa_apply, show y₀ * (y₀⁻¹ * ι B * y₀) * y₀⁻¹ = ι B by group]
    exact hιK' B
  have hdec : ∀ z ∈ K, ∃ w ∈ K, (∀ v ∈ K, w * v = v * w) ∧
      y₀ * w * y₀⁻¹ ∈ torusGroup Tag.E6 Ω ∧ ∃ B, z = w * ιa B := by
    intro z hz
    obtain ⟨w', hw'K, hw'T, hw'c, B, hB⟩ := exists_central_mul_fixedA2Rho hιK' hKS
      ((hconj z).2 hz)
    refine ⟨y₀⁻¹ * w' * y₀, ?_, ?_, ?_, B, ?_⟩
    · rw [← hconj, show y₀ * (y₀⁻¹ * w' * y₀) * y₀⁻¹ = w' by group]
      exact hw'K
    · intro v hv
      have hc := hw'c _ ((hconj v).2 hv)
      calc y₀⁻¹ * w' * y₀ * v = y₀⁻¹ * (w' * (y₀ * v * y₀⁻¹)) * y₀ := by group
        _ = y₀⁻¹ * ((y₀ * v * y₀⁻¹) * w') * y₀ := by rw [hc]
        _ = v * (y₀⁻¹ * w' * y₀) := by group
    · rw [show y₀ * (y₀⁻¹ * w' * y₀) * y₀⁻¹ = w' by group]
      exact hw'T
    · rw [hιa_apply]
      calc z = y₀⁻¹ * (y₀ * z * y₀⁻¹) * y₀ := by group
        _ = y₀⁻¹ * (w' * ι B) * y₀ := by rw [hB]
        _ = y₀⁻¹ * w' * y₀ * (y₀⁻¹ * ι B * y₀) := by group
  have hFι : ∀ B, twistHom TwistTag.E6 Ω Fr (ιa B) ∈ ιa.range :=
    TwE6FixedComponent.twistHom_mem_range_of_central_mul hk Fr hFr hHF (by norm_num) ιa hιaK
      fun z hz => by
        obtain ⟨w, hwK, hwc, -, B, hB⟩ := hdec z hz
        exact ⟨w, hwK, hwc, B, hB⟩
  let e₀ : SL(3, Ω) ≃* ιa.range := MonoidHom.ofInjective hιainj
  let Fι : SL(3, Ω) →* ιa.range :=
    ((twistHom TwistTag.E6 Ω Fr).comp ιa).codRestrict ιa.range hFι
  let σ : SL(3, Ω) →* SL(3, Ω) := e₀.symm.toMonoidHom.comp Fι
  have hισ : ∀ B, ιa (σ B) = twistHom TwistTag.E6 Ω Fr (ιa B) := fun B =>
    (MonoidHom.ofInjective_apply hιainj (x := e₀.symm (Fι B))).symm.trans
      (congrArg Subtype.val (e₀.apply_symm_apply (Fι B)))
  set be := zetaVec ζ hζ (combC y) with hbe
  have hreg : ∀ γ ∈ fixedA2E6, rootChar be γ ≠ 1 := fun γ hγ h =>
    dotZ3_fixedA2E6_combC_ne y hy0 γ hγ ((rootChar_zetaVec_eq_one_iff_dotZ3 hζo hζ _ γ).1 h)
  have hFe : twistHom TwistTag.E6 Ω Fr e = e := heF.2
  have hσD : ∀ D : SL(3, Ω), (∀ i j, i ≠ j → (D : Matrix (Fin 3) (Fin 3) Ω) i j = 0) →
      ∀ i j, i ≠ j → ((σ D : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) i j = 0 := by
    intro D hD
    obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
      (fixedA2Rho_diag_mem_torusGroup Ω D hD)
    have h1 : ιa D * e = e * ιa D := by
      rw [hιa_apply]
      have k : ι D * (y₀ * e * y₀⁻¹) = (y₀ * e * y₀⁻¹) * ι D := by
        rw [hey, hl, ← CFSG.LieType.Chevalley.rootDiagUnit_mul,
          ← CFSG.LieType.Chevalley.rootDiagUnit_mul, mul_comm]
      calc y₀⁻¹ * ι D * y₀ * e = y₀⁻¹ * (ι D * (y₀ * e * y₀⁻¹)) * y₀ := by group
        _ = y₀⁻¹ * ((y₀ * e * y₀⁻¹) * ι D) * y₀ := by rw [k]
        _ = e * (y₀⁻¹ * ι D * y₀) := by group
    have h2 : ιa (σ D) * e = e * ιa (σ D) := by
      let F' : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω := twistHom TwistTag.E6 Ω Fr
      have h := congrArg F' h1
      rw [map_mul, map_mul] at h
      have hFe' : F' e = e := hFe
      rw [hFe'] at h
      rw [hισ]
      exact h
    have h3 : rootDiagUnit Tag.E6 be * ι (σ D) = ι (σ D) * rootDiagUnit Tag.E6 be := by
      rw [hιa_apply] at h2
      rw [← hey]
      have h := congrArg (fun v => y₀ * v * y₀⁻¹) h2
      rw [show y₀ * (y₀⁻¹ * ι (σ D) * y₀ * e) * y₀⁻¹ = ι (σ D) * (y₀ * e * y₀⁻¹) by group,
        show y₀ * (e * (y₀⁻¹ * ι (σ D) * y₀)) * y₀⁻¹ = (y₀ * e * y₀⁻¹) * ι (σ D) by group] at h
      exact h.symm
    exact diag_of_commute_fixedA2Rho be hreg h3
  set P : ModGL Tag.E6 Ω := diagramMap TwistTag.E6 Ω with hP
  set R : ModGL Tag.E6 Ω := y₀ * P * (Units.map (entrywiseHom Fr) y₀)⁻¹ with hR
  have hFdef : ∀ z : ModGL Tag.E6 Ω, twistHom TwistTag.E6 Ω Fr z =
      P * Units.map (entrywiseHom Fr) z * P⁻¹ := fun z => rfl
  have hιaD : ∀ s u : Ωˣ, ιa (diagSL3 s u) = y₀⁻¹ * rootDiagUnit Tag.E6 (diagTuple s u) * y₀ :=
    fun s u => by rw [hιa_apply, fixedA2Rho_diagSL3]
  have hιaD' : ∀ s u : Ωˣ, y₀ * ιa (diagSL3 s u) * y₀⁻¹ = rootDiagUnit Tag.E6 (diagTuple s u) :=
    fun s u => by rw [hιaD]; group
  let F' : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω := twistHom TwistTag.E6 Ω Fr
  have hFD : ∀ s u : Ωˣ, y₀ * F' (ιa (diagSL3 s u)) * y₀⁻¹ =
      R * rootDiagUnit Tag.E6 (diagTuple (s ^ 2 ^ n) (u ^ 2 ^ n)) * R⁻¹ := by
    intro s u
    change y₀ * (P * Units.map (entrywiseHom Fr) (ιa (diagSL3 s u)) * P⁻¹) * y₀⁻¹ = _
    rw [hιaD, map_mul, map_mul, map_inv,
      CFSG.HardMathSupport.Foote.Coordinator.entrywise_frob_rootDiagUnit' hFr, diagTuple_pow, hR,
      mul_inv_rev, mul_inv_rev, inv_inv]
    simp only [mul_assoc]
  have hroot : ∀ w : Ωˣ, ∃ s : Ωˣ, s ^ 2 ^ n = w := by
    intro w
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (w : Ω) (show 0 < 2 ^ n by positivity)
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact w.ne_zero (by rw [← hr, zero_pow (by positivity)])
    exact ⟨Units.mk0 r hr0, Units.ext (by simp [hr])⟩
  have hθ : ∀ s u : Ωˣ, ∃ s' u' : Ωˣ, R * rootDiagUnit Tag.E6 (diagTuple s u) * R⁻¹ =
      rootDiagUnit Tag.E6 (diagTuple s' u') := by
    intro s u
    obtain ⟨s₀, rfl⟩ := hroot s
    obtain ⟨u₀, rfl⟩ := hroot u
    obtain ⟨s', u', hsu⟩ := exists_eq_diagSL3 (σ (diagSL3 s₀ u₀))
      (hσD _ fun i j hij => diagSL3_apply_ne s₀ u₀ hij)
    refine ⟨s', u', ?_⟩
    rw [← hFD]
    have h' : F' (ιa (diagSL3 s₀ u₀)) = ιa (σ (diagSL3 s₀ u₀)) := (hισ _).symm
    rw [h', hsu, hιaD']
  choose θ₁ θ₂ hθ' using hθ
  obtain ⟨ℓ₁, hℓ₁⟩ := exists_diagWt_eq (μ := (1, 0)) (by decide)
  obtain ⟨ℓ₂, hℓ₂⟩ := exists_diagWt_eq (μ := (0, 1)) (by decide)
  obtain ⟨b₁, b₂, hθform, hrows, hcols⟩ := exists_weightMatrix_of_conj_rootDiagUnit
    diagTuple (diagWt 0) (diagWt 2) rootChar_diagTuple R θ₁ θ₂ hθ' (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂)
    ⟨congrArg Prod.fst hℓ₁, congrArg Prod.snd hℓ₁⟩ ⟨congrArg Prod.fst hℓ₂, congrArg Prod.snd hℓ₂⟩
  have hμν : ((diagWt 0 b₁, diagWt 2 b₁), (diagWt 0 b₂, diagWt 2 b₂)) ∈ weylMatList := by
    refine weightMatrix_mem_weylMatList _ (diagWt_mem_diagWtList b₁) _
      (diagWt_mem_diagWtList b₂) ?_ ?_
    · intro α hα
      obtain ⟨a, rfl⟩ := exists_diagWt_eq hα
      obtain ⟨b, hb1, hb2⟩ := hrows a
      rw [← hb1, ← hb2]
      exact diagWt_mem_diagWtList b
    · intro β hβ
      obtain ⟨b, rfl⟩ := exists_diagWt_eq hβ
      obtain ⟨a, ha1, ha2⟩ := hcols b
      exact ⟨(diagWt 0 a, diagWt 2 a), diagWt_mem_diagWtList a, by rw [ha1, ha2]⟩
  obtain ⟨A₀, hA₀⟩ := exists_conj_diagSL3_of_mem_weylMatList (L := Ω) _ _ hμν
  have hσdiag : ∀ s u : Ωˣ, σ (diagSL3 s u) =
      diagSL3 (θ₁ (s ^ 2 ^ n) (u ^ 2 ^ n)) (θ₂ (s ^ 2 ^ n) (u ^ 2 ^ n)) := by
    intro s u
    apply hιainj
    have h1 : y₀ * ιa (σ (diagSL3 s u)) * y₀⁻¹ =
        y₀ * ιa (diagSL3 (θ₁ (s ^ 2 ^ n) (u ^ 2 ^ n)) (θ₂ (s ^ 2 ^ n) (u ^ 2 ^ n))) * y₀⁻¹ := by
      have h' : ιa (σ (diagSL3 s u)) = F' (ιa (diagSL3 s u)) := hισ _
      rw [h', hFD, hθ', hιaD']
    have h2 := congrArg (fun v => y₀⁻¹ * v * y₀) h1
    simpa only [show ∀ v : ModGL Tag.E6 Ω, y₀⁻¹ * (y₀ * v * y₀⁻¹) * y₀ = v from fun v => by
      group] using h2
  have hσT : (∀ D : SL(3, Ω), (D : Matrix (Fin 3) (Fin 3) Ω).IsDiag →
        σ D = CFSG.RankThree.Classical2.conjSLn A₀ (Matrix.SpecialLinearGroup.map Fr D)) ∨
      ∀ D : SL(3, Ω), (D : Matrix (Fin 3) (Fin 3) Ω).IsDiag →
        σ D = CFSG.RankThree.Classical2.conjSLn A₀
          (CFSG.RankThree.Classical2.invTransposeSL (Matrix.SpecialLinearGroup.map Fr D)) := by
    rcases hA₀ with h | h
    · refine Or.inl fun D hD => ?_
      obtain ⟨s, u, rfl⟩ := exists_eq_diagSL3 D fun i j hij => hD hij
      rw [hσdiag, map_diagSL3 Fr hFr, (hθform _ _).1, (hθform _ _).2]
      exact h _ _
    · refine Or.inr fun D hD => ?_
      obtain ⟨s, u, rfl⟩ := exists_eq_diagSL3 D fun i j hij => hD hij
      rw [hσdiag, map_diagSL3 Fr hFr, (hθform _ _).1, (hθform _ _).2]
      exact h _ _
  let Zc : Subgroup (ModGL Tag.E6 Ω) := K ⊓ Subgroup.centralizer (K : Set (ModGL Tag.E6 Ω))
  have hZcent : ∀ z ∈ Zc, ∀ v ∈ K, z * v = v * z := fun z hz v hv =>
    (Subgroup.mem_centralizer_iff.1 hz.2 v hv).symm
  have hZodd : ∀ z ∈ Zc, ∃ m, Odd m ∧ z ^ m = 1 := by
    intro z hz
    obtain ⟨w, hwK, hwc, hwT, B, rfl⟩ := hdec z hz.1
    have hBc : ∀ A, ιa B * ιa A = ιa A * ιa B := by
      intro A
      have h1 := hZcent _ hz (ιa A) (hιaK A)
      have h2 := hwc (ιa A) (hιaK A)
      have h3 : w * (ιa B * ιa A) = w * (ιa A * ιa B) := by
        calc w * (ιa B * ιa A) = w * ιa B * ιa A := (mul_assoc _ _ _).symm
          _ = ιa A * (w * ιa B) := h1
          _ = w * (ιa A * ιa B) := by rw [← mul_assoc, ← h2, mul_assoc]
      exact mul_left_cancel h3
    have hBcent : B ∈ Subgroup.center (SL(3, Ω)) := Subgroup.mem_center_iff.2 fun A =>
      hιainj (by rw [map_mul, map_mul]; exact (hBc A).symm)
    have hB3 : B ^ 3 = 1 := by
      obtain ⟨r, hr, hrB⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hBcent
      have hr3 : r ^ 3 = 1 := by simpa [Fintype.card_fin] using hr
      ext i j
      rw [Matrix.SpecialLinearGroup.coe_pow, ← hrB, Matrix.SpecialLinearGroup.coe_one,
        ← map_pow, hr3, map_one]
    obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hwT
    obtain ⟨N, hNodd, hlN⟩ :=
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141e.exists_odd_pow_eq_one
        (K := k) (ringChar.eq k 2) l
    have hl1 : l ^ N = 1 := funext hlN
    have hwN : w ^ N = 1 := by
      have h1 : (y₀ * w * y₀⁻¹) ^ N = 1 := by
        rw [hl, ← CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_pow', hl1,
          CFSG.LieType.Chevalley.rootDiagUnit_one]
      rw [conj_pow, conj_eq_one_iff] at h1
      exact h1
    refine ⟨3 * N, Odd.mul (by decide) hNodd, ?_⟩
    have hcomm : Commute w (ιa B) := hwc _ (hιaK B)
    rw [hcomm.mul_pow, pow_mul, pow_mul, ← map_pow, hB3, map_one, one_pow, mul_one,
      ← pow_mul, mul_comm, pow_mul, hwN, one_pow]
  have hKdec : ∀ v ∈ K, ∃ z ∈ Zc, ∃ B : SL(3, Ω), v = z * ιa B := by
    intro v hv
    obtain ⟨w, hwK, hwc, -, B, hB⟩ := hdec v hv
    exact ⟨w, ⟨hwK, Subgroup.mem_centralizer_iff.2 fun u hu => (hwc u hu).symm⟩, B, hB⟩
  exact TwE6FixedComponent.isQuasisimple_jgeom_of_lift Fr Hh hn hk hFr hHF le_rfl ιa hιaK
    (by rw [(MonoidHom.ker_eq_bot_iff ιa).mpr hιainj]; exact bot_le) σ (fun B => (hισ B).symm)
    A₀ hσT hZcent hZodd hKdec heK heF he1 he3 hgK hgF hg2 hinv

end Recognition

end CFSG.StandardType.TwE6FixedA2SL3

end
