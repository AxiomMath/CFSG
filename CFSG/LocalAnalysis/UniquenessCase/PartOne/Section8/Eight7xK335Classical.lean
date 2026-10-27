module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335Coord
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335Orders
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335Torus
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194OmegaTorus
import CFSG.CharacterTheory.Wreathed.CentralSL2.NonsplitField
import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalFrame
public import CFSG.ClassicalGroups.SpecialLinear.SLnThreeLocalDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsDomain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

open Matrix
open Polynomial
open CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven
open CFSG.LieType.BorelTits
open CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal
open CFSG.Wreathed.CentralSL2
open CFSG.Open
open scoped commutatorElement

theorem k335_coord_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {H : Subgroup (GL ι K)} {a : ℕ}
    (h3 : ¬ 3 ∣ Nat.card ((CFSG.Open.StatedScalars ι K).subgroupOf H))
    (hc : K335Coord ↥H a) : K335Coord (CFSG.Open.StatedProj H) a :=
  hc.map (QuotientGroup.mk' _) (by rwa [QuotientGroup.ker_mk'])

section K335PspAux

private def k335psp_shift : Equiv.Perm (Fin 3) where
  toFun i := i + 1
  invFun i := i - 1
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private lemma k335psp_shift_pow_three : k335psp_shift ^ 3 = 1 := by
  ext i
  fin_cases i <;> decide

private def k335psp_shiftInv : Equiv.Perm (Fin 3) := k335psp_shift⁻¹

private def k335psp_P (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  Equiv.Perm.permMatrix K k335psp_shift⁻¹

private lemma k335psp_P_transpose (K : Type) [Field K] :
    (k335psp_P K)ᵀ = Equiv.Perm.permMatrix K k335psp_shift := by
  rw [k335psp_P, Matrix.transpose_permMatrix, inv_inv]

private lemma k335psp_P_pow_three (K : Type) [Field K] : (k335psp_P K) ^ 3 = 1 := by
  rw [k335psp_P,
    show Equiv.Perm.permMatrix K k335psp_shift⁻¹ =
      Matrix.permMatrixHom (R := K) k335psp_shift from rfl]
  rw [← map_pow, k335psp_shift_pow_three, map_one]

private lemma k335psp_P_mul_transpose (K : Type) [Field K] :
    k335psp_P K * (k335psp_P K)ᵀ = 1 := by
  rw [k335psp_P_transpose, k335psp_P,
    ← Matrix.permMatrix_mul (σ := k335psp_shift) (τ := k335psp_shift⁻¹)]
  simp

private lemma k335psp_P_transpose_mul (K : Type) [Field K] :
    (k335psp_P K)ᵀ * k335psp_P K = 1 := by
  rw [k335psp_P_transpose, k335psp_P,
    ← Matrix.permMatrix_mul (σ := k335psp_shift⁻¹) (τ := k335psp_shift)]
  simp

private lemma k335psp_perm_conj (K : Type) [Field K] (A : Matrix (Fin 3) (Fin 3) K) :
    k335psp_P K * A * (k335psp_P K)ᵀ =
      A.submatrix k335psp_shiftInv k335psp_shiftInv := by
  rw [k335psp_P_transpose, k335psp_P]
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl

private lemma k335psp_perm_conj_diag (K : Type) [Field K] (v : Fin 3 → K) :
    k335psp_P K * diagonal v * (k335psp_P K)ᵀ =
      diagonal (v ∘ k335psp_shiftInv) := by
  rw [k335psp_perm_conj, submatrix_diagonal_equiv]

private def k335psp_J (K : Type) [Field K] : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  fromBlocks (0 : Matrix (Fin 3) (Fin 3) K) 1 (-1) 0

private def k335psp_blk {K : Type} [Field K]
    (M : Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  fromBlocks
    (diagonal fun i => (M i : Matrix (Fin 2) (Fin 2) K) 0 0)
    (diagonal fun i => (M i : Matrix (Fin 2) (Fin 2) K) 0 1)
    (diagonal fun i => (M i : Matrix (Fin 2) (Fin 2) K) 1 0)
    (diagonal fun i => (M i : Matrix (Fin 2) (Fin 2) K) 1 1)

private lemma k335psp_blk_mul {K : Type} [Field K]
    (M N : Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K) :
    k335psp_blk (M * N) = k335psp_blk M * k335psp_blk N := by
  rw [k335psp_blk, k335psp_blk, k335psp_blk, fromBlocks_multiply, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [diagonal_mul_diagonal, diagonal_mul_diagonal, diagonal_add,
        Matrix.diagonal_injective.eq_iff]
      funext i
      rw [Pi.mul_apply, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

private lemma k335psp_blk_one (K : Type) [Field K] :
    k335psp_blk (1 : Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K) = 1 := by
  simp [k335psp_blk, Matrix.fromBlocks_one]

private lemma k335psp_diag_anticomm (K : Type) [Field K] (u v : Fin 3 → K) :
    -(diagonal u) * diagonal v + diagonal v * diagonal u = 0 := by
  rw [neg_mul, diagonal_mul_diagonal, diagonal_mul_diagonal, diagonal_neg, diagonal_add,
    show (0 : Matrix (Fin 3) (Fin 3) K) = diagonal (fun _ => 0) from diagonal_zero.symm,
    Matrix.diagonal_injective.eq_iff]
  funext i
  ring

private lemma k335psp_diag_cross (K : Type) [Field K] (a b c d : Fin 3 → K)
    (h : ∀ i, a i * d i - c i * b i = 1) :
    -(diagonal c) * diagonal b + diagonal a * diagonal d = 1 := by
  rw [neg_mul, diagonal_mul_diagonal, diagonal_mul_diagonal, diagonal_neg, diagonal_add,
    show (1 : Matrix (Fin 3) (Fin 3) K) = diagonal (fun _ => 1) from diagonal_one.symm,
    Matrix.diagonal_injective.eq_iff]
  funext i
  linear_combination h i

private lemma k335psp_diag_cross_neg (K : Type) [Field K] (a b c d : Fin 3 → K)
    (h : ∀ i, a i * d i - c i * b i = 1) :
    -(diagonal d) * diagonal a + diagonal b * diagonal c = -1 := by
  rw [neg_mul, diagonal_mul_diagonal, diagonal_mul_diagonal, diagonal_neg, diagonal_add,
    show (-1 : Matrix (Fin 3) (Fin 3) K) = diagonal (fun _ => -1) from by
      rw [show (-1 : Matrix (Fin 3) (Fin 3) K) = -(1 : Matrix (Fin 3) (Fin 3) K) from rfl,
        show (1 : Matrix (Fin 3) (Fin 3) K) = diagonal (fun _ => 1) from diagonal_one.symm,
        diagonal_neg],
    Matrix.diagonal_injective.eq_iff]
  funext i
  linear_combination -(h i)

private lemma k335psp_blk_symp {K : Type} [Field K]
    (M : Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K) :
    (k335psp_blk M)ᵀ * k335psp_J K * k335psp_blk M = k335psp_J K := by
  set a : Fin 3 → K := fun i => (M i : Matrix (Fin 2) (Fin 2) K) 0 0 with ha
  set b : Fin 3 → K := fun i => (M i : Matrix (Fin 2) (Fin 2) K) 0 1 with hb
  set c : Fin 3 → K := fun i => (M i : Matrix (Fin 2) (Fin 2) K) 1 0 with hc
  set d : Fin 3 → K := fun i => (M i : Matrix (Fin 2) (Fin 2) K) 1 1 with hd
  have hdet : ∀ i : Fin 3, a i * d i - c i * b i = 1 := by
    intro i
    have hh := Matrix.SpecialLinearGroup.det_coe (M i)
    rw [Matrix.det_fin_two] at hh
    simp only [ha, hb, hc, hd] at hh ⊢
    linear_combination hh
  have hblk : k335psp_blk M =
      fromBlocks (diagonal a) (diagonal b) (diagonal c) (diagonal d) := rfl
  rw [hblk, k335psp_J, fromBlocks_transpose]
  simp only [diagonal_transpose]
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  simp only [mul_zero, add_zero, zero_add, mul_one, mul_neg]
  exact ⟨k335psp_diag_anticomm K c a, k335psp_diag_cross K a b c d hdet,
    k335psp_diag_cross_neg K a b c d hdet, k335psp_diag_anticomm K d b⟩

private def k335psp_blkUnit {K : Type} [Field K]
    (M : Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K) :
    Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) K :=
  Units.mk (k335psp_blk M) (k335psp_blk M⁻¹)
    (by rw [← k335psp_blk_mul, mul_inv_cancel, k335psp_blk_one])
    (by rw [← k335psp_blk_mul, inv_mul_cancel, k335psp_blk_one])

private lemma k335psp_blkUnit_coe {K : Type} [Field K]
    (M : Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K) :
    (k335psp_blkUnit M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = k335psp_blk M := rfl

private lemma k335psp_blkUnit_mem {K : Type} [Field K]
    (M : Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K) :
    k335psp_blkUnit M ∈ CFSG.Open.StatedSp 3 K := by
  rw [CFSG.Open.StatedAPI.mem_statedSp_iff]
  simpa only [k335psp_blkUnit_coe, k335psp_J] using k335psp_blk_symp M

private def k335psp_Phi {K : Type} [Field K] :
    (Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K) →* ↥(CFSG.Open.StatedSp 3 K) where
  toFun M := ⟨k335psp_blkUnit M, k335psp_blkUnit_mem M⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    change k335psp_blk (1 : Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K) = 1
    rw [k335psp_blk_one]
  map_mul' M N := by
    apply Subtype.ext
    apply Units.ext
    change k335psp_blk (M * N) = k335psp_blk M * k335psp_blk N
    rw [k335psp_blk_mul]

private lemma k335psp_Phi_injective {K : Type} [Field K] :
    Function.Injective (k335psp_Phi (K := K)) := by
  intro M N h
  have hmat : k335psp_blk M = k335psp_blk N := by
    have h1 : k335psp_blkUnit M = k335psp_blkUnit N := congrArg Subtype.val h
    have h2 := congrArg (fun u : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) K =>
      (u : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)) h1
    simpa only [k335psp_blkUnit_coe] using h2
  funext i
  apply Matrix.SpecialLinearGroup.ext
  intro r s
  fin_cases r <;> fin_cases s
  · have hh := congrFun (congrFun hmat (Sum.inl i)) (Sum.inl i)
    simpa [k335psp_blk, Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply] using hh
  · have hh := congrFun (congrFun hmat (Sum.inl i)) (Sum.inr i)
    simpa [k335psp_blk, Matrix.fromBlocks_apply₁₂, Matrix.diagonal_apply] using hh
  · have hh := congrFun (congrFun hmat (Sum.inr i)) (Sum.inl i)
    simpa [k335psp_blk, Matrix.fromBlocks_apply₂₁, Matrix.diagonal_apply] using hh
  · have hh := congrFun (congrFun hmat (Sum.inr i)) (Sum.inr i)
    simpa [k335psp_blk, Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply] using hh

private def k335psp_coeHom {K : Type} [Field K]
    (T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) :
    (Fin 3 → ↥T) →* (Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K) :=
  MonoidHom.mk' (fun x i => (x i : Matrix.SpecialLinearGroup (Fin 2) K)) (by intro x y; rfl)

private def k335psp_sMat (K : Type) [Field K] :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  fromBlocks (k335psp_P K) 0 0 (k335psp_P K)

private def k335psp_sUnit (K : Type) [Field K] :
    Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) K :=
  Units.mk (k335psp_sMat K)
    (fromBlocks (k335psp_P K)ᵀ (0 : Matrix (Fin 3) (Fin 3) K) 0 (k335psp_P K)ᵀ)
    (by
      rw [k335psp_sMat, fromBlocks_multiply]
      simp only [zero_mul, mul_zero, add_zero, zero_add, k335psp_P_mul_transpose,
        Matrix.fromBlocks_one])
    (by
      rw [k335psp_sMat, fromBlocks_multiply]
      simp only [zero_mul, mul_zero, add_zero, zero_add, k335psp_P_transpose_mul,
        Matrix.fromBlocks_one])

private lemma k335psp_sUnit_mem (K : Type) [Field K] :
    k335psp_sUnit K ∈ CFSG.Open.StatedSp 3 K := by
  rw [CFSG.Open.StatedAPI.mem_statedSp_iff]
  show (k335psp_sMat K)ᵀ * fromBlocks (0 : Matrix (Fin 3) (Fin 3) K) 1 (-1) 0 *
      k335psp_sMat K = fromBlocks (0 : Matrix (Fin 3) (Fin 3) K) 1 (-1) 0
  rw [k335psp_sMat, fromBlocks_transpose]
  simp only [Matrix.transpose_zero]
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [k335psp_P_transpose_mul]

private def k335psp_s (K : Type) [Field K] : ↥(CFSG.Open.StatedSp 3 K) :=
  ⟨k335psp_sUnit K, k335psp_sUnit_mem K⟩

private lemma k335psp_s_pow_three (K : Type) [Field K] : (k335psp_s K) ^ 3 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change (k335psp_sMat K) ^ 3 = 1
  rw [k335psp_sMat, fromBlocks_diagonal_pow, k335psp_P_pow_three, Matrix.fromBlocks_one]

private lemma k335psp_sMat_conj (K : Type) [Field K]
    (M : Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K) :
    k335psp_sMat K * k335psp_blk M *
        fromBlocks (k335psp_P K)ᵀ (0 : Matrix (Fin 3) (Fin 3) K) 0 (k335psp_P K)ᵀ =
      k335psp_blk (fun i => M (i - 1)) := by
  have hR : k335psp_blk (fun i => M (i - 1)) =
      fromBlocks
        (diagonal fun i => (M (i - 1) : Matrix (Fin 2) (Fin 2) K) 0 0)
        (diagonal fun i => (M (i - 1) : Matrix (Fin 2) (Fin 2) K) 0 1)
        (diagonal fun i => (M (i - 1) : Matrix (Fin 2) (Fin 2) K) 1 0)
        (diagonal fun i => (M (i - 1) : Matrix (Fin 2) (Fin 2) K) 1 1) := rfl
  rw [hR, k335psp_sMat, k335psp_blk, fromBlocks_multiply, fromBlocks_multiply]
  simp only [zero_mul, mul_zero, add_zero, zero_add]
  rw [fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (rw [k335psp_perm_conj_diag]; rfl)

private lemma k335psp_s_conj_Phi (K : Type) [Field K]
    (M : Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K) :
    k335psp_s K * k335psp_Phi M * (k335psp_s K)⁻¹ =
      k335psp_Phi (fun i => M (i - 1)) := by
  apply Subtype.ext
  apply Units.ext
  change k335psp_sMat K * k335psp_blk M *
      fromBlocks (k335psp_P K)ᵀ (0 : Matrix (Fin 3) (Fin 3) K) 0 (k335psp_P K)ᵀ =
    k335psp_blk (fun i => M (i - 1))
  exact k335psp_sMat_conj K M

private lemma k335psp_phi_move {K : Type} [Field K]
    (T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K))
    (w : Matrix.SpecialLinearGroup (Fin 2) K) (hw : ∀ x ∈ T, w * x * w⁻¹ = x⁻¹)
    (c : ↥T) (_hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    ∃ g : ↥(CFSG.Open.StatedSp 3 K), ∃ u : Fin 3 → ↥T,
      (∀ i, u i ∈ Subgroup.zpowers c) ∧ u 0 * u 1 * u 2 ≠ 1 ∧
        g * (k335psp_Phi.comp (k335psp_coeHom T)) (fun _ => c) * g⁻¹ =
          (k335psp_Phi.comp (k335psp_coeHom T)) u := by
  let u : Fin 3 → ↥T := fun i => if i = 2 then c else c⁻¹
  let gw : Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K := fun i => if i = 2 then 1 else w
  have hu_mem : ∀ i, u i ∈ Subgroup.zpowers c := by
    intro i
    fin_cases i <;> simp [u]
  have hu_prod : u 0 * u 1 * u 2 = c⁻¹ := by
    change c⁻¹ * c⁻¹ * c = c⁻¹
    group
  have hu_ne : u 0 * u 1 * u 2 ≠ 1 := by
    rw [hu_prod]
    exact fun h => hc1 (inv_eq_one.mp h)
  have harg : gw * (fun _ : Fin 3 => (c : Matrix.SpecialLinearGroup (Fin 2) K)) * gw⁻¹ =
      fun i => (u i : Matrix.SpecialLinearGroup (Fin 2) K) := by
    funext i
    fin_cases i
    · change w * (c : Matrix.SpecialLinearGroup (Fin 2) K) * w⁻¹ = (c⁻¹ : ↥T)
      rw [hw (c : Matrix.SpecialLinearGroup (Fin 2) K) c.2]
      rfl
    · change w * (c : Matrix.SpecialLinearGroup (Fin 2) K) * w⁻¹ = (c⁻¹ : ↥T)
      rw [hw (c : Matrix.SpecialLinearGroup (Fin 2) K) c.2]
      rfl
    · change 1 * (c : Matrix.SpecialLinearGroup (Fin 2) K) * 1⁻¹ = (c : ↥T)
      rw [one_mul, inv_one, mul_one]
  refine ⟨k335psp_Phi gw, u, hu_mem, hu_ne, ?_⟩
  change k335psp_Phi gw *
      k335psp_Phi (fun _ => (c : Matrix.SpecialLinearGroup (Fin 2) K)) *
      (k335psp_Phi gw)⁻¹ =
    k335psp_Phi (fun i => (u i : Matrix.SpecialLinearGroup (Fin 2) K))
  rw [← map_inv, ← map_mul, ← map_mul, harg]

private theorem k335psp_coord_matrix {K : Type} [Field K] [Finite K]
    (T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K))
    (hTcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hTcard : Nat.card T = 3 ^ ((Nat.card K ^ 2 - 1).factorization 3))
    (w : Matrix.SpecialLinearGroup (Fin 2) K) (hw : ∀ x ∈ T, w * x * w⁻¹ = x⁻¹) :
    K335Coord ↥(CFSG.Open.StatedSp 3 K) ((Nat.card K ^ 2 - 1).factorization 3) := by
  let CG : CommGroup ↥T :=
    { (inferInstance : Group ↥T) with
      mul_comm := fun a b => Subtype.ext (hTcomm a a.2 b b.2) }
  let φ : (Fin 3 → ↥T) →* ↥(CFSG.Open.StatedSp 3 K) :=
    k335psp_Phi.comp (k335psp_coeHom T)
  have hφ_inj : Function.Injective φ :=
    k335psp_Phi_injective.comp (by
      intro x y hxy
      funext i
      exact Subtype.ext (congrFun hxy i))
  have hs_shift : ∀ x : Fin 3 → ↥T,
      k335psp_s K * φ x * (k335psp_s K)⁻¹ = φ (fun i => x (i - 1)) := by
    intro x
    change k335psp_s K * k335psp_Phi (k335psp_coeHom T x) * (k335psp_s K)⁻¹ =
      k335psp_Phi (k335psp_coeHom T (fun i => x (i - 1)))
    rw [k335psp_s_conj_Phi]
    rfl
  have hmove : ∀ c : ↥T, c ^ 3 = 1 → c ≠ 1 → ∃ g : ↥(CFSG.Open.StatedSp 3 K),
      ∃ u : Fin 3 → ↥T,
        (∀ i, u i ∈ Subgroup.zpowers c) ∧ u 0 * u 1 * u 2 ≠ 1 ∧
          g * φ (fun _ => c) * g⁻¹ = φ u :=
    fun c hc3 hc1 => k335psp_phi_move T w hw c hc3 hc1
  exact ⟨↥T, CG, inferInstance, hTcard, φ, hφ_inj, k335psp_s K, k335psp_s_pow_three K,
    hs_shift, hmove⟩

private theorem k335psp_core {X : Type} [Group X] {p f : ℕ}
    (htor : ∀ {K : Type} [Field K] [Fintype K], ¬ 3 ∣ Nat.card K →
      ∃ T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K),
        (∀ x ∈ T, ∀ y ∈ T, x * y = y * x) ∧
        Nat.card T = 3 ^ ((Nat.card K ^ 2 - 1).factorization 3) ∧
        ∃ w : Matrix.SpecialLinearGroup (Fin 2) K, ∀ x ∈ T, w * x * w⁻¹ = x⁻¹)
    (h : LieModel X .PSp 3 p f) (hp : p ≠ 3) :
    K335Coord X (((p ^ f) ^ 2 - 1).factorization 3) := by
  obtain ⟨hadm, K, hKfield, hKfin, hKcard, ⟨e⟩⟩ :=
    h.statedClassicalModel_of_ne_zero (by norm_num)
  have hpP : p.Prime := hadm.1
  have h3K : ¬ 3 ∣ Nat.card K := by
    rw [hKcard]
    exact k335_three_not_dvd hpP hp
  obtain ⟨T, hTcomm, hTcard, w, hw⟩ :=
    @htor K hKfield (Fintype.ofFinite K) h3K
  have hcoord : K335Coord ↥(CFSG.Open.StatedSp 3 K)
      ((Nat.card K ^ 2 - 1).factorization 3) :=
    k335psp_coord_matrix T hTcomm hTcard w hw
  have hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3) c ∈
      CFSG.Open.StatedSp 3 K → c ^ 2 = 1 := fun c hc =>
    (CFSG.Open.StatedAPI.scalar_mem_statedSp_iff (n := 3) (by norm_num) c).1 hc
  have hproj : K335Coord (CFSG.Open.StatedProj (CFSG.Open.StatedSp 3 K))
      ((Nat.card K ^ 2 - 1).factorization 3) :=
    k335_coord_statedProj
      (CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf (CFSG.Open.StatedSp 3 K)
        Nat.prime_three (by norm_num : ¬ 3 ∣ 2) hd) hcoord
  have hX : K335Coord X ((Nat.card K ^ 2 - 1).factorization 3) :=
    K335Coord.of_mulEquiv e.symm hproj
  simpa only [hKcard] using hX

end K335PspAux

theorem k335_coord_psp6 {X : Type} [Group X] {p f : ℕ} (h : LieModel X .PSp 3 p f)
    (hp : p ≠ 3) : K335Coord X (((p ^ f) ^ 2 - 1).factorization 3) :=
  k335psp_core k335_sl2_torus h hp

private theorem k335o7s_sq_sub_one (q : ℕ) : q ^ 2 - 1 = (q - 1) * (q + 1) := by
  symm
  have h1 : (q + 1) * (q - 1) = (q + 1) * q - (q + 1) := Nat.mul_sub_one (q+1) q
  have h2 : (q + 1) * q = q * q + q := by rw [Nat.add_mul, one_mul]
  have h3 : q * q + q - (q + 1) = q * q - 1 := by omega
  rw [mul_comm, h1, h2, h3, sq]

private theorem k335o7s_factorization_sq_sub_one {q : ℕ} (h2 : 2 ≤ q) (hq : q % 3 = 1) :
    (q ^ 2 - 1).factorization 3 = (q - 1).factorization 3 := by
  have hq1 : ¬ 3 ∣ q + 1 := by
    intro hd
    have h0 : (q + 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
    omega
  rw [k335o7s_sq_sub_one q, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hq1, add_zero]

private def k335o7s_block (σ : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 3 ⊕ Fin 3 ⊕ Unit) :=
  Equiv.sumCongr σ (Equiv.sumCongr σ (Equiv.refl Unit))

@[simp] private theorem k335o7s_block_inl (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    k335o7s_block σ (.inl i) = .inl (σ i) := rfl
@[simp] private theorem k335o7s_block_inr_inl (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    k335o7s_block σ (.inr (.inl i)) = .inr (.inl (σ i)) := rfl
@[simp] private theorem k335o7s_block_inr_inr (σ : Equiv.Perm (Fin 3)) (u : Unit) :
    k335o7s_block σ (.inr (.inr u)) = .inr (.inr u) := rfl

private theorem k335o7s_block_quad {K : Type} [Field K] (σ : Equiv.Perm (Fin 3))
    (v : Fin 3 ⊕ Fin 3 ⊕ Unit → K) :
    CFSG.Open.StatedQuadOdd 3 K (v ∘ k335o7s_block σ) = CFSG.Open.StatedQuadOdd 3 K v := by
  simp only [CFSG.Open.StatedQuadOdd, Function.comp_apply, k335o7s_block_inl,
    k335o7s_block_inr_inl, k335o7s_block_inr_inr]
  congr 1
  exact Equiv.sum_comp σ (fun j => v (.inl j) * v (.inr (.inl j)))

private def k335o7s_tau01 : Equiv.Perm (Fin 3 ⊕ Fin 3 ⊕ Unit) :=
  k335o7s_block (Equiv.swap (0 : Fin 3) 1)

private def k335o7s_tau12 : Equiv.Perm (Fin 3 ⊕ Fin 3 ⊕ Unit) :=
  k335o7s_block (Equiv.swap (1 : Fin 3) 2)

private theorem k335o7s_tau01_quad {K : Type} [Field K]
    (v : Fin 3 ⊕ Fin 3 ⊕ Unit → K) :
    CFSG.Open.StatedQuadOdd 3 K (v ∘ k335o7s_tau01) = CFSG.Open.StatedQuadOdd 3 K v :=
  k335o7s_block_quad _ v

private theorem k335o7s_tau12_quad {K : Type} [Field K]
    (v : Fin 3 ⊕ Fin 3 ⊕ Unit → K) :
    CFSG.Open.StatedQuadOdd 3 K (v ∘ k335o7s_tau12) = CFSG.Open.StatedQuadOdd 3 K v :=
  k335o7s_block_quad _ v

private def k335o7s_rhoFun (j : Fin 3 ⊕ Fin 3 ⊕ Unit) : Fin 3 ⊕ Fin 3 ⊕ Unit :=
  match j with
  | .inl i => .inl (i + 1)
  | .inr (.inl i) => .inr (.inl (i + 1))
  | .inr (.inr u) => .inr (.inr u)

private def k335o7s_rhoInvFun (j : Fin 3 ⊕ Fin 3 ⊕ Unit) : Fin 3 ⊕ Fin 3 ⊕ Unit :=
  match j with
  | .inl i => .inl (i - 1)
  | .inr (.inl i) => .inr (.inl (i - 1))
  | .inr (.inr u) => .inr (.inr u)

private def k335o7s_rho : Equiv.Perm (Fin 3 ⊕ Fin 3 ⊕ Unit) where
  toFun := k335o7s_rhoFun
  invFun := k335o7s_rhoInvFun
  left_inv := by
    intro j
    rcases j with i | i | u <;> simp [k335o7s_rhoFun, k335o7s_rhoInvFun]
  right_inv := by
    intro j
    rcases j with i | i | u <;> simp [k335o7s_rhoFun, k335o7s_rhoInvFun]

@[simp] private theorem k335o7s_rho_inl (i : Fin 3) :
    k335o7s_rho (.inl i) = .inl (i + 1) := rfl
@[simp] private theorem k335o7s_rho_inr_inl (i : Fin 3) :
    k335o7s_rho (.inr (.inl i)) = .inr (.inl (i + 1)) := rfl
@[simp] private theorem k335o7s_rho_inr_inr (u : Unit) :
    k335o7s_rho (.inr (.inr u)) = .inr (.inr u) := rfl
@[simp] private theorem k335o7s_rho_symm_inl (i : Fin 3) :
    (k335o7s_rho)⁻¹ (.inl i) = .inl (i - 1) := rfl
@[simp] private theorem k335o7s_rho_symm_inr_inl (i : Fin 3) :
    (k335o7s_rho)⁻¹ (.inr (.inl i)) = .inr (.inl (i - 1)) := rfl
@[simp] private theorem k335o7s_rho_symm_inr_inr (u : Unit) :
    (k335o7s_rho)⁻¹ (.inr (.inr u)) = .inr (.inr u) := rfl

private theorem k335o7s_rho_pow_three : k335o7s_rho ^ 3 = 1 := by
  ext j
  rcases j with i | i | u
  · fin_cases i <;> decide
  · fin_cases i <;> decide
  · rcases u with ⟨⟩
    decide

private theorem k335o7s_rho_eq_comm : k335o7s_rho = ⁅k335o7s_tau12, k335o7s_tau01⁆ := by
  ext j
  rcases j with i | i | u
  · fin_cases i <;> decide
  · fin_cases i <;> decide
  · rcases u with ⟨⟩
    decide

private def k335o7s_swapAllFun (j : Fin 3 ⊕ Fin 3 ⊕ Unit) : Fin 3 ⊕ Fin 3 ⊕ Unit :=
  match j with
  | .inl i => .inr (.inl i)
  | .inr (.inl i) => .inl i
  | .inr (.inr u) => .inr (.inr u)

private theorem k335o7s_swapAllFun_involutive : Function.Involutive k335o7s_swapAllFun := by
  intro j; rcases j with i | i | u <;> rfl

private def k335o7s_swapAll : Equiv.Perm (Fin 3 ⊕ Fin 3 ⊕ Unit) :=
  k335o7s_swapAllFun_involutive.toPerm k335o7s_swapAllFun

@[simp] private theorem k335o7s_swapAll_inl (i : Fin 3) :
    k335o7s_swapAll (.inl i) = .inr (.inl i) := rfl
@[simp] private theorem k335o7s_swapAll_inr_inl (i : Fin 3) :
    k335o7s_swapAll (.inr (.inl i)) = .inl i := rfl
@[simp] private theorem k335o7s_swapAll_inr_inr (u : Unit) :
    k335o7s_swapAll (.inr (.inr u)) = .inr (.inr u) := rfl

private theorem k335o7s_swapAll_quad {K : Type} [Field K]
    (v : Fin 3 ⊕ Fin 3 ⊕ Unit → K) :
    CFSG.Open.StatedQuadOdd 3 K (v ∘ k335o7s_swapAll) = CFSG.Open.StatedQuadOdd 3 K v := by
  simp only [CFSG.Open.StatedQuadOdd, Function.comp_apply, k335o7s_swapAll_inl,
    k335o7s_swapAll_inr_inl, k335o7s_swapAll_inr_inr]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private def k335o7s_dφ {K : Type} [Field K] {C : Subgroup Kˣ}
    (d : Fin 3 → C) : Fin 3 ⊕ Fin 3 ⊕ Unit → Kˣ :=
  fun j => match j with
    | .inl i => (d i : Kˣ)
    | .inr (.inl i) => ((d i : Kˣ))⁻¹
    | .inr (.inr _) => 1

@[simp] private theorem k335o7s_dφ_inl {K : Type} [Field K] {C : Subgroup Kˣ}
    (d : Fin 3 → C) (i : Fin 3) :
    k335o7s_dφ d (.inl i) = (d i : Kˣ) := rfl
@[simp] private theorem k335o7s_dφ_inr_inl {K : Type} [Field K] {C : Subgroup Kˣ}
    (d : Fin 3 → C) (i : Fin 3) :
    k335o7s_dφ d (.inr (.inl i)) = ((d i : Kˣ))⁻¹ := rfl
@[simp] private theorem k335o7s_dφ_inr_inr {K : Type} [Field K] {C : Subgroup Kˣ}
    (d : Fin 3 → C) (u : Unit) :
    k335o7s_dφ d (.inr (.inr u)) = 1 := rfl

private def k335o7s_dφHom {K : Type} [Field K] {C : Subgroup Kˣ} :
    (Fin 3 → C) →* (Fin 3 ⊕ Fin 3 ⊕ Unit → Kˣ) where
  toFun := k335o7s_dφ
  map_one' := by
    funext j; rcases j with i | i | u <;> simp [k335o7s_dφ]
  map_mul' d e := by
    funext j
    rcases j with i | i | u <;> simp [k335o7s_dφ, Pi.mul_apply, _root_.mul_inv_rev, mul_comm]

private theorem k335o7s_dφ_mem {K : Type} [Field K] {C : Subgroup Kˣ}
    {r : ℕ} (hr : Odd r) (hC : ∀ c : C, c ^ r = 1) (d : Fin 3 → C) :
    diagGL (k335o7s_dφ d) ∈ CFSG.Open.StatedOmega (CFSG.Open.StatedQuadOdd 3 K) := by
  refine diagGL_mem_statedOmega (Q := CFSG.Open.StatedQuadOdd 3 K)
    (σ := k335o7s_swapAll) (fun v => k335o7s_swapAll_quad v) hr ?_ ?_ ?_
  · intro j
    rcases j with i | i | u
    · simpa using congrArg (fun x : C => (x : Kˣ)) (hC (d i))
    · rw [k335o7s_dφ_inr_inl, inv_pow]
      simpa using congrArg (fun x : C => (x : Kˣ)) (hC (d i))
    · simp
  · intro v
    simp only [CFSG.Open.StatedQuadOdd, k335o7s_dφ_inl, k335o7s_dφ_inr_inl, k335o7s_dφ_inr_inr,
      Units.val_one, one_mul]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      linear_combination (v (.inl i) * v (.inr (.inl i))) * ((d i : Kˣ)).mul_inv
  · intro j
    rcases j with i | i | u <;> simp [k335o7s_swapAll, k335o7s_swapAllFun]

private theorem k335o7s_dφ_diag_injective {K : Type} [Field K] {C : Subgroup Kˣ} :
    Function.Injective (fun d : Fin 3 → C => diagGL (k335o7s_dφ d)) := by
  intro d e h
  funext i
  have h1 := congrArg (fun A : GL (Fin 3 ⊕ Fin 3 ⊕ Unit) K =>
    ((A : Matrix (Fin 3 ⊕ Fin 3 ⊕ Unit) (Fin 3 ⊕ Fin 3 ⊕ Unit) K) (.inl i) (.inl i))) h
  simp only [coe_diagGL, Matrix.diagonal_apply_eq, k335o7s_dφ_inl] at h1
  exact Subtype.ext (Units.ext h1)

private theorem k335o7s_isometry_of_mem_statedOmega {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {Q : (ι → K) → K} {g : GL ι K} (hg : g ∈ CFSG.Open.StatedOmega Q)
    (v : ι → K) : Q ((g : Matrix ι ι K) *ᵥ v) = Q v := by
  let I : Subgroup (GL ι K) :=
    { carrier := {A | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v}
      one_mem' := fun v => by simp
      mul_mem' := fun {a b} ha hb v => by
        simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
        rw [ha, hb]
      inv_mem' := fun {a} ha v => by
        have := ha (((a⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v)
        simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using this.symm }
  have hcl : Subgroup.closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} ≤ I :=
    (Subgroup.closure_le I).mpr fun A hA => hA
  have hg' : g ∈ Subgroup.closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} :=
    Subgroup.commutator_le_self _ hg
  exact hcl hg' v

private theorem k335o7s_scalar_sq {K : Type} [Field K] {c : Kˣ}
    (hc : Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3 ⊕ Unit) c ∈
      CFSG.Open.StatedOmega (CFSG.Open.StatedQuadOdd 3 K)) : c ^ 2 = 1 := by
  have hiso := k335o7s_isometry_of_mem_statedOmega hc
  let v : Fin 3 ⊕ Fin 3 ⊕ Unit → K := Pi.single (.inr (.inr ())) 1
  have hmul : ((Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3 ⊕ Unit) c :
      Matrix (Fin 3 ⊕ Fin 3 ⊕ Unit) (Fin 3 ⊕ Fin 3 ⊕ Unit) K) *ᵥ v) =
      fun j => (c : K) * v j := by
    ext j
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have h := hiso v
  rw [hmul] at h
  have hL : CFSG.Open.StatedQuadOdd 3 K (fun j => (c : K) * v j) = (c : K) ^ 2 := by
    simp only [CFSG.Open.StatedQuadOdd]
    rw [Finset.sum_eq_zero (fun i _ => by simp [v])]
    simp [v]
  have hR : CFSG.Open.StatedQuadOdd 3 K v = 1 := by
    simp only [CFSG.Open.StatedQuadOdd]
    rw [Finset.sum_eq_zero (fun i _ => by simp [v])]
    simp [v]
  rw [hL, hR] at h
  have h' : ((c : K)) ^ 2 = 1 := h
  exact Units.ext h'

private theorem k335o7s_permGL_mem_isometryCore {K : Type} [Field K]
    {Q : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) → K} {σ : Equiv.Perm (Fin 3 ⊕ Fin 3 ⊕ Unit)}
    (hσ : ∀ v, Q (v ∘ σ) = Q v) :
    permGL σ ∈ CFSG.MatrixModel.isometryCore Q :=
  Subgroup.subset_closure (fun v => by
    rw [mulVec_permGL]
    have h := hσ (v ∘ ⇑(σ⁻¹ : Equiv.Perm _))
    rw [show (v ∘ ⇑(σ⁻¹ : Equiv.Perm _)) ∘ σ = v from funext fun j => by simp] at h
    exact h.symm)

private theorem k335o7s_permGL_comm_mem {K : Type} [Field K]
    {Q : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) → K}
    {σ₁ σ₂ : Equiv.Perm (Fin 3 ⊕ Fin 3 ⊕ Unit)}
    (h₁ : ∀ v, Q (v ∘ σ₁) = Q v) (h₂ : ∀ v, Q (v ∘ σ₂) = Q v) :
    permGL ⁅σ₁, σ₂⁆ ∈ CFSG.Open.StatedOmega Q := by
  rw [map_commutatorElement]
  exact Subgroup.commutator_mem_commutator (k335o7s_permGL_mem_isometryCore h₁)
    (k335o7s_permGL_mem_isometryCore h₂)

private theorem k335o7s_permGL_conj_diagGL {K : Type} [Field K]
    (τ : Equiv.Perm (Fin 3 ⊕ Fin 3 ⊕ Unit)) (e : Fin 3 ⊕ Fin 3 ⊕ Unit → Kˣ) :
    permGL τ * diagGL e * (permGL τ)⁻¹ = diagGL (fun j => e (τ⁻¹ j)) := by
  calc permGL τ * diagGL e * (permGL τ)⁻¹
      = (permGL τ * diagGL e) * (permGL τ)⁻¹ := by rw [mul_assoc]
    _ = (diagGL (fun j => e (τ⁻¹ j)) * permGL τ) * (permGL τ)⁻¹ := by rw [permGL_mul_diagGL]
    _ = diagGL (fun j => e (τ⁻¹ j)) * (permGL τ * (permGL τ)⁻¹) := by rw [mul_assoc]
    _ = diagGL (fun j => e (τ⁻¹ j)) := by rw [mul_inv_cancel, mul_one]

private def k335o7s_sig0 : Equiv.Perm (Fin 3 ⊕ Fin 3 ⊕ Unit) :=
  Equiv.swap (.inl (0 : Fin 3)) (.inr (.inl (0 : Fin 3)))

private def k335o7s_sig1 : Equiv.Perm (Fin 3 ⊕ Fin 3 ⊕ Unit) :=
  Equiv.swap (.inl (1 : Fin 3)) (.inr (.inl (1 : Fin 3)))

private theorem k335o7s_sig0_quad {K : Type} [Field K]
    (v : Fin 3 ⊕ Fin 3 ⊕ Unit → K) :
    CFSG.Open.StatedQuadOdd 3 K (v ∘ k335o7s_sig0) = CFSG.Open.StatedQuadOdd 3 K v := by
  simp only [CFSG.Open.StatedQuadOdd, Function.comp_apply]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : i = 0
    · subst h
      simp only [k335o7s_sig0, Equiv.swap_apply_left, Equiv.swap_apply_right]
      exact mul_comm _ _
    · have h1 : k335o7s_sig0 (.inl i) = .inl i := by
        rw [k335o7s_sig0, Equiv.swap_apply_of_ne_of_ne]
        · intro e; exact h (Sum.inl_injective e)
        · exact Sum.inl_ne_inr
      have h2 : k335o7s_sig0 (.inr (.inl i)) = .inr (.inl i) := by
        rw [k335o7s_sig0, Equiv.swap_apply_of_ne_of_ne]
        · exact Sum.inr_ne_inl
        · intro e; exact h (Sum.inl_injective (Sum.inr_injective e))
      rw [h1, h2]

private theorem k335o7s_sig01_eq_comm :
    k335o7s_sig0 * k335o7s_sig1 = ⁅k335o7s_sig0, k335o7s_tau01⁆ := by
  ext j
  rcases j with i | i | u
  · fin_cases i <;> decide
  · fin_cases i <;> decide
  · rcases u with ⟨⟩
    decide

private theorem k335o7s_sig01_inv :
    (k335o7s_sig0 * k335o7s_sig1)⁻¹ = k335o7s_sig0 * k335o7s_sig1 := by
  ext j
  rcases j with i | i | u
  · fin_cases i <;> decide
  · fin_cases i <;> decide
  · rcases u with ⟨⟩
    decide

theorem k335_coord_omega7_split {X : Type} [Group X] {p f : ℕ}
    (h : LieModel X .POmegaOdd 3 p f) (hq : p ^ f % 3 = 1) :
    K335Coord X (((p ^ f) ^ 2 - 1).factorization 3) := by
  obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num)
  let : Field K := hfield
  let : Finite K := hfinite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq2 : 2 ≤ p ^ f := by
    rw [← hK]
    exact Finite.one_lt_card
  let a : ℕ := ((p ^ f) ^ 2 - 1).factorization 3
  let C : Sylow 3 Kˣ := default
  have hCcard : Nat.card C = 3 ^ a := by
    dsimp only [a]
    rw [Sylow.card_eq_multiplicity C, Nat.card_units, hK]
    congr 1
    exact (k335o7s_factorization_sq_sub_one hq2 hq).symm
  have hCpow : ∀ c : C, c ^ (3 ^ a) = 1 := by
    intro c
    rw [← hCcard]
    exact pow_card_eq_one'
  have hOdd : Odd (3 ^ a) := (by decide : Odd 3).pow (n := a)
  let H : Subgroup (GL (Fin 3 ⊕ Fin 3 ⊕ Unit) K) :=
    CFSG.Open.StatedOmega (CFSG.Open.StatedQuadOdd 3 K)
  have hφmem : ∀ d : Fin 3 → C, diagGL (k335o7s_dφHom d) ∈ H := fun d =>
    k335o7s_dφ_mem hOdd hCpow d
  let φ : (Fin 3 → C) →* H := (diagGL.comp k335o7s_dφHom).codRestrict H hφmem
  have hφinj : Function.Injective φ := by
    intro d d' hdd
    apply k335o7s_dφ_diag_injective
    exact congrArg (fun x : H => (x : GL (Fin 3 ⊕ Fin 3 ⊕ Unit) K)) hdd
  have hρH : permGL k335o7s_rho ∈ H := by
    rw [k335o7s_rho_eq_comm]
    exact k335o7s_permGL_comm_mem k335o7s_tau12_quad k335o7s_tau01_quad
  let s : H := ⟨permGL k335o7s_rho, hρH⟩
  have hs3 : s ^ 3 = 1 := by
    apply Subtype.ext
    show (permGL k335o7s_rho) ^ 3 = 1
    rw [← map_pow, k335o7s_rho_pow_three, map_one]
  have hs : ∀ x : Fin 3 → C, s * φ x * s⁻¹ = φ (fun i => x (i - 1)) := by
    intro x
    apply Subtype.ext
    show permGL k335o7s_rho * diagGL (k335o7s_dφHom x) * (permGL k335o7s_rho)⁻¹ =
      diagGL (k335o7s_dφHom (fun i => x (i - 1)))
    rw [k335o7s_permGL_conj_diagGL]
    congr 1
    funext j
    rcases j with i | i | u
    · simp [k335o7s_dφHom, k335o7s_rho_symm_inl]
    · simp [k335o7s_dφHom, k335o7s_rho_symm_inr_inl]
    · simp [k335o7s_dφHom]
  have hgH : permGL (k335o7s_sig0 * k335o7s_sig1) ∈ H := by
    rw [k335o7s_sig01_eq_comm]
    exact k335o7s_permGL_comm_mem k335o7s_sig0_quad k335o7s_tau01_quad
  have hmove : ∀ c : C, c ^ 3 = 1 → c ≠ 1 → ∃ g : H, ∃ u : Fin 3 → C,
      (∀ i, u i ∈ Subgroup.zpowers c) ∧ u 0 * u 1 * u 2 ≠ 1 ∧
      g * φ (fun _ => c) * g⁻¹ = φ u := by
    intro c hc3 hc1
    let g : H := ⟨permGL (k335o7s_sig0 * k335o7s_sig1), hgH⟩
    let u : Fin 3 → C := ![c⁻¹, c⁻¹, c]
    refine ⟨g, u, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [u]
    · have h1 : u 0 * u 1 * u 2 = c⁻¹ := by
        simp only [u, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]
        rw [mul_assoc, inv_mul_cancel, mul_one]
      rw [h1]
      exact fun h => hc1 (inv_eq_one.mp h)
    · apply Subtype.ext
      show permGL (k335o7s_sig0 * k335o7s_sig1) * diagGL (k335o7s_dφHom (fun _ => c)) *
        (permGL (k335o7s_sig0 * k335o7s_sig1))⁻¹ = diagGL (k335o7s_dφHom u)
      rw [k335o7s_permGL_conj_diagGL, k335o7s_sig01_inv]
      congr 1
      funext j
      rcases j with i | i | u'
      · fin_cases i <;> simp (disch := decide) [u, k335o7s_dφHom, k335o7s_sig0, k335o7s_sig1,
          Equiv.swap_apply_of_ne_of_ne]
      · fin_cases i
        · simp (disch := decide) [u, k335o7s_dφHom, k335o7s_sig0, k335o7s_sig1,
            Equiv.swap_apply_of_ne_of_ne]
        · simp (disch := decide) [u, k335o7s_dφHom, k335o7s_sig0, k335o7s_sig1,
            Equiv.swap_apply_of_ne_of_ne]
        · simp (disch := decide) [u, k335o7s_dφHom, k335o7s_sig0, k335o7s_sig1,
            Equiv.swap_apply_of_ne_of_ne]
      · rcases u' with ⟨⟩
        rfl
  refine K335Coord.of_mulEquiv e.symm (k335_coord_statedProj ?_ ?_)
  · exact CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf H Nat.prime_three
      (by norm_num) (fun c hc => k335o7s_scalar_sq hc)
  · exact ⟨C, inferInstance, inferInstance, hCcard, φ, hφinj, s, hs3, hs, hmove⟩

private def k335o7n_N {K : Type} [Field K] (ν : K) (v : Fin 2 → K) : K :=
  v 0 ^ 2 - ν * v 1 ^ 2

private lemma k335o7n_leftMulMatrix_basis {K : Type} [Field K] (ν : K)
    (z : QuadraticAlgebra K ν 0) :
    Algebra.leftMulMatrix (QuadraticAlgebra.basis (R := K) (a := ν) (b := 0)) z =
      !![z.re, ν * z.im; z.im, z.re] := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis_repr_apply,
      QuadraticAlgebra.basis_apply_zero, QuadraticAlgebra.basis_apply_one,
      ]

private lemma k335o7n_N_mulVec {K : Type} [Field K] (ν α β : K)
    (h : α ^ 2 - ν * β ^ 2 = 1) (v : Fin 2 → K) :
    k335o7n_N ν (Matrix.mulVec (!![α, ν * β; β, α] : Matrix (Fin 2) (Fin 2) K) v) =
      k335o7n_N ν v := by
  simp only [Matrix.mulVec, dotProduct, k335o7n_N, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (v 0 ^ 2 - ν * v 1 ^ 2) * h

private lemma k335o7n_N_Fmat {K : Type} [Field K] (ν : K) (v : Fin 2 → K) :
    k335o7n_N ν (Matrix.mulVec (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) K) v) =
      k335o7n_N ν v := by
  simp only [Matrix.mulVec, dotProduct, k335o7n_N, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private lemma k335o7n_one_fin_two {K : Type} [Field K] :
    (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private lemma k335o7n_Fmat_mul {K : Type} [Field K] (ν α β : K)
    (h : α ^ 2 - ν * β ^ 2 = 1) :
    (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) K) *
        (!![α, ν * β; β, α] : Matrix (Fin 2) (Fin 2) K) *
        (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) K) *
        (!![α, ν * β; β, α] : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_zero', Matrix.cons_val_one, Matrix.cons_val_succ']
  · linear_combination h
  · ring
  · ring
  · linear_combination h

private theorem k335o7n_torus {K : Type} [Field K] [Fintype K]
    (h2 : (2 : K) ≠ 0) (hcard : Nat.card K % 3 = 2) :
    ∃ (ν : K) (C : Subgroup (GL (Fin 2) K)) (F : GL (Fin 2) K),
      ¬ IsSquare ν ∧
      (∀ x ∈ C, ∀ y ∈ C, x * y = y * x) ∧
      Nat.card C = 3 ^ ((Nat.card K ^ 2 - 1).factorization 3) ∧
      (∀ x ∈ C, F * x * F⁻¹ = x⁻¹) ∧
      (∀ x ∈ C, ∀ v : Fin 2 → K,
        k335o7n_N ν ((x : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = k335o7n_N ν v) ∧
      (∀ v : Fin 2 → K,
        k335o7n_N ν ((F : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = k335o7n_N ν v) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar : ringChar K ≠ 2 := by
    intro hc
    exact h2 (by
      have : CharP K 2 := ringChar.of_eq hc
      exact CharP.cast_eq_zero K 2)
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare (F := K) hchar
  let L := QuadraticAlgebra K ν 0
  let : Fact (¬ IsSquare ν) := ⟨hν⟩
  let : Field L := inferInstance
  let : Fintype L := Fintype.ofEquiv (K × K) (QuadraticAlgebra.equivProd ν 0).symm
  let bs : Module.Basis (Fin 2) K L := QuadraticAlgebra.basis (R := K) (a := ν) (b := 0)
  let μ : Lˣ →* GL (Fin 2) K := Units.map (Algebra.leftMulMatrix bs).toMonoidHom
  let normU : Lˣ →* Kˣ := Units.map (QuadraticAlgebra.norm (a := ν) (b := 0))
  let C0 : Sylow 3 Lˣ := default
  have hcardL : Nat.card L = Nat.card K ^ 2 := by
    rw [Nat.card_congr (QuadraticAlgebra.equivProd ν 0), Nat.card_prod, sq]
  have hC0card : Nat.card C0 = 3 ^ ((Nat.card K ^ 2 - 1).factorization 3) := by
    rw [Sylow.card_eq_multiplicity C0, Nat.card_units, hcardL]
  have h3K : ¬ 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    intro hd
    have h0 : (Nat.card K - 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd hd
    omega
  have hnorm1 (c : C0) : QuadraticAlgebra.norm ((c : Lˣ) : L) = 1 := by
    have h1 : orderOf (normU (c : Lˣ)) ∣ 3 ^ ((Nat.card K ^ 2 - 1).factorization 3) := by
      rw [← hC0card]
      refine (orderOf_map_dvd normU (c : Lˣ)).trans ?_
      rw [Subgroup.orderOf_coe]
      exact orderOf_dvd_natCard c
    have h2 : orderOf (normU (c : Lˣ)) ∣ Nat.card Kˣ := orderOf_dvd_natCard _
    have hcop : Nat.Coprime (3 ^ ((Nat.card K ^ 2 - 1).factorization 3)) (Nat.card Kˣ) :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3K).pow_left _
    have hone : orderOf (normU (c : Lˣ)) = 1 := by
      have hd : orderOf (normU (c : Lˣ)) ∣ Nat.gcd _ _ := Nat.dvd_gcd h1 h2
      rw [hcop, Nat.dvd_one] at hd
      exact hd
    have htriv : normU (c : Lˣ) = 1 := orderOf_eq_one_iff.mp hone
    have := congrArg (fun u : Kˣ => (u : K)) htriv
    simpa [normU] using this
  have hμinj : Function.Injective μ := by
    intro x y hxy
    apply Units.ext
    apply Algebra.leftMulMatrix_injective bs
    simpa [μ] using congrArg Units.val hxy
  have hμ_eq (c : Lˣ) :
      ((μ c : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        !![(c : L).re, ν * (c : L).im; (c : L).im, (c : L).re] := by
    simpa [μ, bs] using k335o7n_leftMulMatrix_basis (K := K) ν (c : L)
  have hnorm_re_im (c : C0) :
      ((c : Lˣ) : L).re ^ 2 - ν * ((c : Lˣ) : L).im ^ 2 = 1 := by
    have h := hnorm1 c
    rw [QuadraticAlgebra.norm_def] at h
    linear_combination h
  have hisom (c : C0) : ∀ v : Fin 2 → K,
      k335o7n_N ν (Matrix.mulVec ((μ (c : Lˣ) : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) v) = k335o7n_N ν v := by
    intro v
    rw [hμ_eq (c : Lˣ)]
    exact k335o7n_N_mulVec ν _ _ (hnorm_re_im c) v
  let Fmat : Matrix (Fin 2) (Fin 2) K := !![1, 0; 0, -1]
  have hFF : Fmat * Fmat = 1 := by
    funext i j
    fin_cases i <;> fin_cases j <;> simp [Fmat]
  let F : GL (Fin 2) K := ⟨Fmat, Fmat, hFF, hFF⟩
  have hFval : ((F : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Fmat := rfl
  have hFinv : F⁻¹ = F := Units.ext rfl
  have hFconj (c : Lˣ) (hc : QuadraticAlgebra.norm (c : L) = 1) :
      F * μ c * F⁻¹ = (μ c)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    apply Units.ext
    simp only [Units.val_mul, Units.val_one]
    rw [hFinv, hFval, hμ_eq c]
    have hnorm : (c : L).re ^ 2 - ν * (c : L).im ^ 2 = 1 := by
      rw [QuadraticAlgebra.norm_def] at hc
      linear_combination hc
    rw [← k335o7n_one_fin_two]
    exact k335o7n_Fmat_mul ν _ _ hnorm
  have hFisom : ∀ v : Fin 2 → K,
      k335o7n_N ν ((F : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = k335o7n_N ν v := by
    intro v
    rw [hFval]
    exact k335o7n_N_Fmat ν v
  let C : Subgroup (GL (Fin 2) K) := C0.map μ
  refine ⟨ν, C, F, hν, ?_, ?_, ?_, ?_, hFisom⟩
  · intro x hx y hy
    obtain ⟨a, _, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, _, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul, mul_comm a b]
  · rw [Subgroup.card_map_of_injective hμinj, hC0card]
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    exact hFconj a (hnorm1 ⟨a, ha⟩)
  · intro x hx v
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    exact hisom ⟨a, ha⟩ v

private abbrev k335o7n_σ := Fin 2 × Fin 3 ⊕ Unit

private def k335o7n_pair {K : Type} (v : k335o7n_σ → K) (i : Fin 3) : Fin 2 → K :=
  fun j => v (.inl (j, i))

private def k335o7n_Qmodel {K : Type} [Field K] (ν : K) (v : k335o7n_σ → K) : K :=
  (∑ i : Fin 3, k335o7n_N ν (k335o7n_pair v i)) + ν * v (.inr ()) ^ 2

private def k335o7n_blkMat {K : Type} [Field K] (A : Fin 3 → Matrix (Fin 2) (Fin 2) K) :
    Matrix k335o7n_σ k335o7n_σ K :=
  Matrix.fromBlocks (Matrix.blockDiagonal A) 0 0 (1 : Matrix Unit Unit K)

private lemma k335o7n_blockDiagonal_mulVec {K : Type} [Field K]
    (A : Fin 3 → Matrix (Fin 2) (Fin 2) K) (u : Fin 2 × Fin 3 → K) (i : Fin 3) :
    (Matrix.blockDiagonal A *ᵥ u) ∘ (fun k => (k, i)) = A i *ᵥ (fun j => u (j, i)) := by
  funext k
  simp only [Function.comp_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single i]
  · simp [Matrix.blockDiagonal_apply_eq]
  · intro b _ hb
    rw [Matrix.blockDiagonal_apply_ne A k x (Ne.symm hb), zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private lemma k335o7n_blkMat_mulVec {K : Type} [Field K]
    (A : Fin 3 → Matrix (Fin 2) (Fin 2) K) (v : k335o7n_σ → K) :
    (k335o7n_blkMat A *ᵥ v) ∘ Sum.inl =
        fun p : Fin 2 × Fin 3 => (A p.2 *ᵥ (fun j => v (.inl (j, p.2)))) p.1 := by
  funext p
  rw [k335o7n_blkMat, Matrix.fromBlocks_mulVec]
  simp only [zero_mulVec, add_zero]
  exact congrFun (k335o7n_blockDiagonal_mulVec A (v ∘ Sum.inl) p.2) p.1

private lemma k335o7n_blkMat_mul {K : Type} [Field K]
    (A B : Fin 3 → Matrix (Fin 2) (Fin 2) K) :
    k335o7n_blkMat (fun i => A i * B i) = k335o7n_blkMat A * k335o7n_blkMat B := by
  rw [k335o7n_blkMat, k335o7n_blkMat, k335o7n_blkMat, Matrix.fromBlocks_multiply]
  simp only [Matrix.blockDiagonal_mul, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.mul_one, add_zero, zero_add]

private lemma k335o7n_blkMat_one {K : Type} [Field K] :
    k335o7n_blkMat (1 : Fin 3 → Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [k335o7n_blkMat, Matrix.blockDiagonal_one, Matrix.fromBlocks_one]

private lemma k335o7n_blkMat_inv {K : Type} [Field K] (A : Fin 3 → GL (Fin 2) K) :
    k335o7n_blkMat (fun i => (A i : Matrix (Fin 2) (Fin 2) K)) *
      k335o7n_blkMat (fun i => (((A i)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = 1 := by
  rw [← k335o7n_blkMat_mul]
  convert k335o7n_blkMat_one (K := K) using 2
  funext i
  exact congrArg Units.val (mul_inv_cancel (A i))

private lemma k335o7n_blkMat_inv' {K : Type} [Field K] (A : Fin 3 → GL (Fin 2) K) :
    k335o7n_blkMat (fun i => (((A i)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
      k335o7n_blkMat (fun i => (A i : Matrix (Fin 2) (Fin 2) K)) = 1 := by
  rw [← k335o7n_blkMat_mul]
  convert k335o7n_blkMat_one (K := K) using 2
  funext i
  exact congrArg Units.val (inv_mul_cancel (A i))

private def k335o7n_blk {K : Type} [Field K] : (Fin 3 → GL (Fin 2) K) →* GL k335o7n_σ K where
  toFun A := ⟨k335o7n_blkMat (fun i => (A i : Matrix (Fin 2) (Fin 2) K)),
    k335o7n_blkMat (fun i => (((A i)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)),
    k335o7n_blkMat_inv A, k335o7n_blkMat_inv' A⟩
  map_one' := by
    apply Units.ext
    rw [Units.val_one, Units.val_mk]
    convert k335o7n_blkMat_one (K := K) using 2
  map_mul' A B := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mk]
    rw [show (fun i : Fin 3 => ((A * B) i : Matrix (Fin 2) (Fin 2) K)) =
        (fun i : Fin 3 => (A i : Matrix (Fin 2) (Fin 2) K) *
          (B i : Matrix (Fin 2) (Fin 2) K)) from by
      funext i
      rw [Pi.mul_apply, Units.val_mul]]
    rw [k335o7n_blkMat_mul]

private lemma k335o7n_blk_apply {K : Type} [Field K] (A : Fin 3 → GL (Fin 2) K) :
    ((k335o7n_blk A : GL k335o7n_σ K) : Matrix k335o7n_σ k335o7n_σ K) =
      k335o7n_blkMat (fun i => (A i : Matrix (Fin 2) (Fin 2) K)) := rfl

private lemma k335o7n_blkMat_mulVec_apply {K : Type} [Field K]
    (A : Fin 3 → GL (Fin 2) K) (v : k335o7n_σ → K) (k : Fin 2) (i : Fin 3) :
    (((k335o7n_blk A : GL k335o7n_σ K) : Matrix k335o7n_σ k335o7n_σ K) *ᵥ v) (.inl (k, i)) =
      (((A i : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
        (fun j => v (.inl (j, i)))) k := by
  rw [k335o7n_blk_apply]
  have h := congrFun (k335o7n_blkMat_mulVec (fun i => (A i : Matrix (Fin 2) (Fin 2) K)) v) (k, i)
  simpa using h

private lemma k335o7n_blkMat_mulVec_line {K : Type} [Field K]
    (A : Fin 3 → GL (Fin 2) K) (v : k335o7n_σ → K) :
    (((k335o7n_blk A : GL k335o7n_σ K) : Matrix k335o7n_σ k335o7n_σ K) *ᵥ v) (.inr ()) =
      v (.inr ()) := by
  rw [k335o7n_blk_apply, k335o7n_blkMat, Matrix.fromBlocks_mulVec]
  simp

private lemma k335o7n_pair_blk {K : Type} [Field K] (A : Fin 3 → GL (Fin 2) K)
    (v : k335o7n_σ → K) (i : Fin 3) :
    k335o7n_pair (((k335o7n_blk A : GL k335o7n_σ K) :
        Matrix k335o7n_σ k335o7n_σ K) *ᵥ v) i =
      ((A i : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ k335o7n_pair v i := by
  funext k
  exact k335o7n_blkMat_mulVec_apply A v k i

private lemma k335o7n_Qmodel_blk {K : Type} [Field K] (ν : K)
    (A : Fin 3 → GL (Fin 2) K)
    (hA : ∀ i : Fin 3, ∀ w : Fin 2 → K,
      k335o7n_N ν (((A i : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ w) = k335o7n_N ν w)
    (v : k335o7n_σ → K) :
    k335o7n_Qmodel ν (((k335o7n_blk A : GL k335o7n_σ K) :
        Matrix k335o7n_σ k335o7n_σ K) *ᵥ v) = k335o7n_Qmodel ν v := by
  rw [k335o7n_Qmodel, k335o7n_Qmodel]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [k335o7n_pair_blk]
    exact hA i (k335o7n_pair v i)
  · rw [k335o7n_blkMat_mulVec_line]

private def k335o7n_σPermHom : Equiv.Perm (Fin 3) →* Equiv.Perm k335o7n_σ where
  toFun τ := Equiv.sumCongr (Equiv.prodCongr (Equiv.refl (Fin 2)) τ) (Equiv.refl Unit)
  map_one' := by
    ext x
    rcases x with ⟨⟨j, i⟩⟩ | ⟨⟩ <;> simp
  map_mul' σ τ := by
    ext x
    rcases x with ⟨⟨j, i⟩⟩ | ⟨⟩ <;> simp

private def k335o7n_σPerm (τ : Equiv.Perm (Fin 3)) : Equiv.Perm k335o7n_σ :=
  k335o7n_σPermHom τ

@[simp] private lemma k335o7n_σPerm_inl (τ : Equiv.Perm (Fin 3)) (j : Fin 2) (i : Fin 3) :
    k335o7n_σPerm τ (.inl (j, i)) = .inl (j, τ i) := rfl

@[simp] private lemma k335o7n_σPerm_inr (τ : Equiv.Perm (Fin 3)) (u : Unit) :
    k335o7n_σPerm τ (.inr u) = .inr u := rfl

private noncomputable def k335o7n_permGLHom {K : Type} [Field K] :
    Equiv.Perm k335o7n_σ →* GL k335o7n_σ K :=
  (Matrix.permMatrixHom (n := k335o7n_σ) (R := K)).toHomUnits

private noncomputable abbrev k335o7n_permGL {K : Type} [Field K] (τ : Equiv.Perm k335o7n_σ) :
    GL k335o7n_σ K :=
  k335o7n_permGLHom τ

private lemma k335o7n_permGL_mulVec {K : Type} [Field K] (τ : Equiv.Perm k335o7n_σ)
    (v : k335o7n_σ → K) :
    ((k335o7n_permGL τ : GL k335o7n_σ K) : Matrix k335o7n_σ k335o7n_σ K) *ᵥ v =
      v ∘ ⇑(τ⁻¹) := by
  rw [show (k335o7n_permGL τ : GL k335o7n_σ K) =
      (Matrix.permMatrixHom (n := k335o7n_σ) (R := K)).toHomUnits τ from rfl]
  rw [MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, Matrix.permMatrix_mulVec]

private lemma k335o7n_permGL_inv {K : Type} [Field K] (τ : Equiv.Perm k335o7n_σ) :
    (k335o7n_permGL (K := K) τ)⁻¹ = k335o7n_permGL (K := K) τ⁻¹ :=
  (map_inv (k335o7n_permGLHom (K := K)) τ).symm

private lemma k335o7n_pair_permGL {K : Type} [Field K] (τ : Equiv.Perm (Fin 3)) (v : k335o7n_σ → K)
    (i : Fin 3) :
    k335o7n_pair (((k335o7n_permGL (k335o7n_σPerm τ) : GL k335o7n_σ K) :
        Matrix k335o7n_σ k335o7n_σ K) *ᵥ v) i = k335o7n_pair v (τ⁻¹ i) := by
  funext j
  rw [k335o7n_permGL_mulVec]
  simp only [Function.comp_apply, k335o7n_pair]
  rw [show (k335o7n_σPerm τ)⁻¹ = k335o7n_σPerm τ⁻¹ from (map_inv k335o7n_σPermHom τ).symm]
  simp

private lemma k335o7n_permGL_pair_line {K : Type} [Field K] (τ : Equiv.Perm (Fin 3))
    (v : k335o7n_σ → K) :
    (((k335o7n_permGL (k335o7n_σPerm τ) : GL k335o7n_σ K) :
        Matrix k335o7n_σ k335o7n_σ K) *ᵥ v) (.inr ()) = v (.inr ()) := by
  rw [k335o7n_permGL_mulVec,
    show (k335o7n_σPerm τ)⁻¹ = k335o7n_σPerm τ⁻¹ from (map_inv k335o7n_σPermHom τ).symm]
  rfl

private lemma k335o7n_pair_permGL_inv {K : Type} [Field K] (τ : Equiv.Perm (Fin 3))
    (v : k335o7n_σ → K) (i : Fin 3) :
    k335o7n_pair ((((k335o7n_permGL (k335o7n_σPerm τ))⁻¹ : GL k335o7n_σ K) :
        Matrix k335o7n_σ k335o7n_σ K) *ᵥ v) i = k335o7n_pair v (τ i) := by
  have h : (((k335o7n_permGL (k335o7n_σPerm τ))⁻¹ : GL k335o7n_σ K) :
      Matrix k335o7n_σ k335o7n_σ K) =
      ((k335o7n_permGL (k335o7n_σPerm τ⁻¹) : GL k335o7n_σ K) :
        Matrix k335o7n_σ k335o7n_σ K) := by
    rw [k335o7n_permGL_inv,
      show (k335o7n_σPerm τ)⁻¹ = k335o7n_σPerm τ⁻¹ from (map_inv k335o7n_σPermHom τ).symm]
  rw [h]
  simpa using k335o7n_pair_permGL τ⁻¹ v i

private lemma k335o7n_permGL_conj_blk_mulVec {K : Type} [Field K] (τ : Equiv.Perm (Fin 3))
    (A : Fin 3 → GL (Fin 2) K) (v : k335o7n_σ → K) :
    (((k335o7n_permGL (k335o7n_σPerm τ) * k335o7n_blk A *
        (k335o7n_permGL (k335o7n_σPerm τ))⁻¹ : GL k335o7n_σ K) :
        Matrix k335o7n_σ k335o7n_σ K) *ᵥ v) =
      (((k335o7n_blk (fun i => A (τ⁻¹ i)) : GL k335o7n_σ K) :
        Matrix k335o7n_σ k335o7n_σ K) *ᵥ v) := by
  have h1 : ((k335o7n_permGL (k335o7n_σPerm τ) * k335o7n_blk A *
      (k335o7n_permGL (k335o7n_σPerm τ))⁻¹ : GL k335o7n_σ K) :
      Matrix k335o7n_σ k335o7n_σ K) *ᵥ v =
      ((k335o7n_permGL (k335o7n_σPerm τ) : GL k335o7n_σ K) :
        Matrix k335o7n_σ k335o7n_σ K) *ᵥ
      (((k335o7n_blk A : GL k335o7n_σ K) : Matrix k335o7n_σ k335o7n_σ K) *ᵥ
        (((k335o7n_permGL (k335o7n_σPerm τ))⁻¹ : GL k335o7n_σ K) :
          Matrix k335o7n_σ k335o7n_σ K) *ᵥ v) := by
    simp only [Units.val_mul, Matrix.mulVec_mulVec, mul_assoc]
  rw [h1]
  funext x
  rcases x with ⟨⟨k, i⟩⟩ | ⟨⟩
  · show k335o7n_pair (((k335o7n_permGL (k335o7n_σPerm τ) : GL k335o7n_σ K) :
        Matrix k335o7n_σ k335o7n_σ K) *ᵥ
      (((k335o7n_blk A : GL k335o7n_σ K) : Matrix k335o7n_σ k335o7n_σ K) *ᵥ
        (((k335o7n_permGL (k335o7n_σPerm τ))⁻¹ : GL k335o7n_σ K) :
          Matrix k335o7n_σ k335o7n_σ K) *ᵥ v)) i k =
      k335o7n_pair (((k335o7n_blk (fun i => A (τ⁻¹ i)) : GL k335o7n_σ K) :
        Matrix k335o7n_σ k335o7n_σ K) *ᵥ v) i k
    rw [k335o7n_pair_permGL, k335o7n_pair_blk, k335o7n_pair_permGL_inv, k335o7n_pair_blk]
    simp
  · show (((k335o7n_permGL (k335o7n_σPerm τ) : GL k335o7n_σ K) :
        Matrix k335o7n_σ k335o7n_σ K) *ᵥ
      (((k335o7n_blk A : GL k335o7n_σ K) : Matrix k335o7n_σ k335o7n_σ K) *ᵥ
        (((k335o7n_permGL (k335o7n_σPerm τ))⁻¹ : GL k335o7n_σ K) :
          Matrix k335o7n_σ k335o7n_σ K) *ᵥ v)) (.inr ()) =
      (((k335o7n_blk (fun i => A (τ⁻¹ i)) : GL k335o7n_σ K) :
        Matrix k335o7n_σ k335o7n_σ K) *ᵥ v) (.inr ())
    rw [show ((k335o7n_permGL (k335o7n_σPerm τ))⁻¹ : GL k335o7n_σ K) =
        k335o7n_permGL (k335o7n_σPerm τ⁻¹) from by
      rw [k335o7n_permGL_inv,
        show (k335o7n_σPerm τ)⁻¹ = k335o7n_σPerm τ⁻¹ from (map_inv k335o7n_σPermHom τ).symm]]
    rw [k335o7n_permGL_pair_line τ, k335o7n_blkMat_mulVec_line,
      k335o7n_permGL_pair_line τ⁻¹, k335o7n_blkMat_mulVec_line]

private lemma k335o7n_permGL_conj_blk {K : Type} [Field K] (τ : Equiv.Perm (Fin 3))
    (A : Fin 3 → GL (Fin 2) K) :
    k335o7n_permGL (k335o7n_σPerm τ) * k335o7n_blk A *
      (k335o7n_permGL (k335o7n_σPerm τ))⁻¹ =
      k335o7n_blk (fun i => A (τ⁻¹ i)) := by
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro i
  exact k335o7n_permGL_conj_blk_mulVec τ A (Pi.single i 1)

private def k335o7n_τ01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1

private def k335o7n_τ12 : Equiv.Perm (Fin 3) := Equiv.swap 1 2

private def k335o7n_ρ : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

private lemma k335o7n_ρ_eq_comm : k335o7n_ρ = ⁅k335o7n_τ12, k335o7n_τ01⁆ := by
  ext i
  fin_cases i <;> decide

private lemma k335o7n_ρ_pow_three : k335o7n_ρ ^ 3 = 1 := by
  ext i
  fin_cases i <;> decide

private lemma k335o7n_pair_comp_σPerm_inv {K : Type} [Field K] (τ : Equiv.Perm (Fin 3))
    (v : k335o7n_σ → K) (i : Fin 3) :
    k335o7n_pair (v ∘ ⇑(k335o7n_σPerm τ)⁻¹) i = k335o7n_pair v (τ⁻¹ i) := by
  funext j
  simp only [k335o7n_pair, Function.comp_apply]
  rw [show (k335o7n_σPerm τ)⁻¹ = k335o7n_σPerm τ⁻¹ from (map_inv k335o7n_σPermHom τ).symm]
  simp

private lemma k335o7n_Qmodel_perm {K : Type} [Field K] (ν : K) (τ : Equiv.Perm (Fin 3))
    (v : k335o7n_σ → K) :
    k335o7n_Qmodel ν (v ∘ ⇑(k335o7n_σPerm τ)⁻¹) = k335o7n_Qmodel ν v := by
  have hsum : (∑ i : Fin 3, k335o7n_N ν (k335o7n_pair (v ∘ ⇑(k335o7n_σPerm τ)⁻¹) i)) =
      ∑ i : Fin 3, k335o7n_N ν (k335o7n_pair v i) := by
    refine Fintype.sum_equiv (τ⁻¹) (fun i => k335o7n_N ν
      (k335o7n_pair (v ∘ ⇑(k335o7n_σPerm τ)⁻¹) i)) (fun i => k335o7n_N ν (k335o7n_pair v i))
      (fun i => by
        rw [k335o7n_pair_comp_σPerm_inv])
  rw [k335o7n_Qmodel, k335o7n_Qmodel, hsum]
  congr 1

private lemma k335o7n_permGL_mem_isometryCore {K : Type} [Field K] (ν : K)
    (τ : Equiv.Perm (Fin 3)) :
    k335o7n_permGL (k335o7n_σPerm τ) ∈ CFSG.MatrixModel.isometryCore (k335o7n_Qmodel ν) :=
  Subgroup.subset_closure fun v => by
    rw [k335o7n_permGL_mulVec]
    exact k335o7n_Qmodel_perm ν τ v

private lemma k335o7n_blk_mem_isometryCore {K : Type} [Field K] (ν : K)
    (A : Fin 3 → GL (Fin 2) K)
    (hA : ∀ i : Fin 3, ∀ w : Fin 2 → K,
      k335o7n_N ν (((A i : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ w) = k335o7n_N ν w) :
    k335o7n_blk A ∈ CFSG.MatrixModel.isometryCore (k335o7n_Qmodel ν) :=
  Subgroup.subset_closure fun v => k335o7n_Qmodel_blk ν A hA v

private lemma k335o7n_blk_mem_statedOmega {K : Type} [Field K] (ν : K)
    (A B : Fin 3 → GL (Fin 2) K) (F : GL (Fin 2) K)
    (hA : ∀ i : Fin 3, (B i)⁻¹ * (B i)⁻¹ = A i)
    (hF : ∀ i : Fin 3, F * B i * F⁻¹ = (B i)⁻¹)
    (hB : ∀ i : Fin 3, ∀ w : Fin 2 → K,
      k335o7n_N ν (((B i : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ w) = k335o7n_N ν w)
    (hFiso : ∀ w : Fin 2 → K,
      k335o7n_N ν (((F : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ w) = k335o7n_N ν w) :
    k335o7n_blk A ∈ CFSG.Open.StatedOmega (k335o7n_Qmodel ν) := by
  have hcomm : k335o7n_blk A =
      ⁅k335o7n_blk (fun _ : Fin 3 => F), k335o7n_blk B⁆ := by
    rw [← map_commutatorElement]
    congr 1
    funext i
    simp only [commutatorElement_def, Pi.mul_apply, Pi.inv_apply]
    rw [hF i, hA i]
  rw [hcomm]
  exact Subgroup.commutator_mem_commutator
    (k335o7n_blk_mem_isometryCore ν _ fun _ => hFiso)
    (k335o7n_blk_mem_isometryCore ν _ hB)

private theorem k335o7n_isometry_of_mem_statedOmega {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {f : (ι → K) → K} {g : GL ι K} (hg : g ∈ CFSG.Open.StatedOmega f)
    (v : ι → K) : f ((g : Matrix ι ι K) *ᵥ v) = f v := by
  let I : Subgroup (GL ι K) :=
    { carrier := {A | ∀ v, f ((A : Matrix ι ι K) *ᵥ v) = f v}
      one_mem' := fun v => by simp
      mul_mem' := fun {a b} ha hb v => by
        simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
        rw [ha, hb]
      inv_mem' := fun {a} ha v => by
        have := ha (((a⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v)
        simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using this.symm }
  have hcl : Subgroup.closure {A : GL ι K | ∀ v, f ((A : Matrix ι ι K) *ᵥ v) = f v} ≤ I :=
    (Subgroup.closure_le I).mpr fun A hA => hA
  have hg' : g ∈ Subgroup.closure {A : GL ι K | ∀ v, f ((A : Matrix ι ι K) *ᵥ v) = f v} :=
    Subgroup.commutator_le_self _ hg
  exact hcl hg' v

private def k335o7n_Qstd {K : Type} [Field K] (v : k335o7n_σ → K) : K :=
  (∑ i : Fin 3, k335o7n_pair v i 0 * k335o7n_pair v i 1) + v (.inr ()) ^ 2

private def k335o7n_G {K : Type} [Field K] (ν a b p r : K) :
    Matrix k335o7n_σ k335o7n_σ K :=
  fun x y =>
    match x, y with
    | .inl (0, 0), .inl (0, 0) => 1
    | .inl (0, 0), .inl (1, 0) => a
    | .inl (0, 0), .inl (0, 2) => p * b
    | .inl (0, 0), .inl (1, 2) => r * b
    | .inl (1, 0), .inl (0, 0) => 1
    | .inl (1, 0), .inl (1, 0) => -a
    | .inl (1, 0), .inl (0, 2) => -(p * b)
    | .inl (1, 0), .inl (1, 2) => -(r * b)
    | .inl (0, 1), .inl (0, 1) => 1
    | .inl (0, 1), .inl (0, 2) => r
    | .inl (0, 1), .inl (1, 2) => ν * p
    | .inl (1, 1), .inl (0, 1) => 1
    | .inl (1, 1), .inl (0, 2) => -r
    | .inl (1, 1), .inl (1, 2) => -(ν * p)
    | .inl (0, 2), .inl (1, 1) => 1
    | .inl (0, 2), .inr () => 1
    | .inl (1, 2), .inl (1, 1) => -ν
    | .inl (1, 2), .inr () => ν
    | .inr (), .inl (1, 0) => b
    | .inr (), .inl (0, 2) => p * a
    | .inr (), .inl (1, 2) => r * a
    | _, _ => 0

private lemma k335o7n_G_isometry {K : Type} [Field K] (ν a b p r : K)
    (hab : a ^ 2 - b ^ 2 = ν) (hp : ν * p ^ 2 - r ^ 2 = 1) (v : k335o7n_σ → K) :
    k335o7n_Qstd (k335o7n_G ν a b p r *ᵥ v) = k335o7n_Qmodel ν v := by
  simp only [k335o7n_Qstd, k335o7n_Qmodel, k335o7n_N, k335o7n_pair, Matrix.mulVec,
    dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_succ,
    Fin.succ_zero_eq_one,
    Finset.sum_add_distrib, Finset.univ_unique, Finset.sum_singleton]
  simp only [k335o7n_G, Fin.default_eq_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  linear_combination
    (-(v (.inl (1, 0)) ^ 2) + p ^ 2 * v (.inl (0, 2)) ^ 2 + r ^ 2 * v (.inl (1, 2)) ^ 2 +
      2 * p * r * v (.inl (0, 2)) * v (.inl (1, 2))) * hab +
    (v (.inl (0, 2)) ^ 2 - ν * v (.inl (1, 2)) ^ 2) * hp

private lemma k335o7n_G_mulVec_apply_00 {K : Type} [Field K] (ν a b p r : K)
    (v : k335o7n_σ → K) :
    (k335o7n_G ν a b p r *ᵥ v) (.inl (0, 0)) =
      v (.inl (0, 0)) + a * v (.inl (1, 0)) + p * b * v (.inl (0, 2)) +
        r * b * v (.inl (1, 2)) := by
  rw [Matrix.mulVec, dotProduct]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
    Finset.univ_unique, Finset.sum_singleton]
  simp only [k335o7n_G]
  ring_nf

private lemma k335o7n_G_mulVec_apply_10 {K : Type} [Field K] (ν a b p r : K)
    (v : k335o7n_σ → K) :
    (k335o7n_G ν a b p r *ᵥ v) (.inl (1, 0)) =
      v (.inl (0, 0)) - a * v (.inl (1, 0)) - p * b * v (.inl (0, 2)) -
        r * b * v (.inl (1, 2)) := by
  rw [Matrix.mulVec, dotProduct]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
    Finset.univ_unique, Finset.sum_singleton]
  simp only [k335o7n_G]
  ring_nf

private lemma k335o7n_G_mulVec_apply_01 {K : Type} [Field K] (ν a b p r : K)
    (v : k335o7n_σ → K) :
    (k335o7n_G ν a b p r *ᵥ v) (.inl (0, 1)) =
      v (.inl (0, 1)) + r * v (.inl (0, 2)) + ν * p * v (.inl (1, 2)) := by
  rw [Matrix.mulVec, dotProduct]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
    Finset.univ_unique, Finset.sum_singleton]
  simp only [k335o7n_G]
  ring_nf

private lemma k335o7n_G_mulVec_apply_11 {K : Type} [Field K] (ν a b p r : K)
    (v : k335o7n_σ → K) :
    (k335o7n_G ν a b p r *ᵥ v) (.inl (1, 1)) =
      v (.inl (0, 1)) - r * v (.inl (0, 2)) - ν * p * v (.inl (1, 2)) := by
  rw [Matrix.mulVec, dotProduct]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
    Finset.univ_unique, Finset.sum_singleton]
  simp only [k335o7n_G]
  ring_nf

private lemma k335o7n_G_mulVec_apply_02 {K : Type} [Field K] (ν a b p r : K)
    (v : k335o7n_σ → K) :
    (k335o7n_G ν a b p r *ᵥ v) (.inl (0, 2)) =
      v (.inl (1, 1)) + v (.inr ()) := by
  rw [Matrix.mulVec, dotProduct]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
    Finset.univ_unique, Finset.sum_singleton]
  simp only [k335o7n_G]
  ring_nf

private lemma k335o7n_G_mulVec_apply_12 {K : Type} [Field K] (ν a b p r : K)
    (v : k335o7n_σ → K) :
    (k335o7n_G ν a b p r *ᵥ v) (.inl (1, 2)) =
      -ν * v (.inl (1, 1)) + ν * v (.inr ()) := by
  rw [Matrix.mulVec, dotProduct]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
    Finset.univ_unique, Finset.sum_singleton]
  simp only [k335o7n_G]
  ring_nf

private lemma k335o7n_G_mulVec_apply_inr {K : Type} [Field K] (ν a b p r : K)
    (v : k335o7n_σ → K) :
    (k335o7n_G ν a b p r *ᵥ v) (.inr ()) =
      b * v (.inl (1, 0)) + p * a * v (.inl (0, 2)) + r * a * v (.inl (1, 2)) := by
  rw [Matrix.mulVec, dotProduct]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
    Finset.univ_unique, Finset.sum_singleton]
  simp only [k335o7n_G]
  ring_nf

private lemma k335o7n_G_mulVec_eq_zero {K : Type} [Field K] (ν a b p r : K) (h2 : (2 : K) ≠ 0)
    (hν : ν ≠ 0) (hab : a ^ 2 - b ^ 2 = ν) (hp : ν * p ^ 2 - r ^ 2 = 1)
    (v : k335o7n_σ → K) (hv : k335o7n_G ν a b p r *ᵥ v = 0) : v = 0 := by
  have e0 := congrFun hv (.inl (0, 0))
  have e1 := congrFun hv (.inl (1, 0))
  have e2 := congrFun hv (.inl (0, 1))
  have e3 := congrFun hv (.inl (1, 1))
  have e4 := congrFun hv (.inl (0, 2))
  have e5 := congrFun hv (.inl (1, 2))
  have e6 := congrFun hv (.inr ())
  have key : ∀ x : k335o7n_σ, (k335o7n_G ν a b p r *ᵥ v) x = 0 := fun x => congrFun hv x
  rw [k335o7n_G_mulVec_apply_00] at e0
  rw [k335o7n_G_mulVec_apply_10] at e1
  rw [k335o7n_G_mulVec_apply_01] at e2
  rw [k335o7n_G_mulVec_apply_11] at e3
  rw [k335o7n_G_mulVec_apply_02] at e4
  rw [k335o7n_G_mulVec_apply_12] at e5
  rw [k335o7n_G_mulVec_apply_inr] at e6
  simp only [Pi.zero_apply] at e0 e1 e2 e3 e4 e5 e6
  have h0 : v (.inl (0, 0)) = 0 := by
    have h : 2 * v (.inl (0, 0)) = 0 := by linear_combination (norm := ring_nf) e0 + e1
    exact (mul_eq_zero.mp h).resolve_left h2
  have h1 : v (.inl (0, 1)) = 0 := by
    have h : 2 * v (.inl (0, 1)) = 0 := by linear_combination (norm := ring_nf) e2 + e3
    exact (mul_eq_zero.mp h).resolve_left h2
  have hz : v (.inr ()) = 0 := by
    have h : 2 * ν * v (.inr ()) = 0 := by
      linear_combination (norm := ring_nf) e5 + ν * e4
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero h2 hν)
  have ht1 : v (.inl (1, 1)) = 0 := by
    have h : v (.inl (1, 1)) + v (.inr ()) = 0 := e4
    rw [hz, add_zero] at h
    exact h
  have hA : a * v (.inl (1, 0)) + p * b * v (.inl (0, 2)) + r * b * v (.inl (1, 2)) = 0 := by
    have h : 2 * (a * v (.inl (1, 0)) + p * b * v (.inl (0, 2)) + r * b * v (.inl (1, 2))) = 0 := by
      linear_combination (norm := ring_nf) e0 - e1
    exact (mul_eq_zero.mp h).resolve_left h2
  have hC : r * v (.inl (0, 2)) + ν * p * v (.inl (1, 2)) = 0 := by
    have h : 2 * (r * v (.inl (0, 2)) + ν * p * v (.inl (1, 2))) = 0 := by
      linear_combination (norm := ring_nf) e2 - e3
    exact (mul_eq_zero.mp h).resolve_left h2
  have hG : b * v (.inl (1, 0)) + p * a * v (.inl (0, 2)) + r * a * v (.inl (1, 2)) = 0 := by
    linear_combination (norm := ring_nf) e6
  have hD : p * v (.inl (0, 2)) + r * v (.inl (1, 2)) = 0 := by
    have h : ν * (p * v (.inl (0, 2)) + r * v (.inl (1, 2))) = 0 := by
      linear_combination (norm := ring_nf) a * hG - b * hA -
        (p * v (.inl (0, 2)) + r * v (.inl (1, 2))) * hab
    exact (mul_eq_zero.mp h).resolve_left hν
  have hs2 : v (.inl (0, 2)) = 0 := by
    linear_combination (norm := ring_nf) (ν * p) * hD - r * hC - v (.inl (0, 2)) * hp
  have ht2 : v (.inl (1, 2)) = 0 := by
    linear_combination (norm := ring_nf) p * hC - r * hD - v (.inl (1, 2)) * hp
  have ht0 : v (.inl (1, 0)) = 0 := by
    by_cases ha : a = 0
    · by_cases hb : b = 0
      · exact absurd (by rw [ha, hb] at hab; exact hab.symm.trans (by ring) : ν = 0) hν
      · have h : b * v (.inl (1, 0)) = 0 := by
          rw [ht2, hs2, mul_zero, mul_zero, add_zero, add_zero] at hG
          exact hG
        exact (mul_eq_zero.mp h).resolve_left hb
    · have h : a * v (.inl (1, 0)) = 0 := by
        rw [ht2, hs2, mul_zero, mul_zero, add_zero, add_zero] at hA
        exact hA
      exact (mul_eq_zero.mp h).resolve_left ha
  funext x
  rcases x with ⟨⟨j, i⟩⟩ | ⟨⟩
  · fin_cases j <;> fin_cases i <;> simp_all
  · simpa using hz

private noncomputable def k335o7n_g {K : Type} [Field K] (ν a b p r : K) (h2 : (2 : K) ≠ 0)
    (hν : ν ≠ 0) (hab : a ^ 2 - b ^ 2 = ν) (hp : ν * p ^ 2 - r ^ 2 = 1) :
    GL k335o7n_σ K :=
  (Matrix.mulVec_injective_iff_isUnit.mp fun v w hvw => by
    have hz : k335o7n_G ν a b p r *ᵥ (v - w) = 0 := by
      rw [Matrix.mulVec_sub, hvw, sub_self]
    have := k335o7n_G_mulVec_eq_zero ν a b p r h2 hν hab hp (v - w) hz
    exact sub_eq_zero.mp this).unit

private lemma k335o7n_g_coe {K : Type} [Field K] (ν a b p r : K) (h2 : (2 : K) ≠ 0)
    (hν : ν ≠ 0) (hab : a ^ 2 - b ^ 2 = ν) (hp : ν * p ^ 2 - r ^ 2 = 1) :
    ((k335o7n_g ν a b p r h2 hν hab hp : GL k335o7n_σ K) :
        Matrix k335o7n_σ k335o7n_σ K) = k335o7n_G ν a b p r :=
  IsUnit.unit_spec _

private lemma k335o7n_g_isometry {K : Type} [Field K] (ν a b p r : K) (h2 : (2 : K) ≠ 0)
    (hν : ν ≠ 0) (hab : a ^ 2 - b ^ 2 = ν) (hp : ν * p ^ 2 - r ^ 2 = 1)
    (v : k335o7n_σ → K) :
    k335o7n_Qstd (((k335o7n_g ν a b p r h2 hν hab hp : GL k335o7n_σ K) :
        Matrix k335o7n_σ k335o7n_σ K) *ᵥ v) = k335o7n_Qmodel ν v := by
  rw [k335o7n_g_coe]
  exact k335o7n_G_isometry ν a b p r hab hp v

private theorem k335o7n_map_statedOmega_conj {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {Q Q' : (ι → K) → K} (g : GL ι K)
    (hg : ∀ v, Q' ((g : Matrix ι ι K) *ᵥ v) = Q v) :
    (CFSG.Open.StatedOmega Q).map (MulAut.conj g).toMonoidHom = CFSG.Open.StatedOmega Q' := by
  have hgi : ∀ w, (g : Matrix ι ι K) *ᵥ (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hgi' : ∀ v, ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ ((g : Matrix ι ι K) *ᵥ v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hiff : ∀ A : GL ι K,
      (∀ w, Q' ((((MulAut.conj g) A : GL ι K) : Matrix ι ι K) *ᵥ w) = Q' w) ↔
      ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v := by
    intro A
    have hc : ∀ w, ((((MulAut.conj g) A : GL ι K) : Matrix ι ι K) *ᵥ w) =
        (g : Matrix ι ι K) *ᵥ ((A : Matrix ι ι K) *ᵥ
          (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w)) := by
      intro w
      simp only [MulAut.conj_apply, Units.val_mul, ← Matrix.mulVec_mulVec]
    constructor
    · intro h v
      have h' := h ((g : Matrix ι ι K) *ᵥ v)
      rw [hc, hgi', hg, hg] at h'
      exact h'
    · intro h w
      rw [hc, hg, h]
      conv_rhs => rw [← hgi w]
      rw [hg]
  rw [CFSG.Open.StatedOmega, CFSG.Open.StatedOmega, Subgroup.map_commutator,
    MonoidHom.map_closure]
  have hset : (MulAut.conj g).toMonoidHom ''
      {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} =
      {B : GL ι K | ∀ w, Q' ((B : Matrix ι ι K) *ᵥ w) = Q' w} := by
    ext B
    constructor
    · rintro ⟨A, hA, rfl⟩
      exact (hiff A).2 hA
    · intro hB
      refine ⟨(MulAut.conj g).symm B, ?_, (MulAut.conj g).apply_symm_apply B⟩
      exact (hiff ((MulAut.conj g).symm B)).1 (by rw [MulEquiv.apply_symm_apply]; exact hB)
  rw [hset]

private def k335o7n_eFun : k335o7n_σ → (Fin 3 ⊕ Fin 3 ⊕ Unit)
  | .inl (0, i) => .inl i
  | .inl (1, i) => .inr (.inl i)
  | .inr () => .inr (.inr ())

private def k335o7n_eInvFun : (Fin 3 ⊕ Fin 3 ⊕ Unit) → k335o7n_σ
  | .inl i => .inl (0, i)
  | .inr (.inl i) => .inl (1, i)
  | .inr (.inr ()) => .inr ()

private def k335o7n_e : k335o7n_σ ≃ (Fin 3 ⊕ Fin 3 ⊕ Unit) where
  toFun := k335o7n_eFun
  invFun := k335o7n_eInvFun
  left_inv x := by
    rcases x with ⟨j, i⟩ | ⟨⟩
    · fin_cases j <;> rfl
    · rfl
  right_inv x := by
    rcases x with i | i | ⟨⟩ <;> rfl

private lemma k335o7n_StatedQuadOdd_e {K : Type} [Field K] (v : k335o7n_σ → K) :
    CFSG.Open.StatedQuadOdd 3 K (fun i => v (k335o7n_e.symm i)) = k335o7n_Qstd v := by
  simp only [CFSG.Open.StatedQuadOdd, k335o7n_Qstd, k335o7n_pair, k335o7n_e,
    Equiv.symm_mk, Equiv.coe_fn_mk]
  rfl

private lemma k335o7n_blk_injective {K : Type} [Field K] :
    Function.Injective (k335o7n_blk : (Fin 3 → GL (Fin 2) K) → GL k335o7n_σ K) := by
  intro A B hAB
  funext i
  apply Units.ext
  funext k l
  have h : (k335o7n_blk A : Matrix k335o7n_σ k335o7n_σ K) (.inl (k, i)) (.inl (l, i)) =
      (k335o7n_blk B : Matrix k335o7n_σ k335o7n_σ K) (.inl (k, i)) (.inl (l, i)) := by
    rw [congrArg Units.val hAB]
  simp only [k335o7n_blk_apply, k335o7n_blkMat, Matrix.fromBlocks_apply₁₁,
    Matrix.blockDiagonal_apply] at h
  simpa using h

private noncomputable def k335o7n_Phi {K : Type} [Field K] :
    GL k335o7n_σ K ≃* GL (Fin 3 ⊕ Fin 3 ⊕ Unit) K :=
  Units.mapEquiv (Matrix.reindexAlgEquiv K K k335o7n_e).toRingEquiv.toMulEquiv

private lemma k335o7n_Phi_apply {K : Type} [Field K] (A : GL k335o7n_σ K) :
    ((k335o7n_Phi A : GL (Fin 3 ⊕ Fin 3 ⊕ Unit) K) :
        Matrix (Fin 3 ⊕ Fin 3 ⊕ Unit) (Fin 3 ⊕ Fin 3 ⊕ Unit) K) =
      Matrix.reindex k335o7n_e k335o7n_e (A : Matrix k335o7n_σ k335o7n_σ K) := rfl

private lemma k335o7n_Phi_mulVec {K : Type} [Field K] (A : GL k335o7n_σ K)
    (v : (Fin 3 ⊕ Fin 3 ⊕ Unit) → K) :
    ((k335o7n_Phi A : GL (Fin 3 ⊕ Fin 3 ⊕ Unit) K) :
        Matrix (Fin 3 ⊕ Fin 3 ⊕ Unit) (Fin 3 ⊕ Fin 3 ⊕ Unit) K) *ᵥ v =
      fun i => ((A : Matrix k335o7n_σ k335o7n_σ K) *ᵥ
        (fun j => v (k335o7n_e j))) (k335o7n_e.symm i) := by
  rw [k335o7n_Phi_apply, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  rfl

private lemma k335o7n_Phi_mem_iff {K : Type} [Field K] (A : GL k335o7n_σ K) :
    k335o7n_Phi A ∈ {B : GL (Fin 3 ⊕ Fin 3 ⊕ Unit) K |
        ∀ v, CFSG.Open.StatedQuadOdd 3 K ((B : Matrix _ _ K) *ᵥ v) =
          CFSG.Open.StatedQuadOdd 3 K v} ↔
      A ∈ {B : GL k335o7n_σ K | ∀ v, k335o7n_Qstd ((B : Matrix _ _ K) *ᵥ v) =
        k335o7n_Qstd v} := by
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h v
    have := h (fun i => v (k335o7n_e.symm i))
    rw [k335o7n_Phi_mulVec, k335o7n_StatedQuadOdd_e, k335o7n_StatedQuadOdd_e] at this
    simpa using this
  · intro h v
    rw [k335o7n_Phi_mulVec, k335o7n_StatedQuadOdd_e,
      show CFSG.Open.StatedQuadOdd 3 K v = k335o7n_Qstd (fun j => v (k335o7n_e j)) from by
        simpa using k335o7n_StatedQuadOdd_e (K := K) (fun j => v (k335o7n_e j))]
    exact h (fun j => v (k335o7n_e j))

private lemma k335o7n_Phi_isoSet {K : Type} [Field K] :
    {B : GL (Fin 3 ⊕ Fin 3 ⊕ Unit) K |
        ∀ v, CFSG.Open.StatedQuadOdd 3 K ((B : Matrix _ _ K) *ᵥ v) =
          CFSG.Open.StatedQuadOdd 3 K v} =
      k335o7n_Phi '' {A : GL k335o7n_σ K | ∀ v, k335o7n_Qstd ((A : Matrix _ _ K) *ᵥ v) =
        k335o7n_Qstd v} := by
  ext B
  constructor
  · intro hB
    refine ⟨k335o7n_Phi.symm B, (k335o7n_Phi_mem_iff _).1 ?_, by simp⟩
    simpa using hB
  · rintro ⟨A, hA, rfl⟩
    exact (k335o7n_Phi_mem_iff A).2 hA

private lemma k335o7n_Phi_statedOmega {K : Type} [Field K] :
    (CFSG.Open.StatedOmega (k335o7n_Qstd (K := K))).map k335o7n_Phi.toMonoidHom =
      CFSG.Open.StatedOmega (CFSG.Open.StatedQuadOdd 3 K) := by
  rw [CFSG.Open.StatedOmega, CFSG.Open.StatedOmega, Subgroup.map_commutator,
    MonoidHom.map_closure]
  rw [show ((k335o7n_Phi.toMonoidHom : GL k335o7n_σ K →*
      GL (Fin 3 ⊕ Fin 3 ⊕ Unit) K) : GL k335o7n_σ K → GL (Fin 3 ⊕ Fin 3 ⊕ Unit) K) =
    ⇑k335o7n_Phi from rfl, k335o7n_Phi_isoSet (K := K)]

private theorem k335o7n_scalar_sq {K : Type} [Field K] {c : Kˣ}
    (hc : Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3 ⊕ Unit) c ∈
      CFSG.Open.StatedOmega (CFSG.Open.StatedQuadOdd 3 K)) : c ^ 2 = 1 := by
  have hiso := k335o7n_isometry_of_mem_statedOmega hc
  let v : Fin 3 ⊕ Fin 3 ⊕ Unit → K := Pi.single (.inr (.inr ())) 1
  have hmul : ((Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3 ⊕ Unit) c :
      Matrix (Fin 3 ⊕ Fin 3 ⊕ Unit) (Fin 3 ⊕ Fin 3 ⊕ Unit) K) *ᵥ v) =
      fun j => (c : K) * v j := by
    ext j
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have h := hiso v
  rw [hmul] at h
  have hL : CFSG.Open.StatedQuadOdd 3 K (fun j => (c : K) * v j) = (c : K) ^ 2 := by
    simp only [CFSG.Open.StatedQuadOdd]
    rw [Finset.sum_eq_zero (fun i _ => by simp [v])]
    simp [v]
  have hR : CFSG.Open.StatedQuadOdd 3 K v = 1 := by
    simp only [CFSG.Open.StatedQuadOdd]
    rw [Finset.sum_eq_zero (fun i _ => by simp [v])]
    simp [v]
  rw [hL, hR] at h
  exact Units.ext h

private theorem k335o7n_exists_sq_sub_eq_neg_one {F : Type} [Field F] [Finite F]
    (hF2 : ringChar F ≠ 2) (l : F) (hl : l ≠ 0) :
    ∃ a b : F, a ^ 2 - l * b ^ 2 = -1 := by
  have : Fintype F := Fintype.ofFinite F
  have hdeg : (Polynomial.X ^ 2 : Polynomial F).degree = 2 := by
    rw [Polynomial.degree_X_pow]; rfl
  have hdeg2 :
      (Polynomial.C (-l) * Polynomial.X ^ 2 + Polynomial.C 1 : Polynomial F).degree = 2 := by
    rw [Polynomial.degree_add_C (by
      rw [Polynomial.degree_C_mul_X_pow 2 (neg_ne_zero.2 hl)]; norm_num)]
    rw [Polynomial.degree_C_mul_X_pow 2 (neg_ne_zero.2 hl)]
    rfl
  obtain ⟨a, b, h⟩ := FiniteField.exists_root_sum_quadratic
    (f := (Polynomial.X ^ 2 : Polynomial F))
    (g := (Polynomial.C (-l) * Polynomial.X ^ 2 + Polynomial.C 1)) hdeg hdeg2
    (FiniteField.odd_card_of_char_ne_two hF2)
  refine ⟨a, b, ?_⟩
  simp at h
  linear_combination h

theorem k335_coord_omega7_nonsplit {X : Type} [Group X] {p f : ℕ}
    (h : LieModel X .POmegaOdd 3 p f) (hq : p ^ f % 3 = 2) :
    K335Coord X (((p ^ f) ^ 2 - 1).factorization 3) := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨eX⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num)
  let : Field K := hfield
  let : Finite K := hfinite
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 : p ≠ 2 := hadm.2.2.2
  have : Fact p.Prime := ⟨hadm.1⟩
  have : CharP K p := charP_of_card_eq_prime_pow (p := p) (f := f) (by
    rw [← Nat.card_eq_fintype_card]; exact hK)
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have hp_dvd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp h0
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp_dvd
    have hge : 2 ≤ p := hadm.1.two_le
    exact hp2 (by omega)
  have hchar : ringChar K ≠ 2 := by
    intro hc
    have : CharP K 2 := ringChar.of_eq hc
    exact h2 (CharP.cast_eq_zero K 2)
  have hcard : Nat.card K % 3 = 2 := by rw [hK]; exact hq
  obtain ⟨ν, C, F, hν, hCcomm, hCcard, hFinv, hCiso, hFiso⟩ := k335o7n_torus h2 hcard
  have hν0 : ν ≠ 0 := fun h0 => hν (h0 ▸ ⟨0, by ring⟩)
  obtain ⟨r', p', hp'⟩ := k335o7n_exists_sq_sub_eq_neg_one hchar ν hν0
  have hp : ν * p' ^ 2 - r' ^ 2 = 1 := by linear_combination -hp'
  let a : ℕ := (Nat.card K ^ 2 - 1).factorization 3
  let CG : CommGroup ↥C := { (inferInstance : Group ↥C) with
    mul_comm := fun x y => Subtype.ext (hCcomm x x.2 y y.2) }
  have hCpow : ∀ c : ↥C, c ^ (3 ^ a) = 1 := by
    intro c
    rw [show (3 : ℕ) ^ a = Nat.card ↥C from hCcard.symm]
    exact pow_card_eq_one'
  have hOdd : Odd (3 ^ a) := (by decide : Odd 3).pow
  let k : ℕ := (3 ^ a + 1) / 2
  have h2k : 2 * k = 3 ^ a + 1 := by
    obtain ⟨m, hm⟩ := hOdd
    simp only [k]
    omega
  have hy2 : ∀ x : Fin 3 → ↥C, ∀ i, x i ^ k * x i ^ k = x i := by
    intro x i
    rw [← pow_add, ← two_mul, h2k, pow_succ, hCpow, one_mul]
  let φ'hom : (Fin 3 → ↥C) →* (Fin 3 → GL (Fin 2) K) :=
    { toFun := fun x i => (x i : GL (Fin 2) K)
      map_one' := rfl
      map_mul' := fun x y => by funext i; rfl }
  have hφ'mem : ∀ x, k335o7n_blk (φ'hom x) ∈ CFSG.Open.StatedOmega (k335o7n_Qmodel ν) := by
    intro x
    refine k335o7n_blk_mem_statedOmega ν (φ'hom x)
      (fun i => (((x i ^ k)⁻¹ : ↥C) : GL (Fin 2) K)) F ?_ ?_ ?_ hFiso
    · intro i
      show ((((x i ^ k)⁻¹ : ↥C) : GL (Fin 2) K))⁻¹ *
          ((((x i ^ k)⁻¹ : ↥C) : GL (Fin 2) K))⁻¹ = ((x i : ↥C) : GL (Fin 2) K)
      rw [Subgroup.coe_inv, inv_inv, ← Subgroup.coe_mul, hy2]
    · intro i
      exact hFinv ((x i ^ k)⁻¹) (inv_mem (pow_mem (x i).2 k))
    · intro i w
      exact hCiso ((x i ^ k)⁻¹) (inv_mem (pow_mem (x i).2 k)) w
  let φ : (Fin 3 → ↥C) →* ↥(CFSG.Open.StatedOmega (k335o7n_Qmodel ν)) :=
    (k335o7n_blk.comp φ'hom).codRestrict _ hφ'mem
  have hφinj : Function.Injective φ := by
    intro x y hxy
    funext i
    apply Subtype.ext
    have h1 : (k335o7n_blk (φ'hom x) : GL k335o7n_σ K) = k335o7n_blk (φ'hom y) := by
      have := congrArg (fun z : ↥(CFSG.Open.StatedOmega (k335o7n_Qmodel ν)) =>
        (z : GL k335o7n_σ K)) hxy
      simpa [φ] using this
    exact congrFun (k335o7n_blk_injective h1) i
  have hs_mem : k335o7n_permGL (k335o7n_σPerm k335o7n_ρ) ∈
      CFSG.Open.StatedOmega (k335o7n_Qmodel ν) := by
    have hcomm : k335o7n_permGL (K := K) (k335o7n_σPerm k335o7n_ρ) =
        ⁅k335o7n_permGL (K := K) (k335o7n_σPerm k335o7n_τ12),
          k335o7n_permGL (K := K) (k335o7n_σPerm k335o7n_τ01)⁆ := by
      change k335o7n_permGLHom (K := K) (k335o7n_σPermHom k335o7n_ρ) =
        ⁅k335o7n_permGLHom (K := K) (k335o7n_σPermHom k335o7n_τ12),
          k335o7n_permGLHom (K := K) (k335o7n_σPermHom k335o7n_τ01)⁆
      rw [k335o7n_ρ_eq_comm, map_commutatorElement k335o7n_σPermHom,
        map_commutatorElement (k335o7n_permGLHom (K := K))]
    rw [hcomm]
    exact Subgroup.commutator_mem_commutator
      (k335o7n_permGL_mem_isometryCore ν k335o7n_τ12)
      (k335o7n_permGL_mem_isometryCore ν k335o7n_τ01)
  let s : ↥(CFSG.Open.StatedOmega (k335o7n_Qmodel ν)) :=
    ⟨k335o7n_permGL (k335o7n_σPerm k335o7n_ρ), hs_mem⟩
  have hs3 : s ^ 3 = 1 := by
    apply Subtype.ext
    change (k335o7n_permGLHom (K := K) (k335o7n_σPermHom k335o7n_ρ)) ^ 3 = 1
    rw [← map_pow, ← map_pow, k335o7n_ρ_pow_three, map_one, map_one]
  have hρinv : ∀ i : Fin 3, k335o7n_ρ⁻¹ i = i - 1 := by
    intro i
    have hρ : k335o7n_ρ⁻¹ = Equiv.swap 1 2 * Equiv.swap 0 1 := by
      ext j
      fin_cases j <;> decide
    rw [hρ]
    fin_cases i <;> rfl
  have hs : ∀ x : Fin 3 → ↥C, s * φ x * s⁻¹ = φ (fun i => x (i - 1)) := by
    intro x
    apply Subtype.ext
    show k335o7n_permGL (k335o7n_σPerm k335o7n_ρ) * k335o7n_blk (φ'hom x) *
        (k335o7n_permGL (k335o7n_σPerm k335o7n_ρ))⁻¹ =
      k335o7n_blk (φ'hom (fun i => x (i - 1)))
    rw [k335o7n_permGL_conj_blk]
    congr 1
    funext i
    show (x (k335o7n_ρ⁻¹ i) : GL (Fin 2) K) = (x (i - 1) : GL (Fin 2) K)
    rw [hρinv i]
  have hg_mem : k335o7n_blk ![F, F⁻¹, 1] ∈ CFSG.Open.StatedOmega (k335o7n_Qmodel ν) := by
    have hconj := k335o7n_permGL_conj_blk k335o7n_τ01 ![F, 1, 1]
    have hconj' : k335o7n_permGL (k335o7n_σPerm k335o7n_τ01) * k335o7n_blk ![F, 1, 1] *
        (k335o7n_permGL (k335o7n_σPerm k335o7n_τ01))⁻¹ = k335o7n_blk ![1, F, 1] := by
      rw [hconj]
      congr 1
      funext i
      fin_cases i <;> rfl
    have hcomm : k335o7n_blk ![F, F⁻¹, 1] =
        ⁅k335o7n_blk ![F, 1, 1], k335o7n_permGL (k335o7n_σPerm k335o7n_τ01)⁆ := by
      rw [commutatorElement_def]
      rw [show (k335o7n_blk ![F, 1, 1]) * k335o7n_permGL (k335o7n_σPerm k335o7n_τ01) *
          (k335o7n_blk ![F, 1, 1])⁻¹ * (k335o7n_permGL (k335o7n_σPerm k335o7n_τ01))⁻¹ =
          k335o7n_blk ![F, 1, 1] * (k335o7n_permGL (k335o7n_σPerm k335o7n_τ01) *
            (k335o7n_blk ![F, 1, 1])⁻¹ * (k335o7n_permGL (k335o7n_σPerm k335o7n_τ01))⁻¹)
          from by group]
      rw [show k335o7n_permGL (k335o7n_σPerm k335o7n_τ01) * (k335o7n_blk ![F, 1, 1])⁻¹ *
          (k335o7n_permGL (k335o7n_σPerm k335o7n_τ01))⁻¹ = (k335o7n_blk ![1, F, 1])⁻¹ from by
        rw [← hconj']; group]
      rw [← map_inv, ← map_mul]
      congr 1
      funext i
      fin_cases i <;> simp [Pi.mul_apply, Pi.inv_apply]
    rw [hcomm]
    exact Subgroup.commutator_mem_commutator
      (k335o7n_blk_mem_isometryCore ν (![F, 1, 1] : Fin 3 → GL (Fin 2) K)
        (fun i w => by
          fin_cases i
          · exact hFiso w
          · simp
          · simp))
      (k335o7n_permGL_mem_isometryCore ν k335o7n_τ01)
  let g : ↥(CFSG.Open.StatedOmega (k335o7n_Qmodel ν)) :=
    ⟨k335o7n_blk ![F, F⁻¹, 1], hg_mem⟩
  have hFinv' : ∀ x ∈ C, F⁻¹ * x * F = x⁻¹ := by
    intro x hx
    have h1 := hFinv x hx
    have h2 : F⁻¹ * x⁻¹ * F = x := by
      have h1 := hFinv x hx
      have h3 := congrArg (fun y => F⁻¹ * y * F) h1
      rw [show F⁻¹ * (F * x * F⁻¹) * F = x from by group] at h3
      exact h3.symm
    calc F⁻¹ * x * F = (F⁻¹ * x⁻¹ * F)⁻¹ := by group
      _ = x⁻¹ := by rw [h2]
  have hmove : ∀ c : ↥C, c ^ 3 = 1 → c ≠ 1 →
      ∃ g' : ↥(CFSG.Open.StatedOmega (k335o7n_Qmodel ν)), ∃ u : Fin 3 → ↥C,
        (∀ i, u i ∈ Subgroup.zpowers c) ∧ u 0 * u 1 * u 2 ≠ 1 ∧
        g' * φ (fun _ => c) * g'⁻¹ = φ u := by
    intro c hc3 hc1
    refine ⟨g, ![c⁻¹, c⁻¹, c], ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, Matrix.cons_val_two]
      rw [mul_assoc, inv_mul_cancel, mul_one]
      exact fun hh => hc1 (inv_eq_one.mp hh)
    · apply Subtype.ext
      show k335o7n_blk ![F, F⁻¹, 1] * k335o7n_blk (φ'hom (fun _ => c)) *
          (k335o7n_blk ![F, F⁻¹, 1])⁻¹ = k335o7n_blk (φ'hom ![c⁻¹, c⁻¹, c])
      simp only [← map_mul, ← map_inv]
      congr 1
      funext i
      fin_cases i <;> simp [φ'hom, Pi.mul_apply, Pi.inv_apply, hFinv, hFinv']
  have hcoord : K335Coord ↥(CFSG.Open.StatedOmega (k335o7n_Qmodel ν)) a :=
    ⟨↥C, CG, inferInstance, hCcard, φ, hφinj, s, hs3, hs, hmove⟩
  have hab : ((ν + 1) / 2) ^ 2 - ((ν - 1) / 2) ^ 2 = ν := by
    field_simp; ring
  have hg_iso := k335o7n_g_isometry ν ((ν + 1) / 2) ((ν - 1) / 2) p' r' h2 hν0 hab hp
  have hmap1 := k335o7n_map_statedOmega_conj
    (k335o7n_g ν ((ν + 1) / 2) ((ν - 1) / 2) p' r' h2 hν0 hab hp) hg_iso
  have hcoord_std : K335Coord ↥(CFSG.Open.StatedOmega (k335o7n_Qstd (K := K))) a :=
    K335Coord.of_mulEquiv
      ((MulEquiv.subgroupMap (MulAut.conj
        (k335o7n_g ν ((ν + 1) / 2) ((ν - 1) / 2) p' r' h2 hν0 hab hp))
        (CFSG.Open.StatedOmega (k335o7n_Qmodel ν))).trans
        (MulEquiv.subgroupCongr hmap1)) hcoord
  have hmap2 := k335o7n_Phi_statedOmega (K := K)
  have hcoord_odd : K335Coord ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadOdd 3 K)) a :=
    K335Coord.of_mulEquiv
      ((MulEquiv.subgroupMap (k335o7n_Phi (K := K))
        (CFSG.Open.StatedOmega (k335o7n_Qstd (K := K)))).trans
        (MulEquiv.subgroupCongr hmap2)) hcoord_std
  have hproj : K335Coord (CFSG.Open.StatedProj
      (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadOdd 3 K))) a :=
    k335_coord_statedProj
      (CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf
        (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadOdd 3 K)) Nat.prime_three (by norm_num)
        (fun c hc => k335o7n_scalar_sq hc)) hcoord_odd
  have hgoal : a = ((p ^ f) ^ 2 - 1).factorization 3 := by
    simp only [a, hK]
  rw [hgoal] at hproj
  exact K335Coord.of_mulEquiv eX.symm hproj

private theorem k335o8s_sq_sub_one (q : ℕ) : q ^ 2 - 1 = (q - 1) * (q + 1) := by
  symm
  have h1 : (q + 1) * (q - 1) = (q + 1) * q - (q + 1) := Nat.mul_sub_one (q + 1) q
  have h2 : (q + 1) * q = q * q + q := by rw [Nat.add_mul, one_mul]
  have h3 : q * q + q - (q + 1) = q * q - 1 := by omega
  rw [mul_comm, h1, h2, h3, sq]

private theorem k335o8s_factorization_sq_sub_one {q : ℕ} (h2 : 2 ≤ q) (hq : q % 3 = 1) :
    (q ^ 2 - 1).factorization 3 = (q - 1).factorization 3 := by
  have hq1 : ¬ 3 ∣ q + 1 := by
    intro hd
    have h0 : (q + 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
    omega
  rw [k335o8s_sq_sub_one q, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hq1, add_zero]

private def k335o8s_block (σ : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 3 ⊕ Fin 3 ⊕ Fin 2) :=
  Equiv.sumCongr σ (Equiv.sumCongr σ (Equiv.refl (Fin 2)))

@[simp] private theorem k335o8s_block_inl (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    k335o8s_block σ (.inl i) = .inl (σ i) := rfl
@[simp] private theorem k335o8s_block_inr_inl (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    k335o8s_block σ (.inr (.inl i)) = .inr (.inl (σ i)) := rfl
@[simp] private theorem k335o8s_block_inr_inr (σ : Equiv.Perm (Fin 3)) (k : Fin 2) :
    k335o8s_block σ (.inr (.inr k)) = .inr (.inr k) := rfl

private theorem k335o8s_block_quad {K : Type} [Field K] (b c : K) (σ : Equiv.Perm (Fin 3))
    (v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K) :
    CFSG.Open.StatedQuadMinus 4 K b c (v ∘ k335o8s_block σ) =
      CFSG.Open.StatedQuadMinus 4 K b c v := by
  change (∑ i : Fin 3, v (k335o8s_block σ (Sum.inl i)) *
        v (k335o8s_block σ (Sum.inr (Sum.inl i))) +
      v (k335o8s_block σ (Sum.inr (Sum.inr 0))) ^ 2 +
      b * v (k335o8s_block σ (Sum.inr (Sum.inr 0))) *
        v (k335o8s_block σ (Sum.inr (Sum.inr 1))) +
      c * v (k335o8s_block σ (Sum.inr (Sum.inr 1))) ^ 2) =
    (∑ i : Fin 3, v (Sum.inl i) * v (Sum.inr (Sum.inl i)) +
      v (Sum.inr (Sum.inr 0)) ^ 2 +
      b * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) +
      c * v (Sum.inr (Sum.inr 1)) ^ 2)
  simp only [k335o8s_block_inl, k335o8s_block_inr_inl, k335o8s_block_inr_inr]
  congr 1
  congr 1
  congr 1
  exact Equiv.sum_comp σ (fun j => v (.inl j) * v (.inr (.inl j)))

private def k335o8s_tau01 : Equiv.Perm (Fin 3 ⊕ Fin 3 ⊕ Fin 2) :=
  k335o8s_block (Equiv.swap (0 : Fin 3) 1)

private def k335o8s_tau12 : Equiv.Perm (Fin 3 ⊕ Fin 3 ⊕ Fin 2) :=
  k335o8s_block (Equiv.swap (1 : Fin 3) 2)

private theorem k335o8s_tau01_quad {K : Type} [Field K] (b c : K)
    (v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K) :
    CFSG.Open.StatedQuadMinus 4 K b c (v ∘ k335o8s_tau01) =
      CFSG.Open.StatedQuadMinus 4 K b c v :=
  k335o8s_block_quad b c _ v

private theorem k335o8s_tau12_quad {K : Type} [Field K] (b c : K)
    (v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K) :
    CFSG.Open.StatedQuadMinus 4 K b c (v ∘ k335o8s_tau12) =
      CFSG.Open.StatedQuadMinus 4 K b c v :=
  k335o8s_block_quad b c _ v

private def k335o8s_rhoFun (j : Fin 3 ⊕ Fin 3 ⊕ Fin 2) : Fin 3 ⊕ Fin 3 ⊕ Fin 2 :=
  match j with
  | .inl i => .inl (i + 1)
  | .inr (.inl i) => .inr (.inl (i + 1))
  | .inr (.inr k) => .inr (.inr k)

private def k335o8s_rhoInvFun (j : Fin 3 ⊕ Fin 3 ⊕ Fin 2) : Fin 3 ⊕ Fin 3 ⊕ Fin 2 :=
  match j with
  | .inl i => .inl (i - 1)
  | .inr (.inl i) => .inr (.inl (i - 1))
  | .inr (.inr k) => .inr (.inr k)

private def k335o8s_rho : Equiv.Perm (Fin 3 ⊕ Fin 3 ⊕ Fin 2) where
  toFun := k335o8s_rhoFun
  invFun := k335o8s_rhoInvFun
  left_inv := by
    intro j
    rcases j with i | i | k <;> simp [k335o8s_rhoFun, k335o8s_rhoInvFun]
  right_inv := by
    intro j
    rcases j with i | i | k <;> simp [k335o8s_rhoFun, k335o8s_rhoInvFun]

@[simp] private theorem k335o8s_rho_inl (i : Fin 3) :
    k335o8s_rho (.inl i) = .inl (i + 1) := rfl
@[simp] private theorem k335o8s_rho_inr_inl (i : Fin 3) :
    k335o8s_rho (.inr (.inl i)) = .inr (.inl (i + 1)) := rfl
@[simp] private theorem k335o8s_rho_inr_inr (k : Fin 2) :
    k335o8s_rho (.inr (.inr k)) = .inr (.inr k) := rfl
@[simp] private theorem k335o8s_rho_symm_inl (i : Fin 3) :
    (k335o8s_rho)⁻¹ (.inl i) = .inl (i - 1) := rfl
@[simp] private theorem k335o8s_rho_symm_inr_inl (i : Fin 3) :
    (k335o8s_rho)⁻¹ (.inr (.inl i)) = .inr (.inl (i - 1)) := rfl
@[simp] private theorem k335o8s_rho_symm_inr_inr (k : Fin 2) :
    (k335o8s_rho)⁻¹ (.inr (.inr k)) = .inr (.inr k) := rfl

private theorem k335o8s_rho_pow_three : k335o8s_rho ^ 3 = 1 := by
  ext j
  rcases j with i | i | k
  · fin_cases i <;> decide
  · fin_cases i <;> decide
  · fin_cases k <;> decide

private theorem k335o8s_rho_eq_comm : k335o8s_rho = ⁅k335o8s_tau12, k335o8s_tau01⁆ := by
  ext j
  rcases j with i | i | k
  · fin_cases i <;> decide
  · fin_cases i <;> decide
  · fin_cases k <;> decide

private def k335o8s_sig0 : Equiv.Perm (Fin 3 ⊕ Fin 3 ⊕ Fin 2) :=
  Equiv.swap (.inl (0 : Fin 3)) (.inr (.inl (0 : Fin 3)))

private def k335o8s_sig1 : Equiv.Perm (Fin 3 ⊕ Fin 3 ⊕ Fin 2) :=
  Equiv.swap (.inl (1 : Fin 3)) (.inr (.inl (1 : Fin 3)))

@[simp] private theorem k335o8s_sig0_inr_inr (k : Fin 2) :
    k335o8s_sig0 (.inr (.inr k)) = .inr (.inr k) := by
  rw [k335o8s_sig0, Equiv.swap_apply_of_ne_of_ne]
  · exact Sum.inr_ne_inl
  · intro e; exact Sum.inr_ne_inl (Sum.inr_injective e)

@[simp] private theorem k335o8s_sig1_inr_inr (k : Fin 2) :
    k335o8s_sig1 (.inr (.inr k)) = .inr (.inr k) := by
  rw [k335o8s_sig1, Equiv.swap_apply_of_ne_of_ne]
  · exact Sum.inr_ne_inl
  · intro e; exact Sum.inr_ne_inl (Sum.inr_injective e)

private theorem k335o8s_sig0_quad {K : Type} [Field K] (b c : K)
    (v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K) :
    CFSG.Open.StatedQuadMinus 4 K b c (v ∘ k335o8s_sig0) =
      CFSG.Open.StatedQuadMinus 4 K b c v := by
  change (∑ i : Fin 3, v (k335o8s_sig0 (Sum.inl i)) *
        v (k335o8s_sig0 (Sum.inr (Sum.inl i))) +
      v (k335o8s_sig0 (Sum.inr (Sum.inr 0))) ^ 2 +
      b * v (k335o8s_sig0 (Sum.inr (Sum.inr 0))) *
        v (k335o8s_sig0 (Sum.inr (Sum.inr 1))) +
      c * v (k335o8s_sig0 (Sum.inr (Sum.inr 1))) ^ 2) =
    (∑ i : Fin 3, v (Sum.inl i) * v (Sum.inr (Sum.inl i)) +
      v (Sum.inr (Sum.inr 0)) ^ 2 +
      b * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) +
      c * v (Sum.inr (Sum.inr 1)) ^ 2)
  simp only [k335o8s_sig0_inr_inr]
  congr 1
  congr 1
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i = 0
  · subst h
    simp only [k335o8s_sig0, Equiv.swap_apply_left, Equiv.swap_apply_right]
    exact mul_comm _ _
  · have h1 : k335o8s_sig0 (.inl i) = .inl i := by
      rw [k335o8s_sig0, Equiv.swap_apply_of_ne_of_ne]
      · intro e; exact h (Sum.inl_injective e)
      · exact Sum.inl_ne_inr
    have h2 : k335o8s_sig0 (.inr (.inl i)) = .inr (.inl i) := by
      rw [k335o8s_sig0, Equiv.swap_apply_of_ne_of_ne]
      · exact Sum.inr_ne_inl
      · intro e; exact h (Sum.inl_injective (Sum.inr_injective e))
    rw [h1, h2]

private theorem k335o8s_sig01_eq_comm :
    k335o8s_sig0 * k335o8s_sig1 = ⁅k335o8s_sig0, k335o8s_tau01⁆ := by
  ext j
  rcases j with i | i | k
  · fin_cases i <;> decide
  · fin_cases i <;> decide
  · fin_cases k <;> decide

private theorem k335o8s_sig01_inv :
    (k335o8s_sig0 * k335o8s_sig1)⁻¹ = k335o8s_sig0 * k335o8s_sig1 := by
  ext j
  rcases j with i | i | k
  · fin_cases i <;> decide
  · fin_cases i <;> decide
  · fin_cases k <;> decide

private lemma k335o8s_torus_inl {K : Type} [Field K] {C : Subgroup Kˣ}
    (d : Fin 3 → C) (i : Fin 3) :
    torusEntMinus 3 K (C.subtype.compLeft (Fin 3) d) (Sum.inl i) = (d i : Kˣ) := by
  simp [torusEntMinus, MonoidHom.compLeft_apply]

private lemma k335o8s_torus_inr_inl {K : Type} [Field K] {C : Subgroup Kˣ}
    (d : Fin 3 → C) (i : Fin 3) :
    torusEntMinus 3 K (C.subtype.compLeft (Fin 3) d) (Sum.inr (Sum.inl i)) =
      ((d i : C) : Kˣ)⁻¹ := by
  simp [torusEntMinus, MonoidHom.compLeft_apply]

private lemma k335o8s_torus_inr_inr {K : Type} [Field K] {C : Subgroup Kˣ}
    (d : Fin 3 → C) (k : Fin 2) :
    torusEntMinus 3 K (C.subtype.compLeft (Fin 3) d) (Sum.inr (Sum.inr k)) = 1 := by
  simp [torusEntMinus]

private theorem k335o8s_torus_mem {K : Type} [Field K] {b c : K} {C : Subgroup Kˣ}
    {r : ℕ} (hr : Odd r) (hC : ∀ z : C, z ^ r = 1) (d : Fin 3 → C) :
    diagGL (torusEntMinus 3 K (C.subtype.compLeft (Fin 3) d)) ∈
      CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c) := by
  refine diagGL_mem_statedOmega (Q := CFSG.Open.StatedQuadMinus 4 K b c)
    (σ := swapMinusPerm 3) (fun v => ?_) hr ?_ ?_ ?_
  · change (∑ i : Fin 3, v (Sum.inr (Sum.inl i)) * v (Sum.inl i) +
        v (Sum.inr (Sum.inr 0)) ^ 2 +
        b * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) +
        c * v (Sum.inr (Sum.inr 1)) ^ 2) =
      (∑ i : Fin 3, v (Sum.inl i) * v (Sum.inr (Sum.inl i)) +
        v (Sum.inr (Sum.inr 0)) ^ 2 +
        b * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) +
        c * v (Sum.inr (Sum.inr 1)) ^ 2)
    rw [Finset.sum_congr rfl fun i _ => mul_comm (v (Sum.inr (Sum.inl i))) (v (Sum.inl i))]
  · intro j
    rcases j with i | i | k
    · rw [k335o8s_torus_inl]
      simpa using congrArg (fun x : C => (x : Kˣ)) (hC (d i))
    · rw [k335o8s_torus_inr_inl, inv_pow]
      simpa using congrArg (fun x : C => (x : Kˣ)) (hC (d i))
    · rw [k335o8s_torus_inr_inr]; simp
  · intro v
    let t : Fin 3 → Kˣ := C.subtype.compLeft (Fin 3) d
    change (∑ i : Fin 3, ((t i : K) * v (Sum.inl i)) *
          ((((t i)⁻¹ : Kˣ) : K) * v (Sum.inr (Sum.inl i))) +
        (((1 : Kˣ) : K) * v (Sum.inr (Sum.inr 0))) ^ 2 +
        b * (((1 : Kˣ) : K) * v (Sum.inr (Sum.inr 0))) *
          (((1 : Kˣ) : K) * v (Sum.inr (Sum.inr 1))) +
        c * (((1 : Kˣ) : K) * v (Sum.inr (Sum.inr 1))) ^ 2) =
      (∑ i : Fin 3, v (Sum.inl i) * v (Sum.inr (Sum.inl i)) +
        v (Sum.inr (Sum.inr 0)) ^ 2 + b * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) +
          c * v (Sum.inr (Sum.inr 1)) ^ 2)
    simp only [Units.val_one, one_mul]
    rw [Finset.sum_congr rfl fun i _ => (by
      linear_combination (v (Sum.inl i) * v (Sum.inr (Sum.inl i))) * (t i).mul_inv :
      ((t i : K) * v (Sum.inl i)) * ((((t i)⁻¹ : Kˣ) : K) * v (Sum.inr (Sum.inl i))) =
        v (Sum.inl i) * v (Sum.inr (Sum.inl i)))]
  · intro j
    rcases j with i | i | k
    · change (torusEntMinus 3 K (C.subtype.compLeft (Fin 3) d)) (Sum.inr (Sum.inl i)) =
        ((torusEntMinus 3 K (C.subtype.compLeft (Fin 3) d)) (Sum.inl i))⁻¹
      rw [k335o8s_torus_inr_inl, k335o8s_torus_inl]
    · change (torusEntMinus 3 K (C.subtype.compLeft (Fin 3) d)) (Sum.inl i) =
        ((torusEntMinus 3 K (C.subtype.compLeft (Fin 3) d)) (Sum.inr (Sum.inl i)))⁻¹
      rw [k335o8s_torus_inl, k335o8s_torus_inr_inl, inv_inv]
    · change (torusEntMinus 3 K (C.subtype.compLeft (Fin 3) d)) (Sum.inr (Sum.inr k)) =
        ((torusEntMinus 3 K (C.subtype.compLeft (Fin 3) d)) (Sum.inr (Sum.inr k)))⁻¹
      rw [k335o8s_torus_inr_inr, inv_one]

private theorem k335o8s_diag_injective {K : Type} [Field K] {C : Subgroup Kˣ} :
    Function.Injective (fun d : Fin 3 → C =>
      diagGL (torusEntMinus 3 K (C.subtype.compLeft (Fin 3) d))) := by
  intro d e h
  funext i
  have h1 := congrArg (fun A : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K =>
    ((A : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) (.inl i) (.inl i))) h
  simp only [coe_diagGL, Matrix.diagonal_apply_eq, k335o8s_torus_inl] at h1
  exact Subtype.ext (Units.ext h1)

private theorem k335o8s_permGL_mem_isometryCore {K : Type} [Field K]
    {Q : (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K) → K} {σ : Equiv.Perm (Fin 3 ⊕ Fin 3 ⊕ Fin 2)}
    (hσ : ∀ v, Q (v ∘ σ) = Q v) :
    permGL σ ∈ CFSG.MatrixModel.isometryCore Q :=
  Subgroup.subset_closure (fun v => by
    rw [mulVec_permGL]
    have h := hσ (v ∘ ⇑(σ⁻¹ : Equiv.Perm _))
    rw [show (v ∘ ⇑(σ⁻¹ : Equiv.Perm _)) ∘ σ = v from funext fun j => by simp] at h
    exact h.symm)

private theorem k335o8s_permGL_comm_mem {K : Type} [Field K]
    {Q : (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K) → K}
    {σ₁ σ₂ : Equiv.Perm (Fin 3 ⊕ Fin 3 ⊕ Fin 2)}
    (h₁ : ∀ v, Q (v ∘ σ₁) = Q v) (h₂ : ∀ v, Q (v ∘ σ₂) = Q v) :
    permGL ⁅σ₁, σ₂⁆ ∈ CFSG.Open.StatedOmega Q := by
  rw [map_commutatorElement]
  exact Subgroup.commutator_mem_commutator (k335o8s_permGL_mem_isometryCore h₁)
    (k335o8s_permGL_mem_isometryCore h₂)

private theorem k335o8s_permGL_conj_diagGL {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] (τ : Equiv.Perm ι) (e : ι → Kˣ) :
    permGL τ * diagGL e * (permGL τ)⁻¹ = diagGL (fun j => e (τ⁻¹ j)) := by
  calc permGL τ * diagGL e * (permGL τ)⁻¹
      = (permGL τ * diagGL e) * (permGL τ)⁻¹ := by rw [mul_assoc]
    _ = (diagGL (fun j => e (τ⁻¹ j)) * permGL τ) * (permGL τ)⁻¹ := by rw [permGL_mul_diagGL]
    _ = diagGL (fun j => e (τ⁻¹ j)) * (permGL τ * (permGL τ)⁻¹) := by rw [mul_assoc]
    _ = diagGL (fun j => e (τ⁻¹ j)) := by rw [mul_inv_cancel, mul_one]

private theorem k335o8s_isometry_of_mem_statedOmega {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {Q : (ι → K) → K} {g : GL ι K} (hg : g ∈ CFSG.Open.StatedOmega Q)
    (v : ι → K) : Q ((g : Matrix ι ι K) *ᵥ v) = Q v := by
  let I : Subgroup (GL ι K) :=
    { carrier := {A | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v}
      one_mem' := fun v => by simp
      mul_mem' := fun {a b} ha hb v => by
        simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
        rw [ha, hb]
      inv_mem' := fun {a} ha v => by
        have := ha (((a⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v)
        simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using this.symm }
  have hcl : Subgroup.closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} ≤ I :=
    (Subgroup.closure_le I).mpr fun A hA => hA
  have hg' : g ∈ Subgroup.closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} :=
    Subgroup.commutator_le_self _ hg
  exact hcl hg' v

private theorem k335o8s_scalar_sq {K : Type} [Field K] {b c : K} {z : Kˣ}
    (hc : Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3 ⊕ Fin 2) z ∈
      CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c)) : z ^ 2 = 1 := by
  have hiso := k335o8s_isometry_of_mem_statedOmega hc
  let v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K := Pi.single (.inr (.inr 0)) 1
  have hmul : ((Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3 ⊕ Fin 2) z :
      Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) *ᵥ v) =
      fun j => (z : K) * v j := by
    ext j
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have h := hiso v
  rw [hmul] at h
  have hL : CFSG.Open.StatedQuadMinus 4 K b c (fun j => (z : K) * v j) = (z : K) ^ 2 := by
    simp only [CFSG.Open.StatedQuadMinus]
    rw [Finset.sum_eq_zero (fun i _ => by simp [v])]
    simp [v]
  have hR : CFSG.Open.StatedQuadMinus 4 K b c v = 1 := by
    simp only [CFSG.Open.StatedQuadMinus]
    rw [Finset.sum_eq_zero (fun i _ => by simp [v])]
    simp [v]
  rw [hL, hR] at h
  exact Units.ext h

theorem k335_coord_omegaMinus8_split {X : Type} [Group X] {p f : ℕ}
    (h : LieModel X .POmegaMinus 4 p f) (hq : p ^ f % 3 = 1) :
    K335Coord X (((p ^ f) ^ 2 - 1).factorization 3) := by
  obtain ⟨-, K, hfield, hfinite, hK, b, c, _hbc, ⟨e⟩⟩ :=
    h.statedClassicalModel_of_ne_zero (by norm_num)
  let : Field K := hfield
  let : Finite K := hfinite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq2 : 2 ≤ p ^ f := by
    rw [← hK]
    exact Finite.one_lt_card
  let a : ℕ := ((p ^ f) ^ 2 - 1).factorization 3
  let C : Sylow 3 Kˣ := default
  have hCcard : Nat.card C = 3 ^ a := by
    dsimp only [a]
    rw [Sylow.card_eq_multiplicity C, Nat.card_units, hK]
    congr 1
    exact (k335o8s_factorization_sq_sub_one hq2 hq).symm
  have hCpow : ∀ z : C, z ^ (3 ^ a) = 1 := by
    intro z
    rw [← hCcard]
    exact pow_card_eq_one'
  have hOdd : Odd (3 ^ a) := (by decide : Odd 3).pow (n := a)
  let H : Subgroup (GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) :=
    CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c)
  have hφmem : ∀ d : Fin 3 → C,
      diagGL (torusEntMinus 3 K ((C : Subgroup Kˣ).subtype.compLeft (Fin 3) d)) ∈ H :=
    fun d => k335o8s_torus_mem (C := (C : Subgroup Kˣ)) hOdd hCpow d
  let φ : (Fin 3 → C) →* H :=
    ((diagGL.comp (torusEntMinus 3 K)).comp
      ((C : Subgroup Kˣ).subtype.compLeft (Fin 3))).codRestrict H hφmem
  have hφinj : Function.Injective φ := by
    intro d d' hdd
    apply k335o8s_diag_injective
    exact congrArg (fun x : H => (x : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K)) hdd
  have hρH : permGL k335o8s_rho ∈ H := by
    rw [k335o8s_rho_eq_comm]
    exact k335o8s_permGL_comm_mem (k335o8s_tau12_quad b c) (k335o8s_tau01_quad b c)
  let s : H := ⟨permGL k335o8s_rho, hρH⟩
  have hs3 : s ^ 3 = 1 := by
    apply Subtype.ext
    show (permGL k335o8s_rho) ^ 3 = 1
    rw [← map_pow, k335o8s_rho_pow_three, map_one]
  have hs : ∀ x : Fin 3 → C, s * φ x * s⁻¹ = φ (fun i => x (i - 1)) := by
    intro x
    apply Subtype.ext
    show permGL k335o8s_rho *
        diagGL (torusEntMinus 3 K ((C : Subgroup Kˣ).subtype.compLeft (Fin 3) x)) *
        (permGL k335o8s_rho)⁻¹ =
      diagGL (torusEntMinus 3 K
        ((C : Subgroup Kˣ).subtype.compLeft (Fin 3) (fun i => x (i - 1))))
    rw [k335o8s_permGL_conj_diagGL]
    congr 1
    funext j
    rcases j with i | i | k
    · simp [k335o8s_rho_symm_inl, k335o8s_torus_inl]
    · simp [k335o8s_rho_symm_inr_inl, k335o8s_torus_inr_inl]
    · simp [k335o8s_rho_symm_inr_inr, k335o8s_torus_inr_inr]
  have hgH : permGL (k335o8s_sig0 * k335o8s_sig1) ∈ H := by
    rw [k335o8s_sig01_eq_comm]
    exact k335o8s_permGL_comm_mem (k335o8s_sig0_quad b c) (k335o8s_tau01_quad b c)
  have hmove : ∀ z : C, z ^ 3 = 1 → z ≠ 1 → ∃ g : H, ∃ u : Fin 3 → C,
      (∀ i, u i ∈ Subgroup.zpowers z) ∧ u 0 * u 1 * u 2 ≠ 1 ∧
      g * φ (fun _ => z) * g⁻¹ = φ u := by
    intro z hz3 hz1
    let g : H := ⟨permGL (k335o8s_sig0 * k335o8s_sig1), hgH⟩
    let u : Fin 3 → C := ![z⁻¹, z⁻¹, z]
    refine ⟨g, u, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [u]
    · have h1 : u 0 * u 1 * u 2 = z⁻¹ := by
        simp only [u, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]
        rw [mul_assoc, inv_mul_cancel, mul_one]
      rw [h1]
      exact fun h => hz1 (inv_eq_one.mp h)
    · apply Subtype.ext
      show permGL (k335o8s_sig0 * k335o8s_sig1) *
          diagGL (torusEntMinus 3 K
            ((C : Subgroup Kˣ).subtype.compLeft (Fin 3) (fun _ => z))) *
          (permGL (k335o8s_sig0 * k335o8s_sig1))⁻¹ =
        diagGL (torusEntMinus 3 K ((C : Subgroup Kˣ).subtype.compLeft (Fin 3) u))
      rw [k335o8s_permGL_conj_diagGL, k335o8s_sig01_inv]
      congr 1
      funext j
      rcases j with i | i | k
      · fin_cases i <;>
          simp [u, k335o8s_torus_inl, k335o8s_torus_inr_inl, k335o8s_sig0, k335o8s_sig1,
            Equiv.swap_apply_of_ne_of_ne]
      · fin_cases i <;>
          simp [u, k335o8s_torus_inl, k335o8s_torus_inr_inl, k335o8s_sig0, k335o8s_sig1,
            Equiv.swap_apply_of_ne_of_ne]
      · fin_cases k <;>
          simp [u, k335o8s_torus_inr_inr, k335o8s_sig0, k335o8s_sig1,
            Equiv.swap_apply_of_ne_of_ne]
  refine K335Coord.of_mulEquiv e.symm (k335_coord_statedProj ?_ ?_)
  · exact CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf H Nat.prime_three
      (by norm_num) (fun z hz => k335o8s_scalar_sq hz)
  · exact ⟨C, inferInstance, inferInstance, hCcard, φ, hφinj, s, hs3, hs, hmove⟩

section K335O8NAux

private noncomputable def k335o8n_f (K : Type) [Field K] : K[X] := X ^ 2 + X + 1

private theorem k335o8n_natDegree_f (K : Type) [Field K] : (k335o8n_f K).natDegree = 2 := by
  unfold k335o8n_f; compute_degree!

private theorem k335o8n_f_ne_zero (K : Type) [Field K] : k335o8n_f K ≠ 0 := by
  intro h
  have := k335o8n_natDegree_f K
  rw [h] at this; simp at this

private theorem k335o8n_irreducible (K : Type) [Field K] [Finite K] (h3 : (3 : K) ≠ 0)
    (hq : Nat.card K % 3 = 2) : Irreducible (k335o8n_f K) := by
  have hns : ¬ IsSplit K := by
    rw [isSplit_iff_card_mod_three h3]
    omega
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [k335o8n_natDegree_f]; norm_num
  · intro x hx
    apply hns
    refine ⟨x, ?_⟩
    simpa [Polynomial.IsRoot, k335o8n_f] using hx

private noncomputable def k335o8n_planeEquiv {K : Type} [Field K]
    {E : Type} [Field E] [Algebra K E] (b : Module.Basis (Fin 2) K E) :
    E ≃ₗ[K] (K × K) :=
  b.equivFun.trans (LinearEquiv.finTwoArrow K K)

private theorem k335o8n_planeEquiv_apply {K : Type} [Field K]
    {E : Type} [Field E] [Algebra K E] (b : Module.Basis (Fin 2) K E) (x : E) :
    k335o8n_planeEquiv b x = (b.repr x 0, b.repr x 1) := by
  simp [k335o8n_planeEquiv, LinearEquiv.finTwoArrow]

private theorem k335o8n_leftMulMatrix_form {K : Type} [Field K]
    {E : Type} [Field E] [Algebra K E] (b : Module.Basis (Fin 2) K E)
    (hb0 : b 0 = 1) (hb1 : b 1 ^ 2 + b 1 + 1 = 0) (x : E) :
    Algebra.leftMulMatrix b x =
      !![b.repr x 0, -b.repr x 1; b.repr x 1, b.repr x 0 - b.repr x 1] := by
  have hx : x = b.repr x 0 • b 0 + b.repr x 1 • b 1 := by
    conv_lhs => rw [← b.sum_repr x]
    rw [Fin.sum_univ_two]
  have hsq : b 1 * b 1 = -b 1 - 1 := by linear_combination hb1
  have hmul : x * b 1 = (-b.repr x 1) • b 0 + (b.repr x 0 - b.repr x 1) • b 1 := by
    nth_rewrite 1 [hx]
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, hb0, hsq]
    simp only [Algebra.smul_def, map_neg, map_sub]
    ring
  have h00 : (Algebra.leftMulMatrix b x) 0 0 = b.repr x 0 := by
    rw [Algebra.leftMulMatrix_eq_repr_mul, hb0, mul_one]
  have h10 : (Algebra.leftMulMatrix b x) 1 0 = b.repr x 1 := by
    rw [Algebra.leftMulMatrix_eq_repr_mul, hb0, mul_one]
  have h01 : (Algebra.leftMulMatrix b x) 0 1 = -b.repr x 1 := by
    rw [Algebra.leftMulMatrix_eq_repr_mul, hmul]
    simp
  have h11 : (Algebra.leftMulMatrix b x) 1 1 = b.repr x 0 - b.repr x 1 := by
    rw [Algebra.leftMulMatrix_eq_repr_mul, hmul]
    simp
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

private theorem k335o8n_norm_eq_rotForm {K : Type} [Field K]
    {E : Type} [Field E] [Algebra K E] (b : Module.Basis (Fin 2) K E)
    (hb0 : b 0 = 1) (hb1 : b 1 ^ 2 + b 1 + 1 = 0) (x : E) :
    Algebra.norm K x = rotForm K (k335o8n_planeEquiv b x) := by
  rw [k335o8n_planeEquiv_apply, Algebra.norm_eq_matrix_det b,
    k335o8n_leftMulMatrix_form b hb0 hb1 x]
  simp only [Matrix.det_fin_two, rotForm_apply, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

private noncomputable def k335o8n_planeMul {K : Type} [Field K]
    {E : Type} [Field E] [Algebra K E] (b : Module.Basis (Fin 2) K E) :
    Eˣ →* (K × K) ≃ₗ[K] (K × K) where
  toFun t := (k335o8n_planeEquiv b).symm.trans
    ((Units.mulLeftLinearEquiv K E t).trans (k335o8n_planeEquiv b))
  map_one' := by
    ext v <;>
      simp [LinearEquiv.trans_apply]
  map_mul' t s := by
    ext v <;>
      simp [LinearEquiv.trans_apply, Units.mulLeftLinearEquiv_apply]

private theorem k335o8n_planeMul_apply {K : Type} [Field K]
    {E : Type} [Field E] [Algebra K E] (b : Module.Basis (Fin 2) K E) (t : Eˣ)
    (v : K × K) :
    k335o8n_planeMul b t v =
      k335o8n_planeEquiv b ((t : E) * (k335o8n_planeEquiv b).symm v) := rfl

private theorem k335o8n_norm_eq_one {K : Type} [Field K]
    {E : Type} [Field E] [Algebra K E] (b : Module.Basis (Fin 2) K E) [Fintype K]
    {t : Eˣ} (ht : t ∈ normOne K E) : Algebra.norm K (t : E) = 1 := by
  apply (algebraMap K E).injective
  rw [map_one, algebraMap_norm K E b]
  exact (mem_normOne_iff K E t).mp ht

private theorem k335o8n_planeMul_mem {K : Type} [Field K]
    {E : Type} [Field E] [Algebra K E] (b : Module.Basis (Fin 2) K E) [Fintype K]
    (hb0 : b 0 = 1) (hb1 : b 1 ^ 2 + b 1 + 1 = 0) {t : Eˣ} (ht : t ∈ normOne K E) :
    k335o8n_planeMul b t ∈ TauCeti.QuadraticMap.orthogonalGroup (rotForm K) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  rw [k335o8n_planeMul_apply, ← k335o8n_norm_eq_rotForm b hb0 hb1, map_mul,
    k335o8n_norm_eq_one b ht, one_mul]
  rw [k335o8n_norm_eq_rotForm b hb0 hb1 ((k335o8n_planeEquiv b).symm v),
    LinearEquiv.apply_symm_apply]

private theorem k335o8n_planeMul_injective {K : Type} [Field K]
    {E : Type} [Field E] [Algebra K E] (b : Module.Basis (Fin 2) K E) :
    Function.Injective (k335o8n_planeMul b) := by
  intro t s h
  have h1 := congrArg (fun e : (K × K) ≃ₗ[K] (K × K) => e (k335o8n_planeEquiv b 1)) h
  rw [k335o8n_planeMul_apply, k335o8n_planeMul_apply, LinearEquiv.symm_apply_apply,
    mul_one, mul_one] at h1
  exact Units.ext ((k335o8n_planeEquiv b).injective h1)

private noncomputable def k335o8n_frob {K : Type} [Field K]
    {E : Type} [Field E] [Algebra K E] (b : Module.Basis (Fin 2) K E) [Fintype K]
    [Algebra.IsAlgebraic K E] : (K × K) ≃ₗ[K] (K × K) :=
  (k335o8n_planeEquiv b).symm.trans
    (((FiniteField.frobeniusAlgEquivOfAlgebraic K E).toLinearEquiv).trans
      (k335o8n_planeEquiv b))

private theorem k335o8n_frob_apply {K : Type} [Field K]
    {E : Type} [Field E] [Algebra K E] (b : Module.Basis (Fin 2) K E) [Fintype K]
    [Algebra.IsAlgebraic K E] (v : K × K) :
    k335o8n_frob b v =
      k335o8n_planeEquiv b ((FiniteField.frobeniusAlgEquivOfAlgebraic K E)
        ((k335o8n_planeEquiv b).symm v)) := rfl

private theorem k335o8n_frob_mem {K : Type} [Field K]
    {E : Type} [Field E] [Algebra K E] (b : Module.Basis (Fin 2) K E) [Fintype K]
    [Algebra.IsAlgebraic K E] (hb0 : b 0 = 1) (hb1 : b 1 ^ 2 + b 1 + 1 = 0) :
    k335o8n_frob b ∈ TauCeti.QuadraticMap.orthogonalGroup (rotForm K) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  rw [k335o8n_frob_apply, ← k335o8n_norm_eq_rotForm b hb0 hb1,
    Algebra.norm_eq_of_algEquiv (FiniteField.frobeniusAlgEquivOfAlgebraic K E),
    k335o8n_norm_eq_rotForm b hb0 hb1 ((k335o8n_planeEquiv b).symm v),
    LinearEquiv.apply_symm_apply]

private theorem k335o8n_frob_sq {K : Type} [Field K]
    {E : Type} [Field E] [Algebra K E] (b : Module.Basis (Fin 2) K E) [Fintype K]
    [Algebra.IsAlgebraic K E] (_hb0 : b 0 = 1) (_hb1 : b 1 ^ 2 + b 1 + 1 = 0) :
    k335o8n_frob b * k335o8n_frob b = 1 := by
  have hsq : ∀ x : E, (FiniteField.frobeniusAlgEquivOfAlgebraic K E)
      ((FiniteField.frobeniusAlgEquivOfAlgebraic K E) x) = x := by
    intro x
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    change (x ^ Fintype.card K) ^ Fintype.card K = x
    rw [← Nat.card_eq_fintype_card, pow_card_pow_card K E b]
  ext v <;>
    simp only [k335o8n_frob, LinearEquiv.mul_apply, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply, AlgEquiv.coe_toLinearEquiv,
      hsq] <;> rfl

private theorem k335o8n_frob_mul_planeMul {K : Type} [Field K]
    {E : Type} [Field E] [Algebra K E] (b : Module.Basis (Fin 2) K E) [Fintype K]
    [Algebra.IsAlgebraic K E] (t : Eˣ) :
    k335o8n_frob b * k335o8n_planeMul b t =
      k335o8n_planeMul b
        (Units.map (FiniteField.frobeniusAlgEquivOfAlgebraic K E : E →* E) t) *
        k335o8n_frob b := by
  ext v <;>
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, k335o8n_frob_apply, k335o8n_frob_apply,
      k335o8n_planeMul_apply, k335o8n_planeMul_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply, Units.coe_map]
  all_goals
    rw [map_mul]
    rfl

private theorem k335o8n_frob_conj_inv {K : Type} [Field K]
    {E : Type} [Field E] [Algebra K E] (b : Module.Basis (Fin 2) K E) [Fintype K]
    [Algebra.IsAlgebraic K E] (hb0 : b 0 = 1) (hb1 : b 1 ^ 2 + b 1 + 1 = 0) {t : Eˣ}
    (ht : t ∈ normOne K E) :
    k335o8n_frob b * k335o8n_planeMul b t * (k335o8n_frob b)⁻¹ =
      k335o8n_planeMul b t⁻¹ := by
  have hσel : (FiniteField.frobeniusAlgEquivOfAlgebraic K E : E →* E) (t : E) =
      (t : E)⁻¹ := by
    change (FiniteField.frobeniusAlgEquivOfAlgebraic K E) (t : E) = (t : E)⁻¹
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    change (t : E) ^ Fintype.card K = (t : E)⁻¹
    rw [← Nat.card_eq_fintype_card, pow_card_of_mem_normOne K E ht]
  have hσ : Units.map (FiniteField.frobeniusAlgEquivOfAlgebraic K E : E →* E) t =
      t⁻¹ := by
    apply Units.ext
    rw [Units.coe_map]
    simpa only [Units.val_inv_eq_inv_val] using hσel
  have hFinv : (k335o8n_frob b)⁻¹ = k335o8n_frob b :=
    inv_eq_of_mul_eq_one_right (k335o8n_frob_sq b hb0 hb1)
  rw [k335o8n_frob_mul_planeMul b t, hσ, hFinv, mul_assoc, k335o8n_frob_sq b hb0 hb1, mul_one]

private noncomputable def k335o8n_psiFun {K : Type} [Field K] {C : Type} [Group C]
    (m : C →* (K × K) ≃ₗ[K] (K × K)) (x : Fin 3 → C) :
    ModelSpace K ≃ₗ[K] ModelSpace K where
  toFun v := (fun i => m (x i) (v.1 i), v.2)
  invFun v := (fun i => (m (x i))⁻¹ (v.1 i), v.2)
  map_add' v w := by
    refine Prod.ext (funext fun i => ?_) rfl
    simp [Pi.add_apply, map_add]
  map_smul' r v := by
    refine Prod.ext (funext fun i => ?_) rfl
    simp [Pi.smul_apply, map_smul]
  left_inv v := by
    refine Prod.ext (funext fun i => ?_) rfl
    simp
  right_inv v := by
    refine Prod.ext (funext fun i => ?_) rfl
    simp

private theorem k335o8n_psiFun_apply {K : Type} [Field K] {C : Type} [Group C]
    (m : C →* (K × K) ≃ₗ[K] (K × K)) (x : Fin 3 → C) (v : ModelSpace K) :
    k335o8n_psiFun (K := K) m x v = (fun i => m (x i) (v.1 i), v.2) := rfl

private theorem k335o8n_psiFun_one {K : Type} [Field K] {C : Type} [Group C]
    (m : C →* (K × K) ≃ₗ[K] (K × K)) :
    k335o8n_psiFun (K := K) m 1 = 1 := by
  apply LinearEquiv.ext; intro v
  refine Prod.ext (funext fun i => ?_) rfl
  simp [k335o8n_psiFun_apply]

private theorem k335o8n_psiFun_mul {K : Type} [Field K] {C : Type} [Group C]
    (m : C →* (K × K) ≃ₗ[K] (K × K)) (x y : Fin 3 → C) :
    k335o8n_psiFun (K := K) m (x * y) =
      k335o8n_psiFun (K := K) m x * k335o8n_psiFun (K := K) m y := by
  apply LinearEquiv.ext; intro v
  refine Prod.ext (funext fun i => ?_) rfl
  simp [k335o8n_psiFun_apply, LinearEquiv.mul_apply, Pi.mul_apply, map_mul]

private noncomputable def k335o8n_psi {K : Type} [Field K] {C : Type} [Group C]
    (m : C →* (K × K) ≃ₗ[K] (K × K)) :
    (Fin 3 → C) →* (ModelSpace K ≃ₗ[K] ModelSpace K) where
  toFun := k335o8n_psiFun (K := K) m
  map_one' := k335o8n_psiFun_one m
  map_mul' := k335o8n_psiFun_mul m

private theorem k335o8n_psi_apply {K : Type} [Field K] {C : Type} [Group C]
    (m : C →* (K × K) ≃ₗ[K] (K × K)) (x : Fin 3 → C) (v : ModelSpace K) :
    k335o8n_psi (K := K) m x v = (fun i => m (x i) (v.1 i), v.2) := rfl

private theorem k335o8n_psi_pow_apply {K : Type} [Field K] {C : Type} [Group C]
    (m : C →* (K × K) ≃ₗ[K] (K × K)) (x : Fin 3 → C) (n : ℕ) (v : ModelSpace K) :
    ((k335o8n_psi (K := K) m x) ^ n) v =
      (fun i => ((m (x i)) ^ n) (v.1 i), v.2) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, LinearEquiv.mul_apply, k335o8n_psi_apply, ih]
    refine Prod.ext (funext fun i => ?_) rfl
    simp [pow_succ, LinearEquiv.mul_apply]

private theorem k335o8n_psi_mem_modelO {K : Type} [Field K] {C : Type} [Group C]
    (m : C →* (K × K) ≃ₗ[K] (K × K))
    (hm : ∀ t, m t ∈ TauCeti.QuadraticMap.orthogonalGroup (rotForm K))
    (b c : K) (x : Fin 3 → C) :
    k335o8n_psi (K := K) m x ∈ modelO b c := by
  rw [modelO, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  rw [modelForm_apply, modelForm_apply, k335o8n_psi_apply]
  congr 1
  exact Finset.sum_congr rfl fun i _ =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hm (x i)) (v.1 i)

private theorem k335o8n_psi_mem_modelOmega {K : Type} [Field K] [Finite K]
    (h3 : (3 : K) ≠ 0) {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {C : Type} [Group C] [Finite C] (m : C →* (K × K) ≃ₗ[K] (K × K))
    (hm : ∀ t, m t ∈ TauCeti.QuadraticMap.orthogonalGroup (rotForm K))
    {a : ℕ} (hCa : ∀ t : C, t ^ (3 ^ a) = 1) (x : Fin 3 → C) :
    k335o8n_psi (K := K) m x ∈ modelOmega b c := by
  refine mem_modelOmega_of_odd (b := b) (c := c) h3 hbc
    (k335o8n_psi_mem_modelO (K := K) m hm b c x) ?_
  have hpow : (k335o8n_psi (K := K) m x) ^ (3 ^ a) = 1 := by
    apply LinearEquiv.ext; intro v
    rw [k335o8n_psi_pow_apply]
    refine Prod.ext (funext fun i => ?_) rfl
    change ((m (x i)) ^ (3 ^ a)) (v.1 i) = v.1 i
    rw [← map_pow, hCa (x i), map_one]
    rfl
  exact Odd.of_dvd_nat ((by decide : Odd 3).pow (n := a)) (orderOf_dvd_of_pow_eq_one hpow)

private theorem k335o8n_psi_injective {K : Type} [Field K] {C : Type} [Group C]
    (m : C →* (K × K) ≃ₗ[K] (K × K)) (hm : Function.Injective m) :
    Function.Injective (k335o8n_psi (K := K) m) := by
  intro x y h
  funext i
  apply hm
  apply LinearEquiv.ext
  intro p
  have h1 := congrArg (fun e : ModelSpace K ≃ₗ[K] ModelSpace K =>
    e (planeVec i p)) h
  simp only [k335o8n_psi_apply, planeVec] at h1
  simpa using congrFun (congrArg Prod.fst h1) i

private noncomputable def k335o8n_blockPerm {K : Type} [Field K] (σ : Equiv.Perm (Fin 3)) :
    ModelSpace K ≃ₗ[K] ModelSpace K where
  toFun v := (fun i => v.1 (σ.symm i), v.2)
  invFun v := (fun i => v.1 (σ i), v.2)
  map_add' v w := by
    refine Prod.ext (funext fun i => ?_) rfl
    simp [Pi.add_apply]
  map_smul' r v := by
    refine Prod.ext (funext fun i => ?_) rfl
    simp [Pi.smul_apply]
  left_inv v := by
    refine Prod.ext (funext fun i => ?_) rfl
    simp
  right_inv v := by
    refine Prod.ext (funext fun i => ?_) rfl
    simp

private theorem k335o8n_blockPerm_apply {K : Type} [Field K]
    (σ : Equiv.Perm (Fin 3)) (v : ModelSpace K) :
    k335o8n_blockPerm (K := K) σ v = (fun i => v.1 (σ.symm i), v.2) := rfl

private theorem k335o8n_blockPerm_mul {K : Type} [Field K] (σ τ : Equiv.Perm (Fin 3)) :
    k335o8n_blockPerm (K := K) (σ * τ) =
      k335o8n_blockPerm (K := K) σ * k335o8n_blockPerm (K := K) τ := by
  apply LinearEquiv.ext; intro v
  refine Prod.ext (funext fun i => ?_) rfl
  simp only [k335o8n_blockPerm_apply, LinearEquiv.mul_apply]
  congr 1

private noncomputable def k335o8n_blockPermHom {K : Type} [Field K] :
    Equiv.Perm (Fin 3) →* (ModelSpace K ≃ₗ[K] ModelSpace K) :=
  MonoidHom.mk' (k335o8n_blockPerm (K := K)) (k335o8n_blockPerm_mul (K := K))

private theorem k335o8n_blockPerm_mem_modelO {K : Type} [Field K]
    (σ : Equiv.Perm (Fin 3)) (b c : K) :
    k335o8n_blockPerm (K := K) σ ∈ modelO b c := by
  rw [modelO, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  change modelForm b c (fun i => v.1 (σ.symm i), v.2) = modelForm b c v
  rw [modelForm_apply, modelForm_apply]
  change (∑ i, rotForm K (v.1 (σ.symm i))) + wForm b c v.2 =
    (∑ i, rotForm K (v.1 i)) + wForm b c v.2
  rw [Equiv.sum_comp σ.symm (fun i => rotForm K (v.1 i))]

private theorem k335o8n_blockPerm_conj_planeExtend {K : Type} [Field K]
    (σ : Equiv.Perm (Fin 3)) (i : Fin 3)
    (g : (K × K) ≃ₗ[K] (K × K)) :
    k335o8n_blockPerm (K := K) σ * planeExtend K i g =
      planeExtend K (σ i) g * k335o8n_blockPerm (K := K) σ := by
  apply LinearEquiv.ext; intro v
  refine Prod.ext (funext fun k => ?_) rfl
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, k335o8n_blockPerm_apply, planeExtend_apply,
    k335o8n_blockPerm_apply, planeExtend_apply]
  by_cases hk : k = σ i
  · subst hk
    simp [Equiv.symm_apply_apply]
  · have hk' : σ.symm k ≠ i := fun h => hk (by rw [← h, Equiv.apply_symm_apply])
    simp [Function.update_of_ne hk', hk]

private theorem k335o8n_blockPerm_conj_psi {K : Type} [Field K] {C : Type} [Group C]
    (m : C →* (K × K) ≃ₗ[K] (K × K)) (σ : Equiv.Perm (Fin 3)) (x : Fin 3 → C) :
    k335o8n_blockPerm (K := K) σ * k335o8n_psi (K := K) m x =
      k335o8n_psi (K := K) m (fun i => x (σ.symm i)) * k335o8n_blockPerm (K := K) σ := by
  apply LinearEquiv.ext; intro v
  refine Prod.ext (funext fun k => ?_) rfl
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, k335o8n_blockPerm_apply, k335o8n_psi_apply,
    k335o8n_blockPerm_apply, k335o8n_psi_apply]

private theorem k335o8n_factorization_sq_sub_one {q : ℕ} (h2 : 2 ≤ q) (hq : q % 3 = 2) :
    (q ^ 2 - 1).factorization 3 = (q + 1).factorization 3 := by
  have hq1 : ¬ 3 ∣ q - 1 := by
    intro hd
    have h0 : (q - 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
    omega
  rw [k335o7s_sq_sub_one q, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hq1, zero_add]

private theorem k335o8n_scalar_sq {K : Type} [Field K] {b c : K} {u : Kˣ}
    (hu : Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3 ⊕ Fin 2) u ∈
      StatedOmega (StatedQuadMinus 4 K b c)) : u ^ 2 = 1 := by
  have hiso := k335o7s_isometry_of_mem_statedOmega hu
  let v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K := Pi.single (.inr (.inr 0)) 1
  have hmul : ((Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3 ⊕ Fin 2) u :
      Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) *ᵥ v) =
      fun j => (u : K) * v j := by
    ext j
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have h := hiso v
  rw [hmul] at h
  have hL : StatedQuadMinus 4 K b c (fun j => (u : K) * v j) = (u : K) ^ 2 := by
    simp only [StatedQuadMinus]
    rw [Finset.sum_eq_zero (fun i _ => by simp [v])]
    simp [v]
  have hR : StatedQuadMinus 4 K b c v = 1 := by
    simp only [StatedQuadMinus]
    rw [Finset.sum_eq_zero (fun i _ => by simp [v])]
    simp [v]
  rw [hL, hR] at h
  exact Units.ext h

private theorem k335o8n_planeExtend_conj_psi {K : Type} [Field K] {C : Type} [Group C]
    (m : C →* (K × K) ≃ₗ[K] (K × K)) (j : Fin 3)
    (h : (K × K) ≃ₗ[K] (K × K)) (hh : ∀ t, h * m t * h⁻¹ = m t⁻¹) (x : Fin 3 → C) :
    planeExtend K j h * k335o8n_psi (K := K) m x * (planeExtend K j h)⁻¹ =
      k335o8n_psi (K := K) m (fun i => if i = j then (x i)⁻¹ else x i) := by
  apply LinearEquiv.ext; intro v
  refine Prod.ext (funext fun k => ?_) rfl
  simp only [LinearEquiv.mul_apply, ← map_inv, k335o8n_psi_apply, planeExtend_apply,
    Function.update_apply]
  by_cases hk : k = j
  · subst hk
    simp only [if_true]
    rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, hh]
  · simp only [if_neg hk]

end K335O8NAux

theorem k335_coord_omegaMinus8_nonsplit {X : Type} [Group X] {p f : ℕ}
    (h : LieModel X .POmegaMinus 4 p f) (hq : p ^ f % 3 = 2) :
    K335Coord X (((p ^ f) ^ 2 - 1).factorization 3) := by
  obtain ⟨hadm, K, hfield, hfinite, hK, b, c, hbc, ⟨e⟩⟩ :=
    h.statedClassicalModel_of_ne_zero (by norm_num)
  let : Field K := hfield
  let : Finite K := hfinite
  have : Fintype K := Fintype.ofFinite K
  have hp : p.Prime := hadm.1
  have : Fact p.Prime := ⟨hp⟩
  have hqK : Nat.card K % 3 = 2 := by rw [hK]; exact hq
  have hp3 : p ≠ 3 := k335_ne_three h (by omega)
  have h3K : (3 : K) ≠ 0 := three_ne_zero_of_card_eq (r := p) (f := f) hK hp3
  let : Fact (Irreducible (k335o8n_f K)) := ⟨k335o8n_irreducible K h3K hqK⟩
  let bE : Module.Basis (Fin 2) K (AdjoinRoot (k335o8n_f K)) :=
    (AdjoinRoot.powerBasis (k335o8n_f_ne_zero K)).basis.reindex
      (finCongr (by rw [AdjoinRoot.powerBasis_dim, k335o8n_natDegree_f]))
  have : Finite (AdjoinRoot (k335o8n_f K)) := finite_of_basis K _ bE
  have : Module.Finite K (AdjoinRoot (k335o8n_f K)) := Module.Finite.of_basis bE
  have : Algebra.IsAlgebraic K (AdjoinRoot (k335o8n_f K)) :=
    Algebra.IsAlgebraic.of_finite K _
  have hb0 : bE 0 = 1 := by
    simp only [bE, Module.Basis.reindex_apply, PowerBasis.coe_basis, AdjoinRoot.powerBasis_gen]
    rfl
  have hb1 : bE 1 ^ 2 + bE 1 + 1 = 0 := by
    have hroot : (AdjoinRoot.root (k335o8n_f K)) ^ 2 + AdjoinRoot.root (k335o8n_f K) + 1 = 0 := by
      have h : AdjoinRoot.mk (k335o8n_f K) (Polynomial.X ^ 2 + Polynomial.X + 1) = 0 := by
        rw [show (Polynomial.X ^ 2 + Polynomial.X + 1 : K[X]) = k335o8n_f K from rfl,
          AdjoinRoot.mk_self]
      have h1 : AdjoinRoot.mk (k335o8n_f K) (Polynomial.X ^ 2 + Polynomial.X + 1) =
          (AdjoinRoot.root (k335o8n_f K)) ^ 2 + AdjoinRoot.root (k335o8n_f K) + 1 := by
        simp only [map_add, map_pow, AdjoinRoot.mk_X, map_one]
      rw [h1] at h
      exact h
    have hb1' : bE 1 = AdjoinRoot.root (k335o8n_f K) := by
      simp only [bE, Module.Basis.reindex_apply, PowerBasis.coe_basis, AdjoinRoot.powerBasis_gen]
      simp
    rw [hb1', hroot]
  let C : Sylow 3 (normOne K (AdjoinRoot (k335o8n_f K))) := default
  let CG : CommGroup ↥C :=
    { (inferInstance : Group ↥C) with mul_comm := fun a b => Subtype.ext (mul_comm _ _) }
  have : Finite ↥C := inferInstance
  let a : ℕ := ((Nat.card K) ^ 2 - 1).factorization 3
  have hCcard : Nat.card ↥C = 3 ^ a := by
    have h1 : Nat.card ↥C =
        3 ^ Nat.factorization (Nat.card ↥(normOne K (AdjoinRoot (k335o8n_f K)))) 3 :=
      Sylow.card_eq_multiplicity C
    rw [h1, card_normOne K _ bE]
    congr 1
    dsimp only [a]
    exact (k335o8n_factorization_sq_sub_one (Finite.one_lt_card.trans_le (le_refl _)) hqK).symm
  have hCa : ∀ t : ↥C, t ^ (3 ^ a) = 1 := by
    intro t
    rw [← hCcard]
    exact (pow_card_eq_one' : t ^ Nat.card ↥C = 1)
  let m : ↥C →* (K × K) ≃ₗ[K] (K × K) :=
    (k335o8n_planeMul bE).comp
      ((normOne K (AdjoinRoot (k335o8n_f K))).subtype.comp
        (C : Subgroup (normOne K (AdjoinRoot (k335o8n_f K)))).subtype)
  have hm : ∀ t : ↥C, m t ∈ TauCeti.QuadraticMap.orthogonalGroup (rotForm K) := by
    intro t
    exact k335o8n_planeMul_mem bE hb0 hb1 ((t : ↥(normOne K (AdjoinRoot (k335o8n_f K)))).2)
  have hm_inj : Function.Injective m := by
    intro t s hts
    have h1 : (t : (AdjoinRoot (k335o8n_f K))ˣ) = (s : (AdjoinRoot (k335o8n_f K))ˣ) :=
      k335o8n_planeMul_injective bE hts
    exact Subtype.ext (Subtype.ext h1)
  let ψ : (Fin 3 → ↥C) →* (ModelSpace K ≃ₗ[K] ModelSpace K) := k335o8n_psi m
  have hψO : ∀ x : Fin 3 → ↥C, ψ x ∈ modelO b c := fun x =>
    k335o8n_psi_mem_modelO m hm b c x
  have hψΩ : ∀ x : Fin 3 → ↥C, ψ x ∈ modelOmega b c := fun x =>
    k335o8n_psi_mem_modelOmega h3K hbc m hm hCa x
  let φ : (Fin 3 → ↥C) →* ↥(modelOmega b c) := ψ.codRestrict (modelOmega b c) hψΩ
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    exact k335o8n_psi_injective m hm_inj (congrArg Subtype.val hxy)
  have hs3 : (k335o8n_blockPerm (K := K) k335psp_shift) ^ 3 = 1 := by
    change (k335o8n_blockPermHom (K := K) k335psp_shift) ^ 3 = 1
    rw [← map_pow, k335psp_shift_pow_three, map_one]
  let s : ↥(modelOmega b c) :=
    ⟨k335o8n_blockPerm (K := K) k335psp_shift,
      mem_modelOmega_of_odd h3K hbc (k335o8n_blockPerm_mem_modelO _ b c)
        (Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hs3))⟩
  have hs3' : s ^ 3 = 1 := by
    apply Subtype.ext
    change (k335o8n_blockPerm (K := K) k335psp_shift) ^ 3 = 1
    exact hs3
  have hs : ∀ x : Fin 3 → ↥C, s * φ x * s⁻¹ = φ (fun i => x (i - 1)) := by
    intro x
    apply Subtype.ext
    change k335o8n_blockPerm (K := K) k335psp_shift * ψ x *
        (k335o8n_blockPerm (K := K) k335psp_shift)⁻¹ = ψ (fun i => x (i - 1))
    rw [k335o8n_blockPerm_conj_psi, mul_assoc, mul_inv_cancel, mul_one]
    congr 1
  let F : (K × K) ≃ₗ[K] (K × K) := k335o8n_frob bE
  let g : ModelSpace K ≃ₗ[K] ModelSpace K := planeExtend K 0 F * planeExtend K 1 F
  have hFmem : F ∈ TauCeti.QuadraticMap.orthogonalGroup (rotForm K) :=
    k335o8n_frob_mem bE hb0 hb1
  have hFconj : ∀ t : ↥C, F * m t * F⁻¹ = m t⁻¹ := by
    intro t
    exact k335o8n_frob_conj_inv bE hb0 hb1
      ((t : ↥(normOne K (AdjoinRoot (k335o8n_f K)))).2)
  have hg_conj : ∀ c : ↥C, g * ψ (fun _ => c) * g⁻¹ = ψ ![c⁻¹, c⁻¹, c] := by
    intro c
    have h1 : planeExtend K 1 F * ψ (fun _ => c) * (planeExtend K 1 F)⁻¹ =
        ψ (fun i => if i = 1 then c⁻¹ else c) :=
      k335o8n_planeExtend_conj_psi m 1 F hFconj (fun _ => c)
    have h0 : planeExtend K 0 F * ψ (fun i => if i = 1 then c⁻¹ else c) *
        (planeExtend K 0 F)⁻¹ = ψ ![c⁻¹, c⁻¹, c] := by
      rw [k335o8n_planeExtend_conj_psi m 0 F hFconj (fun i => if i = 1 then c⁻¹ else c)]
      congr 1
      funext i
      fin_cases i <;> rfl
    calc g * ψ (fun _ => c) * g⁻¹
        = planeExtend K 0 F * (planeExtend K 1 F * ψ (fun _ => c) *
            (planeExtend K 1 F)⁻¹) * (planeExtend K 0 F)⁻¹ := by
          simp only [g]
          group
      _ = planeExtend K 0 F * ψ (fun i => if i = 1 then c⁻¹ else c) *
            (planeExtend K 0 F)⁻¹ := by rw [h1]
      _ = ψ ![c⁻¹, c⁻¹, c] := h0
  have hgΩ : g ∈ modelOmega b c := by
    have ha : planeExtend K 0 F ∈ modelO b c := planeExtend_mem_modelO 0 hFmem
    have hb : k335o8n_blockPerm (K := K) (Equiv.swap 0 1) ∈ modelO b c :=
      k335o8n_blockPerm_mem_modelO _ b c
    have hba : k335o8n_blockPerm (K := K) (Equiv.swap 0 1) * planeExtend K 0 F *
        (k335o8n_blockPerm (K := K) (Equiv.swap 0 1))⁻¹ = planeExtend K 1 F := by
      rw [k335o8n_blockPerm_conj_planeExtend, mul_assoc, mul_inv_cancel, mul_one]
      simp
    have hcomm : g = ⁅planeExtend K 0 F, k335o8n_blockPerm (K := K) (Equiv.swap 0 1)⁆ := by
      rw [commutatorElement_def]
      have h1 : k335o8n_blockPerm (K := K) (Equiv.swap 0 1) * (planeExtend K 0 F)⁻¹ *
          (k335o8n_blockPerm (K := K) (Equiv.swap 0 1))⁻¹ = (planeExtend K 1 F)⁻¹ := by
        have := congrArg (fun x => x⁻¹) hba
        simpa only [_root_.mul_inv_rev, inv_inv, mul_assoc] using this
      have h2 : (planeExtend K 1 F)⁻¹ = planeExtend K 1 F := by
        apply inv_eq_of_mul_eq_one_right
        rw [← map_mul, k335o8n_frob_sq bE hb0 hb1, map_one]
      rw [show planeExtend K 0 F * k335o8n_blockPerm (K := K) (Equiv.swap 0 1) *
          (planeExtend K 0 F)⁻¹ * (k335o8n_blockPerm (K := K) (Equiv.swap 0 1))⁻¹ =
          planeExtend K 0 F * (k335o8n_blockPerm (K := K) (Equiv.swap 0 1) *
            (planeExtend K 0 F)⁻¹ * (k335o8n_blockPerm (K := K) (Equiv.swap 0 1))⁻¹) from by
          group]
      rw [h1, h2]
    rw [hcomm]
    exact Subgroup.commutator_mem_commutator ha hb
  have hmove : ∀ d : ↥C, d ^ 3 = 1 → d ≠ 1 → ∃ g' : ↥(modelOmega b c), ∃ u : Fin 3 → ↥C,
      (∀ i, u i ∈ Subgroup.zpowers d) ∧ u 0 * u 1 * u 2 ≠ 1 ∧
        g' * φ (fun _ => d) * g'⁻¹ = φ u := by
    intro d hd3 hd1
    refine ⟨⟨g, hgΩ⟩, ![d⁻¹, d⁻¹, d], ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp
    · have hprod : (![d⁻¹, d⁻¹, d] : Fin 3 → ↥C) 0 * ![d⁻¹, d⁻¹, d] 1 *
          ![d⁻¹, d⁻¹, d] 2 = d⁻¹ := by
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]
        group
      rw [hprod]
      exact fun h => hd1 (inv_eq_one.mp h)
    · apply Subtype.ext
      change g * ψ (fun _ => d) * g⁻¹ = ψ ![d⁻¹, d⁻¹, d]
      exact hg_conj d
  have hModel : K335Coord ↥(modelOmega b c) a :=
    ⟨↥C, CG, inferInstance, hCcard, φ, hφ_inj, s, hs3', hs, hmove⟩
  have hH : K335Coord ↥(StatedOmega (StatedQuadMinus 4 K b c)) a :=
    K335Coord.of_mulEquiv (omegaEquiv (toModelIso h3K hbc)).symm hModel
  refine K335Coord.of_mulEquiv e.symm
    (k335_coord_statedProj ?_ (by simpa only [a, hK] using hH))
  refine CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf _ Nat.prime_three
    (by norm_num) (fun u hu => k335o8n_scalar_sq hu)

section K335L67Aux

open CFSG.ClassicalGroups.SLnThreeLocal

private def k335l67_shift : Equiv.Perm (Fin 3) where
  toFun i := i + 1
  invFun i := i - 1
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private theorem k335l67_shift_pow_three : k335l67_shift ^ 3 = 1 := by
  ext i
  fin_cases i <;> decide

private def k335l67_blkPerm (σ : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 2 × Fin 3) :=
  Equiv.prodCongrRight fun _ => σ⁻¹

private def k335l67_permGL (K : Type) [Field K] (σ : Equiv.Perm (Fin 3)) :
    GL (Fin 2 × Fin 3) K :=
  (Matrix.permMatrixHom (n := Fin 2 × Fin 3) (R := K)).toHomUnits (k335l67_blkPerm σ)

private theorem k335l67_coe_permGL (K : Type) [Field K] (σ : Equiv.Perm (Fin 3)) :
    ((k335l67_permGL K σ : GL (Fin 2 × Fin 3) K) :
        Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K) =
      ((k335l67_blkPerm σ)⁻¹).permMatrix K := rfl

private theorem k335l67_det_permGL (K : Type) [Field K] (σ : Equiv.Perm (Fin 3)) :
    ((k335l67_permGL K σ : GL (Fin 2 × Fin 3) K) :
        Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K).det = 1 := by
  rw [k335l67_coe_permGL, Matrix.det_permutation]
  simp [k335l67_blkPerm, Equiv.Perm.sign_prodCongrRight]

private lemma k335l67_prodCongrRight_mul {α β : Type*} (f g : α → Equiv.Perm β) :
    Equiv.prodCongrRight f * Equiv.prodCongrRight g =
      Equiv.prodCongrRight (f * g) := by
  apply Equiv.ext
  rintro ⟨a, b⟩
  rw [Equiv.Perm.mul_apply, Equiv.prodCongrRight_apply, Equiv.prodCongrRight_apply,
    Equiv.prodCongrRight_apply, Pi.mul_apply, Equiv.Perm.mul_apply]

private lemma k335l67_prodCongrRight_pow {α β : Type*} (f : α → Equiv.Perm β) (n : ℕ) :
    (Equiv.prodCongrRight f) ^ n = Equiv.prodCongrRight (fun a => (f a) ^ n) := by
  induction n with
  | zero =>
    apply Equiv.ext
    rintro ⟨a, b⟩
    rw [pow_zero, Equiv.prodCongrRight_apply, pow_zero]
    rfl
  | succ n ih =>
    rw [pow_succ, ih, k335l67_prodCongrRight_mul]
    congr 1
    funext a
    rw [Pi.mul_apply, pow_succ]

private theorem k335l67_blkPerm_shift_inv_pow_three :
    (k335l67_blkPerm k335l67_shift⁻¹) ^ 3 = 1 := by
  have h : k335l67_blkPerm k335l67_shift⁻¹ =
      Equiv.prodCongrRight (fun _ : Fin 2 => k335l67_shift) := rfl
  rw [h, k335l67_prodCongrRight_pow]
  apply Equiv.ext
  rintro ⟨a, b⟩
  rw [Equiv.prodCongrRight_apply, k335l67_shift_pow_three]
  rfl

private theorem k335l67_permGL_shift_inv_pow_three (K : Type) [Field K] :
    (k335l67_permGL K k335l67_shift⁻¹) ^ 3 = 1 := by
  unfold k335l67_permGL
  rw [← map_pow, k335l67_blkPerm_shift_inv_pow_three, map_one]

private theorem k335l67_permGL_mul_blockDiagGL (K : Type) [Field K]
    (σ : Equiv.Perm (Fin 3)) (M : Fin 3 → GL (Fin 2) K) :
    k335l67_permGL K σ * blockDiagGL K M =
      blockDiagGL K (fun i => M (σ i)) * k335l67_permGL K σ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, k335l67_coe_permGL, coe_blockDiagGL, coe_blockDiagGL,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext ⟨p, i⟩ ⟨q, j⟩
  simp [k335l67_blkPerm, Matrix.submatrix_apply, Matrix.blockDiagonal_apply, Equiv.Perm.inv_def,
    Equiv.eq_symm_apply]

private theorem k335l67_permGL_conj (K : Type) [Field K] (σ : Equiv.Perm (Fin 3))
    (M : Fin 3 → GL (Fin 2) K) :
    k335l67_permGL K σ * blockDiagGL K M * (k335l67_permGL K σ)⁻¹ =
      blockDiagGL K (fun i => M (σ i)) := by
  rw [k335l67_permGL_mul_blockDiagGL K σ M, mul_assoc, mul_inv_cancel, mul_one]

private theorem k335l67_core {X : Type} [Group X] {n p f : ℕ}
    (htor : ∀ {K : Type} [Field K] [Fintype K], ¬ 3 ∣ Nat.card K →
      ∃ T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K),
        (∀ x ∈ T, ∀ y ∈ T, x * y = y * x) ∧
        Nat.card T = 3 ^ ((Nat.card K ^ 2 - 1).factorization 3) ∧
        ∃ w : Matrix.SpecialLinearGroup (Fin 2) K, ∀ x ∈ T, w * x * w⁻¹ = x⁻¹)
    (h : LieModel X .PSL n p f) (hn : n = 6 ∨ n = 7) (hq : p ^ f % 3 = 2) :
    K335Coord X (((p ^ f) ^ 2 - 1).factorization 3) := by
  have hn0 : n ≠ 0 := by rcases hn with rfl | rfl <;> norm_num
  obtain ⟨hadm, K, hKfield, hKfin, hKcard, ⟨e⟩⟩ :=
    h.statedClassicalModel_of_ne_zero hn0
  let : Field K := hKfield
  let : Finite K := hKfin
  let : Fintype K := Fintype.ofFinite K
  have hpP : p.Prime := hadm.1
  have hp3 : p ≠ 3 := k335_ne_three h (by omega)
  have h3K : ¬ 3 ∣ Nat.card K := by
    rw [hKcard]
    exact k335_three_not_dvd hpP hp3
  obtain ⟨T, hTcomm, hTcard, w, hw⟩ := @htor K _ _ h3K
  let CG : CommGroup ↥T :=
    { (inferInstance : Group ↥T) with
      mul_comm := fun a b => Subtype.ext (hTcomm a a.2 b b.2) }
  let Φbig : (Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K) →* GL (Fin n) K :=
    (blkGL hn).comp (MonoidHom.compLeft Matrix.SpecialLinearGroup.toGL (Fin 3))
  have hΦbig : ∀ M : Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K,
      Φbig M ∈ StatedSL n K := by
    intro M
    apply blkGL_mem_statedSL
    refine Finset.prod_eq_one fun i _ => ?_
    exact Matrix.SpecialLinearGroup.det_coe (M i)
  let Φ : (Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K) →* ↥(StatedSL n K) :=
    Φbig.codRestrict (StatedSL n K) hΦbig
  have hΦinj : Function.Injective Φ := by
    intro M N hMN
    have h1 : Φbig M = Φbig N := congrArg Subtype.val hMN
    have h2 : (MonoidHom.compLeft Matrix.SpecialLinearGroup.toGL (Fin 3)) M =
        (MonoidHom.compLeft Matrix.SpecialLinearGroup.toGL (Fin 3)) N :=
      blkGL_injective hn h1
    funext i
    exact Matrix.SpecialLinearGroup.toGL_injective (congrFun h2 i)
  let coeHom : (Fin 3 → ↥T) →* (Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K) :=
    MonoidHom.compLeft (Subgroup.subtype T) (Fin 3)
  let φ : (Fin 3 → ↥T) →* ↥(StatedSL n K) := Φ.comp coeHom
  have hφinj : Function.Injective φ := hΦinj.comp (by
    intro x y hxy
    funext i
    exact Subtype.ext (congrFun hxy i))
  have hs_mem : embGL hn (k335l67_permGL K k335l67_shift⁻¹) ∈ StatedSL n K :=
    embGL_mem_statedSL hn _ (k335l67_det_permGL K k335l67_shift⁻¹)
  let s : ↥(StatedSL n K) :=
    ⟨embGL hn (k335l67_permGL K k335l67_shift⁻¹), hs_mem⟩
  have hs3 : s ^ 3 = 1 := by
    apply Subtype.ext
    show (embGL hn (k335l67_permGL K k335l67_shift⁻¹) : GL (Fin n) K) ^ 3 = 1
    rw [← map_pow, k335l67_permGL_shift_inv_pow_three, map_one]
  have hs_conj : ∀ M : Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K,
      s * Φ M * s⁻¹ = Φ (fun i => M (i - 1)) := by
    intro M
    apply Subtype.ext
    show (embGL hn (k335l67_permGL K k335l67_shift⁻¹) : GL (Fin n) K) *
        (embGL hn (blockDiagGL K (fun i => Matrix.SpecialLinearGroup.toGL (M i)))) *
        (embGL hn (k335l67_permGL K k335l67_shift⁻¹))⁻¹ =
      (embGL hn (blockDiagGL K (fun i => Matrix.SpecialLinearGroup.toGL (M (i - 1)))))
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    rw [k335l67_permGL_conj]
    rfl
  have hs : ∀ x : Fin 3 → ↥T, s * φ x * s⁻¹ = φ (fun i => x (i - 1)) := by
    intro x
    change s * Φ (fun i => (x i : Matrix.SpecialLinearGroup (Fin 2) K)) * s⁻¹ =
      Φ (fun i => (x (i - 1) : Matrix.SpecialLinearGroup (Fin 2) K))
    exact hs_conj (fun i => (x i : Matrix.SpecialLinearGroup (Fin 2) K))
  have hmove : ∀ c : ↥T, c ^ 3 = 1 → c ≠ 1 → ∃ g : ↥(StatedSL n K), ∃ u : Fin 3 → ↥T,
      (∀ i, u i ∈ Subgroup.zpowers c) ∧ u 0 * u 1 * u 2 ≠ 1 ∧
        g * φ (fun _ => c) * g⁻¹ = φ u := by
    intro c _hc3 hc1
    let u : Fin 3 → ↥T := fun i => if i = 2 then c else c⁻¹
    let gw : Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K := fun i => if i = 2 then 1 else w
    have hu_mem : ∀ i, u i ∈ Subgroup.zpowers c := by
      intro i
      fin_cases i <;> simp [u]
    have hu_prod : u 0 * u 1 * u 2 = c⁻¹ := by
      change c⁻¹ * c⁻¹ * c = c⁻¹
      group
    have hu_ne : u 0 * u 1 * u 2 ≠ 1 := by
      rw [hu_prod]
      exact fun h => hc1 (inv_eq_one.mp h)
    have harg : gw * (fun _ : Fin 3 => (c : Matrix.SpecialLinearGroup (Fin 2) K)) * gw⁻¹ =
        fun i => ((u i : ↥T) : Matrix.SpecialLinearGroup (Fin 2) K) := by
      funext i
      fin_cases i
      · change w * (c : Matrix.SpecialLinearGroup (Fin 2) K) * w⁻¹ = _
        rw [hw (c : Matrix.SpecialLinearGroup (Fin 2) K) c.2]
        rfl
      · change w * (c : Matrix.SpecialLinearGroup (Fin 2) K) * w⁻¹ = _
        rw [hw (c : Matrix.SpecialLinearGroup (Fin 2) K) c.2]
        rfl
      · change 1 * (c : Matrix.SpecialLinearGroup (Fin 2) K) * 1⁻¹ = _
        rw [one_mul, inv_one, mul_one]
        rfl
    refine ⟨Φ gw, u, hu_mem, hu_ne, ?_⟩
    change Φ gw * Φ (fun _ => c) * (Φ gw)⁻¹ =
      Φ (fun i => ((u i : ↥T) : Matrix.SpecialLinearGroup (Fin 2) K))
    rw [← map_inv, ← map_mul, ← map_mul, harg]
  have hcoord : K335Coord ↥(StatedSL n K) ((Nat.card K ^ 2 - 1).factorization 3) :=
    ⟨↥T, CG, inferInstance, hTcard, φ, hφinj, s, hs3, hs, hmove⟩
  have hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ StatedSL n K →
      c ^ (Nat.card K - 1) = 1 := fun c _ => by
    rw [← Nat.card_units]
    exact pow_card_eq_one'
  have hKmod : Nat.card K % 3 = 2 := by rwa [hKcard]
  have hpd : ¬ 3 ∣ Nat.card K - 1 := by
    intro hdvd
    have h0 : (Nat.card K - 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd hdvd
    have hle : 1 ≤ Nat.card K := Nat.card_pos
    have h1 : Nat.card K % 3 = 1 := by
      have hsub : Nat.card K = (Nat.card K - 1) + 1 := (Nat.sub_add_cancel hle).symm
      rw [hsub, Nat.add_mod, h0]
    omega
  have hproj : K335Coord (StatedProj (StatedSL n K))
      ((Nat.card K ^ 2 - 1).factorization 3) :=
    k335_coord_statedProj
      (CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf (StatedSL n K)
        Nat.prime_three hpd hd) hcoord
  have hX : K335Coord X ((Nat.card K ^ 2 - 1).factorization 3) :=
    K335Coord.of_mulEquiv e.symm hproj
  simpa only [hKcard] using hX

end K335L67Aux

theorem k335_coord_psl67 {X : Type} [Group X] {n p f : ℕ} (h : LieModel X .PSL n p f)
    (hn : n = 6 ∨ n = 7) (hq : p ^ f % 3 = 2) :
    K335Coord X (((p ^ f) ^ 2 - 1).factorization 3) :=
  k335l67_core k335_sl2_torus h hn hq

private lemma k335u67_reindexMap {ι κ : Type} [Fintype ι] {K : Type} [Field K] (e : ι ≃ κ)
    (φ : K → K) (A : Matrix ι ι K) :
    (Matrix.reindex e e A).map φ = Matrix.reindex e e (A.map φ) := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.map_apply]

private theorem k335u67_sq_sub_one (q : ℕ) : q ^ 2 - 1 = (q - 1) * (q + 1) := by
  symm
  have h1 : (q + 1) * (q - 1) = (q + 1) * q - (q + 1) := Nat.mul_sub_one (q + 1) q
  have h2 : (q + 1) * q = q * q + q := by rw [Nat.add_mul, one_mul]
  have h3 : q * q + q - (q + 1) = q * q - 1 := by omega
  rw [mul_comm, h1, h2, h3, sq]

private theorem k335u67_fact_sq_sub_one {q : ℕ} (hq2 : 2 ≤ q) (hq : q % 3 = 1) :
    (q ^ 2 - 1).factorization 3 = (q - 1).factorization 3 := by
  have hq1 : ¬ 3 ∣ q + 1 := by
    intro hd
    have h0 : (q + 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
    rw [Nat.add_mod, hq] at h0
    norm_num at h0
  rw [k335u67_sq_sub_one q, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hq1, add_zero]

private structure k335u67_TwoData (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime]
    [CharP K p] where
  u : K
  w : K
  hu : unitaryInvolution K p f u * u = -1
  hw : unitaryInvolution K p f w * w = 1
  hw1 : w ≠ 1

private theorem k335u67_TwoData.exists (K : Type) [Field K] [Finite K] (p f : ℕ)
    [Fact p.Prime] [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) :
    Nonempty (k335u67_TwoData K p f) := by
  obtain ⟨u, hu⟩ := CFSG.LieType.Universal.Unitary.exists_norm_eq_neg_one (F := K) hK
  obtain ⟨w, hw, hw1⟩ := CFSG.LieType.Universal.Unitary.exists_norm_eq_one_ne_one (F := K) hK
  exact ⟨⟨u, w, hu, hw, hw1⟩⟩

private lemma k335u67_TwoData.u_ne_zero {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] [CharP K p] (T : k335u67_TwoData K p f) : T.u ≠ 0 := by
  intro h
  have h1 : (0 : K) = -1 := by simpa [h] using T.hu
  exact one_ne_zero (neg_eq_zero.mp h1.symm)

private def k335u67_J (K : Type) [Field K] : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]

private lemma k335u67_J_mul_J (K : Type) [Field K] : k335u67_J K * k335u67_J K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [k335u67_J, Matrix.mul_apply, Fin.sum_univ_two]

private lemma k335u67_map_pow_eq_map {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (A : Matrix (Fin 2) (Fin 2) K) :
    A.map (· ^ (p ^ f)) = A.map (unitaryInvolution K p f) := by
  ext i j
  rfl

private def k335u67_Bmat {K : Type} [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p]
    (T : k335u67_TwoData K p f) : Matrix (Fin 2) (Fin 2) K :=
  !![1, (1 - T.w)⁻¹; T.u, (1 - T.w)⁻¹ * T.u * T.w]

private lemma k335u67_Bmat_det {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (T : k335u67_TwoData K p f) : (k335u67_Bmat p f T).det = -T.u := by
  have h : (1 : K) - T.w ≠ 0 := sub_ne_zero.mpr (Ne.symm T.hw1)
  rw [k335u67_Bmat, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  field_simp
  ring

private def k335u67_B {K : Type} [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p]
    (T : k335u67_TwoData K p f) : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero (k335u67_Bmat p f T) (by
    rw [k335u67_Bmat_det]
    exact neg_ne_zero.mpr T.u_ne_zero)

private lemma k335u67_B_coe {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (T : k335u67_TwoData K p f) :
    (k335u67_B p f T : Matrix (Fin 2) (Fin 2) K) = k335u67_Bmat p f T := rfl

private lemma k335u67_B_unitary {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (T : k335u67_TwoData K p f) :
    ((GeneralLinearGroup.map (unitaryInvolution K p f).toRingHom (k335u67_B p f T) : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)ᵀ * (k335u67_B p f T : Matrix (Fin 2) (Fin 2) K) =
      k335u67_J K := by
  have h1w : (1 : K) - T.w ≠ 0 := sub_ne_zero.mpr (Ne.symm T.hw1)
  have hu0 : T.u ≠ 0 := T.u_ne_zero
  have hw0 : T.w ≠ 0 := by
    intro h
    have hw := T.hw
    rw [h, mul_zero] at hw
    exact one_ne_zero hw.symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.GeneralLinearGroup.map_apply, Matrix.transpose_apply, Matrix.mul_apply,
      Fin.sum_univ_two, k335u67_B_coe, k335u67_Bmat, k335u67_J] <;>
    simp
  all_goals
    (try rw [show (iterateFrobenius K p f) T.u = -T.u⁻¹ from by field_simp [hu0]; exact T.hu])
    (try rw [show (iterateFrobenius K p f) T.w = T.w⁻¹ from by field_simp [hw0]; exact T.hw])
    (try field_simp [h1w, sub_ne_zero.mpr T.hw1])
    ring

private def k335u67_N {K : Type} [Field K] (c : Kˣ) : GL (Fin 2) K :=
  Units.mk !![(c : K), 0; 0, (c⁻¹ : Kˣ)] !![((c⁻¹ : Kˣ) : K), 0; 0, (c : K)]
    (by ext i j; fin_cases i <;> fin_cases j <;> simp)
    (by ext i j; fin_cases i <;> fin_cases j <;> simp)

private lemma k335u67_N_coe {K : Type} [Field K] (c : Kˣ) :
    (k335u67_N c : Matrix (Fin 2) (Fin 2) K) = !![(c : K), 0; 0, (c⁻¹ : Kˣ)] := rfl

private lemma k335u67_N_det {K : Type} [Field K] (c : Kˣ) :
    (k335u67_N c : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  rw [k335u67_N_coe, Matrix.det_fin_two]
  simp

private lemma k335u67_N_unitary {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (c : Kˣ) (hc : unitaryInvolution K p f (c : K) = (c : K)) :
    ((GeneralLinearGroup.map (unitaryInvolution K p f).toRingHom (k335u67_N c) : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)ᵀ * k335u67_J K * (k335u67_N c : Matrix (Fin 2) (Fin 2) K) =
      k335u67_J K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.GeneralLinearGroup.map_apply, Matrix.transpose_apply, Matrix.mul_apply,
      Fin.sum_univ_two, k335u67_N_coe, k335u67_J] <;>
    simp [hc]

private def k335u67_JGL (K : Type) [Field K] : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero (k335u67_J K) (by
    rw [k335u67_J, Matrix.det_fin_two]; norm_num)

private lemma k335u67_JGL_coe (K : Type) [Field K] :
    (k335u67_JGL K : Matrix (Fin 2) (Fin 2) K) = k335u67_J K := rfl

private lemma k335u67_JGL_mul_self (K : Type) [Field K] : k335u67_JGL K * k335u67_JGL K = 1 := by
  apply Units.ext
  rw [Units.val_mul, k335u67_JGL_coe, k335u67_J_mul_J, Units.val_one]

private lemma k335u67_JGL_inv (K : Type) [Field K] : (k335u67_JGL K)⁻¹ = k335u67_JGL K :=
  inv_eq_of_mul_eq_one_left (k335u67_JGL_mul_self K)

private lemma k335u67_JGL_det (K : Type) [Field K] :
    GeneralLinearGroup.det (k335u67_JGL K) = -1 := by
  apply Units.ext
  change (k335u67_JGL K : Matrix (Fin 2) (Fin 2) K).det = (-1 : K)
  rw [k335u67_JGL_coe, k335u67_J, Matrix.det_fin_two]
  norm_num

private def k335u67_star {K : Type} [Field K] (A : GL (Fin 2) K) : GL (Fin 2) K :=
  Units.mk (A : Matrix (Fin 2) (Fin 2) K)ᵀ
    (((A⁻¹ : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K)ᵀ
    (by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.transpose_one])
    (by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.transpose_one])

private lemma k335u67_star_coe {K : Type} [Field K] (A : GL (Fin 2) K) :
    (k335u67_star A : Matrix (Fin 2) (Fin 2) K) = (A : Matrix (Fin 2) (Fin 2) K)ᵀ := rfl

private lemma k335u67_star_mul {K : Type} [Field K] (A B : GL (Fin 2) K) :
    k335u67_star (A * B) = k335u67_star B * k335u67_star A := by
  apply Units.ext
  rw [k335u67_star_coe, Units.val_mul, Units.val_mul, k335u67_star_coe, k335u67_star_coe,
    Matrix.transpose_mul]

private lemma k335u67_star_inv {K : Type} [Field K] (A : GL (Fin 2) K) :
    k335u67_star A⁻¹ = (k335u67_star A)⁻¹ := by
  have h : k335u67_star A⁻¹ * k335u67_star A = 1 := by
    rw [← k335u67_star_mul, mul_inv_cancel]
    apply Units.ext
    rw [k335u67_star_coe, Units.val_one, Matrix.transpose_one]
  exact (inv_eq_of_mul_eq_one_left h).symm

private lemma k335u67_B_star {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (T : k335u67_TwoData K p f) :
    k335u67_star (GeneralLinearGroup.map (unitaryInvolution K p f).toRingHom (k335u67_B p f T)) *
        k335u67_B p f T = k335u67_JGL K := by
  apply Units.ext
  rw [Units.val_mul, k335u67_star_coe, k335u67_JGL_coe, k335u67_B_coe]
  exact k335u67_B_unitary T

private lemma k335u67_N_star {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (c : Kˣ) (hc : unitaryInvolution K p f (c : K) = (c : K)) :
    k335u67_star (GeneralLinearGroup.map (unitaryInvolution K p f).toRingHom (k335u67_N c)) *
        k335u67_JGL K * k335u67_N c = k335u67_JGL K := by
  apply Units.ext
  simp only [Units.val_mul, k335u67_star_coe, k335u67_JGL_coe, k335u67_N_coe]
  exact k335u67_N_unitary c hc

private lemma k335u67_JGL_star {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] :
    k335u67_star (GeneralLinearGroup.map (unitaryInvolution K p f).toRingHom (k335u67_JGL K)) =
      k335u67_JGL K := by
  apply Units.ext
  rw [k335u67_star_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k335u67_JGL_coe, k335u67_J]

private lemma k335u67_conj_star {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (B N J : GL (Fin 2) K)
    (hB : k335u67_star (GeneralLinearGroup.map (unitaryInvolution K p f).toRingHom B) * B = J)
    (hN : k335u67_star (GeneralLinearGroup.map (unitaryInvolution K p f).toRingHom N) * J * N = J)
    (hJ : J * J = 1) :
    k335u67_star (GeneralLinearGroup.map (unitaryInvolution K p f).toRingHom (B * N * B⁻¹)) *
      (B * N * B⁻¹) = 1 := by
  have hm : GeneralLinearGroup.map (unitaryInvolution K p f).toRingHom (B * N * B⁻¹) =
      GeneralLinearGroup.map (unitaryInvolution K p f).toRingHom B *
        GeneralLinearGroup.map (unitaryInvolution K p f).toRingHom N *
        (GeneralLinearGroup.map (unitaryInvolution K p f).toRingHom B)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  rw [hm, k335u67_star_mul, k335u67_star_mul, k335u67_star_inv]
  have hGb :
      (k335u67_star (GeneralLinearGroup.map (unitaryInvolution K p f).toRingHom B))⁻¹ = B * J := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, hB, hJ]
  rw [hGb]
  rw [show B * J * (k335u67_star (GeneralLinearGroup.map (unitaryInvolution K p f).toRingHom N) *
        k335u67_star (GeneralLinearGroup.map (unitaryInvolution K p f).toRingHom B)) *
        (B * N * B⁻¹) =
      B * J * k335u67_star (GeneralLinearGroup.map (unitaryInvolution K p f).toRingHom N) *
        (k335u67_star (GeneralLinearGroup.map (unitaryInvolution K p f).toRingHom B) * B) * N *
        B⁻¹ from by group]
  rw [hB]
  rw [show B * J * k335u67_star (GeneralLinearGroup.map (unitaryInvolution K p f).toRingHom N) *
        J * N * B⁻¹ =
      B * J * (k335u67_star (GeneralLinearGroup.map (unitaryInvolution K p f).toRingHom N) *
        J * N) * B⁻¹ from by group]
  rw [hN]
  rw [show B * J * J * B⁻¹ = B * (J * J) * B⁻¹ from by group]
  rw [hJ]
  group

private lemma k335u67_D_star {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (T : k335u67_TwoData K p f) (c : Kˣ)
    (hc : unitaryInvolution K p f (c : K) = (c : K)) :
    k335u67_star (GeneralLinearGroup.map (unitaryInvolution K p f).toRingHom
        (k335u67_B p f T * k335u67_N c * (k335u67_B p f T)⁻¹)) *
      (k335u67_B p f T * k335u67_N c * (k335u67_B p f T)⁻¹) = 1 :=
  k335u67_conj_star (k335u67_B p f T) (k335u67_N c) (k335u67_JGL K)
    (k335u67_B_star T) (k335u67_N_star c hc) (k335u67_JGL_mul_self K)

private lemma k335u67_map_coe {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (A : GL (Fin 2) K) :
    ((GeneralLinearGroup.map (unitaryInvolution K p f).toRingHom A : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) =
      (A : Matrix (Fin 2) (Fin 2) K).map (unitaryInvolution K p f) := rfl

private lemma k335u67_D_unitary {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (T : k335u67_TwoData K p f) (c : Kˣ)
    (hc : unitaryInvolution K p f (c : K) = (c : K)) :
    (((k335u67_B p f T * k335u67_N c * (k335u67_B p f T)⁻¹ : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K).map (· ^ (p ^ f)))ᵀ *
      (k335u67_B p f T * k335u67_N c * (k335u67_B p f T)⁻¹ : GL (Fin 2) K) = 1 := by
  have h := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K))
    (k335u67_D_star T c hc)
  rw [k335u67_map_pow_eq_map]
  simpa only [Units.val_mul, Units.val_one, k335u67_star_coe, k335u67_map_coe] using h

private def k335u67_Xs {K : Type} [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p]
    (T : k335u67_TwoData K p f) : GL (Fin 2) K :=
  k335u67_B p f T * k335u67_JGL K * (k335u67_B p f T)⁻¹

private lemma k335u67_Xs_star {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (T : k335u67_TwoData K p f) :
    k335u67_star (GeneralLinearGroup.map (unitaryInvolution K p f).toRingHom (k335u67_Xs p f T)) *
      k335u67_Xs p f T = 1 := by
  rw [k335u67_Xs]
  exact k335u67_conj_star (k335u67_B p f T) (k335u67_JGL K) (k335u67_JGL K)
    (k335u67_B_star T)
    (by rw [k335u67_JGL_star, k335u67_JGL_mul_self, one_mul])
    (k335u67_JGL_mul_self K)

private lemma k335u67_Xs_unitary {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (T : k335u67_TwoData K p f) :
    (((k335u67_Xs p f T : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map (· ^ (p ^ f)))ᵀ *
      (k335u67_Xs p f T : Matrix (Fin 2) (Fin 2) K) = 1 := by
  have h := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K))
    (k335u67_Xs_star T)
  rw [k335u67_map_pow_eq_map]
  simpa only [Units.val_mul, Units.val_one, k335u67_star_coe, k335u67_map_coe] using h

private lemma k335u67_Xs_det {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (T : k335u67_TwoData K p f) :
    (k335u67_Xs p f T : Matrix (Fin 2) (Fin 2) K).det = -1 := by
  have h : Matrix.GeneralLinearGroup.det (k335u67_Xs p f T) = -1 := by
    rw [k335u67_Xs, map_mul, map_mul, map_inv, k335u67_JGL_det]
    rw [mul_comm (Matrix.GeneralLinearGroup.det (k335u67_B p f T)) (-1), mul_assoc,
      mul_inv_cancel, mul_one]
  simpa [Matrix.GeneralLinearGroup.det] using congrArg (fun u : Kˣ => (u : K)) h

private lemma k335u67_Xs_conj {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (T : k335u67_TwoData K p f) (c : Kˣ) :
    k335u67_Xs p f T * (k335u67_B p f T * k335u67_N c * (k335u67_B p f T)⁻¹) *
        (k335u67_Xs p f T)⁻¹ =
      k335u67_B p f T * k335u67_N c⁻¹ * (k335u67_B p f T)⁻¹ := by
  have hJN : k335u67_JGL K * k335u67_N c * (k335u67_JGL K)⁻¹ = k335u67_N c⁻¹ := by
    rw [k335u67_JGL_inv]
    apply Units.ext
    simp only [Units.val_mul, k335u67_JGL_coe, k335u67_N_coe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [k335u67_J, Matrix.mul_apply, Fin.sum_univ_two]
  rw [k335u67_Xs]
  rw [show (k335u67_B p f T * k335u67_JGL K * (k335u67_B p f T)⁻¹) *
        (k335u67_B p f T * k335u67_N c * (k335u67_B p f T)⁻¹) *
        (k335u67_B p f T * k335u67_JGL K * (k335u67_B p f T)⁻¹)⁻¹ =
      k335u67_B p f T * (k335u67_JGL K * k335u67_N c * (k335u67_JGL K)⁻¹) *
        (k335u67_B p f T)⁻¹ from by group]
  rw [hJN]

private lemma k335u67_N_one {K : Type} [Field K] : k335u67_N (1 : Kˣ) = 1 := by
  apply Units.ext
  rw [k335u67_N_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private lemma k335u67_N_mul {K : Type} [Field K] (c d : Kˣ) :
    k335u67_N (c * d) = k335u67_N c * k335u67_N d := by
  apply Units.ext
  simp only [k335u67_N_coe, Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, mul_comm]

private lemma k335u67_D_det {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (T : k335u67_TwoData K p f) (c : Kˣ) :
    (k335u67_B p f T * k335u67_N c * (k335u67_B p f T)⁻¹ :
      Matrix (Fin 2) (Fin 2) K).det = 1 := by
  have hNdet : Matrix.GeneralLinearGroup.det (k335u67_N c) = 1 := by
    apply Units.ext
    exact k335u67_N_det c
  have h : Matrix.GeneralLinearGroup.det
      (k335u67_B p f T * k335u67_N c * (k335u67_B p f T)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, hNdet]
    group
  simpa [Matrix.GeneralLinearGroup.det] using congrArg (fun u : Kˣ => (u : K)) h

private def k335u67_bdHom {K : Type} [Field K] :
    (Fin 3 → GL (Fin 2) K) →* GL (Fin 2 × Fin 3) K :=
  (Units.map (Matrix.blockDiagonalRingHom (Fin 2) (Fin 3) K).toMonoidHom).comp
    (MulEquiv.piUnits.symm.toMonoidHom)

private lemma k335u67_bd_coe {K : Type} [Field K] (A : Fin 3 → GL (Fin 2) K) :
    (k335u67_bdHom A : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K) =
      Matrix.blockDiagonal (fun i => (A i : Matrix (Fin 2) (Fin 2) K)) := rfl

private lemma k335u67_N_injective {K : Type} [Field K] :
    Function.Injective (k335u67_N (K := K)) := by
  intro c d h
  have h1 := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
  rw [k335u67_N_coe, k335u67_N_coe] at h1
  simp at h1
  exact Units.ext h1

private lemma k335u67_D_inj {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (T : k335u67_TwoData K p f) :
    Function.Injective (fun c : Kˣ => k335u67_B p f T * k335u67_N c * (k335u67_B p f T)⁻¹) := by
  intro c d h
  have h1 : k335u67_B p f T * k335u67_N c = k335u67_B p f T * k335u67_N d :=
    mul_right_cancel h
  exact k335u67_N_injective (mul_left_cancel h1)

section K335U67Aux

open CFSG.ClassicalGroups.SLnThreeLocal

private lemma k335u67_permMatrix_map_pow {K : Type} [Field K] {q : ℕ} (hq : q ≠ 0)
    (π : Equiv.Perm (Fin 2 × Fin 3)) :
    ((π.permMatrix K).map (· ^ q)) = π.permMatrix K := by
  ext i j
  rw [Matrix.map_apply]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  split <;> simp [zero_pow hq]

private lemma k335u67_permGL_mem {K : Type} [Field K] {q : ℕ} (hq : q ≠ 0) :
    k335l67_permGL K k335l67_shift⁻¹ ∈
      CFSG.MatrixModel.unitaryCore (Fin 2 × Fin 3) K q := by
  apply Subgroup.subset_closure
  refine ⟨k335l67_det_permGL K k335l67_shift⁻¹, ?_⟩
  rw [k335l67_coe_permGL, k335u67_permMatrix_map_pow hq, Matrix.transpose_permMatrix,
    ← Matrix.permMatrix_mul]
  simp

private lemma k335u67_bdHom_injective {K : Type} [Field K] :
    Function.Injective (k335u67_bdHom (K := K)) := by
  intro M N h
  have h1 := congrArg
    (fun g : GL (Fin 2 × Fin 3) K => (g : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K)) h
  rw [k335u67_bd_coe, k335u67_bd_coe] at h1
  have h2 := Matrix.blockDiagonal_injective h1
  funext i
  exact Units.ext (congrFun h2 i)

private lemma k335u67_bdHom_conj {K : Type} [Field K] (σ : Equiv.Perm (Fin 3))
    (M : Fin 3 → GL (Fin 2) K) :
    k335l67_permGL K σ * k335u67_bdHom M * (k335l67_permGL K σ)⁻¹ =
      k335u67_bdHom (fun i => M (σ i)) :=
  k335l67_permGL_conj K σ M

private lemma k335u67_bd_mem_prod_det {K : Type} [Field K] {q : ℕ} (hq : q ≠ 0)
    (A : Fin 3 → GL (Fin 2) K)
    (hdet : ∏ i, (A i : Matrix (Fin 2) (Fin 2) K).det = 1)
    (huni : ∀ i, (((A i : Matrix (Fin 2) (Fin 2) K).map (· ^ q))ᵀ) *
      (A i : Matrix (Fin 2) (Fin 2) K) = 1) :
    k335u67_bdHom A ∈ CFSG.MatrixModel.unitaryCore (Fin 2 × Fin 3) K q := by
  apply Subgroup.subset_closure
  rw [Set.mem_setOf_eq, k335u67_bd_coe]
  have hmap : (Matrix.blockDiagonal fun i => (A i : Matrix (Fin 2) (Fin 2) K)).map (· ^ q) =
      Matrix.blockDiagonal (fun i => ((A i : Matrix (Fin 2) (Fin 2) K)).map (· ^ q)) :=
    Matrix.blockDiagonal_map (M := fun i => (A i : Matrix (Fin 2) (Fin 2) K)) (f := (· ^ q))
      (by cases q with
          | zero => exact absurd rfl hq
          | succ q => simp)
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_blockDiagonal]
    exact hdet
  · rw [hmap, Matrix.blockDiagonal_transpose, ← Matrix.blockDiagonal_mul]
    have : (fun i => (((A i : Matrix (Fin 2) (Fin 2) K).map (· ^ q))ᵀ) *
        (A i : Matrix (Fin 2) (Fin 2) K)) = fun _ => (1 : Matrix (Fin 2) (Fin 2) K) := by
      funext i
      exact huni i
    rw [this]
    exact Matrix.blockDiagonal_one

private def k335u67_Dhom {K : Type} [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p]
    (T : k335u67_TwoData K p f) : Kˣ →* GL (Fin 2) K where
  toFun c := k335u67_B p f T * k335u67_N c * (k335u67_B p f T)⁻¹
  map_one' := by rw [k335u67_N_one, mul_one, mul_inv_cancel]
  map_mul' c d := by rw [k335u67_N_mul]; group

private lemma k335u67_embMat_map_pow {K : Type} [Field K] {n q : ℕ} (hn : n = 6 ∨ n = 7)
    (hq : q ≠ 0) (X : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K) :
    (embMat hn X).map (· ^ q) = embMat hn (X.map (· ^ q)) := by
  simp only [embMat, k335u67_reindexMap, Matrix.fromBlocks_map]
  rw [Matrix.map_zero (f := (· ^ q)) (zero_pow hq),
    Matrix.map_one (f := (· ^ q)) (zero_pow hq) (one_pow q),
    Matrix.map_zero (f := (· ^ q)) (zero_pow hq)]

private lemma k335u67_embMat_transpose {K : Type} [Field K] {n : ℕ} (hn : n = 6 ∨ n = 7)
    (X : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K) :
    (embMat hn X)ᵀ = embMat hn Xᵀ := by
  simp only [embMat, Matrix.transpose_reindex, Matrix.fromBlocks_transpose]
  simp

private lemma k335u67_embGL_le {K : Type} [Field K] [Fintype K] {q : ℕ} (hq : q ≠ 0)
    {n : ℕ} (hn : n = 6 ∨ n = 7) :
    CFSG.MatrixModel.unitaryCore (Fin 2 × Fin 3) K q ≤
      (CFSG.MatrixModel.unitaryCore (Fin n) K q).comap (embGL hn) := by
  rw [CFSG.MatrixModel.unitaryCore, Subgroup.closure_le]
  intro A hA
  obtain ⟨hdet, huni⟩ := hA
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · rw [coe_embGL, det_embMat]
    exact hdet
  · rw [coe_embGL, k335u67_embMat_map_pow hn hq, k335u67_embMat_transpose hn,
      ← embMat_mul, huni, embMat_one]

private theorem k335u67_core {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 3 = 1) (hf : 1 ≤ f) :
    K335Coord ↥(CFSG.MatrixModel.unitaryCore (Fin 2 × Fin 3) K (p ^ f))
      (((p ^ f) ^ 2 - 1).factorization 3) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T⟩ := k335u67_TwoData.exists K p f hK
  have hq0 : p ^ f ≠ 0 := pow_ne_zero f (Fact.out : p.Prime).ne_zero
  have hq2 : 2 ≤ p ^ f := by
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    calc 2 ≤ p := hp2
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right (by omega) hf
  let C : Sylow 3 Kˣ := Sylow.nonempty.some
  let a : ℕ := ((p ^ f) ^ 2 - 1).factorization 3
  have hCcard : Nat.card ↥C = 3 ^ a := by
    have h1 : (Nat.card Kˣ).factorization 3 = a := by
      rw [Nat.card_units, hK]
    have h := Sylow.card_eq_multiplicity C
    rw [h1] at h
    exact h
  have haeq : a = (p ^ f - 1).factorization 3 := k335u67_fact_sq_sub_one hq2 hq
  have h3dvd : 3 ^ a ∣ p ^ f - 1 := by
    rw [haeq]
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (by omega)).mpr le_rfl
  have hpow : ∀ c : ↥C, (c : Kˣ) ^ (p ^ f - 1) = 1 := by
    intro c
    obtain ⟨k, hk⟩ := h3dvd
    have hc : (c : Kˣ) ^ Nat.card ↥C = 1 := by
      show ((c ^ Nat.card ↥C : ↥C) : Kˣ) = ((1 : ↥C) : Kˣ)
      rw [pow_card_eq_one']
    rw [hCcard] at hc
    calc (c : Kˣ) ^ (p ^ f - 1) = (c : Kˣ) ^ (3 ^ a * k) := by rw [hk]
      _ = ((c : Kˣ) ^ 3 ^ a) ^ k := by rw [pow_mul]
      _ = 1 := by rw [hc, one_pow]
  have hcq : ∀ c : ↥C, (c : Kˣ) ^ (p ^ f) = (c : Kˣ) := by
    intro c
    have h1 : (c : Kˣ) ^ (p ^ f - 1) = 1 := hpow c
    calc (c : Kˣ) ^ (p ^ f) = (c : Kˣ) ^ ((p ^ f - 1) + 1) := by
          rw [Nat.sub_add_cancel (by omega : 1 ≤ p ^ f)]
      _ = (c : Kˣ) ^ (p ^ f - 1) * (c : Kˣ) := pow_succ _ _
      _ = 1 * (c : Kˣ) := by rw [h1]
      _ = (c : Kˣ) := one_mul _
  have hfix : ∀ c : ↥C, unitaryInvolution K p f ((c : Kˣ) : K) = ((c : Kˣ) : K) := by
    intro c
    rw [unitaryInvolution_apply]
    simpa using congrArg (fun u : Kˣ => (u : K)) (hcq c)
  let Dhom : ↥C →* GL (Fin 2) K :=
    { toFun := fun c => k335u67_B p f T * k335u67_N (c : Kˣ) * (k335u67_B p f T)⁻¹
      map_one' := by rw [Submonoid.coe_one, k335u67_N_one, mul_one, mul_inv_cancel]
      map_mul' := by intro c d; rw [Submonoid.coe_mul, k335u67_N_mul]; group }
  let φbig : (Fin 3 → ↥C) →* GL (Fin 2 × Fin 3) K :=
    (k335u67_bdHom (K := K)).comp (MonoidHom.compLeft Dhom (Fin 3))
  have hφbig : ∀ x : Fin 3 → ↥C, φbig x ∈
      CFSG.MatrixModel.unitaryCore (Fin 2 × Fin 3) K (p ^ f) := by
    intro x
    change k335u67_bdHom (fun i => Dhom (x i)) ∈
      CFSG.MatrixModel.unitaryCore (Fin 2 × Fin 3) K (p ^ f)
    apply k335u67_bd_mem_prod_det (q := p ^ f) hq0 (fun i => Dhom (x i))
    · exact Finset.prod_eq_one fun i _ => k335u67_D_det T (x i : Kˣ)
    · intro i
      exact k335u67_D_unitary T (x i : Kˣ) (hfix (x i))
  let φ : (Fin 3 → ↥C) →* ↥(CFSG.MatrixModel.unitaryCore (Fin 2 × Fin 3) K (p ^ f)) :=
    φbig.codRestrict _ hφbig
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have h1 : φbig x = φbig y := congrArg Subtype.val hxy
    have h2 : MonoidHom.compLeft Dhom (Fin 3) x = MonoidHom.compLeft Dhom (Fin 3) y :=
      k335u67_bdHom_injective h1
    funext i
    exact Subtype.ext (k335u67_D_inj T (congrFun h2 i))
  have hs_mem : k335l67_permGL K k335l67_shift⁻¹ ∈
      CFSG.MatrixModel.unitaryCore (Fin 2 × Fin 3) K (p ^ f) :=
    k335u67_permGL_mem hq0
  let s : ↥(CFSG.MatrixModel.unitaryCore (Fin 2 × Fin 3) K (p ^ f)) :=
    ⟨k335l67_permGL K k335l67_shift⁻¹, hs_mem⟩
  have hs3 : s ^ 3 = 1 := by
    apply Subtype.ext
    show (k335l67_permGL K k335l67_shift⁻¹ : GL (Fin 2 × Fin 3) K) ^ 3 = 1
    exact k335l67_permGL_shift_inv_pow_three K
  have hs : ∀ x : Fin 3 → ↥C, s * φ x * s⁻¹ = φ (fun i => x (i - 1)) := by
    intro x
    apply Subtype.ext
    change k335l67_permGL K k335l67_shift⁻¹ * k335u67_bdHom ((MonoidHom.compLeft Dhom (Fin 3)) x) *
        (k335l67_permGL K k335l67_shift⁻¹)⁻¹ =
      k335u67_bdHom ((MonoidHom.compLeft Dhom (Fin 3)) (fun i => x (i - 1)))
    rw [k335u67_bdHom_conj]
    rfl
  have hmove : ∀ c : ↥C, c ^ 3 = 1 → c ≠ 1 →
      ∃ g : ↥(CFSG.MatrixModel.unitaryCore (Fin 2 × Fin 3) K (p ^ f)), ∃ u : Fin 3 → ↥C,
        (∀ i, u i ∈ Subgroup.zpowers c) ∧ u 0 * u 1 * u 2 ≠ 1 ∧
          g * φ (fun _ => c) * g⁻¹ = φ u := by
    intro c _hc3 hc1
    let u : Fin 3 → ↥C := fun i => if i = 2 then c else c⁻¹
    let gw : Fin 3 → GL (Fin 2) K := fun i => if i = 2 then 1 else k335u67_Xs p f T
    have hgw_det : ∏ i, (gw i : Matrix (Fin 2) (Fin 2) K).det = 1 := by
      rw [Fin.prod_univ_three]
      simp [gw, k335u67_Xs_det]
    have hgw_uni : ∀ i, (((gw i : Matrix (Fin 2) (Fin 2) K).map (· ^ (p ^ f)))ᵀ) *
        (gw i : Matrix (Fin 2) (Fin 2) K) = 1 := by
      intro i
      fin_cases i <;> simp [gw, k335u67_Xs_unitary, zero_pow hq0]
    have hgw_mem : k335u67_bdHom gw ∈
        CFSG.MatrixModel.unitaryCore (Fin 2 × Fin 3) K (p ^ f) :=
      k335u67_bd_mem_prod_det hq0 gw hgw_det hgw_uni
    refine ⟨⟨k335u67_bdHom gw, hgw_mem⟩, u, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [u]
    · have hprod : u 0 * u 1 * u 2 = c⁻¹ := by
        change c⁻¹ * c⁻¹ * c = c⁻¹
        group
      rw [hprod]
      exact fun h => hc1 (inv_eq_one.mp h)
    · have hconj : gw * (fun _ : Fin 3 => Dhom c) * gw⁻¹ = fun i => Dhom (u i) := by
        funext i
        fin_cases i
        · change k335u67_Xs p f T * (k335u67_B p f T * k335u67_N (c : Kˣ) *
              (k335u67_B p f T)⁻¹) * (k335u67_Xs p f T)⁻¹ = Dhom (u 0)
          rw [k335u67_Xs_conj]
          rfl
        · change k335u67_Xs p f T * (k335u67_B p f T * k335u67_N (c : Kˣ) *
              (k335u67_B p f T)⁻¹) * (k335u67_Xs p f T)⁻¹ = Dhom (u 1)
          rw [k335u67_Xs_conj]
          rfl
        · change (1 : GL (Fin 2) K) * (k335u67_B p f T * k335u67_N (c : Kˣ) *
              (k335u67_B p f T)⁻¹) * (1 : GL (Fin 2) K)⁻¹ = Dhom (u 2)
          rw [one_mul, inv_one, mul_one]
          rfl
      have hgl : k335u67_bdHom gw * k335u67_bdHom (fun _ => Dhom c) * (k335u67_bdHom gw)⁻¹ =
          k335u67_bdHom (fun i => Dhom (u i)) := by
        rw [← map_inv, ← map_mul, ← map_mul, hconj]
      apply Subtype.ext
      change k335u67_bdHom gw * k335u67_bdHom (fun _ => Dhom c) * (k335u67_bdHom gw)⁻¹ =
        k335u67_bdHom (fun i => Dhom (u i))
      exact hgl
  exact ⟨↥C, Subgroup.toCommGroup (C : Subgroup Kˣ), inferInstance, hCcard, φ, hφinj, s,
    hs3, hs, hmove⟩

private theorem k335u67_coord_SU {K : Type} [Field K] [Fintype K] {p f : ℕ} [Fact p.Prime]
    (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 3 = 1) (hf : 1 ≤ f) {n : ℕ}
    (hn : n = 6 ∨ n = 7) :
    K335Coord ↥(CFSG.MatrixModel.unitaryCore (Fin n) K (p ^ f))
      (((p ^ f) ^ 2 - 1).factorization 3) := by
  have : CharP K p := charP_of_card_eq_prime_pow (p := p) (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcore := k335u67_core (K := K) hK hq hf
  have hq0 : p ^ f ≠ 0 := pow_ne_zero f (Fact.out : p.Prime).ne_zero
  have hle := k335u67_embGL_le (K := K) (q := p ^ f) hq0 hn
  let ψ : ↥(CFSG.MatrixModel.unitaryCore (Fin 2 × Fin 3) K (p ^ f)) →*
      ↥(CFSG.MatrixModel.unitaryCore (Fin n) K (p ^ f)) :=
    ((embGL hn).comp (Subgroup.subtype _)).codRestrict _ (fun A => hle A.2)
  have hψinj : Function.Injective ψ := by
    intro A B h
    apply Subtype.ext
    have h1 : (embGL hn (A : GL (Fin 2 × Fin 3) K) : GL (Fin n) K) = embGL hn B :=
      congrArg Subtype.val h
    exact embGL_injective hn h1
  refine K335Coord.map ψ ?_ hcore
  have hker : ψ.ker = ⊥ := ψ.ker_eq_bot_iff.mpr hψinj
  rw [hker, Subgroup.card_bot]
  norm_num

end K335U67Aux

theorem k335_coord_psu67 {X : Type} [Group X] {n p f : ℕ} (h : LieModel X .PSU n p f)
    (hn : n = 6 ∨ n = 7) (hq : p ^ f % 3 = 1) :
    K335Coord X (((p ^ f) ^ 2 - 1).factorization 3) := by
  have hn0 : n ≠ 0 := by rcases hn with rfl | rfl <;> norm_num
  obtain ⟨hadm, K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero hn0
  let : Field K := hKfield
  let : Finite K := hKfin
  let : Fintype K := Fintype.ofFinite K
  have hpP : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have : Fact p.Prime := ⟨hpP⟩
  have hd3 : ¬ 3 ∣ p ^ f + 1 := by
    intro hd
    have h0 : (p ^ f + 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
    rw [Nat.add_mod, hq] at h0
    norm_num at h0
  have hcoord := k335u67_coord_SU (K := K) hKcard hq hf hn
  have hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin n) c ∈
      CFSG.Open.StatedSU n (p ^ f) K → c ^ (p ^ f + 1) = 1 := fun c hc =>
    (CFSG.LinearGroups.scalar_mem_statedSU_iff hpP hKcard (by omega) c).mp hc |>.2
  have hproj : K335Coord (CFSG.Open.StatedProj (CFSG.Open.StatedSU n (p ^ f) K))
      (((p ^ f) ^ 2 - 1).factorization 3) :=
    k335_coord_statedProj
      (CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf
        (CFSG.Open.StatedSU n (p ^ f) K) Nat.prime_three hd3 hd) hcoord
  exact K335Coord.of_mulEquiv e.symm hproj

section K335L4Aux

private def k335l4_σ : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2

private theorem k335l4_σ_pow_three : k335l4_σ ^ 3 = 1 := by
  ext i
  fin_cases i <;> decide

private theorem k335l4_σ_sign : Equiv.Perm.sign k335l4_σ = 1 := by
  decide

@[simp] private theorem k335l4_σ_inv_zero : k335l4_σ⁻¹ 0 = 2 := by decide
@[simp] private theorem k335l4_σ_inv_one : k335l4_σ⁻¹ 1 = 0 := by decide
@[simp] private theorem k335l4_σ_inv_two : k335l4_σ⁻¹ 2 = 1 := by decide
@[simp] private theorem k335l4_σ_inv_three : k335l4_σ⁻¹ 3 = 3 := by decide

private def k335l4_dφ {K : Type} [Field K] {C : Subgroup Kˣ} (x : Fin 3 → C) : Fin 4 → Kˣ :=
  ![(x 0 : Kˣ), (x 1 : Kˣ), (x 2 : Kˣ), ((x 0 : Kˣ) * (x 1 : Kˣ) * (x 2 : Kˣ))⁻¹]

@[simp] private theorem k335l4_dφ_apply_zero {K : Type} [Field K] {C : Subgroup Kˣ}
    (x : Fin 3 → C) : k335l4_dφ x 0 = (x 0 : Kˣ) := rfl
@[simp] private theorem k335l4_dφ_apply_one {K : Type} [Field K] {C : Subgroup Kˣ}
    (x : Fin 3 → C) : k335l4_dφ x 1 = (x 1 : Kˣ) := rfl
@[simp] private theorem k335l4_dφ_apply_two {K : Type} [Field K] {C : Subgroup Kˣ}
    (x : Fin 3 → C) : k335l4_dφ x 2 = (x 2 : Kˣ) := rfl
@[simp] private theorem k335l4_dφ_apply_three {K : Type} [Field K] {C : Subgroup Kˣ}
    (x : Fin 3 → C) :
    k335l4_dφ x 3 = ((x 0 : Kˣ) * (x 1 : Kˣ) * (x 2 : Kˣ))⁻¹ := rfl

private def k335l4_dφHom {K : Type} [Field K] {C : Subgroup Kˣ} :
    (Fin 3 → C) →* (Fin 4 → Kˣ) where
  toFun := k335l4_dφ
  map_one' := by
    funext i
    fin_cases i <;> simp [k335l4_dφ]
  map_mul' x y := by
    funext i
    fin_cases i <;>
      simp [k335l4_dφ, Pi.mul_apply, _root_.mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]

private theorem k335l4_dφ_mem {K : Type} [Field K] {C : Subgroup Kˣ} (x : Fin 3 → C) :
    diagGL (k335l4_dφHom x) ∈ CFSG.Open.StatedSL 4 K := by
  apply CFSG.Open.StatedAPI.mem_statedSL_of_det
  rw [coe_diagGL, Matrix.det_diagonal]
  have hprod : (∏ i : Fin 4, k335l4_dφHom x i) = 1 := by
    rw [Fin.prod_univ_four]
    change (x 0 : Kˣ) * (x 1 : Kˣ) * (x 2 : Kˣ) *
      ((x 0 : Kˣ) * (x 1 : Kˣ) * (x 2 : Kˣ))⁻¹ = 1
    exact mul_inv_cancel _
  calc (∏ i : Fin 4, ((k335l4_dφHom x i : Kˣ) : K))
      = ((∏ i : Fin 4, k335l4_dφHom x i : Kˣ) : K) := (Units.coe_prod _ _).symm
    _ = 1 := by rw [hprod, Units.val_one]

private theorem k335l4_dφ_injective {K : Type} [Field K] {C : Subgroup Kˣ} :
    Function.Injective (fun x : Fin 3 → C => diagGL (k335l4_dφHom x)) := by
  intro x y h
  have h1 : (fun i => ((k335l4_dφHom x) i : K)) = (fun i => ((k335l4_dφHom y) i : K)) :=
    Matrix.diagonal_injective (by
      rw [← coe_diagGL, ← coe_diagGL]
      exact congrArg (fun A : GL (Fin 4) K => (A : Matrix (Fin 4) (Fin 4) K)) h)
  have h2 : k335l4_dφHom x = k335l4_dφHom y := by
    funext i
    exact Units.ext (congrFun h1 i)
  funext i
  fin_cases i
  · exact Subtype.ext (congrFun h2 (0 : Fin 4))
  · exact Subtype.ext (congrFun h2 (1 : Fin 4))
  · exact Subtype.ext (congrFun h2 (2 : Fin 4))

private noncomputable def k335l4_φ {K : Type} [Field K] {C : Subgroup Kˣ} :
    (Fin 3 → C) →* ↥(CFSG.Open.StatedSL 4 K) :=
  (diagGL.comp k335l4_dφHom).codRestrict (CFSG.Open.StatedSL 4 K) k335l4_dφ_mem

private theorem k335l4_φ_injective {K : Type} [Field K] {C : Subgroup Kˣ} :
    Function.Injective (k335l4_φ (C := C)) := by
  intro x y h
  apply k335l4_dφ_injective
  exact congrArg (fun z : ↥(CFSG.Open.StatedSL 4 K) => (z : GL (Fin 4) K)) h

private theorem k335l4_permGL_det {K : Type} [Field K] (σ : Equiv.Perm (Fin 4)) :
    ((permGL σ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = Equiv.Perm.sign σ := by
  have hcoe : ((permGL σ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (σ⁻¹).permMatrix K := rfl
  rw [hcoe, Matrix.det_permutation, Equiv.Perm.sign_inv]

private theorem k335l4_σ_mem {K : Type} [Field K] :
    permGL k335l4_σ ∈ CFSG.Open.StatedSL 4 K := by
  apply CFSG.Open.StatedAPI.mem_statedSL_of_det
  rw [k335l4_permGL_det, k335l4_σ_sign]
  simp

private noncomputable def k335l4_s {K : Type} [Field K] : ↥(CFSG.Open.StatedSL 4 K) :=
  ⟨permGL k335l4_σ, k335l4_σ_mem⟩

private theorem k335l4_s_pow_three {K : Type} [Field K] :
    k335l4_s (K := K) ^ 3 = 1 := by
  apply Subtype.ext
  change (permGL k335l4_σ : GL (Fin 4) K) ^ 3 = 1
  rw [← map_pow, k335l4_σ_pow_three, map_one]

private theorem k335l4_permGL_conj_diagGL {K : Type} [Field K]
    (σ : Equiv.Perm (Fin 4)) (e : Fin 4 → Kˣ) :
    permGL σ * diagGL e * (permGL σ)⁻¹ = diagGL (fun j => e (σ⁻¹ j)) := by
  rw [permGL_mul_diagGL, mul_assoc, mul_inv_cancel, mul_one]

private theorem k335l4_dφ_shift {K : Type} [Field K] {C : Subgroup Kˣ} (x : Fin 3 → C) :
    (fun j => k335l4_dφ x (k335l4_σ⁻¹ j)) = k335l4_dφ (fun i => x (i - 1)) := by
  funext j
  fin_cases j
  · show k335l4_dφ x (k335l4_σ⁻¹ (0 : Fin 4)) = k335l4_dφ (fun i => x (i - 1)) (0 : Fin 4)
    rw [k335l4_σ_inv_zero]
    change (x 2 : Kˣ) = (x ((0 : Fin 3) - 1) : Kˣ)
    rw [show (0 : Fin 3) - 1 = 2 from by decide]
  · show k335l4_dφ x (k335l4_σ⁻¹ (1 : Fin 4)) = k335l4_dφ (fun i => x (i - 1)) (1 : Fin 4)
    rw [k335l4_σ_inv_one]
    change (x 0 : Kˣ) = (x ((1 : Fin 3) - 1) : Kˣ)
    rw [show (1 : Fin 3) - 1 = 0 from by decide]
  · show k335l4_dφ x (k335l4_σ⁻¹ (2 : Fin 4)) = k335l4_dφ (fun i => x (i - 1)) (2 : Fin 4)
    rw [k335l4_σ_inv_two]
    change (x 1 : Kˣ) = (x ((2 : Fin 3) - 1) : Kˣ)
    rw [show (2 : Fin 3) - 1 = 1 from by decide]
  · show k335l4_dφ x (k335l4_σ⁻¹ (3 : Fin 4)) = k335l4_dφ (fun i => x (i - 1)) (3 : Fin 4)
    rw [k335l4_σ_inv_three]
    change ((x 0 : Kˣ) * (x 1 : Kˣ) * (x 2 : Kˣ))⁻¹ =
      ((x ((0 : Fin 3) - 1) : Kˣ) * (x ((1 : Fin 3) - 1) : Kˣ) *
        (x ((2 : Fin 3) - 1) : Kˣ))⁻¹
    rw [show (0 : Fin 3) - 1 = 2 from by decide,
      show (1 : Fin 3) - 1 = 0 from by decide,
      show (2 : Fin 3) - 1 = 1 from by decide]
    congr 1
    ac_rfl

private theorem k335l4_s_conj {K : Type} [Field K] {C : Subgroup Kˣ} (x : Fin 3 → C) :
    k335l4_s * k335l4_φ x * (k335l4_s)⁻¹ = k335l4_φ (fun i => x (i - 1)) := by
  apply Subtype.ext
  show permGL k335l4_σ * diagGL (k335l4_dφHom x) * (permGL k335l4_σ)⁻¹ =
    diagGL (k335l4_dφHom (fun i => x (i - 1)))
  rw [k335l4_permGL_conj_diagGL]
  congr 1
  exact k335l4_dφ_shift x

private theorem k335l4_coe_pow_three {K : Type} [Field K] {C : Subgroup Kˣ}
    (c : ↥C) (hc3 : c ^ 3 = 1) : (c : Kˣ) ^ 3 = 1 := by
  rw [← Subgroup.coe_pow, hc3, Subgroup.coe_one]

private theorem k335l4_mul_three {K : Type} [Field K] {C : Subgroup Kˣ} (c : ↥C) :
    (c : Kˣ) * (c : Kˣ) * (c : Kˣ) = (c : Kˣ) ^ 3 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_two, pow_one]

private theorem k335l4_dφ_const_three {K : Type} [Field K] {C : Subgroup Kˣ}
    (c : ↥C) (hc3 : c ^ 3 = 1) : k335l4_dφHom (fun _ : Fin 3 => c) 3 = 1 := by
  change k335l4_dφ (fun _ : Fin 3 => c) 3 = 1
  rw [k335l4_dφ_apply_three, k335l4_mul_three c, k335l4_coe_pow_three c hc3, inv_one]

private theorem k335l4_dφ_sq_inv {K : Type} [Field K] {C : Subgroup Kˣ}
    (c : ↥C) (hc3 : c ^ 3 = 1) : ((c : Kˣ) * (c : Kˣ) * 1)⁻¹ = c := by
  rw [mul_one, inv_eq_iff_mul_eq_one, k335l4_mul_three c, k335l4_coe_pow_three c hc3]

private theorem k335l4_move {K : Type} [Field K] {C : Subgroup Kˣ} (c : ↥C)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    ∃ g : ↥(CFSG.Open.StatedSL 4 K), ∃ u : Fin 3 → ↥C,
      (∀ i, u i ∈ Subgroup.zpowers c) ∧ u 0 * u 1 * u 2 ≠ 1 ∧
      g * k335l4_φ (fun _ => c) * g⁻¹ = k335l4_φ u := by
  have hc2 : c ^ 2 ≠ 1 := by
    intro h
    have hd : orderOf c ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
    have h3 : orderOf c = 3 := orderOf_eq_prime hc3 hc1
    rw [h3] at hd
    exact absurd hd (by norm_num)
  let τ : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3
  have hτsign : Equiv.Perm.sign τ = 1 := by decide
  have hτmem : permGL τ ∈ CFSG.Open.StatedSL 4 K := by
    apply CFSG.Open.StatedAPI.mem_statedSL_of_det
    rw [k335l4_permGL_det, hτsign]
    simp
  let g : ↥(CFSG.Open.StatedSL 4 K) := ⟨permGL τ, hτmem⟩
  let u : Fin 3 → ↥C := ![c, c, 1]
  have hu_mem : ∀ i, u i ∈ Subgroup.zpowers c := by
    intro i
    fin_cases i <;> simp [u]
  have hu_ne : u 0 * u 1 * u 2 ≠ 1 := by
    have h : u 0 * u 1 * u 2 = c ^ 2 := by
      change c * c * 1 = c ^ 2
      rw [mul_one, pow_two]
    rw [h]
    exact hc2
  refine ⟨g, u, hu_mem, hu_ne, ?_⟩
  apply Subtype.ext
  show permGL τ * diagGL (k335l4_dφHom (fun _ => c)) * (permGL τ)⁻¹ =
    diagGL (k335l4_dφHom u)
  rw [k335l4_permGL_conj_diagGL]
  congr 1
  funext j
  fin_cases j
  · show k335l4_dφHom (fun _ : Fin 3 => c) (τ⁻¹ 0) = k335l4_dφHom u 0
    rw [show τ⁻¹ 0 = 1 from by decide]
    rfl
  · show k335l4_dφHom (fun _ : Fin 3 => c) (τ⁻¹ 1) = k335l4_dφHom u 1
    rw [show τ⁻¹ 1 = 0 from by decide]
    rfl
  · show k335l4_dφHom (fun _ : Fin 3 => c) (τ⁻¹ 2) = k335l4_dφHom u 2
    rw [show τ⁻¹ 2 = 3 from by decide, k335l4_dφ_const_three c hc3]
    rfl
  · show k335l4_dφHom (fun _ : Fin 3 => c) (τ⁻¹ 3) = k335l4_dφHom u 3
    rw [show τ⁻¹ 3 = 2 from by decide]
    show (c : Kˣ) = ((c : Kˣ) * (c : Kˣ) * 1)⁻¹
    rw [k335l4_dφ_sq_inv c hc3]

private theorem k335l4_coord_matrix {K : Type} [Field K] [Finite K]
    (hq : Nat.card K % 3 = 1) :
    K335Coord ↥(CFSG.Open.StatedSL 4 K) ((Nat.card K ^ 2 - 1).factorization 3) := by
  let C : Sylow 3 Kˣ := default
  have hq2 : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  have hCcard : Nat.card C = 3 ^ ((Nat.card K ^ 2 - 1).factorization 3) := by
    rw [Sylow.card_eq_multiplicity C, Nat.card_units]
    congr 1
    exact (k335o7s_factorization_sq_sub_one hq2 hq).symm
  refine ⟨↥C, inferInstance, inferInstance, hCcard, k335l4_φ (K := K) (C := C),
    k335l4_φ_injective (K := K) (C := C), k335l4_s (K := K), k335l4_s_pow_three (K := K),
    ?_, ?_⟩
  · intro x
    exact k335l4_s_conj (K := K) (C := C) x
  · intro c hc3 hc1
    exact k335l4_move (K := K) (C := C) c hc3 hc1

private theorem k335l4_core {X : Type} [Group X] {p f : ℕ}
    (h : LieModel X .PSL 4 p f) (hq : p ^ f % 3 = 1) :
    K335Coord X (((p ^ f) ^ 2 - 1).factorization 3) := by
  obtain ⟨-, K, hKfield, hKfin, hKcard, ⟨e⟩⟩ :=
    h.statedClassicalModel_of_ne_zero (by norm_num)
  let : Field K := hKfield
  let : Finite K := hKfin
  have hKq : Nat.card K % 3 = 1 := by rw [hKcard]; exact hq
  have hcoord : K335Coord ↥(CFSG.Open.StatedSL 4 K)
      ((Nat.card K ^ 2 - 1).factorization 3) := k335l4_coord_matrix hKq
  have hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈
      CFSG.Open.StatedSL 4 K → c ^ 4 = 1 := by
    intro c hc
    have h := CFSG.Open.StatedAPI.det_of_mem_statedSL hc
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Fin.prod_univ_four] at h
    have h2 : (c : K) ^ 4 = 1 := by
      rw [show (c : K) ^ 4 = (c : K) * c * c * c by ring]
      exact h
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h2)
  have hproj : K335Coord (CFSG.Open.StatedProj (CFSG.Open.StatedSL 4 K))
      ((Nat.card K ^ 2 - 1).factorization 3) :=
    k335_coord_statedProj
      (CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf (CFSG.Open.StatedSL 4 K)
        Nat.prime_three (by norm_num : ¬ 3 ∣ 4) hd) hcoord
  have hX : K335Coord X ((Nat.card K ^ 2 - 1).factorization 3) :=
    K335Coord.of_mulEquiv e.symm hproj
  simpa only [hKcard] using hX

end K335L4Aux

theorem k335_coord_psl4 {X : Type} [Group X] {p f : ℕ} (h : LieModel X .PSL 4 p f)
    (hq : p ^ f % 3 = 1) : K335Coord X (((p ^ f) ^ 2 - 1).factorization 3) :=
  k335l4_core h hq

section K335U4Aux

private theorem k335u4_sq_sub_one (q : ℕ) : q ^ 2 - 1 = (q - 1) * (q + 1) := by
  symm
  have h1 : (q + 1) * (q - 1) = (q + 1) * q - (q + 1) := Nat.mul_sub_one (q + 1) q
  have h2 : (q + 1) * q = q * q + q := by rw [Nat.add_mul, one_mul]
  have h3 : q * q + q - (q + 1) = q * q - 1 := by omega
  rw [mul_comm, h1, h2, h3, sq]

private theorem k335u4_factorization_sq_sub_one {q : ℕ} (h2 : 2 ≤ q) (hq : q % 3 = 2) :
    (q ^ 2 - 1).factorization 3 = (q + 1).factorization 3 := by
  have hq1 : ¬ 3 ∣ q - 1 := by
    intro hd
    have h0 : (q - 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
    omega
  rw [k335u4_sq_sub_one q, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hq1, zero_add]

private theorem k335u4_three_pow_dvd_succ {q : ℕ} (h2 : 2 ≤ q) (hq : q % 3 = 2) :
    3 ^ ((q ^ 2 - 1).factorization 3) ∣ q + 1 := by
  rw [k335u4_factorization_sq_sub_one h2 hq]
  exact (Nat.Prime.pow_dvd_iff_le_factorization (p := 3)
    (k := (q + 1).factorization 3) (n := q + 1) Nat.prime_three (by omega)).mpr le_rfl

private def k335u4_dφ {K : Type} [Field K] {C : Subgroup Kˣ} (x : Fin 3 → C) : Fin 4 → Kˣ
  | 0 => (x 0 : Kˣ)
  | 1 => (x 1 : Kˣ)
  | 2 => (x 2 : Kˣ)
  | 3 => ((x 0 * x 1 * x 2 : C) : Kˣ)⁻¹

private def k335u4_dφHom {K : Type} [Field K] {C : Subgroup Kˣ} :
    (Fin 3 → C) →* (Fin 4 → Kˣ) where
  toFun := k335u4_dφ
  map_one' := by
    funext j
    fin_cases j <;> simp [k335u4_dφ]
  map_mul' x y := by
    funext j
    fin_cases j
    · simp [k335u4_dφ, Pi.mul_apply]
    · simp [k335u4_dφ, Pi.mul_apply]
    · simp [k335u4_dφ, Pi.mul_apply]
    · simp only [k335u4_dφ, Pi.mul_apply, Subgroup.coe_mul, _root_.mul_inv_rev]
      ac_rfl

private lemma k335u4_dφ_mem {K : Type} [Field K] {C : Subgroup Kˣ} (x : Fin 3 → C) (j : Fin 4) :
    k335u4_dφ x j ∈ C := by
  fin_cases j
  · exact (x 0).2
  · exact (x 1).2
  · exact (x 2).2
  · exact C.inv_mem (C.mul_mem (C.mul_mem (x 0).2 (x 1).2) (x 2).2)

private lemma k335u4_dφ_pow_succ {K : Type} [Field K] {C : Subgroup Kˣ} {q : ℕ}
    (hC : ∀ c : C, c ^ (q + 1) = 1) (x : Fin 3 → C) (j : Fin 4) :
    (k335u4_dφ x j) ^ (q + 1) = 1 := by
  have h := congrArg (fun u : C => (u : Kˣ)) (hC ⟨k335u4_dφ x j, k335u4_dφ_mem x j⟩)
  simpa using h

private lemma k335u4_dφ_pow {K : Type} [Field K] {C : Subgroup Kˣ} {q : ℕ}
    (hC : ∀ c : C, c ^ (q + 1) = 1) (x : Fin 3 → C) :
    k335u4_dφ x ^ (q + 1) = 1 :=
  funext fun j => k335u4_dφ_pow_succ hC x j

private lemma k335u4_dφ_prod_one {K : Type} [Field K] {C : Subgroup Kˣ} (x : Fin 3 → C) :
    ∏ j, k335u4_dφ x j = 1 := by
  rw [Fin.prod_univ_four]
  simp only [k335u4_dφ, Subgroup.coe_mul]
  rw [mul_inv_cancel]

private lemma k335u4_diagGL_injective {K : Type} [Field K] :
    Function.Injective (diagGL (K := K) (ι := Fin 4)) := by
  intro d e h
  funext j
  apply Units.ext
  have h1 := congrArg (fun A : GL (Fin 4) K => (A : Matrix (Fin 4) (Fin 4) K) j j) h
  simpa [coe_diagGL] using h1

private lemma k335u4_diagGL_det {K : Type} [Field K] {C : Subgroup Kˣ} (x : Fin 3 → C) :
    ((diagGL (k335u4_dφ x) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det =
      ((∏ j, k335u4_dφ x j : Kˣ) : K) := by
  rw [coe_diagGL, Matrix.det_diagonal, ← Units.coe_prod]

private lemma k335u4_diagGL_mem {K : Type} [Field K] {C : Subgroup Kˣ} {q : ℕ}
    (hq0 : q ≠ 0) (hC : ∀ c : C, c ^ (q + 1) = 1) (x : Fin 3 → C) :
    diagGL (k335u4_dφ x) ∈ CFSG.Open.StatedSU 4 q K := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [k335u4_diagGL_det, k335u4_dφ_prod_one x, Units.val_one]
  · rw [coe_diagGL, diagonal_map (f := fun x : K => x ^ q) (zero_pow hq0), diagonal_transpose,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [← pow_succ, ← Units.val_pow_eq_pow_val, ← Pi.pow_apply, k335u4_dφ_pow hC x,
      Pi.one_apply, Units.val_one]

private def k335u4_perm : Equiv.Perm (Fin 4) where
  toFun i := if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 0 else 3
  invFun i := if i = 0 then 2 else if i = 1 then 0 else if i = 2 then 1 else 3
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

private def k335u4_tau : Equiv.Perm (Fin 4) where
  toFun i := if i = 0 then 1 else if i = 1 then 0 else if i = 2 then 3 else 2
  invFun i := if i = 0 then 1 else if i = 1 then 0 else if i = 2 then 3 else 2
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

private theorem k335u4_perm_eq :
    k335u4_perm = Equiv.swap (0 : Fin 4) 1 * Equiv.swap (1 : Fin 4) 2 := by
  ext i; fin_cases i <;> rfl

private theorem k335u4_tau_eq :
    k335u4_tau = Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3 := by
  ext i; fin_cases i <;> rfl

private theorem k335u4_perm_pow_three : k335u4_perm ^ 3 = 1 := by
  ext i
  fin_cases i <;> rfl

private theorem k335u4_perm_sign : Equiv.Perm.sign k335u4_perm = 1 := by
  rw [k335u4_perm_eq, map_mul,
    Equiv.Perm.sign_swap (x := (0 : Fin 4)) (y := 1) (by decide),
    Equiv.Perm.sign_swap (x := (1 : Fin 4)) (y := 2) (by decide)]
  decide

private theorem k335u4_tau_sign : Equiv.Perm.sign k335u4_tau = 1 := by
  rw [k335u4_tau_eq, map_mul,
    Equiv.Perm.sign_swap (x := (0 : Fin 4)) (y := 1) (by decide),
    Equiv.Perm.sign_swap (x := (2 : Fin 4)) (y := 3) (by decide)]
  decide

private theorem k335u4_tau_inv : k335u4_tau⁻¹ = k335u4_tau := by
  ext i
  fin_cases i <;> rfl

@[simp] private theorem k335u4_perm_inv_zero : (k335u4_perm)⁻¹ (0 : Fin 4) = 2 := rfl
@[simp] private theorem k335u4_perm_inv_one : (k335u4_perm)⁻¹ (1 : Fin 4) = 0 := rfl
@[simp] private theorem k335u4_perm_inv_two : (k335u4_perm)⁻¹ (2 : Fin 4) = 1 := rfl
@[simp] private theorem k335u4_perm_inv_three : (k335u4_perm)⁻¹ (3 : Fin 4) = 3 := rfl

@[simp] private theorem k335u4_tau_zero : k335u4_tau (0 : Fin 4) = 1 := rfl
@[simp] private theorem k335u4_tau_one : k335u4_tau (1 : Fin 4) = 0 := rfl
@[simp] private theorem k335u4_tau_two : k335u4_tau (2 : Fin 4) = 3 := rfl
@[simp] private theorem k335u4_tau_three : k335u4_tau (3 : Fin 4) = 2 := rfl

private lemma k335u4_coe_permGL {K : Type} [Field K] (σ : Equiv.Perm (Fin 4)) :
    ((permGL σ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = (σ⁻¹).permMatrix K := rfl

private lemma k335u4_permMatrix_apply {K : Type} [Field K] (σ : Equiv.Perm (Fin 4))
    (i j : Fin 4) :
    (σ.permMatrix K : Matrix (Fin 4) (Fin 4) K) i j = if σ i = j then 1 else 0 := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  by_cases h : σ i = j
  · rw [if_pos (by simpa [Equiv.toPEquiv_apply] using h), if_pos h]
  · rw [if_neg (by simpa [Equiv.toPEquiv_apply] using h), if_neg h]

private lemma k335u4_permGL_map {K : Type} [Field K] {q : ℕ} (hq0 : q ≠ 0)
    (σ : Equiv.Perm (Fin 4)) :
    (((permGL σ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ q)) =
      ((permGL σ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  rw [Matrix.map_apply, k335u4_coe_permGL, k335u4_permMatrix_apply]
  by_cases h : (σ⁻¹ : Equiv.Perm (Fin 4)) i = j
  · simp [h]
  · simp [zero_pow hq0]

private lemma k335u4_permGL_unitary {K : Type} [Field K] {q : ℕ} (hq0 : q ≠ 0)
    (σ : Equiv.Perm (Fin 4)) :
    (((permGL σ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ q))ᵀ *
      ((permGL σ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
  rw [k335u4_permGL_map hq0 σ, k335u4_coe_permGL, Matrix.transpose_permMatrix, inv_inv,
    ← Matrix.permMatrix_mul (R := K) (σ := σ⁻¹) (τ := σ), inv_mul_cancel, Matrix.permMatrix_one]

private lemma k335u4_permGL_det {K : Type} [Field K] (σ : Equiv.Perm (Fin 4))
    (hσ : Equiv.Perm.sign σ = 1) :
    ((permGL σ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  rw [k335u4_coe_permGL, Matrix.det_permutation,
    show Equiv.Perm.sign (σ⁻¹) = 1 by rw [map_inv, hσ, inv_one]]
  norm_num

private lemma k335u4_permGL_mem {K : Type} [Field K] {q : ℕ} (hq0 : q ≠ 0)
    (σ : Equiv.Perm (Fin 4)) (hσ : Equiv.Perm.sign σ = 1) :
    permGL σ ∈ CFSG.Open.StatedSU 4 q K :=
  Subgroup.subset_closure ⟨k335u4_permGL_det σ hσ, k335u4_permGL_unitary hq0 σ⟩

private lemma k335u4_permGL_conj {K : Type} [Field K] (σ : Equiv.Perm (Fin 4)) (e : Fin 4 → Kˣ) :
    (permGL σ : GL (Fin 4) K) * diagGL e * (permGL σ)⁻¹ =
      diagGL (fun j => e (σ⁻¹ j)) := by
  rw [permGL_mul_diagGL, mul_assoc, mul_inv_cancel, mul_one]

private noncomputable def k335u4_s {K : Type} [Field K] {q : ℕ} (hq0 : q ≠ 0) :
    ↥(CFSG.Open.StatedSU 4 q K) :=
  ⟨permGL k335u4_perm, k335u4_permGL_mem hq0 k335u4_perm k335u4_perm_sign⟩

private noncomputable def k335u4_g {K : Type} [Field K] {q : ℕ} (hq0 : q ≠ 0) :
    ↥(CFSG.Open.StatedSU 4 q K) :=
  ⟨permGL k335u4_tau, k335u4_permGL_mem hq0 k335u4_tau k335u4_tau_sign⟩

private noncomputable def k335u4_phi {K : Type} [Field K] {C : Subgroup Kˣ} {q : ℕ}
    (hq0 : q ≠ 0) (hC : ∀ c : C, c ^ (q + 1) = 1) :
    (Fin 3 → C) →* ↥(CFSG.Open.StatedSU 4 q K) :=
  (diagGL.comp k335u4_dφHom).codRestrict _ (fun x => k335u4_diagGL_mem hq0 hC x)

private lemma k335u4_phi_injective {K : Type} [Field K] {C : Subgroup Kˣ} {q : ℕ}
    (hq0 : q ≠ 0) (hC : ∀ c : C, c ^ (q + 1) = 1) :
    Function.Injective (k335u4_phi hq0 hC) := by
  intro x y hxy
  have h1 : (diagGL (k335u4_dφ x) : GL (Fin 4) K) = diagGL (k335u4_dφ y) :=
    congrArg (fun z : ↥(CFSG.Open.StatedSU 4 q K) => (z : GL (Fin 4) K)) hxy
  have h2 : k335u4_dφ x = k335u4_dφ y := k335u4_diagGL_injective h1
  funext i
  fin_cases i
  · exact Subtype.ext (by simpa [k335u4_dφ] using congrFun h2 0)
  · exact Subtype.ext (by simpa [k335u4_dφ] using congrFun h2 1)
  · exact Subtype.ext (by simpa [k335u4_dφ] using congrFun h2 2)

private lemma k335u4_s_pow_three {K : Type} [Field K] {q : ℕ} (hq0 : q ≠ 0) :
    (k335u4_s (K := K) (q := q) hq0) ^ 3 = 1 := by
  apply Subtype.ext
  show (permGL k335u4_perm : GL (Fin 4) K) ^ 3 = 1
  rw [← map_pow, k335u4_perm_pow_three, map_one]

private lemma k335u4_s_conj_phi {K : Type} [Field K] {C : Subgroup Kˣ} {q : ℕ}
    (hq0 : q ≠ 0) (hC : ∀ c : C, c ^ (q + 1) = 1) (x : Fin 3 → C) :
    k335u4_s hq0 * k335u4_phi hq0 hC x * (k335u4_s hq0)⁻¹ =
      k335u4_phi hq0 hC (fun i => x (i - 1)) := by
  apply Subtype.ext
  show (permGL k335u4_perm : GL (Fin 4) K) * diagGL (k335u4_dφ x) *
      (permGL k335u4_perm)⁻¹ = diagGL (k335u4_dφ (fun i => x (i - 1)))
  rw [k335u4_permGL_conj]
  congr 1
  funext j
  fin_cases j
  · simp [k335u4_perm_inv_zero, k335u4_dφ, show ((0 : Fin 3) - 1) = 2 from by decide]
  · simp [k335u4_perm_inv_one, k335u4_dφ]
  · simp [k335u4_perm_inv_two, k335u4_dφ, show ((2 : Fin 3) - 1) = 1 from by decide]
  · have h0 : ((0 : Fin 3) - 1) = 2 := by decide
    have h1 : ((1 : Fin 3) - 1) = 0 := by decide
    have h2 : ((2 : Fin 3) - 1) = 1 := by decide
    simp only [k335u4_dφ, h0, h1, h2, Subgroup.coe_mul]
    ac_rfl

private lemma k335u4_move_diag {K : Type} [Field K] {C : Subgroup Kˣ} (c : C)
    (hc3 : c ^ 3 = 1) :
    (fun j => k335u4_dφ (fun _ : Fin 3 => c) (k335u4_tau⁻¹ j)) =
      k335u4_dφ (![c, c, 1] : Fin 3 → C) := by
  have hc3' : (c : Kˣ) ^ 3 = 1 := by
    simpa using congrArg (fun u : C => (u : Kˣ)) hc3
  have hc3mul : (c : Kˣ) * (c : Kˣ) * (c : Kˣ) = 1 := by
    rw [show (c : Kˣ) * (c : Kˣ) * (c : Kˣ) = (c : Kˣ) ^ 3 by simp [pow_succ], hc3']
  have hc2 : (c : Kˣ) * (c : Kˣ) = (c : Kˣ)⁻¹ :=
    eq_inv_of_mul_eq_one_left hc3mul
  funext j
  fin_cases j
  · rfl
  · rfl
  · change k335u4_dφ (fun _ : Fin 3 => c) (k335u4_tau⁻¹ (2 : Fin 4)) =
      k335u4_dφ (![c, c, 1] : Fin 3 → C) (2 : Fin 4)
    rw [show k335u4_tau⁻¹ (2 : Fin 4) = 3 from rfl]
    simp only [k335u4_dφ, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Subgroup.coe_mul, Subgroup.coe_one]
    rw [show (c : Kˣ) * (c : Kˣ) * (c : Kˣ) = 1 from hc3mul, inv_one]
  · change k335u4_dφ (fun _ : Fin 3 => c) (k335u4_tau⁻¹ (3 : Fin 4)) =
      k335u4_dφ (![c, c, 1] : Fin 3 → C) (3 : Fin 4)
    rw [show k335u4_tau⁻¹ (3 : Fin 4) = 2 from rfl]
    simp only [k335u4_dφ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Subgroup.coe_mul, mul_one]
    rw [show (c : Kˣ) * (c : Kˣ) = (c : Kˣ)⁻¹ from hc2, inv_inv]

private lemma k335u4_move {K : Type} [Field K] {C : Subgroup Kˣ} {q : ℕ}
    (hq0 : q ≠ 0) (hC : ∀ c : C, c ^ (q + 1) = 1) (c : C) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    ∃ g : ↥(CFSG.Open.StatedSU 4 q K), ∃ u : Fin 3 → C,
      (∀ i, u i ∈ Subgroup.zpowers c) ∧ u 0 * u 1 * u 2 ≠ 1 ∧
        g * k335u4_phi hq0 hC (fun _ => c) * g⁻¹ = k335u4_phi hq0 hC u := by
  refine ⟨k335u4_g hq0, ![c, c, 1], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact Subgroup.mem_zpowers_iff.mpr ⟨1, zpow_one c⟩
    · exact Subgroup.mem_zpowers_iff.mpr ⟨1, zpow_one c⟩
    · exact Subgroup.one_mem _
  · have hprod : (![c, c, 1] : Fin 3 → C) 0 * (![c, c, 1] : Fin 3 → C) 1 *
        (![c, c, 1] : Fin 3 → C) 2 = c ^ 2 := by
      simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, pow_two]
    rw [hprod]
    intro h2
    have hc_eq : c = 1 := by
      calc c = c ^ 2 * c := by rw [h2, one_mul]
        _ = c ^ 3 := (pow_succ c 2).symm
        _ = 1 := hc3
    exact hc1 hc_eq
  · apply Subtype.ext
    show (permGL k335u4_tau : GL (Fin 4) K) * diagGL (k335u4_dφ (fun _ => c)) *
        (permGL k335u4_tau)⁻¹ = diagGL (k335u4_dφ (![c, c, 1] : Fin 3 → C))
    rw [k335u4_permGL_conj, k335u4_tau_inv]
    congr 1
    exact k335u4_move_diag c hc3

private theorem k335u4_coord {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : q % 3 = 2) :
    K335Coord ↥(CFSG.Open.StatedSU 4 q K) ((q ^ 2 - 1).factorization 3) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq2 : 2 ≤ q := by
    by_contra h
    rw [not_le] at h
    interval_cases q <;> norm_num at hq
  have hq0 : q ≠ 0 := by omega
  let C : Sylow 3 Kˣ := default
  have hCcard : Nat.card C = 3 ^ ((q ^ 2 - 1).factorization 3) := by
    rw [Sylow.card_eq_multiplicity C, Nat.card_units, hK]
  have hC : ∀ c : C, c ^ (q + 1) = 1 := by
    intro c
    have hcard : c ^ Nat.card C = 1 := pow_card_eq_one'
    rw [hCcard] at hcard
    obtain ⟨k, hk⟩ := k335u4_three_pow_dvd_succ hq2 hq
    rw [hk, pow_mul, hcard, one_pow]
  exact ⟨C, inferInstance, inferInstance, hCcard, k335u4_phi hq0 hC,
    k335u4_phi_injective hq0 hC, k335u4_s hq0, k335u4_s_pow_three hq0,
    k335u4_s_conj_phi hq0 hC, k335u4_move hq0 hC⟩

end K335U4Aux

theorem k335_coord_psu4 {X : Type} [Group X] {p f : ℕ} (h : LieModel X .PSU 4 p f)
    (hq : p ^ f % 3 = 2) : K335Coord X (((p ^ f) ^ 2 - 1).factorization 3) := by
  obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num)
  let : Field K := hfield
  let : Finite K := hfinite
  let q : ℕ := p ^ f
  have hKq : Nat.card K = q ^ 2 := hK
  have hqq : q % 3 = 2 := hq
  have hH : K335Coord ↥(CFSG.Open.StatedSU 4 q K) ((q ^ 2 - 1).factorization 3) :=
    k335u4_coord hKq hqq
  have hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈
      CFSG.Open.StatedSU 4 q K → c ^ 4 = 1 := fun c hc => by
    have hdet := CFSG.Open.StatedAPI.det_of_mem_statedSU hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Fin.prod_univ_four] at hdet
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one,
      show (c : K) ^ 4 = (c : K) * (c : K) * (c : K) * (c : K) by group]
    exact hdet
  have hproj : K335Coord (CFSG.Open.StatedProj (CFSG.Open.StatedSU 4 q K))
      ((q ^ 2 - 1).factorization 3) :=
    k335_coord_statedProj
      (CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf
        (CFSG.Open.StatedSU 4 q K) Nat.prime_three (by norm_num) hd) hH
  exact K335Coord.of_mulEquiv e.symm hproj

theorem k335_noStrong_of_classical (hO : LieOrderFormulasInput) {X : Type} [Group X] [Finite X]
    {t : CFSG.Open.StatedLieTag} {n p f : ℕ} (h : LieModel X t n p f) (hp : p ≠ 3)
    (ht : (t = .PSp ∧ n = 3) ∨ (t = .POmegaOdd ∧ n = 3) ∨ (t = .POmegaMinus ∧ n = 4) ∨
      (t = .PSL ∧ n = 4 ∧ p ^ f % 3 = 1) ∨ (t = .PSU ∧ n = 4 ∧ p ^ f % 3 = 2) ∨
      (t = .PSL ∧ (n = 6 ∨ n = 7) ∧ p ^ f % 3 = 2) ∨
      (t = .PSU ∧ (n = 6 ∨ n = 7) ∧ p ^ f % 3 = 1))
    (hc : K335Coord X (((p ^ f) ^ 2 - 1).factorization 3)) : K335NoStrongE9 X := by
  obtain ⟨hpp, hf, -⟩ := h.admissible
  have h2 : 2 ≤ p ^ f := hpp.two_le.trans (Nat.le_self_pow (by omega) p)
  refine k335_noStrong_of_coordData (k335_one_le_v3 h2 (k335_three_not_dvd hpp hp)) hc ?_
  rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne',
    k335_v3_card_classical hO h hp ht]
  omega

theorem k335_noStrong_psp6 (hO : LieOrderFormulasInput) {X : Type} [Group X] [Finite X]
    {p f : ℕ} (h : LieModel X .PSp 3 p f) (hp : p ≠ 3) : K335NoStrongE9 X :=
  k335_noStrong_of_classical hO h hp (Or.inl ⟨rfl, rfl⟩) (k335_coord_psp6 h hp)

theorem k335_noStrong_omega7 (hO : LieOrderFormulasInput) {X : Type} [Group X] [Finite X]
    {p f : ℕ} (h : LieModel X .POmegaOdd 3 p f) (hp : p ≠ 3) : K335NoStrongE9 X := by
  have h3 := k335_three_not_dvd (f := f) h.admissible.1 hp
  refine k335_noStrong_of_classical hO h hp (Or.inr (Or.inl ⟨rfl, rfl⟩)) ?_
  rcases (by omega : p ^ f % 3 = 1 ∨ p ^ f % 3 = 2) with hq | hq
  · exact k335_coord_omega7_split h hq
  · exact k335_coord_omega7_nonsplit h hq

theorem k335_noStrong_omegaMinus8 (hO : LieOrderFormulasInput) {X : Type} [Group X] [Finite X]
    {p f : ℕ} (h : LieModel X .POmegaMinus 4 p f) (hp : p ≠ 3) : K335NoStrongE9 X := by
  have h3 := k335_three_not_dvd (f := f) h.admissible.1 hp
  refine k335_noStrong_of_classical hO h hp (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) ?_
  rcases (by omega : p ^ f % 3 = 1 ∨ p ^ f % 3 = 2) with hq | hq
  · exact k335_coord_omegaMinus8_split h hq
  · exact k335_coord_omegaMinus8_nonsplit h hq

theorem k335_noStrong_psl4 (hO : LieOrderFormulasInput) {X : Type} [Group X] [Finite X]
    {p f : ℕ} (h : LieModel X .PSL 4 p f) (hq : p ^ f % 3 = 1) : K335NoStrongE9 X :=
  k335_noStrong_of_classical hO h (k335_ne_three h (by omega))
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hq⟩)))) (k335_coord_psl4 h hq)

theorem k335_noStrong_psu4 (hO : LieOrderFormulasInput) {X : Type} [Group X] [Finite X]
    {p f : ℕ} (h : LieModel X .PSU 4 p f) (hq : p ^ f % 3 = 2) : K335NoStrongE9 X :=
  k335_noStrong_of_classical hO h (k335_ne_three h (by omega))
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hq⟩))))) (k335_coord_psu4 h hq)

theorem k335_noStrong_psl67 (hO : LieOrderFormulasInput) {X : Type} [Group X] [Finite X]
    {n p f : ℕ} (h : LieModel X .PSL n p f) (hn : n = 6 ∨ n = 7) (hq : p ^ f % 3 = 2) :
    K335NoStrongE9 X :=
  k335_noStrong_of_classical hO h (k335_ne_three h (by omega))
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hn, hq⟩))))))
    (k335_coord_psl67 h hn hq)

theorem k335_noStrong_psu67 (hO : LieOrderFormulasInput) {X : Type} [Group X] [Finite X]
    {n p f : ℕ} (h : LieModel X .PSU n p f) (hn : n = 6 ∨ n = 7) (hq : p ^ f % 3 = 1) :
    K335NoStrongE9 X :=
  k335_noStrong_of_classical hO h (k335_ne_three h (by omega))
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hn, hq⟩))))))
    (k335_coord_psu67 h hn hq)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
