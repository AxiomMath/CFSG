module

public import CFSG.RankThree.PartTwo.Sec4.RonanEpsL4Diag
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsSU2
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHU4
import CFSG.RankThree.PartTwo.Sec4.RonanK432DiagThree
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSU4Two

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.Assembly.RankThreeEven (projSU projImage)
open CFSG.LieType.Universal.Unitary (SUid mem_SUid conjTr SUid_eq_statedSU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix

section SU

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem u4Eps_conjTr_l4Up2_mul (X Y : Matrix (Fin 2) (Fin 2) K) :
    conjTr σ (l4Up2 X) * l4Up2 Y = l4Up2 (conjTr σ X * Y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [l4Up2, conjTr, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four,
      Matrix.transpose_apply]

theorem u4Eps_conjTr_l4Low2_mul (X Y : Matrix (Fin 2) (Fin 2) K) :
    conjTr σ (l4Low2 X) * l4Low2 Y = l4Low2 (conjTr σ X * Y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [l4Low2, conjTr, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four,
      Matrix.transpose_apply]

theorem u4Eps_blkUp_mem {B : GL (Fin 2) K} (hB : B ∈ SUid σ 2) : blkUp B ∈ SUid σ 4 := by
  obtain ⟨h1, h2⟩ := mem_SUid.mp hB
  refine mem_SUid.mpr ⟨?_, ?_⟩
  · rw [coe_blkUp, det_l4Up2]
    exact h1
  · rw [coe_blkUp, u4Eps_conjTr_l4Up2_mul, h2, l4Up2_one]

theorem u4Eps_blkLow_mem {B : GL (Fin 2) K} (hB : B ∈ SUid σ 2) : blkLow B ∈ SUid σ 4 := by
  obtain ⟨h1, h2⟩ := mem_SUid.mp hB
  refine mem_SUid.mpr ⟨?_, ?_⟩
  · rw [coe_blkLow, det_l4Low2]
    exact h1
  · rw [coe_blkLow, u4Eps_conjTr_l4Low2_mul, h2, l4Low2_one]

theorem u4Eps_conjTr_submatrix (M : Matrix (Fin 4) (Fin 4) K) (f : Fin 2 → Fin 4) :
    (conjTr σ M).submatrix f f = conjTr σ (M.submatrix f f) := by
  ext i j
  simp [conjTr, Matrix.transpose_apply]

theorem u4Eps_mem_SUid_two_of_block {M : GL (Fin 4) K} (hM : M ∈ SUid σ 4)
    (hb : BlockDiag2 (M : Matrix (Fin 4) (Fin 4) K)) :
    (∀ B : GL (Fin 2) K, (B : Matrix (Fin 2) (Fin 2) K) =
        (M : Matrix (Fin 4) (Fin 4) K).submatrix ![0, 1] ![0, 1] →
      (B : Matrix (Fin 2) (Fin 2) K).det = 1 → B ∈ SUid σ 2) ∧
    (∀ B : GL (Fin 2) K, (B : Matrix (Fin 2) (Fin 2) K) =
        (M : Matrix (Fin 4) (Fin 4) K).submatrix ![2, 3] ![2, 3] →
      (B : Matrix (Fin 2) (Fin 2) K).det = 1 → B ∈ SUid σ 2) := by
  obtain ⟨b02, b03, b12, b13, b20, b21, b30, b31⟩ := hb
  have h1 := (mem_SUid.mp hM).2
  have hf₁ : Function.Injective (![0, 1] : Fin 2 → Fin 4) := by decide
  have hf₂ : Function.Injective (![2, 3] : Fin 2 → Fin 4) := by decide
  have hr₁ : ∀ k : Fin 4, (∀ l : Fin 2, (![0, 1] : Fin 2 → Fin 4) l ≠ k) → k = 2 ∨ k = 3 := by
    decide
  have hr₂ : ∀ k : Fin 4, (∀ l : Fin 2, (![2, 3] : Fin 2 → Fin 4) l ≠ k) → k = 0 ∨ k = 1 := by
    decide
  constructor
  · intro B hB hdet
    refine mem_SUid.mpr ⟨hdet, ?_⟩
    have hv : ∀ i k, (∀ l, (![0, 1] : Fin 2 → Fin 4) l ≠ k) →
        conjTr σ (M : Matrix (Fin 4) (Fin 4) K) (![0, 1] i) k = 0 := by
      intro i k hk
      rcases hr₁ k hk with rfl | rfl <;> fin_cases i <;>
        simp [conjTr, Matrix.transpose_apply, b20, b21, b30, b31]
    have h2 : (conjTr σ (M : Matrix (Fin 4) (Fin 4) K) *
        (M : Matrix (Fin 4) (Fin 4) K)).submatrix ![0, 1] ![0, 1] =
        conjTr σ (B : Matrix (Fin 2) (Fin 2) K) * (B : Matrix (Fin 2) (Fin 2) K) := by
      rw [l4_submatrix_mul ![0, 1] hf₁ hv, hB, u4Eps_conjTr_submatrix]
    rw [← h2, h1, submatrix_one _ hf₁]
  · intro B hB hdet
    refine mem_SUid.mpr ⟨hdet, ?_⟩
    have hv : ∀ i k, (∀ l, (![2, 3] : Fin 2 → Fin 4) l ≠ k) →
        conjTr σ (M : Matrix (Fin 4) (Fin 4) K) (![2, 3] i) k = 0 := by
      intro i k hk
      rcases hr₂ k hk with rfl | rfl <;> fin_cases i <;>
        simp [conjTr, Matrix.transpose_apply, b02, b03, b12, b13]
    have h2 : (conjTr σ (M : Matrix (Fin 4) (Fin 4) K) *
        (M : Matrix (Fin 4) (Fin 4) K)).submatrix ![2, 3] ![2, 3] =
        conjTr σ (B : Matrix (Fin 2) (Fin 2) K) * (B : Matrix (Fin 2) (Fin 2) K) := by
      rw [l4_submatrix_mul ![2, 3] hf₂ hv, hB, u4Eps_conjTr_submatrix]
    rw [← h2, h1, submatrix_one _ hf₂]

end SU

theorem u4Eps_good_SUid {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {p f : ℕ}
    (h : UnitaryFieldData p f K) (hσ : ∀ c, σ c = h.bar c) {ω : K} (hω2 : ω ^ 2 + ω + 1 = 0)
    (h3 : (3 : K) ≠ 0) (hmq : 3 ∣ p ^ f + 1) (hQ : IsQuasisimple (SUid σ 3))
    (hQ₂ : IsQuasisimple (SUid σ 2))
    (hfin : ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* SUid σ 2) → EpsQuot X → False)
    (A : SUid σ 4) (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1) :
    GoodEps (Subgroup.centralizer ({(A : GL (Fin 4) K)} : Set (GL (Fin 4) K)) ⊓ SUid σ 4) := by
  have hω := RonanK432.isPrimitiveRoot_three_of_sq_add_add_one hω2 h3
  have hA3' : (A : GL (Fin 4) K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hA3, Subgroup.coe_one]
  have hA1' : (A : GL (Fin 4) K) ≠ 1 := fun h' => hA1 (Subtype.ext h')
  have hAU := ((u4_mem_SUid_iff σ h hσ _).mp A.2).2
  obtain ⟨g, hgU, a, hD⟩ := u4_exists_diag h hω2 h3 hmq hAU hA3'
  refine l4Eps_good_of_conj h3 hω hQ (fun g hg => (mem_SUid.mp hg).1)
    (fun e g => u4_mem_SUid_reindex σ e g) (fun B hB => u4_l4BlkGL3_mem σ hB)
    (fun M hM B hB hz hdet => u4_mem_SUid_three_of_block σ hM hB hz hdet) hQ₂
    (fun B hB => (mem_SUid.mp hB).1) (fun B hB => u4Eps_blkUp_mem σ hB)
    (fun B hB => u4Eps_blkLow_mem σ hB) (fun M hM hb => u4Eps_mem_SUid_two_of_block σ hM hb)
    hfin ?_ A.2 hA3' hA1' ?_ hD
  · intro u hu hu3
    have h4 : u ^ 4 = 1 := by
      have hd := (mem_SUid.mp hu).1
      rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, det_diagonal, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin] at hd
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hd)
    calc u = u ^ 4 * (u ^ 3)⁻¹ := by group
      _ = 1 := by rw [h4, hu3, inv_one, one_mul]
  · intro M
    rw [u4_mem_SUid_iff σ h hσ, u4_mem_SUid_iff σ h hσ]
    have hdet : ((g * M * g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det =
        (M : Matrix (Fin 4) (Fin 4) K).det := by
      have e : GeneralLinearGroup.det (g * M * g⁻¹) = GeneralLinearGroup.det M := by
        rw [map_mul, map_mul, map_inv, mul_comm (GeneralLinearGroup.det g), mul_inv_cancel_right]
      have e' := congrArg Units.val e
      simpa only [GeneralLinearGroup.val_det_apply] using e'
    rw [hdet]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Subgroup.mul_mem _ (Subgroup.mul_mem _ hgU h2) (Subgroup.inv_mem _ hgU)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have h5 := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgU) h2) hgU
      rwa [show g⁻¹ * (g * M * g⁻¹) * g = M by group] at h5

theorem u4Eps_good_SU4 {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hp2 : p % 3 = 2)
    (A : SUid (unitaryInvolution (GaloisField p (2 * 1)) p 1) 4) (hA3 : A ^ 3 = 1)
    (hA1 : A ≠ 1) :
    GoodEps (Subgroup.centralizer ({(A : GL (Fin 4) (GaloisField p (2 * 1)))} :
      Set (GL (Fin 4) (GaloisField p (2 * 1)))) ⊓
        SUid (unitaryInvolution (GaloisField p (2 * 1)) p 1) 4) := by
  have hpp : p.Prime := Fact.out
  have hK := u4_card_galoisField p
  have h := Sec4.unitaryFieldData_galoisField p 1 le_rfl
  have hσ : ∀ c, unitaryInvolution (GaloisField p (2 * 1)) p 1 c = h.bar c := fun c => by
    rw [unitaryInvolution_apply, h.bar_apply]
  have h3 : (3 : GaloisField p (2 * 1)) ≠ 0 := by
    intro h0
    have h0' : ((3 : ℕ) : GaloisField p (2 * 1)) = 0 := by exact_mod_cast h0
    have hdvd : p ∣ 3 := (CharP.cast_eq_zero_iff (GaloisField p (2 * 1)) p 3).mp h0'
    have := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp hdvd
    omega
  have hp21 : p ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hp2]
  have hpos : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hpp.pos
  obtain ⟨ω, hω2⟩ := u4_exists_cube_root (F := GaloisField p (2 * 1)) (by
    rw [hK, pow_one]
    omega)
  have hmq : 3 ∣ p ^ 1 + 1 := by
    rw [pow_one]
    omega
  have hnq : ((3 : ℕ), p ^ 1) ≠ (3, 2) := by
    intro he
    have : p ^ 1 = 2 := (Prod.mk.inj he).2
    rw [pow_one] at this
    omega
  have hQ : IsQuasisimple (SUid (unitaryInvolution (GaloisField p (2 * 1)) p 1) 3) := by
    rw [SUid_eq_statedSU hK 3]
    exact (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hK le_rfl hnq).1
  have h5 : 5 ≤ p := by
    rcases (show p = 4 ∨ 5 ≤ p by omega) with h4 | h5
    · exact absurd (h4 ▸ hpp) (by norm_num)
    · exact h5
  exact u4Eps_good_SUid _ h hσ hω2 h3 hmq hQ (isQuasisimple_SUid_two h5)
    (fun X _ _ ⟨e⟩ hT => false_of_epsQuot_SUid_two h5 e hT) A hA3 hA1

theorem u4Eps_good_projSU {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hp2 : p % 3 = 2)
    (x : projSU 4 p 1) (hx : orderOf x = 3) :
    GoodEps (Subgroup.centralizer ({x} : Set (projSU 4 p 1))) := by
  have hK := u4_card_galoisField p
  have hproj : projSU 4 p 1 =
      projImage (SUid (unitaryInvolution (GaloisField p (2 * 1)) p 1) 4) := by
    rw [SUid_eq_statedSU hK 4, CFSG.PGLModel.projImage_statedSU]
  let e₀ : projSU 4 p 1 ≃*
      projImage (SUid (unitaryInvolution (GaloisField p (2 * 1)) p 1) 4) :=
    MulEquiv.subgroupCongr hproj
  refine GoodEps.of_mulEquiv_centralizer e₀ ?_
  refine l4Eps_good_proj (SUid (unitaryInvolution (GaloisField p (2 * 1)) p 1) 4) ?_
    (fun A hA3 hA1 => u4Eps_good_SU4 hp hp2 A hA3 hA1) (e₀ x)
    (by rw [MulEquiv.orderOf_eq]; exact hx)
  intro u hu
  have hd := (mem_SUid.mp hu).1
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, det_diagonal, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at hd
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hd)

theorem rowSEpsOf_four_SU_mod_two : ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 2 →
    RowSEpsOf (projSU 4 p 1) := by
  intro p _ hp hp2 S _ _ hs hna ⟨e⟩
  haveI := hs
  exact noCfgSEps_of_goodEps_model e (center_eq_bot_of_simple_nonab hna)
    (not_three_dvd_outer_of_mulEquiv e RonanK432.not_three_dvd_card_outer_projSU_four_prime)
    (fun x hx => u4Eps_good_projSU hp hp2 x hx)

end CFSG.RankThree.PartTwo.Sec4.RonanEps
