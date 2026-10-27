module

public import CFSG.RankThree.PartTwo.KFacts.KS21AutThree
public import CFSG.RankThree.PartTwo.KFacts.KS21Sp64
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherGeneration
public import CFSG.Timmesfeld.Transvection.PresSp

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts.KS21.Sp64

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.RankThreeEven (projSp)

abbrev PS := StatedProj (StatedSp 3 F4)

theorem ringAut_mul_self (σ : F4 ≃+* F4) : σ * σ = 1 := by
  obtain ⟨-, -, -, -, hcard, -⟩ := finite_field_automorphism_fixed_field_cardinality
    (F := F4) Nat.prime_two (n := 2) (by norm_num) (by rw [card_F4]; norm_num)
  have := pow_card_eq_one' (G := F4 ≃+* F4) (x := σ)
  rwa [hcard, sq] at this

theorem conjAut_mem_range (A : gsp 3 F4) :
    conjAut 3 F4 A ∈ (MulAut.conj : PS →* MulAut PS).range := by
  set μ := multiplier 3 F4 A with hμ
  have hμ3 : μ ^ 3 = 1 := units_pow_three μ
  set c : F4ˣ := (μ ^ 2)⁻¹ with hc
  set A' : GL (Fin 3 ⊕ Fin 3) F4 :=
    GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3) c * (A : GL (Fin 3 ⊕ Fin 3) F4) with hA'
  have hcoe : ((A' : GL (Fin 3 ⊕ Fin 3) F4) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F4) =
      (c : F4) • ((A : GL (Fin 3 ⊕ Fin 3) F4) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F4) := by
    rw [hA', Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply, smul_eq_diagonal_mul]
  have hcμ : (c : F4) * c * μ = 1 := by
    rw [← Units.val_mul, ← Units.val_mul, hc, ← mul_inv, ← pow_two, ← pow_mul,
      show μ ^ (2 * 2) = μ ^ 3 * μ by rw [← pow_succ], hμ3, one_mul, inv_mul_cancel,
      Units.val_one]
  have hA'Sp : A' ∈ StatedSp 3 F4 := by
    rw [SymplecticTorusWeyl.mem_statedSp_iff, hcoe, transpose_smul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have h : ((A : GL (Fin 3 ⊕ Fin 3) F4) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F4)ᵀ *
        fromBlocks 0 1 (-1) 0 *
          ((A : GL (Fin 3 ⊕ Fin 3) F4) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F4) =
        (μ : F4) • fromBlocks 0 1 (-1) 0 := multiplier_spec A
    rw [h, smul_smul, hcμ, one_smul]
  refine ⟨proj 3 F4 ⟨A', hA'Sp⟩, ?_⟩
  ext x
  obtain ⟨h, rfl⟩ := SymplecticHigher.proj_surjective x
  rw [MulAut.conj_apply, conjAut_proj, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [coe_conjSp]
  have hcen : GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3) c ∈
      Subgroup.center (GL (Fin 3 ⊕ Fin 3) F4) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  have hcomm := Subgroup.mem_center_iff.mp hcen
  change A' * (h : GL (Fin 3 ⊕ Fin 3) F4) * A'⁻¹ = _
  set s := GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3) c
  set B := (A : GL (Fin 3 ⊕ Fin 3) F4)
  set H := (h : GL (Fin 3 ⊕ Fin 3) F4)
  rw [hA', _root_.mul_inv_rev]
  calc s * B * H * (B⁻¹ * s⁻¹) = s * (B * H * B⁻¹) * s⁻¹ := by simp only [mul_assoc]
    _ = B * H * B⁻¹ * s * s⁻¹ := by rw [← hcomm (B * H * B⁻¹)]
    _ = B * H * B⁻¹ := by rw [mul_inv_cancel_right]

theorem mem_range_conj_of_pow (α : MulAut PS) (hα : ∃ k : ℕ, α ^ 3 ^ k = 1) :
    α ∈ (MulAut.conj : PS →* MulAut PS).range := by
  obtain ⟨-, hgen⟩ := SymplecticHigher.automorphism_generation (K := F4) (r := 3) (by norm_num)
  obtain ⟨A, σ, hαeq⟩ := hgen α
  have hff1 : fieldAut 3 F4 σ * fieldAut 3 F4 σ = 1 := by
    rw [← map_mul, ringAut_mul_self, map_one]
  have hc := conjAut_mem_range A
  apply mem_range_conj_of_sq_mem _ hα
  have hrinv : (fieldAut 3 F4 σ)⁻¹ = fieldAut 3 F4 σ := inv_eq_of_mul_eq_one_right hff1
  have : α ^ 2 = conjAut 3 F4 A * (fieldAut 3 F4 σ * conjAut 3 F4 A * (fieldAut 3 F4 σ)⁻¹) := by
    rw [hαeq, sq, hrinv]
    simp only [mul_assoc]
  rw [this]
  exact Subgroup.mul_mem _ hc (conj_range_normal.conj_mem _ hc _)

@[expose] def psEquivSp : PS ≃* Sp :=
  (QuotientGroup.quotientMulEquivOfEq scalars_eq_bot).trans QuotientGroup.quotientBot

theorem center_PS : Subgroup.center PS = ⊥ :=
  center_eq_bot_of_mulEquiv psEquivSp.symm
    (CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (by norm_num))

theorem autThree_projSp : AutThree (projSp 3 F4) 3 :=
  (autThree_of_inner center_PS mem_range_conj_of_pow 3).of_mulEquiv
    (equivSp.trans psEquivSp.symm).symm

end CFSG.RankThree.PartTwo.KFacts.KS21.Sp64
