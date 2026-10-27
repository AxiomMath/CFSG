module

public import CFSG.RankThree.PartTwo.KFacts.KS21AutThree
public import CFSG.RankThree.PartTwo.KFacts.KS21L44
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts.KS21.L44

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.RankThreeEven (projSL)

abbrev PL := projectiveSL 4 F4

theorem ringAut_mul_self (σ : F4 ≃+* F4) : σ * σ = 1 := by
  obtain ⟨-, -, -, -, hcard, -⟩ := finite_field_automorphism_fixed_field_cardinality
    (F := F4) Nat.prime_two (n := 2) (by norm_num) (by rw [card_F4]; norm_num)
  have := pow_card_eq_one' (G := F4 ≃+* F4) (x := σ)
  rwa [hcard, sq] at this

theorem conjAut_mem_range (A : GL (Fin 4) F4) :
    conjAut 4 F4 A ∈ (MulAut.conj : PL →* MulAut PL).range := by
  set d := GeneralLinearGroup.det A with hd
  have hd3 : d ^ 3 = 1 := units_pow_three d
  set A' := GeneralLinearGroup.scalar (Fin 4) d⁻¹ * A with hA'
  have hA'det : GeneralLinearGroup.det A' = 1 := by
    rw [hA', map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin, ← hd, inv_pow,
      show d ^ 4 = d ^ 3 * d by rw [pow_succ], hd3, one_mul, inv_mul_cancel]
  let g : SpecialLinearGroup (Fin 4) F4 :=
    ⟨A', by rw [← GeneralLinearGroup.val_det_apply, hA'det, Units.val_one]⟩
  have hg : SpecialLinearGroup.toGL g = A' := Units.ext rfl
  have hA : A = GeneralLinearGroup.scalar (Fin 4) d * SpecialLinearGroup.toGL g := by
    rw [hg, hA', ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  refine ⟨proj 4 F4 g, ?_⟩
  rw [conj_proj_eq_conjAut, hA, map_mul, conjAut_scalar, one_mul]

theorem mem_range_conj_of_pow (α : MulAut PL) (hα : ∃ k : ℕ, α ^ 3 ^ k = 1) :
    α ∈ (MulAut.conj : PL →* MulAut PL).range := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := F4) (n := 4) (by norm_num)
  obtain ⟨A, σ, ε, hε, hαeq⟩ := hgen α
  obtain ⟨-, hff, -, hδδ, -, hδf, -⟩ := standard_automorphism_transport (K := F4) (n := 4)
  set r := fieldAut 4 F4 σ * dualAut 4 F4 ^ ε with hrdef
  have hff1 : fieldAut 4 F4 σ * fieldAut 4 F4 σ = 1 := by
    rw [hff, ringAut_mul_self, map_one]
  have hr : r * r = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
    · rw [hrdef, pow_zero, mul_one, hff1]
    · rw [hrdef, pow_one]
      calc fieldAut 4 F4 σ * dualAut 4 F4 * (fieldAut 4 F4 σ * dualAut 4 F4)
          = fieldAut 4 F4 σ * (dualAut 4 F4 * fieldAut 4 F4 σ * dualAut 4 F4) := by
            simp only [mul_assoc]
        _ = 1 := by rw [hδf, hff1]
  have hc := conjAut_mem_range A
  apply mem_range_conj_of_sq_mem _ hα
  have hαr : α = conjAut 4 F4 A * r := by rw [hαeq, hrdef, mul_assoc]
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr
  rw [hαr, sq]
  have : conjAut 4 F4 A * r * (conjAut 4 F4 A * r) =
      conjAut 4 F4 A * (r * conjAut 4 F4 A * r⁻¹) := by
    rw [hrinv]
    simp only [mul_assoc]
  rw [this]
  exact Subgroup.mul_mem _ hc (conj_range_normal.conj_mem _ hc r)

theorem center_PL : Subgroup.center PL = ⊥ :=
  center_eq_bot_of_mulEquiv ((L44.equivSL.symm).trans
    (CFSG.RankThree.PartTwo.Sec4.projSLEquivProjectiveSL 4 F4)) L44.center_M

theorem autThree_projSL : AutThree (projSL 4 F4) 3 :=
  (autThree_of_inner center_PL mem_range_conj_of_pow 3).of_mulEquiv
    (CFSG.RankThree.PartTwo.Sec4.projSLEquivProjectiveSL 4 F4).symm

end CFSG.RankThree.PartTwo.KFacts.KS21.L44
