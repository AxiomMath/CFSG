module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1MidDefs
public import CFSG.Open.PGLModelDefs
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism
import TauCeti.LinearAlgebra.Matrix.Commute

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open scoped MatrixGroups
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
  (sl2_center_eq_bot sl2EquivPSL2 mulAutToRingAut inner_eq_ker_mulAutToRingAut
    ringAut_card_and_cyclic)

section Aux

variable {F : Type} [Field F]

private theorem not_mem_range_scalar_of_orderOf_three [CharP F 2] {y : SL(2, F)}
    (hy : orderOf y = 3) :
    (y : Matrix (Fin 2) (Fin 2) F) ∉ Set.range (Matrix.scalar (Fin 2)) := by
  rintro ⟨c, hc⟩
  have hdet : c ^ Fintype.card (Fin 2) = 1 := by
    have h := y.2
    rw [← hc] at h
    simpa [Matrix.scalar_apply, Matrix.det_diagonal, pow_two] using h
  have hmem : y ∈ Subgroup.center SL(2, F) :=
    Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨c, hdet, hc⟩
  rw [sl2_center_eq_bot, Subgroup.mem_bot] at hmem
  rw [hmem, orderOf_one] at hy
  exact absurd hy (by decide)

private theorem sl2_commute_of_nonscalar_centralizer {y a b : SL(2, F)}
    (hy : (y : Matrix (Fin 2) (Fin 2) F) ∉ Set.range (Matrix.scalar (Fin 2)))
    (ha : a * y = y * a) (hb : b * y = y * b) : a * b = b * a := by
  have hmat : ∀ x : SL(2, F), x * y = y * x → Commute (y : Matrix (Fin 2) (Fin 2) F) x := by
    intro x hx
    have h := congrArg (fun z : SL(2, F) => (z : Matrix (Fin 2) (Fin 2) F)) hx
    have h' : (y : Matrix (Fin 2) (Fin 2) F) * x = x * y := by
      simpa only [Matrix.SpecialLinearGroup.coe_mul] using h.symm
    exact h'
  exact Subtype.ext (TauCeti.commute_of_commute_fin_two hy (hmat a ha) (hmat b hb)).eq

end Aux

private theorem mulAut_comm_of_fix {F : Type} [Field F] {n : ℕ} (hcard : Nat.card F = 2 ^ n)
    {y : SL(2, F)}
    (hy : (y : Matrix (Fin 2) (Fin 2) F) ∉ Set.range (Matrix.scalar (Fin 2)))
    {α β : MulAut SL(2, F)} (hα : mulAutToRingAut hcard α = 1) (hβ : mulAutToRingAut hcard β = 1)
    (hαy : α y = y) (hβy : β y = y) : α * β = β * α := by
  have hcom : ∀ γ : MulAut SL(2, F), mulAutToRingAut hcard γ = 1 → γ y = y →
      ∃ g : SL(2, F), MulAut.conj g = γ ∧ g * y = y * g := by
    intro γ hγ hγy
    have hγ' : γ ∈ inner SL(2, F) := by
      rw [inner_eq_ker_mulAutToRingAut hcard]
      exact hγ
    obtain ⟨g, rfl⟩ := hγ'
    refine ⟨g, rfl, ?_⟩
    rw [MulAut.conj_apply] at hγy
    exact mul_inv_eq_iff_eq_mul.mp hγy
  obtain ⟨a, rfl, ha⟩ := hcom α hα hαy
  obtain ⟨b, rfl, hb⟩ := hcom β hβ hβy
  rw [← map_mul, ← map_mul, sl2_commute_of_nonscalar_centralizer hy ha hb]

private theorem res1AutSolv_sl2 {n : ℕ} (hn : 1 ≤ n) :
    Res1AutSolv SL(2, GaloisField 2 n) := by
  intro y hy V hV
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  haveI : IsCyclic (RingAut (GaloisField 2 n)) := (ringAut_card_and_cyclic hcard).2
  have hnc := not_mem_range_scalar_of_orderOf_three (F := GaloisField 2 n) hy
  let ψ : V →* RingAut (GaloisField 2 n) := (mulAutToRingAut hcard).comp V.subtype
  have hcomm : ∀ a b : ψ.ker, a * b = b * a := by
    rintro ⟨⟨α, hαV⟩, hα⟩ ⟨⟨β, hβV⟩, hβ⟩
    exact Subtype.ext (Subtype.ext
      (mulAut_comm_of_fix hcard hnc hα hβ (hV α hαV) (hV β hβV)))
  haveI : Group.IsSolvable ψ.ker := Group.isSolvable_of_comm hcomm
  exact Group.isSolvable_of_ker_le_range ψ.ker.subtype ψ (by rw [Subgroup.range_subtype])

theorem res1AutSolv_projSL_two {n : ℕ} (hn : 1 ≤ n) :
    Res1AutSolv ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n)) :=
  Res1AutSolv.of_mulEquiv
    ((CFSG.RankThree.PartTwo.Sec4.projSLEquivPSL (GaloisField 2 n)).trans
      (sl2EquivPSL2 (F := GaloisField 2 n)).symm)
    (res1AutSolv_sl2 hn)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
