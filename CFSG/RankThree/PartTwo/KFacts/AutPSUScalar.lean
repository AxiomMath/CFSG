module

public import CFSG.RankThree.PartTwo.KFacts.AutPSU

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.LocalAnalysis.ComponentInitial Matrix

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem scalar_mem_unitaryIsom3_of_norm {c : Kˣ} (hc : h.norm (c : K) = 1) :
    GeneralLinearGroup.scalar (Fin 3) c ∈ unitaryIsom3 h := by
  rw [mem_unitaryIsom3, GeneralLinearGroup.coe_scalar, scalar_apply,
    diagonal_map (map_zero h.bar), diagonal_transpose, diagonal_mul_diagonal]
  have h1 : h.bar (c : K) * (c : K) = 1 := by rw [mul_comm]; exact hc
  simp only [h1]
  exact diagonal_one

theorem psuConj_eq_one_of_coe_eq_scalar {A : unitaryIsom3 h} {c : Kˣ}
    (hA : (A : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) c) : psuConj h A = 1 := by
  have hz : GeneralLinearGroup.scalar (Fin 3) c ∈ Subgroup.center (GL (Fin 3) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  ext x
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [psuConj_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [coe_suConj, Subgroup.coe_inv, hA, ← Subgroup.mem_center_iff.1 hz (g : GL (Fin 3) K), mul_inv_cancel_right]

end CFSG.RankThree.PartTwo.KFacts
