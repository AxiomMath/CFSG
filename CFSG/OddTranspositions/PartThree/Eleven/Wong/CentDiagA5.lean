module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentDiag
import CFSG.LocalAnalysis.ComponentClassification.GS82TheoremDDatum

public section

namespace CFSG.OddTranspositions.PartThree.Wong

theorem sl5_mem_center_iff {x : SL5} : x ∈ Subgroup.center SL5 ↔ x = 1 ∨ x = -1 := by
  constructor
  · intro hx
    obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
    rw [Fintype.card_fin, sq] at hr
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hr' : r = 1 ∨ r = -1 := mul_self_eq_one_iff.mp hr
    rcases hr' with rfl | rfl
    · left
      ext i j
      rw [← hrx]
      simp
    · right
      ext i j
      rw [← hrx, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
      fin_cases i <;> fin_cases j <;> simp <;> rfl
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_center_iff.mpr fun g => by rw [mul_neg_one, neg_one_mul]

namespace SwapData

variable {G : Type} [Group G] (D : SwapData G)

theorem ker_d : D.d.ker = Subgroup.center SL5 := by
  ext x
  rw [MonoidHom.mem_ker, D.d_apply, diag_eq_one_iff D.inj1 D.inj2 D.orderOf_t D.range_inf,
    sl5_mem_center_iff]

theorem nonempty_A_mulEquiv_alt5 : Nonempty (D.A ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := CFSG.ComponentClassification.GS82PumpInputs.TheoremD.nonempty_psl_two_five_equiv
  exact ⟨((QuotientGroup.quotientKerEquivRange D.d).symm.trans
    (QuotientGroup.quotientMulEquivOfEq D.ker_d)).trans e⟩

end SwapData

end CFSG.OddTranspositions.PartThree.Wong
