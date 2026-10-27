module

public import CFSG.Quasithin.H13.U4ParModel
public import CFSG.Quasithin.H13.U4ParLine
public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.H13.U4Par

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem isLieOverTwo_psu4 : CFSG.Quasithin.IsLieOverTwo .PSU 4 m (hypSU h 2 0) := by
  refine (CFSG.Blueprint.LieModel.classical_iff (t := .PSU) (by decide)).2 ?_
  obtain ⟨e⟩ := nonempty_hypSU_equiv_statedProj h
  refine ⟨⟨Nat.prime_two, h.one_le, by norm_num, by simp⟩, K, inferInstance, h.finite, ?_, ⟨e⟩⟩
  rw [h.card, ← pow_mul, mul_comm]

theorem sAdm_of_y_zero_iff {x c : K} : SAdm h x 0 c ↔ h.bar c = c := by
  have := h.charP
  unfold SAdm
  simp only [map_zero, mul_zero, zero_mul, add_zero]
  constructor
  · intro hc
    have : h.bar c = -c := eq_neg_of_add_eq_zero_right hc
    rw [this, CharTwo.neg_eq]
  · intro hc
    rw [hc, CharTwo.add_self_eq_zero]

theorem isQ2Mat_sMat_zero (x c : K) : IsQ2Mat (sMat h x 0 c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [sMat_apply, one_apply, ie1, ie2, if1, if2]

theorem mem_radQ_inf_radQ2_iff {g : hypSU h 2 0} :
    g ∈ radQ h ⊓ radQ2 h ↔
      ∃ x c : K, h.bar c = c ∧ ((g : GL Ix K) : Matrix Ix Ix K) = sMat h x 0 c := by
  constructor
  · rintro ⟨⟨x, y, c, hc, hg⟩, hg2⟩
    have hy : h.bar y = 0 := by
      have hq : IsQ2Mat ((g : GL Ix K) : Matrix Ix Ix K) := hg2
      have h12 := hq.2.1
      rw [hg] at h12
      simpa [sMat_apply, one_apply, ie1, ie2, if1, if2] using h12
    have hy0 : y = 0 := by
      rw [← h.bar_bar y, hy, map_zero]
    subst hy0
    exact ⟨x, c, (sAdm_of_y_zero_iff h).mp hc, hg⟩
  · rintro ⟨x, c, hc, hg⟩
    refine ⟨⟨x, 0, c, (sAdm_of_y_zero_iff h).mpr hc, hg⟩, ?_⟩
    show IsQ2Mat ((g : GL Ix K) : Matrix Ix Ix K)
    rw [hg]
    exact isQ2Mat_sMat_zero h x c

end CFSG.Quasithin.F112R.St84

end
