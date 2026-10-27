module

public import CFSG.Timmesfeld.Transvection.ModelRankSp

public section

namespace CFSG.Timmesfeld.Transvection

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM

namespace ModelRank

variable {n : ℕ} {K : Type} [Field K]

theorem exists_eq_smul_of_spForm_imp {v w : Fin n ⊕ Fin n → K}
    (h : ∀ u, spForm v u = 0 → spForm w u = 0) : ∃ l : K, w = l • v := by
  have hle : (⨅ _ : Unit, LinearMap.ker (spFormL v)) ≤ LinearMap.ker (spFormL w) := by
    intro u hu
    rw [Submodule.mem_iInf] at hu
    exact h u (hu ())
  have hmem := mem_span_of_iInf_ker_le_ker (L := fun _ : Unit => spFormL v) hle
  rw [Set.range_const, Submodule.mem_span_singleton] at hmem
  obtain ⟨l, hl⟩ := hmem
  refine ⟨l, ?_⟩
  by_contra hne
  obtain ⟨y, hy⟩ := exists_spForm_ne_zero (sub_ne_zero.2 hne)
  apply hy
  have hly : l * spForm v y = spForm w y := congrArg (fun f => f y) hl
  rw [spForm_sub_left, spForm_smul_left', hly, sub_self]

end ModelRank

end CFSG.Timmesfeld.Transvection
