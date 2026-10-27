module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherParabolicData
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherReducedWord
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSubflag

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K]

variable (h : UnitaryFieldData p f K) (r ε : ℕ) in
@[expose] noncomputable def uCitedPar : Subgroup ↥(hypSU h r ε) :=
  flagStabilizer h r ε (Set.Icc 2 r)

variable {r ε : ℕ}

theorem uCited_borel_le_par (h : UnitaryFieldData p f K) :
    hypBorel h r ε ≤ uCitedPar h r ε :=
  hypBorel_le_flagStabilizer (fun _ hi => ⟨(Set.mem_Icc.mp hi).1.trans' (by omega),
    (Set.mem_Icc.mp hi).2⟩)

theorem uCited_hypScalars_le_par (h : UnitaryFieldData p f K) :
    hypScalars h r ε ≤ uCitedPar h r ε :=
  hypScalars_le_flagStabilizer _

theorem uCited_weylRep_zero_mem_par (h : UnitaryFieldData p f K) (hε : ε ≤ 1) (hr : 2 ≤ r)
    {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) :
    uWeylRep ε h (⟨0, by omega⟩ : Fin r) c hc ∈ uCitedPar h r ε := by
  rw [uCitedPar]
  refine (uWeylRep_mem_flagStabilizer_iff h hε hc hc0 (fun _ hi => ⟨(Set.mem_Icc.mp hi).1.trans'
    (by omega), (Set.mem_Icc.mp hi).2⟩) _).mpr ?_
  intro hcon
  have h1 : (0 : ℕ) + 1 ∈ Set.Icc 2 r := hcon
  rw [Set.mem_Icc] at h1
  omega

end CFSG.LocalAnalysis.WeakClosure81

end
