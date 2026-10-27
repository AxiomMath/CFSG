module

public import CFSG.Milestones.ASVolI.C31.J4NP.VerdictJFacts
import Certificates.Kernel.J4NPVerdict.Glue
import Certificates.Kernel.J4NPVerdict.C7953

public section

namespace Certificates

open CFSG.Sporadic.J4 CFSG.KC.J4NPV CertificateChecks.KernelJ4NPV CFSG.J4Tree.M4
  CFSG.J4Tree.Native

theorem certificate7953 : CFSG.ASVolI.burnsideJ4NP_ConjW539 (CFSG.ASVolI.burnsideJ4NP_Wv 486) ∧
    CFSG.ASVolI.burnsideJ4NP_ConjW539 (CFSG.ASVolI.burnsideJ4NP_Wv 542) ∧
    CFSG.ASVolI.burnsideJ4NP_ConjW539 (Subgroup.closure
      {g | g ∈ CFSG.J4Tree.M4.y136.map CFSG.ASVolI.burnsideJ4NP_treeElt}) ∧
    CFSG.ASVolI.burnsideJ4NP_ConjW539 (Subgroup.closure
      {g | g ∈ CFSG.J4Tree.M4.y266.map CFSG.ASVolI.burnsideJ4NP_treeElt}) := by
  have hall := vj_chunk (f := conjB vjT (treeWv 539)) (n := 4) (m := 1)
    (ds := [c486, c542, c136, c266]) (by decide) (fun i hi => by
      interval_cases i
      exact vj7953c0)
  have key : ∀ d ∈ [c486, c542, c136, c266], ∀ X : Subgroup J, vjSub d.tgt = X →
      CFSG.ASVolI.burnsideJ4NP_ConjW539 X := by
    intro d hd X hX
    obtain ⟨m, hm⟩ := conjB_eq vj_tabs (hall d hd)
    refine ⟨m, ?_⟩
    rw [← hX, hm]
    rfl
  have e486 : c486.tgt = treeWv 486 := by simp only [c486]
  have e542 : c542.tgt = treeWv 542 := by simp only [c542]
  have e136 : c136.tgt = y136 := by
    unfold c136
    rfl
  have e266 : c266.tgt = y266 := by
    unfold c266
    rfl
  refine ⟨key c486 (by simp only [List.mem_cons, true_or]) _ ?_,
    key c542 (by simp only [List.mem_cons, true_or, or_true]) _ ?_,
    key c136 (by simp only [List.mem_cons, true_or, or_true]) _ ?_,
    key c266 (by simp only [List.mem_cons, true_or, or_true]) _ ?_⟩
  · rw [e486]
    rfl
  · rw [e542]
    rfl
  · rw [e136]
    rfl
  · rw [e266]
    rfl

end Certificates
