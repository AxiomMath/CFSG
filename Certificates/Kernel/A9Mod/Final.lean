module

public import Certificates.Kernel.A9Mod.Checks
public import CFSG.Certificates.Kernel.A9Mod.Sound

public section

local instance (priority := high) CFSG.KD.A9Mod.instAddCommGroupZMod2Final :
    AddCommGroup (ZMod 2) :=
  Ring.toAddCommGroup

namespace CFSG.KD.A9Mod

open CFSG.KC.A9Mod CFSG.Sporadic.Th.Recog CFSG.Sporadic.Th.Recog.A9Mod

theorem conjToTarget_all (σ : alternatingGroup (Fin 9) →* Module.End (ZMod 2) V8)
    (hg : σ eltG = toLin N1 ∨ σ eltG = toLin N2) : ConjToTarget σ := by
  rcases hg with hg | hg
  · refine s1OK_sound σ N1Q spin1a recs1a _ ch687010s1a (fun R hR τ hτ h1 => ?_)
      (by rw [lin_N1Q, hg])
    obtain ⟨nd, hnd, rfl⟩ := mem_repsOf hR
    rcases List.mem_singleton.1 hnd with rfl
    exact nodeOK_sound τ N1Q _ ch687010n1a hτ h1
  · refine s1OK_sound σ N2Q spin1b recs1b _ ch687010s1b (fun R hR τ hτ h1 => ?_)
      (by rw [lin_N2Q, hg])
    obtain ⟨nd, hnd, rfl⟩ := mem_repsOf hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hnd
    rcases hnd with rfl | rfl | rfl
    · exact nodeOK_sound τ N2Q _ ch687010n2a hτ h1
    · exact nodeOK_sound τ N2Q _ ch687010n2b hτ h1
    · exact nodeOK_sound τ N2Q _ ch687010n2c hτ h1

end CFSG.KD.A9Mod
