module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8H1Gens

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.StandardType.Triality CFSG.LieType.SpinGeom CFSG.Quasithin.JonesParshall
open scoped Matrix

theorem exists_cob_stab {f : ↥spinH → Fin 8 → ZMod 2} (hf : f ∈ Z1A spinMu) :
    ∃ x : Fin 8 → ZMod 2, ∀ h : ↥spinH,
      (h : MulAut SpinW) (Multiplicative.ofAdd (frameE (ZMod 2) 0)) =
          Multiplicative.ofAdd (frameE (ZMod 2) 0) →
        f h = spinMu h x - x := by
  obtain ⟨x, hx⟩ := exists_cob_of_foxCert spinMu gensP matsP spinMu_gensP relsP
    wordEval_relsP (fun l => bitMat (certPRows l)) (fun j r => bitMat (certCRows j r))
    certP_spec hf
  refine ⟨x, fun h hh => ?_⟩
  have hf' : f - coboundaryA spinMu x ∈ Z1A spinMu :=
    sub_mem hf (B1A_le_Z1A spinMu ⟨x, rfl⟩)
  have hle : Subgroup.closure (Set.range gensP) ≤ vanishSubgroup hf' :=
    (Subgroup.closure_le (vanishSubgroup hf')).mpr (by
      rintro _ ⟨j, rfl⟩
      change f (gensP j) - (spinMu (gensP j) x - x) = 0
      rw [hx j, sub_self])
  have h0 : (f - coboundaryA spinMu x) h = 0 := hle (stab_le_closure h hh)
  exact sub_eq_zero.mp h0

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
