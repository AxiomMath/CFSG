module

public import CFSG.Monster.Schur.M24Cast
public import CFSG.Monster.Schur.M24.Words
public import CFSG.Certificates.Kernel.Bounds.M24Alt.Binding
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

open CFSG CFSG.Monster CFSG.Monster.Schur CFSG.Monster.Schur.M24
open TauCeti

namespace CertificateChecks.Batch9267

open CFSG CFSG.Monster CFSG.Monster.Schur CFSG.Monster.Schur.M24
open TauCeti

theorem castTo_mem (w : List (Fin 2 × Bool))
    (hw : w.map (fun x => ((x.1 : ℕ), x.2)) ∈ CFSG.KBAlt.M24.rels) :
    castTo w ∈ pres.relators := by
  have e : pres.relatorLetters = CFSG.KBAlt.M24.rels := CFSG.KBAlt.M24.rels_eq
  have key : (castTo w).map (fun l => (l.1.val, l.2)) ∈ pres.relatorLetters := by
    rw [e]
    simpa [castTo, idx, List.map_map, Function.comp_def] using hw
  rw [GroupPresentation.relatorLetters_def, List.mem_map] at key
  obtain ⟨r, hr, he⟩ := key
  have hinj : Function.Injective
      (List.map (fun l : Fin pres.generatorCount × Bool => (l.1.val, l.2))) := by
    apply List.map_injective_iff.mpr
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Fin.ext h.1) h.2
  rwa [← hinj he]

end CertificateChecks.Batch9267

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.Schur CFSG.Monster.Schur.M24 in
open TauCeti in
theorem certificate9267 : (castTo a2 ∈ pres.relators)
    ∧ (castTo b3 ∈ pres.relators)
    ∧ (castTo ab23 ∈ pres.relators)
    ∧ (castTo r5 ∈ pres.relators)
    ∧ (castTo r6 ∈ pres.relators)
    ∧ (castTo r7 ∈ pres.relators) := by
  exact ⟨CertificateChecks.Batch9267.castTo_mem _ (by decide +kernel),
    CertificateChecks.Batch9267.castTo_mem _ (by decide +kernel), CertificateChecks.Batch9267.castTo_mem _ (by decide +kernel),
    CertificateChecks.Batch9267.castTo_mem _ (by decide +kernel), CertificateChecks.Batch9267.castTo_mem _ (by decide +kernel),
    CertificateChecks.Batch9267.castTo_mem _ (by decide +kernel)⟩

end Certificates
