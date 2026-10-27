module

public import Certificates.Data.GrSLitL34FactsSpMultJ3UC
public import CFSG.Sporadic.J3.Group
public import CFSG.Sporadic.Bridge.TwoGen
public import Certificates.Data.CFSGNative.J3.Data
import Certificates.Kernel.PresLetters.F22224Glue

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelPresLetters.F22224Glue

open CFSG.ComponentClassification.GSThmB.SpMult CFSG.CosetTable CFSG.Sporadic.Bridge.TwoGen in
open CFSG.Sporadic.J3 (a b J) in
open CFSG.Sporadic.J3.Native (j3Data) in
theorem certificate22224 :
    ((Subgroup.closure {ucUe, ucCe}).FiniteIndex ∧
      (Subgroup.closure {ucUe, ucCe}).index ≤ 6156) ∧
    (Finite (PG 2 gammaRels) ∧ Nat.card (PG 2 gammaRels) ≤ 8160) ∧
    (∀ w ∈ ucABWords, FreeGroup.lift (fun i : Fin 2 => img2 (CFSG.Sporadic.J3.a j3Data) (b j3Data) i.val)
      (FreeGroup.mk w) = 1) ∧
    (∀ w ∈ gammaJ3Words,
      FreeGroup.lift ![FreeGroup.lift (fun i : Fin 2 => img2 (CFSG.Sporadic.J3.a j3Data) (b j3Data) i.val)
          (FreeGroup.mk ucU),
        FreeGroup.lift (fun i : Fin 2 => img2 (CFSG.Sporadic.J3.a j3Data) (b j3Data) i.val) (FreeGroup.mk ucC)]
        (FreeGroup.mk w) = 1) :=
  ⟨uc_index, gamma_card, fun _ hw => ab_words hw, fun _ hw => uc_words hw⟩

end Certificates
