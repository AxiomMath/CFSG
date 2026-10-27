module

public import CFSG.CGT.M24R.R3Inputs
import Certificates.Kernel.M24R.R3KChecks
import Certificates.Kernel.M24R.R3Orb
import Certificates.Kernel.PresLetters.F21194
import CFSG.Certificates.Kernel.M24R.R3OrbSound
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import Certificates.Data.Kernel.Bounds.TableFact
public import Mathlib
import CFSG.Certificates.Kernel.BfsPinSound
import CFSG.Certificates.Kernel.HeModelKSound
import CFSG.Certificates.Kernel.HexaKSound
import CFSG.Certificates.Kernel.J2ModelKSound
import CFSG.Certificates.Kernel.Odd87CCKSound
import CFSG.Certificates.Kernel.SporSch.MathieuOCSound
import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase

public section

open CFSG.CGT.M24R CFSG.CGT.M24R.R3 CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Certificates

namespace CertificateChecks.PresLetters21194

#kc_forall_chunks coll (fun k => KB.TableFact 11
  ((relsN8 ++ thetaRels8 ++ [collRel ⟨(k + 1) % 16, Nat.mod_lt _ (by norm_num)⟩]).map encW)
  ((subsetOf 11 (List.range 10)).map fun x => [(x.val, true)]) 1) 15 CFSG.KBFact.F21194c 1

end CertificateChecks.PresLetters21194

namespace Certificates

open CertificateChecks.PresLetters21194 CFSG.KC.M24R3 in
open CFSG.CGT.M24R CFSG.CGT.M24R.R3 CFSG.CosetTable in
theorem certificate21194 : CFSG.CGT.M24R.R3.relCheck = true ∧ identCheck = true ∧ distinctCheck = true ∧
    (∃ Z : List N0Word, Z.length = 20160 ∧ (Z.map CFSG.CGT.M24R.R3.conjKey).Nodup) ∧
    ∀ i : Fin 16, i ≠ 0 →
      (genSub {r : FreeGroup (Fin 11) | r ∈ (relsN8 ++ thetaRels8 ++ [collRel i]).map FreeGroup.mk}
          (subsetOf 11 (List.range 10))).FiniteIndex ∧
        (genSub {r : FreeGroup (Fin 11) | r ∈ (relsN8 ++ thetaRels8 ++ [collRel i]).map
          FreeGroup.mk} (subsetOf 11 (List.range 10))).index ≤ 1 :=
  ⟨relCheck_of ch21194_rel, identCheck_of ch21194_id, distinctCheck_of ch21194_dist,
    orbit_of (orbOK_of_blocks ch21194_orbAll), fun i hi => by
      have h0 : i.val ≠ 0 := fun e => hi (Fin.ext e)
      refine TableFact.genSub_index _ (by norm_num) (subsetOf 11 (List.range 10)) ?_
      have h := coll (i.val - 1) (by have := i.isLt; change i.val - 1 < 15; omega)
      rwa [show (⟨(i.val - 1 + 1) % 16, Nat.mod_lt _ (by norm_num)⟩ : Fin 16) = i from
        Fin.ext (by have := i.isLt; change (i.val - 1 + 1) % 16 = i.val; omega)] at h⟩

end Certificates
