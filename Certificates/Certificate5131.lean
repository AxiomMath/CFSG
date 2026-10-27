module

public import Mathlib
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.CharacterTheory.Burnside
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFusion
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverLiftClasses
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Check
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Data
public import CFSG.GH74.KGroups.TwoM12CheckInputs
import CFSG.Certificates.Kernel.PermCent.CVSound
import Certificates.Kernel.PermCent.K5131
public import Certificates.Data.Kernel.PermCent.CV

public section

open CFSG.GH74.KGroups CFSG.GH74.KGroups.TwoM12 CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.M12Cover CFSG.Certificates.Kernel.PkCV

namespace Certificates

set_option compiler.extract_closed false in
open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.TwoM12 in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu in
open CFSG.ComponentClassification.M12Cover CFSG.Blueprint Subgroup in
open scoped commutatorElement in
theorem certificate5131 : commCheckOn fixedDQ.orbitTables (elemsT m12CentQ2) = true := by
  have e : ∀ L, commCheckOn fixedDQ.orbitTables L = L.all fun a => L.all fun b =>
      fixedDQ.sift (gzPerm * (a * b * a⁻¹ * b⁻¹) * gzPerm⁻¹) 0 := fun _ => rfl
  rw [e, elemsT_eq_elemsC, eq_ev_cOf gzPerm]
  simp only [List.all_map, Function.comp_def, ev_mul', ev_inv', sift_ev]
  exact K5131.k5131

end Certificates
