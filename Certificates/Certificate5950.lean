module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM12ModelData
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.M12SigCheckInputs
import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.Assembly.RankThreeEvenDefs

public section

open CFSG
open CFSG.RankThree
open CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Sporadic
open CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig
open CFSG CFSG.GH74.M12.Hyp CFSG.RankThree.PartTwo.Toolkit.M12 CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4 Subgroup CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.RankThree.Asc83Table
open scoped commutatorElement

namespace CertificateChecks.Batch5950

open CFSG
open CFSG.RankThree
open CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Sporadic
open CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig
open CFSG CFSG.GH74.M12.Hyp CFSG.RankThree.PartTwo.Toolkit.M12 CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4 Subgroup CFSG.Blueprint CFSG.ComponentClassification.M12Cover
  CFSG.RankThree.Asc83Table
open scoped commutatorElement

private theorem tbl_m12bp_0 : tbl CFSG.Sporadic.Schreier.m12bp = tBp := by
  decide +kernel

end CertificateChecks.Batch5950

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.RankThree in
open CFSG.RankThree.PartTwo in
open CFSG.RankThree.PartTwo.Sec4 in
open CFSG.RankThree.PartTwo.Sec4.Sporadic in
open CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig in
open CFSG CFSG.GH74.M12.Hyp CFSG.RankThree.PartTwo.Toolkit.M12 CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4 Subgroup CFSG.Blueprint CFSG.RankThree.Asc83Table in
open scoped commutatorElement in
theorem certificate5950 : tbl CFSG.Sporadic.Schreier.m12bp = tBp := by
  exact CertificateChecks.Batch5950.tbl_m12bp_0

end Certificates
