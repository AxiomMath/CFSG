module

public import CFSG.Sporadic.Fi23.Rigid
public import CFSG.Fischer.Polar.Facts
public import CFSG.Sporadic.Fi22.LH.Facts
public import Certificates.Certificate744108

public section

namespace CFSG.Sporadic.Fi23

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem fi23_inner_index_nine_package :
    InnerIndexNinePackage ↥J :=
  Certificates.certificate744108

theorem fi23_index_nine_package :
    IndexNinePackage ↥J :=
  IndexNinePackage.of_inner (fun β => by
    obtain ⟨g, hg⟩ := fi23_complete CFSG.Fischer.polarFacts CFSG.Fischer.hyperovalFacts
      (CFSG.Sporadic.Fi22.fi22Facts CFSG.Fischer.polarFacts CFSG.Fischer.hyperovalFacts) β
    exact ⟨g, fun z => by rw [hg, MulAut.conj_apply]⟩) fi23_inner_index_nine_package

end CFSG.Sporadic.Fi23
