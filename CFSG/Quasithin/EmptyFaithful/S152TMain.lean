module

public import CFSG.Quasithin.EmptyFaithful.S152SMain
public import CFSG.Quasithin.EmptyFaithful.S152TBender
public import CFSG.Quasithin.EmptyFaithful.S152TL3
public import CFSG.Quasithin.EmptyFaithful.S152TSp4
public import CFSG.Quasithin.EmptyFaithful.S152TG2
public import CFSG.Quasithin.EmptyFaithful.S152T3D4
public import CFSG.Quasithin.EmptyFaithful.S152T2F4
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L34Size
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma37
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.Milestones.CL_LIT_SQTK_simple_list
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.FFC5Case1
public import CFSG.Quasithin.Background.FFC5Main
public import CFSG.Quasithin.EmptyFaithful.R3c2List
public import CFSG.Quasithin.EmptyFaithful.R3c6Exc
public import CFSG.Quasithin.EmptyFaithful.S153D25
public import CFSG.Quasithin.EmptyFaithful.S153D43
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Walter.J1
public import Certificates.Certificate8026Base

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1

section BigQ


theorem bigQBorelCentralizerTrivial_proof : BigQBorelCentralizerTrivial :=
  BigQBorelCentralizerTrivial.of_families bctFamL2_proof bctFamL3_proof bctFamU3_proof
    bctFamSp4_proof bctFamG2_proof bctFam3D4_proof bctFam2F4_proof bctFamSz_proof

end BigQ

section Main


theorem insp15224NoF2_proof (hA3 : ∀ (G : Type) [Group G] [Finite G], A3Orbits G) :
    Insp15224NoF2 :=
  insp15224NoF2_of_bigQ hA3 bigQBorelCentralizerTrivial_proof

end Main

end CFSG.Quasithin
