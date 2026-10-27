module

public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.Descent
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverFinal
public import CFSG.Quasithin.Background.Harris.L2.Main
public import CFSG.Quasithin.Background.Harris.L2.Natural
public import CFSG.Quasithin.Background.Harris.L2.OmegaMinus
public import CFSG.Quasithin.Background.Harris.L2.Steinberg8
public import CFSG.Foundations
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut

public section

namespace CFSG.Quasithin.G11.Harris

open CFSG.Blueprint

theorem g93Stmt_of_families
    (hT : TwoComp)
    (h5 : OneCompFor (FamAlt 5)) (h6 : OneCompFor (FamAlt 6)) (h7 : OneCompFor (FamAlt 7))
    (h8 : OneCompFor (FamAlt 8)) (hOL2S : OneCompFor FamOddL2Small)
    (hOL2B : OneCompFor FamOddL2Big) (hOL3 : OneCompFor FamOddL3) (hU33 : OneCompFor FamU33)
    (hOU3B : OneCompFor FamOddU3Big) (hL3 : OneCompFor FamL3) (hU3 : OneCompFor FamU3)
    (hSp4 : OneCompFor FamSp4) (hG2 : OneCompFor FamG2) (h3D4 : OneCompFor Fam3D4)
    (h2F4 : OneCompFor Fam2F4) (hSz : OneCompFor FamSz) (hTits : OneCompFor FamTits)
    (hL4 : OneCompFor (FamLn2 4)) (hL5 : OneCompFor (FamLn2 5))
    (hSpor : ∀ s : TauCeti.SporadicName, (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨
      s = .J1 ∨ s = .J2 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) → OneCompFor (FamSpor s))
    (hCSL3 : OneCompFor FamCoverSL3Two) (hCSU3 : OneCompFor FamCoverSU3Two)
    (hCOdd : OneCompFor FamCoverOdd) (hA6 : OneCompFor (FamHat (alternatingGroup (Fin 6))))
    (hA7 : OneCompFor (FamHat (alternatingGroup (Fin 7))))
    (hM22 : OneCompFor (FamHat (NativeSporadic.Carrier .M22))) :
    G93Stmt :=
  g93Stmt_of_interfaces (Background.Harris.CaseClassificationAndDescent.descentOne_of_threeCover
      CFSG.QuasithinUnique.Vol2Native.threeCoverFactCat) hT
    (oneCompFor_compType h5 h6 h7 h8 (oneCompFor_famOddL2 hOL2S hOL2B) hOL3
      (oneCompFor_famOddU3 hU33 hOU3B) (L2.oneCompFor_famL2_of_cases L2.case6_holds L2.case7_holds
          L2.case16_holds) hL3 hU3 hSp4 hG2 h3D4 h2F4 hSz hTits
      hL4 hL5 hSpor (oneCompFor_famCoverSL3 hCSL3 hCSU3 hCOdd) hA6 hA7 hM22)

end CFSG.Quasithin.G11.Harris
