module

public import CFSG.Quasithin.Background.Harris.Assembly
public import CFSG.Quasithin.Background.Harris.L3.Final
public import CFSG.Quasithin.Background.Harris.Sp4.Final
public import CFSG.Quasithin.Background.Harris.Alt6.Final
public import CFSG.Quasithin.Background.Harris.Routing.Small
public import CFSG.Quasithin.Background.Harris.Routing.Exclusions
public import CFSG.Quasithin.Background.Harris.Routing.IMBCases
public import CFSG.Quasithin.Background.Harris.Routing.A7M12
public import CFSG.Quasithin.Background.Harris.Routing.LieExclusions
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Route3D4
public import CFSG.Quasithin.Background.Harris.G2.Final
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.CoverSU3
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.OddWrappers
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.CoverOdd
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.Final
public import CFSG.Quasithin.Background.Harris.Ln2.Final4
public import CFSG.Quasithin.Background.Harris.Ln2.Final5

public section

namespace CFSG.Quasithin.G11.Harris

open CFSG.Open CFSG.Blueprint
open CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent

theorem g93Stmt_of_open
    (hTits : OneCompFor FamTits) : G93Stmt := by
  refine g93Stmt_of_families TwoComp.twoComp_holds oneCompFor_famAlt5 Alt6.oneCompFor_famAlt6
    oneCompFor_famAlt7 (oneCompFor_famAlt8_of Ln2.oneCompFor_famLn2_four)
    (oneCompFor_famOddL2Small_of L3.oneCompFor_famL3 Alt6.oneCompFor_famAlt6) oneCompFor_famOddL2Big
    oneCompFor_famOddL3 G2.oneCompFor_famU33 oneCompFor_famOddU3Big L3.oneCompFor_famL3
    oneCompFor_famU3 Sp4.oneCompFor_famSp4 G2.oneCompFor_famG2 oneCompFor_fam3D4
    oneCompFor_fam2F4 oneCompFor_famSz hTits Ln2.oneCompFor_famLn2_four
    Ln2.oneCompFor_famLn2_five ?_ L3.oneCompFor_famCoverSL3Two
    CFSG.Quasithin.Background.Harris.OrdinaryProofs.oneCompFor_famCoverSU3Two
    oneCompFor_famCoverOdd oneCompFor_famHat_A6 oneCompFor_famHat_A7 oneCompFor_famHat_M22
  intro s hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact oneCompFor_famSpor_M11
  · exact oneCompFor_famSpor_M12
  · exact oneCompFor_famSpor_M22
  · exact oneCompFor_famSpor_M23
  · exact oneCompFor_famSpor_M24
  · exact oneCompFor_famSpor_J1
  · exact oneCompFor_famSpor_J2
  · exact oneCompFor_famSpor_J4
  · exact oneCompFor_famSpor_HS
  · exact oneCompFor_famSpor_He
  · exact oneCompFor_famSpor_Ru

end CFSG.Quasithin.G11.Harris
