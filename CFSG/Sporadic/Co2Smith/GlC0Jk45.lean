module

public import CFSG.Sporadic.Co2Smith.GlC0QuotCheck
public import CFSG.Sporadic.Co2Smith.GlC0JkInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
import Certificates.Kernel.Co2Smith.Mark
import Certificates.Data.Kernel.Co2Smith.Rows
import Mathlib.Logic.Equiv.Defs
import Certificates.Data.Kernel.Census.CatFacts.PkDefs
import Certificates.Kernel.Co2Smith.LettersData
import Certificates.Kernel.Co2Smith.JkData
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
public import Certificates.Certificate21165
public import CFSG.Certificates.CosetTableShort
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import CFSG.Sporadic.Co2Rank3.AutBound
public import CFSG.Sporadic.Co2Smith.CInvar
public import CFSG.Sporadic.Co2Smith.CTree
public import CFSG.Sporadic.Co2Smith.ClassCountFin
public import CFSG.Sporadic.Co2Smith.GlC0MarkFix
public import CFSG.Sporadic.Co2Smith.GlC0Marking
public import CFSG.Sporadic.Co2Smith.GlDefs
public import CFSG.Sporadic.Co2Smith.HPExclude
public import CFSG.Sporadic.Co2Smith.HPTree
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import Certificates.Data.CFSGNative.Co2Smith.Orbit8

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem card_centralizer_x45 :
    Nat.card ↥(QP45.originalSubgroup ⊓ Subgroup.centralizer ({x45} : Set (Equiv.Perm (Fin 45)))) =
      576 := by
  rw [card_inf_centralizer QP45 QP45_ok]
  exact Certificates.certificate21165

theorem card_QA45 : Nat.card QA45.originalSubgroup = 51840 := by
  rw [card_group QA45 QA45_ok, QA45_valid.2]

end CFSG.Sporadic.Co2Smith
