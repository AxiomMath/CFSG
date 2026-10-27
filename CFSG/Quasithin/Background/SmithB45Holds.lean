module

public import CFSG.Quasithin.Background.SmithB45Frontier
public import CFSG.Quasithin.Background.SmithB45Dich
public import CFSG.Quasithin.Background.SmithB45D4
public import CFSG.Quasithin.Background.SmithB45Tits
public import CFSG.Quasithin.Background.SmithB45G2Main
public import CFSG.Quasithin.Background.SmithB45SL3L32
public import CFSG.Quasithin.Background.SmithB45Alt6
public import CFSG.Quasithin.Background.SmithB45HatA6
public import CFSG.Quasithin.Background.SmithB45Alt7
public import CFSG.Quasithin.Background.SmithB45L2Main
public import CFSG.Quasithin.Background.SmithB45U3Nat
public import CFSG.Quasithin.Background.SmithB45SzNat
public import CFSG.Quasithin.Background.SmithB45SL3Even
public import CFSG.Quasithin.Background.SmithB45U33Main
public import CFSG.Quasithin.Background.SmithB45Sp4Main
public import CFSG.Quasithin.Background.SmithB45MatMain
public import CFSG.Quasithin.Background.SmithB45M22HatMain
public import CFSG.Quasithin.Background.SmithB45LnL4Main
public import CFSG.Quasithin.Background.SmithB45Exc3A7
public import CFSG.Quasithin.Background.SmithB45MatM22
public import CFSG.Quasithin.Background.SmithB45MatM12
public import CFSG.Quasithin.Background.SmithB45LnL5Main
public import CFSG.Quasithin.Background.SmithB45DichHolds
public import CFSG.Quasithin.Background.SmithB45J2Main
public import CFSG.Quasithin.Background.SmithB45MatIndM24
public import CFSG.Quasithin.Background.SmithB45HM22Holds
public import CFSG.Quasithin.EmptyFaithful.LRed14B45
public import CFSG.Certificates.CosetTableShort
public import CFSG.CharacterTheory.Blocks.BrauerInduction
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeOrderSylowColumn
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementCharacterSpace
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2Core
public import CFSG.Quasithin.Background.D2Cyclic
public import CFSG.Quasithin.Background.FFC7G
public import CFSG.Quasithin.Background.HTriSolv
public import CFSG.Quasithin.Background.HTriU3
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.J4.QT2LocMain
public import CFSG.Sporadic.J4.QT2LocRadMain

public section

namespace CFSG.Quasithin

open B45Exc

theorem asB45_holds :
    AsB45 :=
  asB45_of_open
    asB45DichotomyNat_holds
    asB45TrialityD4_holds asB45ReeF4_holds asB45G2Even_holds asB45L32_holds
    asB45L42_holds asB45L52_holds asB45Alt6_holds asB45HatA6_holds asB45Alt7_holds asB45Alt5_holds
    asB45L2Even_holds asB45U3Even_holds asB45Sz_holds asB45L3Even_holds asB45U33_holds
    asB45Sp4Even_holds
    asB45M12_holds (asB45HatM22_holds hatM22SmallModules_holds) asB45M22_holds
    (asB45M23_of_smallIrr mathieuSmallIrr23_holds)
    (asB45M24_of_smallIrr mathieuSmallIrr24_holds) asB45J2_holds

theorem asB45Gt1_holds :
    AsB45Gt1 :=
  asB45Gt1_of_b45 asB45_holds

end CFSG.Quasithin
