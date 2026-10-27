module

public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptAssembly
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptB
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptC
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptS
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptF2
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptF3
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptA312Gen
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptYO2
public import CFSG.Quasithin.Vol2.Ch3Sec3FrontierA
public import CFSG.Quasithin.Vol2.Ch3Sec3Frontier
public import CFSG.Quasithin.Background.C124AsmClassify
public import CFSG.Quasithin.Background.C124YZStar
public import CFSG.Quasithin.Background.SmithC27RCaseIOrd
public import CFSG.Quasithin.EmptyFaithful.E22QLift
public import CFSG.Quasithin.MS93.FFGlue
public import CFSG.Quasithin.MS93.S45Gp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Hyp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivStab
public import CFSG.Quasithin.SteinbergCCPrimeWitness
public import CFSG.Quasithin.Vol2.Ch10SecA1011
public import CFSG.Quasithin.Vol2.Ch10SecB5Easy
public import CFSG.Quasithin.Vol2.Ch10SecB6Lt
public import CFSG.Quasithin.Vol2.Ch10SecB6QS
public import CFSG.Quasithin.Vol2.Ch10SecB6Rank
public import CFSG.Quasithin.Vol2.Ch10SecB6Syl
public import CFSG.Quasithin.Vol2.Ch10SecC8Main12
public import CFSG.Quasithin.Vol2.Ch10SecC9Entry
public import CFSG.Quasithin.Vol2.Ch10SecC9L32
public import CFSG.Quasithin.Vol2.Ch10SecC9S5c
public import CFSG.Quasithin.Vol2.Ch10SecC9S5f
public import CFSG.Quasithin.Vol2.Ch10SecEBlockA5
public import CFSG.Quasithin.Vol2.Ch10SecEE3ProdC
public import CFSG.Quasithin.Vol2.Ch10SecFComm
public import CFSG.Quasithin.Vol2.Ch10SecFH
public import CFSG.Quasithin.Vol2.Ch10SecFLJ3
public import CFSG.Quasithin.Vol2.Ch10SecFObl
public import CFSG.Quasithin.Vol2.Ch10SecKIK2g
public import CFSG.Quasithin.Vol2.Ch10SecKIK4b
public import CFSG.Quasithin.Vol2.Ch10SecQ4A3
public import CFSG.Quasithin.Vol2.Ch10SecQ4A4
public import CFSG.Quasithin.Vol2.Ch10SecQ4A5
public import CFSG.Quasithin.Vol2.Ch10SecQ4A9
public import CFSG.Quasithin.Vol2.Ch3Sec3FrontierB
public import CFSG.Quasithin.Vol2.Ch3Sec3FrontierC
public import CFSG.Quasithin.Vol2.Ch6Sec1G22
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem11
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem12
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem3
public import CFSG.Sporadic.Recognition.M23MultiplierTables

public section

namespace CFSG.Quasithin.H13.NF314pt

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)

theorem obl3_3_13D12NF_314pt_of_inputs
    (h36 : A36ForSQTK) (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h128 : Lemma128Two) (h312 : Vol2Native.A312ForSQTKCat) :
    Obl3_3_13D12NF_314pt := by
  have lC : LeafYsplit := leafYsplit_holds h36 h5 h7 h128 h37 h38 h39
  exact obl3_3_13D12NF_314pt_of h36 h5 h7 h128 h37 h38 h39 (leafYO2_holds h37 h38)
    (leafVY_of h36 h5 h7 h128 h37 h38 h39 lC) lC (leafS_holds h128 h37 h38 h39)
    (leafF2_holds h36 h128 h37 h38 h39) (leafF3_holds h37 h38 h39 h312 leafA312_holds)

theorem obl3_3_13D12NF_314pt_holds :
    Obl3_3_13D12NF_314pt :=
  obl3_3_13D12NF_314pt_of_inputs VolI.a36ForSQTK_holds Vol2Native.a37ForSQTKCat_proved
    Frontier331.a38Cat Vol2Native.a39ForSQTKCat_proved
    (stmt3_3_5_of Frontier331.a38Cat Vol2Native.a39ForSQTKCat_proved)
    (stmt3_3_7_of Frontier331.a38Cat Vol2Native.a39ForSQTKCat_proved) lemma128Two_proved
    (Frontier331.a312Cat Frontier331.a312List)

end CFSG.Quasithin.H13.NF314pt
