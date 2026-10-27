module

public import CFSG.Quasithin.Vol2.Ch3T316W
public import CFSG.Quasithin.Vol2.Ch3B513NHolds
public import CFSG.Quasithin.Vol2.Ch3E213MWireAll
public import CFSG.Quasithin.Vol2.Ch3E215MSplit
public import CFSG.Quasithin.Vol2.Ch3E215MP1
public import CFSG.Quasithin.Vol2.Ch3E215MP2
public import CFSG.Quasithin.Vol2.Ch3E215MP3
public import CFSG.Quasithin.Vol2.Ch3E215MP4
public import CFSG.Quasithin.Vol2.Ch3E215MP5
public import CFSG.Quasithin.Vol2.Ch3E215MP7
public import CFSG.Quasithin.Vol2.Ch3E215MP8
public import CFSG.Quasithin.Vol2.Ch3E215MSp4
public import CFSG.Quasithin.Vol2.Ch3T316WAtoms
public import CFSG.Quasithin.Vol2.Ch3E213MP6BK
public import CFSG.Quasithin.EmptyFaithful.E22NMain

public section

namespace CFSG.Quasithin.Ch3T316W

theorem theorem316Statement_of_facts
    (h22N : E2.E22StatementNoN) (hC58 : TheoremC58) (hR : Ch3E213M.FactSp4TransvRefl)
    (hCTwo : Ch3E213M.FactSp4CTwo) : Theorem316Statement :=
  theorem316Statement_of B513N.b513Nonsolvable_holds
    (Ch3E213M.e213Member_of_facts C129Native.a38ForSQTKCat_proved h22N hR hCTwo)
    (Ch3E215M.e215Member_of_packages h22N (Ch3E215M.pkgL2Paired215 C129Native.a38ForSQTKCat_proved)
        (Ch3E215M.pkgSzPaired215 C129Native.a38ForSQTKCat_proved)
        (Ch3E215M.pkgOddPaired215 C129Native.a38ForSQTKCat_proved) Ch3E215M.pkgBenderSingle215
        Ch3E215M.pkgL3215
        (Ch3E213M.pkgSp4215_of Ch3E213M.irrStatement_holds (Ch3E213M.G41.factSp4TransvW_of_refl hR)
            Ch3E215M.Sp4.sp4MemberE215_holds
            (Ch3E213M.pkgSp4C2215 (Ch3E213M.G41.factSp4TransvW_of_refl hR) hCTwo
                Ch3E215M.Sp4.sp4MemberE215_holds)) Ch3E215M.pkgOddSingle215
        (Ch3E215M.pkgOddL3215_of Ch3E213M.OLA.kFactL3U3OuterInv_holds
            Ch3E213M.OLB.kFactL33NoQuadFour_holds))
    h22N hC58

theorem theorem316Statement_of_atoms
    (h80 : E2P.Asc80L3Eps) (hR : Ch3E213M.FactSp4TransvRefl) (hCTwo : Ch3E213M.FactSp4CTwo) :
    Theorem316Statement :=
  theorem316Statement_of_facts (E2.E22N.e22StatementNoN_of_asc80 h80)
    (theoremC58_of_atoms (E2.E22N.e22StatementNoN_of_asc80 h80)) hR hCTwo

end CFSG.Quasithin.Ch3T316W
