module

public import CFSG.Quasithin.Vol2.Ch12Sec4Lemma7
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitL52Fix
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitG2Norm
public import CFSG.Quasithin.Vol2.Ch12Sec4G2NormZorn

public section

namespace CFSG.Quasithin.H13

theorem pre1242_of_stmts
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) : Pre1242 :=
  pre1242_of h331 h1222 VolI.g2NaturalCover_holds l52TenSylowFixedLine

theorem lemma12_4_7_of_stmts
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (hpre : Pre1242) (h1246 : Lemma12_4_6) :
    Lemma12_4_7 :=
  lemma12_4_7_of h331 h1222 hpre h1246 VolI.g2NaturalCover_holds Orbit.orbitG2Weyl
    Orbit.g2WeylNormalizerOrbits

theorem lemma12_4_9_of_stmts
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (hpre : Pre1242) (h12210 : Stmt12_2_10)
    (h1247 : Lemma12_4_7) : Lemma12_4_9 :=
  lemma12_4_9_of h331 h1222 hpre h12210 h1247 b46OffenderCommEqFix

end CFSG.Quasithin.H13
