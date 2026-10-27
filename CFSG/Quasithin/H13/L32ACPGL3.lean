module

public import CFSG.Quasithin.H13.L32ACPGL2
public import CFSG.Quasithin.H13.L32AC42m

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

theorem lemma14_7_42_s5s3_of_leaves
    (h310 : D310) (hB42 : AsB42)
    (hA21 : AsA21SQTKSection) (hN1 : LieSylowOver3) (hN3 : LieBorelThreeInner)
    (hN4 : LieBorelTwoInner) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h5 : Lemma14_7_5) (h28 : Lemma14_7_28) (h29 : Thm14_7_29) (h30 : Lemma14_7_30)
    (h32 : Lemma14_7_32) (h34 : Lemma14_7_34) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) :
    Lemma14_7_42_S5S3 :=
  lemma14_7_42_s5s3_of_inputs h310 hB42 hA21 hN1 hN3 hN4 h1222 h1332 h1334 h5 h28 h29 h30 h32
    h34 hA37 hA38
    (lemma14741PGL_of_inputs h310 hA21 hN1 h29 h1222 h1332 h1334 h30 h32 hA37 hA38)

end CFSG.Quasithin.H13.L32A.C
