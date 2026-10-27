module

public import CFSG.Quasithin.H13.L32NLem14333n
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLocalNormal
public import CFSG.Quasithin.Vol2.Ch1A3Cat
public import CFSG.Quasithin.H13.L32NLem14332

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

theorem a3ForSQTK_holds :
    A37ForSQTK ∧ A38ForSQTK ∧ A39ForSQTK :=
  ⟨a37ForSQTK_of_cat CFSG.QuasithinUnique.Vol2Native.a37ForSQTKCat_proved,
    a38ForSQTK_of_cat (CFSG.QuasithinUnique.Vol2Native.a38ForSQTKCat_of_facts mult2Fact
      CFSG.QuasithinUnique.Vol2Native.a134SQTKFactCat
      CFSG.QuasithinUnique.Vol2Native.a36CoreForSQTKCat_proved
      CFSG.QuasithinUnique.Vol2Native.a37ForSQTKCat_proved),
    a39ForSQTK_of_cat CFSG.QuasithinUnique.Vol2Native.a39ForSQTKCat_proved⟩

theorem lemma14332_of_inputs_a3
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (h1288 : Lemma12_8_8_two) (h12810 : Lemma12_8_10) (h12811 : Lemma12_8_11)
    (h12811h : Lemma12_8_11_hat) (h12812 : Lemma12_8_12_two) (h12813 : Lemma12_8_13)
    (h14323 : Lemma14323Rest) (h14324 : Lemma14324One) (h14331 : Lemma14331One)
    (hKG22 : KGG22PointStab) (hKGr : KGG22Rank) (hKGq : KGSp4Quad) (hKGl : KGSp4Line)
    (hKGL24 : KGL24Quad) : Lemma14332 :=
  lemma14332_of_inputs h1332 h1334 h1222 h12213 a3ForSQTK_holds.1 a3ForSQTK_holds.2.1
    a3ForSQTK_holds.2.2 h1288 h12810 h12811 h12811h h12812 h12813 h14323 h14324
    h14331 hKG22 hKGr hKGq hKGl hKGL24

theorem lemma14333_of_inputs_a3
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (h1288 : Lemma12_8_8_two) (h12884 : Lemma12_8_8_four) (h12810 : Lemma12_8_10)
    (h12811 : Lemma12_8_11) (h12811h : Lemma12_8_11_hat) (h12812 : Lemma12_8_12_two)
    (h12813 : Lemma12_8_13) (h14323 : Lemma14323Rest) (h14324 : Lemma14324One)
    (h14331 : Lemma14331One) (hKG22 : KGG22PointStab) (hKGr : KGG22Rank) (hKGq : KGSp4Quad)
    (hKGl : KGSp4Line) (hKGL24 : KGL24Quad) :
    Lemma14333 :=
  lemma14333_of_inputs h1332 h1334 h1222 h12213 a3ForSQTK_holds.1 a3ForSQTK_holds.2.1
    a3ForSQTK_holds.2.2 h1288 h12884 h12810 h12811 h12811h h12812 h12813 h14323
    h14324 h14331 (lemma14333MEqL_of_inputs h1332 h1334 h1222 h12213 a3ForSQTK_holds.1
      a3ForSQTK_holds.2.1 a3ForSQTK_holds.2.2 h1288 h12884 h12810 h12811 h12811h h12812 h12813
      h14323 h14324 h14331 hKG22 hKGr hKGq hKGl hKGL24)
    hKG22 hKGr hKGq hKGl hKGL24

theorem thm144Big_of_inputs_a3
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (h14323 : Lemma14323Ge) (h14413 : Lemma14413Big) : Thm144Big :=
  thm144Big_of_inputs h1332 h1334 h1222 h12213 a3ForSQTK_holds.1 a3ForSQTK_holds.2.1
    a3ForSQTK_holds.2.2 h14323 h14413

end CFSG.Quasithin.H13
