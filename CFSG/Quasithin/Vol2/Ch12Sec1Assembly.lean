module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem3
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem4
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem6Gen
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem8
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem9Cartan
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem10
public import CFSG.Quasithin.Vol2.Ch12Sec1H9FourTr
public import CFSG.Quasithin.Vol2.Ch12Sec1H9FiveRed
public import CFSG.Quasithin.Vol2.KGFactH91
public import CFSG.Quasithin.Vol2.KGFactPerm

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem stmt12_1_11_of_inputs121 (h1001 : Stmt10_0_1) (h331 : Stmt3_3_1)
    (h443 : Stmt4_4_3Orbit') (hE : E2.E22StatementC) (hHe : Lem1211He) (hN : Lem1211Normal)
    (hNN : Lem1211NotNormal) (hStep : Lem1214Step) (hComp : Lem1216Comp) (hB : Lem12211Borel)
    (hPerm : Lem1219Perm) (hOdd : Lem1219OddLocal) (hH92 : LemH92Use) (hH93 : LemH93Use)
    (hRk : LemH9Rank4) (hFF4 : LemH9FF4) (hFF5 : LemH9FF5) (hComm : LemH9Comm)
    (hCent : LemH9Cent) (hAxes : LemH9Axes) : Stmt12_1_11 :=
  have hH91 := lemH91_holds
  have h1211 := lem1211_of h1001 h331 hHe hN hNN
  have h1213 := lem1213_of h1001 h331 h1211 hH91 hH92 hFF5 hComm
  have h1215 := lem1215_of h1001 h331 h1211 h1213 (lem1214_of h1001 h331 hStep) hH91
  have h1216 := lem1216_of h1001 h331 hH91 h1215 (lem1216Gen_of h1001 h331 h1211 hH91 h1215 hComp)
  have h1217 := lem1217_of h1001 h331 h1211 hH91 h1213 h1216 hH93 hRk hFF4
  have h1218 := lem1218_of h1001 h331 h1211 hH91 h1216 h1217 hH92 hH93 hRk hCent hAxes
  have h1219 := lem1219_of_steps h1001 h331 h443 h1211 hH91 h1217 h1218 hB hE hPerm hOdd
  stmt12_1_11_of_steps h1001 h331 h443 h1211 hH91 h1217 h1218 hB hE hPerm hOdd
    (lem12110_of h1001 h331 hH91 h1217 h1218 h1219 hH92 hH93 hRk)

theorem stmt12_1_11_of_open121
    (h1001 : Stmt10_0_1) (h331 : Stmt3_3_1) (h443 : Stmt4_4_3Orbit') (hE : E2.E22StatementC)
    (hHe : Lem1211He) (hN : Lem1211Normal) (hNN : Lem1211NotNormal) (hStep : Lem1214Step)
    (hComp : Lem1216Comp) (hB : Lem12211Borel) (hOdd : Lem1219OddLocal) : Stmt12_1_11 :=
  stmt12_1_11_of_inputs121 h1001 h331 h443 hE hHe hN hNN hStep hComp hB lem1219Perm_holds hOdd
    H9Lin.lemH92Use_holds H9Four.lemH93Use_holds H9Four.lemH9Rank4_holds H9Four.lemH9FF4_holds
    H9Lin.lemH9FF5_holds H9Lin.lemH9Comm_holds H9Lin.lemH9Cent_holds H9Lin.lemH9Axes_holds

end CFSG.Quasithin.H13
