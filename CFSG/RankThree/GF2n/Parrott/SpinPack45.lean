module

public import CFSG.RankThree.GF2n.Parrott.SpinWords
public import CFSG.RankThree.GF2n.Parrott.PSp43Pack45

public section

namespace CFSG.RankThree.GF2n.Parrott.SpinPack45

open Equiv
open CFSG.KS.PCnt (pkw)
open CFSG.Permutation.FinPack64
open CFSG.RankThree.GF2n.Parrott.Pack45
open CFSG.RankThree.GF2n.Parrott.SpinWords (letterPerm wordPerm)
open CFSG.ComponentClassification.CatFactsSmall.PSp43 (x45 y45 f45)

@[expose] noncomputable def letterK (a : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) cT (fun k _ => Nat.rec (motive := fun _ => ℕ) cY (fun _ _ => cF) k) a

@[expose] noncomputable def wordK (w : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) cOne (fun a _ r => mulW 45 (letterK a) r) w

theorem pk_letter (a : ℕ) : pkw 6 (letterPerm a) = letterK a := by
  rcases a with _ | _ | a
  · exact pk_x
  · exact pk_y
  · exact pk_f

theorem pk_word (w : List ℕ) : pkw 6 (wordPerm w) = wordK w := by
  induction w with
  | nil => exact pk_one
  | cons a w ih =>
    have e : wordPerm (a :: w) = letterPerm a * wordPerm w := by
      rw [wordPerm, List.map_cons, List.prod_cons]
      rfl
    rw [e]
    exact pk_mul h45 (pk_letter a) ih

@[expose] def cW : ℕ :=
  214168135620672026566518453001295663662801448445770912491558100043184797410566182
@[expose] def cB0 : ℕ :=
  184598988831621419290746580027732588008002503521238312024997750977645871978082384
@[expose] def cG1 : ℕ :=
  1173050938608888511508255495703968993239823835994425993011823196704663502457929794
@[expose] def cG2 : ℕ :=
  12716062570207273429000985385640358014898394959028138614422999419981892480968036
@[expose] def cCjA : ℕ :=
  286928647203337126865480826419243968611672286282734750607710236698242191326203975
@[expose] def cCjB : ℕ :=
  1024674296157644638637072821404761896068577554761851927658868041754983481059707221
@[expose] def cCg2 : ℕ :=
  1235274986285181325709593671936193713420615384972889918039534420474531057836501546
@[expose] def cCut : ℕ :=
  876375518574457246425826345393168229852247277940857071428463310979679642766722501
@[expose] def cCv : ℕ :=
  1227060092405378202767753497139164889246232265939626863016709916234191610267439384

theorem pk_W : pkw 6 (f45 * y45 ^ 3 * f45 * y45 ^ 2 * f45 * y45) = cW :=
  (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 pk_f (pk_npow h45 pk_one pk_y 3))
    pk_f) (pk_npow h45 pk_one pk_y 2)) pk_f) pk_y).trans (by decide +kernel)

theorem pk_B0 : pkw 6 (y45 * x45 * y45 * x45 * y45 * f45 * y45 * x45 * y45 * y45) = cB0 :=
  (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45
    (pk_mul h45 (pk_mul h45 pk_y pk_x) pk_y) pk_x) pk_y) pk_f) pk_y) pk_x) pk_y) pk_y).trans
    (by decide +kernel)

theorem pk_G1 : pkw 6 (y45 * y45 * y45 * y45 * x45 * y45) = cG1 :=
  (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 pk_y pk_y) pk_y) pk_y) pk_x)
    pk_y).trans (by decide +kernel)

theorem pk_G2 : pkw 6 (y45 * y45 * f45 * y45 * x45 * y45 * f45 * y45 * x45) = cG2 :=
  (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45
    (pk_mul h45 pk_y pk_y) pk_f) pk_y) pk_x) pk_y) pk_f) pk_y) pk_x).trans (by decide +kernel)

theorem pk_CjA : pkw 6 (y45 * y45 * f45 * y45 * y45 * y45) = cCjA :=
  (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 pk_y pk_y) pk_f) pk_y) pk_y)
    pk_y).trans (by decide +kernel)

theorem pk_CjB : pkw 6 (y45 * x45 * y45 * y45 * y45 * f45 * y45 * f45 * y45) = cCjB :=
  (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45
    (pk_mul h45 pk_y pk_x) pk_y) pk_y) pk_y) pk_f) pk_y) pk_f) pk_y).trans (by decide +kernel)

theorem pk_Cg2 : pkw 6 (y45 * x45 * y45 * y45 * y45 * y45) = cCg2 :=
  (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 pk_y pk_x) pk_y) pk_y) pk_y)
    pk_y).trans (by decide +kernel)

theorem pk_Cut :
    pkw 6 (f45 * y45 * x45 * y45 * y45 * y45 * x45 * f45 * y45 * f45 * y45 * y45) = cCut :=
  (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45
    (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 pk_f pk_y) pk_x) pk_y) pk_y) pk_y) pk_x)
    pk_f) pk_y) pk_f) pk_y) pk_y).trans (by decide +kernel)

theorem pk_Cv :
    pkw 6 (y45 * x45 * f45 * y45 * x45 * y45 * y45 * f45 * y45 * x45 * y45 * f45 * y45) = cCv :=
  (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45
    (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 pk_y pk_x) pk_f) pk_y) pk_x)
    pk_y) pk_y) pk_f) pk_y) pk_x) pk_y) pk_f) pk_y).trans (by decide +kernel)

end CFSG.RankThree.GF2n.Parrott.SpinPack45
