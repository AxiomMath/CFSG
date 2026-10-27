module

public import Certificates.Data.Kernel.X2E6Syl

public section

namespace CFSG.KC.X2E6Syl

@[expose] def qOKQ (gw : List (List Nat)) (G : List (List (List Nat)))
    (Q : List (List (List Nat))) : Bool :=
  gw.length == 4 && gw.all (fun w => w.all fun i => decide (i < 6)) &&
    G.all (fun B => pwL B 3 == idL) && Q.length == 81 && decide Q.Nodup &&
    Q.all fun A => G.all fun B => Q.contains (mulL A B)

theorem qOK_eq (gw : List (List Nat)) : qOK gw = qOKQ gw (gw.map wordL) (qEls gw) := by
  simp only [qOK, qOKQ, List.all_map, Function.comp_def]

@[expose] def famF (F : List (List (List (List Nat)))) (T : List (List (List Nat))) : Bool :=
  F.head? == some [idL] && F.all (fun H => decide H.Nodup) &&
    F.all fun H => T.all fun x =>
      H.contains x || !(H.all fun h => mulL x h == mulL h x) ||
        F.any fun K => K.length == 3 * H.length && sameSet K (extL H x)

theorem famOK_eq (gw mel : List (List Nat)) :
    famOK gw mel = famF (mel.map (famM (qEls gw))) (tEls (qEls gw)) := rfl

@[expose] def fixQ (Q : List (List (List Nat))) (mel : List (List Nat)) (fixS : List (List Nat))
    (fixE : List (List (List Nat))) (fixY : List (List (Nat × List (List Nat)))) (wit : List Wit) :
    Bool :=
  mel.length == fixS.length && mel.length == fixE.length && mel.length == fixY.length &&
  (List.range mel.length).all fun m =>
    let H := famM Q (mel.getD m [])
    let S := fixS.getD m []
    let E := fixE.getD m []
    let Ys := fixY.getD m []
    Ys.all (fun p => H.contains (Q.getD p.1 idL)) &&
      subL idL E == Ys.foldr (fun p acc => addL (mulL p.2 (subL (Q.getD p.1 idL) idL)) acc) zeroL &&
      S.all (fun j => decide (j < 6)) && colsZero E S && boundOK H.length S.length &&
      (!(H.length == 3 && S.length == 4) ||
        wit.any fun w => w.1 == m && witOK1 w && H.all fun A => w.2.1.all fun f => mvL A f == f)

theorem fixOK_eq (gw mel fixS : List (List Nat)) (fixE : List (List (List Nat)))
    (fixY : List (List (Nat × List (List Nat)))) (wit : List Wit) :
    fixOK gw mel fixS fixE fixY wit = fixQ (qEls gw) mel fixS fixE fixY wit := rfl

end CFSG.KC.X2E6Syl

end
