module

public import Certificates.Data.Kernel.HJ12KT
public import CFSG.Quasithin.H13.AS91Sec4FiveInputs

public section

noncomputable section

namespace Certificates.Kernel.AS91K468

open CFSG.KC.Mat12P CFSG.KC.Mat8P Certificates.Kernel.HJ12K

@[expose] def pQ : List ℕ :=
  [5659596365045704864721142394808995562925057, 8389322472514166039870025575933217047846913,
    9820219706086004407936704308795961903113461, 6705195021291883877282066692790280271374129]

@[expose] def p2Q : List ℕ :=
  [11151733957229567414412306689924932879568910, 12197336538852166835894624241825581228053302,
    11151737882606002682240727521210012664878086, 11168067448534241732814282915841850317236229]

@[expose] def gZQ : List ℕ :=
  [2573156193824583219788479952312110266815962, 15005501897667644566228494022703296583526645]

@[expose] def ebQ : List ℕ :=
  [8389322472514166039870025575933217047846913, 12213674142440646272187520239762892771270458,
    8389326460213389038588557755332988139230214, 13703224403077709447542100985693832831213609]

@[expose] def iQ : List ℕ :=
  [12213674142440646272187520239762892771270458, 11151737882606002682240727521210012664878086]

@[expose] def fGQ : List ℕ :=
  [8389322472514166039870025575933217047846913, 13703224403077709447542100985693832831213609,
    10890451187778310229028169627308199510188073]

@[expose] def fRQ (i : ℕ) : List ℕ := fGQ.getD i oneQ :: iQ

@[expose] def w1M : ℕ := maskOf 0 CFSG.Quasithin.H13.AS91.Two.w1List

@[expose] def presW1 (x : ℕ) : Bool :=
  CFSG.Quasithin.H13.AS91.Two.w1List.all fun c => bitQ w1M (mvNR (unpackQ x) c)

@[expose] def baseAt (P P2 Eb I : List ℕ) : Bool :=
  p2Q.all (fun p => P.contains p) && gensOKQ iQ && I.contains oneQ && closedQ iQ I &&
    nodupP I && Nat.beq I.length 4 &&
    iQ.all (fun r => Eb.contains r && P2.contains r) &&
    Eb.all fun x => !P2.contains x || I.contains x

@[expose] def fAt (Eb : List ℕ) (FL : List (List ℕ)) : Bool :=
  (List.range 3).all fun i =>
    gensOKQ (fRQ i) && (FL.getD i []).contains oneQ && closedQ (fRQ i) (FL.getD i []) &&
      nodupP (FL.getD i []) && Nat.beq (FL.getD i []).length 8 &&
      (fRQ i).all (fun r => Eb.contains r) &&
      (List.range 3).all fun j => i == j || !(FL.getD j []).contains (fGQ.getD i oneQ)

@[expose] def conjQ (x : ℕ) (F F' : List ℕ) : Bool :=
  F.all fun f => F'.any fun f' => Nat.beq (mulQ x f) (mulQ f' x)

@[expose] def gAt (G1 P2 Eb : List ℕ) (FL : List (List ℕ)) : Bool :=
  G1.all fun x =>
    (FL.all fun F => FL.any fun F' => conjQ x F F') &&
      (!(FL.all fun F => conjQ x F F) || Eb.any fun e => P2.any fun p => Nat.beq (mulQ p e) x)

@[expose] def fLQ : List (List ℕ) := [enumQ (fRQ 0), enumQ (fRQ 1), enumQ (fRQ 2)]

@[expose] def base47Q : Bool := baseAt (enumQ pQ) (enumQ p2Q) (enumQ ebQ) (enumQ iQ)

@[expose] def f47Q : Bool := fAt (enumQ ebQ) fLQ

@[expose] def g47Q : Bool := gAt ((enumQ gZQ).filter presW1) (enumQ p2Q) (enumQ ebQ) fLQ

end Certificates.Kernel.AS91K468

end

end
