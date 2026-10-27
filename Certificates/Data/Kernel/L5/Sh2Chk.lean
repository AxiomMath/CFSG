module

public import CFSG.GH74.GLS.C3.Layer2.L5C5cInputs
public import Certificates.Data.Kernel.L5.Sh2Mul

public section

namespace CFSG.KD.L5

open CFSG.GH74.GLS.C3.Layer2.L5

@[expose] def bfsWordsGoT (mul : Nat → Nat → Nat) (gs : List Nat) :
    Nat → Array (Option (List Nat)) → List Nat → Array (Option (List Nat))
  | 0, W, _ => W
  | fuel + 1, W, frontier =>
    let st := frontier.foldl (fun (st : Array (Option (List Nat)) × List Nat) g =>
      (List.range gs.length).foldl (fun (st : Array (Option (List Nat)) × List Nat) k =>
        let p := mul g (gs.getD k 0)
        match st.1.getD p none with
        | some _ => st
        | none => (st.1.set! p (some ((st.1.getD g none).getD [] ++ [k])), st.2 ++ [p])) st) (W, [])
    bfsWordsGoT mul gs fuel st.1 st.2

@[expose] def evFromT (mul : Nat → Nat → Nat) (x : List Nat) (a : Nat) (w : List Nat) : Nat :=
  w.foldl (fun a k => mul a (x.getD k 0)) a

@[expose] def mulS (a b : Nat) : Nat :=
  if a < 128 ∧ b < 128 then m0N a b else mt0.getD (a * 128 + b) 0

@[expose] def WdT : Array (List Nat) :=
  (bfsWordsGoT mulS gI 128 ((Array.replicate 128 none).set! 0 (some [])) [0]).map fun o => o.getD []

@[expose] def actChk : Bool :=
  (List.range 8).all fun d => (List.finRange 16).all (fun w => decide (((d8L.getD d 1) w).val =
    actN d w.val)) && decide (d8L.idxOf (d8L.getD d 1) = d)

@[expose] def natChk : Bool :=
  (List.range 8).all fun d => (List.range 16).all (fun x => (List.range 16).all fun y =>
    decide (actN d (x ^^^ y) = actN d x ^^^ actN d y)) &&
    (List.range 8).all fun e => decide (m8N d e < 8) && (List.range 16).all fun x =>
      decide (actN d (actN e x) = actN (m8N d e) x)

@[expose] def gamTChk : Bool :=
  (List.range 4).all fun m => (List.range 128).all fun j =>
    decide (evFromT mulS (xsData.getD m []) 0 (WdT.getD j []) = gamN m j)

@[expose] def invChk : Bool :=
  (List.range 4).all fun ty => (List.range 256).all fun a => decide (mulN ty a (invN ty a) = 0)

@[expose] def sh2MulChk : Bool := actChk && natChk && gamTChk && invChk

end CFSG.KD.L5

end
