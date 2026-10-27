module

public import Certificates.Data.Y63.Tab
public import Certificates.Data.Y63.Model
public import Certificates.Data.Y63.Spec

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23.Y63Chk

@[expose] def bfsWords (tab : Array (Array ℕ)) (_ : Unit := ()) : Array (List ℕ) := Id.run do
  let mut words : Array (List ℕ) := Array.replicate 512 []
  let mut seen : Array Bool := (Array.replicate 512 false).set! 0 true
  let mut queue : Array ℕ := #[0]
  for i in [0:512] do
    if i < queue.size then
      let x := queue[i]!
      for c in [0:10] do
        let y := (tab.getD x #[]).getD c 0
        if !(seen.getD y true) then
          seen := seen.set! y true
          words := words.set! y (words.getD x [] ++ [c])
          queue := queue.push y
  return words

@[expose] def mulTable (tab : Array (Array ℕ)) (W : Array (List ℕ)) (_ : Unit := ()) :
    Array (Array ℕ) :=
  (Array.range 512).map fun x => (Array.range 512).map fun y =>
    (W.getD y []).foldl (fun a c => (tab.getD a #[]).getD c 0) x

@[expose] def invTable (mt : Array (Array ℕ)) (_ : Unit := ()) : Array ℕ :=
  (Array.range 512).map fun x =>
    ((List.range 512).find? fun y => (mt.getD x #[]).getD y 0 == 0).getD 0

@[expose] def dataOf (_ : Unit := ()) : Data :=
  let tab := tabRows ()
  let W := bfsWords tab ()
  let mt := mulTable tab W ()
  let iv := invTable mt ()
  let sk := skData ()
  let tau := tauData ()
  let u0 := u0Data ()
  let cw := cwData ()
  let cj := cjData ()
  { T := fun x c => (tab.getD x #[]).getD c 0
    W := fun y => W.getD y []
    mt := fun x y => (mt.getD x #[]).getD y 0
    iv := fun x => iv.getD x 0
    m0 := m0Data ()
    reps := repsData ()
    sk := fun k => sk.getD k []
    cj := fun i j =>
      match cj.find? fun e => e.1 == i && e.2.1 == j with
      | some e => (e.2.2.1, e.2.2.2)
      | none => (4, 0)
    tau := fun k x => (tau.getD k #[]).getD x 0
    z := zData
    u0 := fun k => u0.getD k []
    cw := fun k => (cw.getD k []).map fun e => ⟨e.1, e.2.1, e.2.2.1, e.2.2.2⟩ }

@[expose] def check (_ : Unit := ()) : Bool := decide (Data.Spec (dataOf ()))

theorem check_sound (h : check () = true) : Data.Spec (dataOf ()) :=
  of_decide_eq_true h

end CFSG.OddStandard.HigherRank.YamadaG23.Y63Chk
