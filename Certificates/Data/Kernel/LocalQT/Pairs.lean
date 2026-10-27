module

public import Certificates.Data.Kernel.LocalQT.SylE
public import Certificates.Data.Kernel.LocalQT.Core

public section

namespace CFSG.KC.LQT.Pairs

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.W CFSG.KC.LQT.T2 CFSG.KC.LQT.Syl

@[expose] noncomputable def newK (seen l : List Nat) : List Nat :=
  List.reverse (List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun y _ ih acc => ih (Bool.rec (motive := fun _ => List Nat) (List.cons y acc) acc
      (orB (memL y seen) (memL y acc)))) l [])

@[expose] noncomputable def clK (n : Nat) (G : List Nat) (k : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) [one n]
    (fun _ L => List.append L (newK L (List.flatten (List.map (fun x =>
      List.map (fun g => mul n g x) G) L)))) k

@[expose] noncomputable def conjI (n g a : Nat) : Nat := mul n (mul n (inv n g) a) g

@[expose] noncomputable def nrmK (n : Nat) (A pre : List Nat) (g : Nat) : Bool :=
  andB (allL pre fun a => memL (conj n g a) A)
    (allL A fun a => andB (memL (conj n g a) A) (memL (conjI n g a) A))

@[expose] noncomputable def subFacts (n e : Nat) (L : List Nat) : Bool :=
  allBs [Nat.ble n 32, Nat.beq (lenL L) (Nat.pow 2 e), distinctS L, memL (one n) L,
    allL L (fun x => allL L fun y => memL (mul n x y) L),
    allL L fun x => Nat.beq (sqK n x e) (one n)]

@[expose] noncomputable def normFacts (n e r : Nat) (K Q : List Nat) : Bool :=
  allBs [subFacts n e Q, allL Q (fun q => memL q K),
    allL K (fun k => allL Q fun q => memL (conj n k q) Q),
    allL K (fun y => impB (allL Q fun q => comm n y q) (memL y Q)),
    allL K (fun b => impB (andB (notB (Nat.beq b (one n))) (Nat.beq (pow n b 3) (one n)))
      (Nat.blt 4 (lenL (dedupL (List.map (fun q => mul n (conj n q b) (inv n b)) Q))))),
    Nat.beq (Nat.div (lenL K) (lenL Q)) r]

@[expose] noncomputable def commsK (n : Nat) (S : List Nat) : List Nat :=
  dedupS (sortN (List.flatten (List.map (fun s => List.map (fun t =>
    mul n (mul n (mul n s t) (inv n s)) (inv n t)) S) S)))

@[expose] noncomputable def centerK (n : Nat) (S : List Nat) : List Nat :=
  filtL S fun x => allL S fun s => comm n s x

@[expose] noncomputable def centDK (n : Nat) (S : List Nat) : List Nat :=
  filtL S fun x => allL (commsK n S) fun c => comm n c x

end CFSG.KC.LQT.Pairs

end
