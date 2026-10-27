module

public import Certificates.Data.Kernel.SporSch.MathieuBT
public import CFSG.LocalAnalysis.OddStandard.MathieuInvolutionSpec
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel

public section

namespace CFSG.KS.SporSch.OddRows

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.M11 CFSG.KS.Prim CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.MBT CFSG.OddStandard

@[expose] noncomputable def wv (n w : Nat) (PS PSI : Nat → Nat) (wd : List Int) : Nat :=
  wordK n w (mask w) (pidn n w) PS PSI wd

@[expose] noncomputable def specK (n w : Nat) (PS PSI LR TR TRI : Nat → Nat) (BP k g cap : Nat)
    (sp : WordRowSpec) : Bool :=
  strictB (wv n w PS PSI sp.repWord) fun R => strictB (wv n w PS PSI sp.conjWord) fun C =>
    lettersK g sp.repWord && lettersK g sp.conjWord && Nat.blt 0 sp.prime &&
      Nat.blt 0 sp.productOrder && Nat.ble sp.classSize cap &&
      Nat.beq (sp.classSize * btK n w (mask w) (n * w) BP k LR TR TRI R R) (ordK LR k) &&
      Nat.beq (ordC n w (mask w) R) sp.prime &&
      Nat.beq (ordC n w (mask w) (pcomp n w (mask w) R (pcomp n w (mask w)
        (pcomp n w (mask w) C R) (pinvS n w (mask w) C)))) sp.productOrder

@[expose] noncomputable def cntIn (n w : Nat) (LR TR : Nat → Nat) (k : Nat) (ps : List Nat) :
    Nat :=
  (List.range (ordK LR k)).countP fun j =>
    strictB (ordC n w (mask w) (elemK n w (mask w) (n * w) (pidn n w) LR TR k j)) fun o =>
      ps.any fun p => Nat.beq o p

@[expose] noncomputable def rowsK (n w : Nat) (PS PSI LR TR TRI : Nat → Nat) (BP k g : Nat)
    (ps : List Nat) (specs : List WordRowSpec) (cap : Nat) : Bool :=
  idK n w (mask w) && allN g (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) &&
    ps.all (fun p => Nat.blt 0 p) && specs.all (specK n w PS PSI LR TR TRI BP k g cap) &&
    allN specs.length (fun j => allN j fun i =>
      Nat.beq (btK n w (mask w) (n * w) BP k LR TR TRI
        (wv n w PS PSI (specs.getD i ⟨0, [], 0, [], 0⟩).repWord)
        (wv n w PS PSI (specs.getD j ⟨0, [], 0, [], 0⟩).repWord)) 0) &&
    Nat.beq (specs.map (·.classSize)).sum (cntIn n w LR TR k ps)

end CFSG.KS.SporSch.OddRows

end
