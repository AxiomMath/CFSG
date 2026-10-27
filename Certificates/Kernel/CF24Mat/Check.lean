module

public import Certificates.Kernel.CF24Mat.Data
public import Certificates.Data.Kernel.CF24Mat
public import CFSG.Certificates.Kernel.Spor.F3R
public import Certificates.Data.Kernel.CosetJ.WordsT
public import Certificates.Kernel.CosetJ.Cover
public import Certificates.Kernel.Bounds.Suz.Route
import all CFSG.Sporadic.Recognition.SuzMultiplierInputs
import all CFSG.Sporadic.Presentation.SuzInputs
import all CFSG.LieType.Multipliers.CoverWords
import all CFSG.Certificates.CentralizerRelations
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Suzuki

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCF24M

open CFSG.F3.Native CFSG.KS.F3R CFSG.KS.F3L CFSG.KC.McLMult CFSG.KC.CF24M CFSG.KC.Enum
  CFSG.ComponentClassification.GSThmB.CF24 CFSG.Sporadic.Recognition.SuzMultiplier
  CFSG.LieType.Multipliers CFSG.LieType.Multipliers.Tits CertificateChecks.KernelCosetJ

instance : NeZero gcS := ⟨by decide⟩

@[expose] noncomputable def ysOf (d E : Nat) (I A Ai B Bi : V) (IW : List (List Int)) : List V :=
  List.rec (motive := fun _ => List V) [] (fun w _ ih => abK4 d E I A Ai B Bi w :: ih) IW

@[expose] noncomputable def yisOf (d E : Nat) (I A Ai B Bi : V) (IW : List (List Int)) : List V :=
  List.rec (motive := fun _ => List V) [] (fun w _ ih => abK4 d E I A Ai B Bi (invZ w) :: ih) IW

@[expose] noncomputable def esOf (d E : Nat) (I : V) (Y Yi : List V) : List V :=
  (List.finRange gcS).map fun i => evalKn d E I (at6 Y) (at6 Yi) (suzCommWord i)

@[expose] noncomputable def eisOf (d E : Nat) (I : V) (Y Yi : List V) : List V :=
  (List.finRange gcS).map fun i =>
    evalKn d E I (at6 Y) (at6 Yi) (FreeGroup.invRev (suzCommWord i))

@[expose] noncomputable def withEs {α : Type} (A B : V) (IW : List (List Int))
    (k : Nat → V → List V → List V → α) : α :=
  strictT (spreadE 12 12) fun E => strictV (idLane 12) fun I => strictV A fun A =>
    strictV B fun B => strictV (powLane 12 E I A 3) fun Ai => strictV (powLane 12 E I B 2) fun Bi =>
      strictLs (ysOf 12 E I A Ai B Bi IW) fun Y => strictLs (yisOf 12 E I A Ai B Bi IW) fun Yi =>
        strictLs (esOf 12 E I Y Yi) fun X => strictLs (eisOf 12 E I Y Yi) fun Xi => k E I X Xi

@[expose] def coverL : List (List (Fin gcS × Bool)) :=
  coverWords (decodeW gcS CFSG.KBRoute.Suz.rels) suzCommWord

@[expose] noncomputable def matAB (A B : V) (IW : List (List Int)) : Bool :=
  withEs A B IW fun E I X Xi =>
    matCheckK 12 E I (at6 X) (at6 Xi) gcS coverL suzR3 (suzW [6, 6]) cf24C

theorem seedA_ok : seedK 12 (laneOf AT.chars) AT.chars = true := by
  decide +kernel

theorem seedB_ok : seedK 12 (laneOf BT.chars) BT.chars = true := by
  decide +kernel

theorem id12_ok : bAnd(canonL 12 (idLane 12), eqMK 12 (idM 12) (unlane 12 (idLane 12))) = true := by
  decide +kernel

theorem iw_ok : CFSG.KC.WordsT.wordsT IT.chars IT.W = true := by
  decide +kernel

theorem mat_ok : matAB (laneOf AT.chars) (laneOf BT.chars) IT.W = true := by
  decide +kernel

end CertificateChecks.KernelCF24M

end
