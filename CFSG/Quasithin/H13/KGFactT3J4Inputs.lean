module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4CheckInputs
public import CFSG.Sporadic.J4.QTRankNative
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase
public import Certificates.Data.J4Loc.Native

public section

namespace CFSG.Quasithin.H13.KGT3J4

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.M24 CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs
open CFSG.Sporadic.J4.QT

@[expose] def invTab24 (t : List Nat) : List Nat := (List.range 24).map fun j => t.idxOf j

@[expose] def starLetterTab (ℓ : Int) : List Nat :=
  if 0 < ℓ then starPermOf (ℓ.toNat - 1) else invTab24 (starPermOf ((-ℓ).toNat - 1))

@[expose] def starWordTab (w : List Int) : List Nat :=
  w.foldr (fun ℓ t => compTab (starLetterTab ℓ) t) (List.range 24)

@[expose] def t3yWord : List Nat :=
  [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1,
  0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1,
  0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0,
  1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1,
  0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1,
  1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0]

@[expose] def t3cWord : List Int :=
  [-2, 1, -2, -3, -3, -1, -1, -1, -2, -3, 1, 3, 3, -1, 3, -1, 2, 3, 3, 1, 2, -3, 1, -2, -2, -3, 2,
  3, 1, 1, 1, 3, 3, 2]

@[expose] def t3yTab : Array Nat := wordTabA #[m24ta.toArray, m24tb.toArray] 24 t3yWord

@[expose] def t3yLab : List Nat := codeSetAct 24 t3yTab m24Delta

@[expose] def t3cTab : Array Nat := (starWordTab t3cWord).toArray

@[expose] def T3J4Check : Prop :=
  (∀ k < 3, ∀ q < 24, (invTab24 (starPermOf k)).getD ((starPermOf k).getD q 0) 0 = q) ∧
  (∀ i < 4, codeSetAct 24 (starWordTab (kWords.getD i [])).toArray t3yLab = t3yLab) ∧
  (∀ i < 4, ∀ v ∈ [422, 553, 1131], actT (kTab i) v ∈ CFSG.Quasithin.J4Loc.V0L) ∧
  (∀ v ∈ [422, 553, 1131], actT (wordT t3cWord) v = v)

instance : Decidable T3J4Check := by
  unfold T3J4Check
  infer_instance

end CFSG.Quasithin.H13.KGT3J4
