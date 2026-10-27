module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatQuot

public section

namespace CFSG.Quasithin.A312S

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def fixLabs (t : Array Nat) (labs : List (List Nat)) : Bool :=
  labs.all fun l => ptAct t l == l

@[expose] def ExtraOK (n : Nat) (B : List Nat) (es : List (Array Nat)) (z : Array Nat)
    (Ts : Array (List Nat)) (par cl : Array Nat) (r : Nat) : Prop :=
  BaseEnumOK n B es (es.map fun e => powTab n e 3) Ts par cl ∧ Ts.size = r ∧
  (∀ e ∈ es, compArr e z = compArr z e) ∧
  compArr z z = Array.range n ∧ z ≠ Array.range n ∧
  applyTab z (ptsOf B es) ∈ Ts.toList ∧
  (∀ e ∈ es, compArr e e = Array.range n ∨ compArr e e = z) ∧
  (∀ e ∈ es, ∀ f ∈ es, compArr e f = compArr f e ∨ compArr e f = compArr z (compArr f e)) ∧
  (∀ T ∈ Ts.toList, (∀ t < es.length, ∀ j < B.length,
      T.getD (B.length * (1 + t) + j) 0 = img (es.getD t #[]) (T.getD j 0)) →
    T = ptsOf B es ∨ T = applyTab z (ptsOf B es))

instance (n : Nat) (B : List Nat) (es : List (Array Nat)) (z : Array Nat) (Ts : Array (List Nat))
    (par cl : Array Nat) (r : Nat) : Decidable (ExtraOK n B es z Ts par cl r) := by
  unfold ExtraOK; infer_instance

@[expose] def Z4StarOK (n : Nat) (B : List Nat) (z4 : Array Nat) (es : List (Array Nat))
    (TsE : Array (List Nat)) (parE clE : Array Nat) (TsV : Array (List Nat))
    (parV clV : Array Nat) : Prop :=
  ExtraOK n B es (compArr z4 z4) TsE parE clE 32 ∧
  powTab n z4 4 = Array.range n ∧
  (∀ e ∈ es, compArr z4 e = compArr e z4) ∧
  applyTab z4 (ptsOf B es) ∉ TsE.toList ∧
  BaseEnumOK n B (z4 :: es) ((z4 :: es).map fun e => powTab n e 3) TsV parV clV ∧ TsV.size = 64

instance (n : Nat) (B : List Nat) (z4 : Array Nat) (es : List (Array Nat)) (TsE : Array (List Nat))
    (parE clE : Array Nat) (TsV : Array (List Nat)) (parV clV : Array Nat) :
    Decidable (Z4StarOK n B z4 es TsE parE clE TsV parV clV) := by
  unfold Z4StarOK; infer_instance

@[expose] def Z4CubedOK (n : Nat) (B : List Nat) (ws : List (Array Nat)) (Ts : Array (List Nat))
    (par cl : Array Nat) : Prop :=
  ws.length = 3 ∧ (∀ w ∈ ws, powTab n w 4 = Array.range n) ∧
  (∀ w ∈ ws, ∀ w' ∈ ws, compArr w w' = compArr w' w) ∧
  BaseEnumOK n B ws (ws.map fun w => powTab n w 3) Ts par cl ∧ Ts.size = 64

instance (n : Nat) (B : List Nat) (ws : List (Array Nat)) (Ts : Array (List Nat))
    (par cl : Array Nat) : Decidable (Z4CubedOK n B ws Ts par cl) := by
  unfold Z4CubedOK; infer_instance

end CFSG.Quasithin.A312S
