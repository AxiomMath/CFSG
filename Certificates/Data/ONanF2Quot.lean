module

public import Certificates.Data.ONanF2Facts
public import CFSG.GH74.GLS.Bg.TwoGroups.L23Models
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.DeriveFintype

public section

namespace CFSG.OddStandard.ONanRec.F2

open AlpE CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

abbrev TcM : Type := UT3 F4c

@[expose] def mE : AlpE := gen 3 ^ 2 * gen 2 ^ 2
@[expose] def lE : AlpE := gen 0 * (gen 1)⁻¹
@[expose] def stE : AlpE := gen 3 * gen 4
@[expose] def dE : AlpE := gen 3 ^ 2 * gen 0 * gen 2 ^ 2

@[expose] def genTE : List AlpE := [mE, lE, stE]
@[expose] def genSE : List AlpE := [xE, stE]
@[expose] def genCTSE : List AlpE := [lE, zc]
@[expose] def genNE : List AlpE := [xE]
@[expose] def genQ8E : List AlpE := [lE, dE * (gen 0)⁻¹, xE]
@[expose] def genA12E : List AlpE := [gen 0, gen 1, xE]
@[expose] def genCDE : List AlpE := [gen 4, dE, xE]

@[expose] def ballTE : List AlpE := ballFix genTE
@[expose] def ballSE : List AlpE := ballFix genSE
@[expose] def ballCTSE : List AlpE := ballFix genCTSE
@[expose] def ballNE : List AlpE := ballFix genNE
@[expose] def ballQ8E : List AlpE := ballFix genQ8E
@[expose] def ballA12E : List AlpE := ballFix genA12E
@[expose] def ballCDE : List AlpE := ballFix genCDE
@[expose] def zPrimes : List AlpE := [lE, lE⁻¹, lE * zc, lE⁻¹ * zc]
@[expose] def ballZpL : List (List AlpE) := zPrimes.map fun w => ballFix [w]

def enc (x : AlpE) : ℕ := x.d.val * 64 + x.v0.val * 16 + x.v1.val * 4 + x.v2.val

def p0Imgs : List TcM :=
  [⟨⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩⟩, ⟨⟨0, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩⟩, ⟨⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩⟩,
    ⟨⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩⟩, ⟨⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩]

def stepImg (gi : List (AlpE × TcM)) (img : Array (Option TcM))
    (fr : List (AlpE × TcM)) : Array (Option TcM) × List (AlpE × TcM) :=
  fr.foldl (fun acc p =>
    gi.foldl (fun acc g =>
      match acc.1[enc (p.1 * g.1)]! with
      | some _ => acc
      | none => (acc.1.set! (enc (p.1 * g.1)) (some (p.2 * g.2)),
          (p.1 * g.1, p.2 * g.2) :: acc.2)) acc) (img, [])

def bfsImg (gi : List (AlpE × TcM)) :
    ℕ → Array (Option TcM) → List (AlpE × TcM) → Array (Option TcM)
  | 0, img, _ => img
  | n + 1, img, fr =>
    let r := stepImg gi img fr
    if r.2.isEmpty then r.1 else bfsImg gi n r.1 r.2

def imgTable : Array (Option TcM) :=
  bfsImg ((genMaxE 1).zip p0Imgs) 64 ((Array.replicate 512 none).set! (enc 1) (some 1))
    [(1, 1)]

def fE (x : AlpE) : TcM := (imgTable[enc x]!).getD 1

@[expose] def congN (a b : AlpE) : Bool := decide (a⁻¹ * b ∈ ballNE)

@[expose] def relP : Bool :=
  let a1 := gen 0; let a2 := gen 1; let c := gen 4; let d := dE; let e := stE
  congN (c⁻¹ * a1 * c) (a1⁻¹ * a2 ^ 2) && congN (d⁻¹ * a1 * d) (a1 * a2 ^ 2) &&
  congN (e⁻¹ * a1 * e) a2⁻¹ && congN (e⁻¹ * c * e) (c * d * a1⁻¹ * a2 ^ 2) &&
  congN (c⁻¹ * a2 * c) a2⁻¹ && congN (d⁻¹ * a2 * d) (a1 ^ 2 * a2) &&
  congN (e⁻¹ * a2 * e) a1⁻¹ && congN (e⁻¹ * d * e) (d * a1⁻¹ * a2⁻¹)

@[expose] def factP0 : Prop :=
  SubOK genNE ballNE 4 ∧ SubOK (genMaxE 1) (ballMaxL.getD 1 []) 256 ∧
  (∀ g : AlpE, g * xE * g⁻¹ ∈ ballNE) ∧
  (∀ a ∈ ballMaxL.getD 1 [], ∀ b ∈ ballMaxL.getD 1 [], fE (a * b) = fE a * fE b) ∧
  (∀ a ∈ ballMaxL.getD 1 [], (fE a = 1 ↔ a ∈ ballNE)) ∧
  (∀ y : TcM, ∃ a ∈ ballMaxL.getD 1 [], fE a = y) ∧
  relP = true ∧ SubOK genA12E ballA12E 64 ∧ SubOK genCDE ballCDE 16 ∧
  SubOK genQ8E ballQ8E 32 ∧
  (∀ g ∈ ballMaxL.getD 1 [], ((g * stE)⁻¹ * (stE * g) ∈ ballNE ↔ g ∈ ballQ8E)) ∧
  (let A := lE; let B := dE * (gen 0)⁻¹
   A ^ 4 ∈ ballNE ∧ A ^ 2 ∉ ballNE ∧ (A ^ 2)⁻¹ * B ^ 2 ∈ ballNE ∧ B⁻¹ * A * B * A ∈ ballNE)

@[expose] def ZpOK (w : AlpE) (B : List AlpE) : Prop :=
  SubOK [w] B 4 ∧ (∀ y ∈ B, y ∈ ballSE → y = 1) ∧ (∀ t ∈ ballTE, ∀ y ∈ B, t * y * t⁻¹ ∈ B) ∧
  mE ^ 8 ∈ B ∧ mE ^ 4 ∉ B ∧ stE ^ 2 ∈ B ∧ stE ∉ B ∧ (stE⁻¹ * mE * stE) * (mE ^ 3)⁻¹ ∈ B

instance (w : AlpE) (B : List AlpE) : Decidable (ZpOK w B) := by
  unfold ZpOK
  infer_instance

@[expose] def factT : Prop :=
  SubOK genTE ballTE 64 ∧ SubOK genSE ballSE 8 ∧ SubOK genCTSE ballCTSE 8 ∧
  (mE ^ 8 = 1 ∧ mE ^ 4 ≠ 1) ∧ (lE ^ 4 = 1 ∧ lE ^ 2 ≠ 1) ∧ (stE ^ 2 = 1 ∧ stE ≠ 1) ∧
  mE⁻¹ * lE * mE = lE⁻¹ ∧ stE⁻¹ * lE * stE = lE ∧ stE⁻¹ * mE * stE = mE ^ 3 * lE ^ 2 ∧
  xE = lE ^ 2 * mE ^ 2 ∧ mE ^ 4 = zc ∧
  xE ^ 4 = 1 ∧ xE ^ 2 ≠ 1 ∧ stE⁻¹ * xE * stE = xE⁻¹ ∧
  (∀ t ∈ ballTE, ∀ s ∈ ballSE, t * s * t⁻¹ ∈ ballSE) ∧
  (∀ t ∈ ballTE, ((∀ s ∈ genSE, t * s = s * t) ↔ t ∈ ballCTSE)) ∧
  (∀ t ∈ ballCTSE, t ∈ ballSE → t = 1 ∨ t = zc) ∧
  (∀ y ∈ ballCTSE, y ^ 4 = 1 → y ^ 2 ≠ 1 → y ∈ zPrimes) ∧
  (∀ i : Fin 4, ZpOK (zPrimes.getD i 1) (ballZpL.getD i [])) ∧
  (let A := mE * lE; let B := lE
   A ^ 4 ∈ ballSE ∧ A ^ 2 ∉ ballSE ∧ (A ^ 2)⁻¹ * B ^ 2 ∈ ballSE ∧ B⁻¹ * A * B * A ∈ ballSE)

set_option synthInstance.maxSize 1024 in
instance : Decidable factP0 := by
  unfold factP0
  infer_instance

set_option synthInstance.maxSize 1024 in
instance : Decidable factT := by
  unfold factT
  infer_instance

@[expose] def f2QuotCheck : Bool := decide factP0 && decide factT

end CFSG.OddStandard.ONanRec.F2
