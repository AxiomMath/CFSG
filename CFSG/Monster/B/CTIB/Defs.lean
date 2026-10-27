module

public import CFSG.Monster.B.Final.Max2Nodes
public import CFSG.Monster.B.Dyadic.Nodes
public import CFSG.Monster.B.TwoA.Base.FullCent
public import CFSG.Monster.B.CTIB.QModel
public import Certificates.Data.CFSGNative.CTIB.Data
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3027

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.Rep4371

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

noncomputable local instance instAddCommGroupVst' : AddCommGroup Vst :=
  Module.addCommMonoidToAddCommGroup ℚ

theorem betaS_explicit :
    IsExplicitBinary Dyadic.betaS :=
  CFSG.Monster.B.betaS_explicit

@[expose] noncomputable def iotaS :
    NativeSporadic.B →* Sbp :=
  Classical.choose (iota_facts betaS_explicit)

theorem iotaS_spec :
    Function.Injective iotaS ∧
    (∀ X, ((betaRow Dyadic.betaS (iotaS X) : MatBˣ) : MatB) = Tmat * bMat X * Tmat⁻¹) ∧
    iotaS bA₁ = aB ∧ iotaS bA₂ = bB ∧ iotaS.range = HB :=
  Classical.choose_spec (iota_facts betaS_explicit)

theorem iotaS_beta
    (X : NativeSporadic.B) :
    ((betaRow Dyadic.betaS (iotaS X) : MatBˣ) : MatB) = Tmat * bMat X * Tmat⁻¹ :=
  iotaS_spec.2.1 X

@[expose] noncomputable def Qs : Subgroup Sbp := Ebar.op

@[expose] noncomputable def xs : Sbp := op xbar

@[expose] noncomputable def es (i : ℕ) : Sbp := eS gSeq i

@[expose] noncomputable def gs
    (k : ℕ) : Sbp :=
  if k = 0 then etaS gSeq iotaS cB else if k = 1 then etaS gSeq iotaS dB else op taubar

@[expose] noncomputable def qS (n : ℕ) : Sbp := qOf es xs n

@[expose] noncomputable def liftWordS
    (w : List ℕ) : Sbp := (w.map gs).prod

@[expose] noncomputable def letterS
    (l : ℤ) : Sbp :=
  if 0 < l then gs (l.toNat - 1) else (gs ((-l).toNat - 1))⁻¹

@[expose] noncomputable def wordS'
    (w : List ℤ) : Sbp := (w.map letterS).prod

@[expose] def seed10 : List ℕ := [1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1]

@[expose] noncomputable def hs
    (k : ℕ) : Sbp :=
  if k = 6 then gs 1 ^ 12 else if k = 8 then gs 0 else if k = 10 then liftWordS seed10 ^ 10
  else 1

@[expose] noncomputable def rs
    (i : ℕ) : Sbp :=
  hs (Native.repTable.getD i (0, 0)).1 * qS (Native.repTable.getD i (0, 0)).2

@[expose] noncomputable def toShat (s : Sbp) : Shat := ⟨iotaD s.unop, s.unop, rfl⟩

@[expose] def centWord (k j : ℕ) : List ℤ :=
  (Native.parseWords Native.centWordStr).getD ((if k = 6 then 0 else if k = 8 then 15 else 30) + j)
    []

@[expose] def deltaVal (k j : ℕ) : ℕ :=
  Native.deltaVals.getD ((if k = 6 then 0 else if k = 8 then 15 else 30) + j) 0

theorem native_involution_certificate_data :
    IsExplicitBinary Dyadic.betaS ∧
    (∀ X, ((betaRow Dyadic.betaS (iotaS X) : MatBˣ) : MatB) = Tmat * bMat X * Tmat⁻¹) ∧
    Qs = Ebar.op ∧ xs = op xbar ∧ gs 0 = etaS gSeq iotaS cB ∧ gs 1 = etaS gSeq iotaS dB ∧
    gs 2 = op taubar ∧ (∀ i, es i = eS gSeq i) ∧
    (∀ n, qS n = (if n.testBit 22 then xs else 1) *
      ((List.range 22).map fun i => if n.testBit i then es i else 1).prod) ∧
    hs 6 = gs 1 ^ 12 ∧ hs 8 = gs 0 ∧
    hs 10 = (gs 1 * gs 1 * gs 1 * gs 0 * gs 1 * gs 0 * gs 1 * gs 1 * gs 1 * gs 1 * gs 1 * gs 1 *
      gs 1) ^ 10 ∧
    rs 0 = qS 4194304 ∧ rs 1 = qS 1 ∧ rs 2 = qS 3 ∧ rs 3 = qS 7 ∧ rs 4 = hs 6 * qS 43 ∧
    rs 5 = hs 6 * qS 61 ∧ rs 6 = hs 6 * qS 10541 ∧ rs 7 = hs 6 * qS 26925 ∧
    rs 8 = hs 6 * qS 46090 ∧ rs 9 = hs 8 * qS 0 ∧ rs 10 = hs 8 * qS 128 ∧
    rs 11 = hs 8 * qS 35764 ∧ rs 12 = hs 10 * qS 107 ∧ rs 13 = hs 10 * qS 66038 ∧
    (∀ s : Sbp, (toShat s : Dfull) = iotaD s.unop) := by
  refine ⟨betaS_explicit, iotaS_beta, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun n => ?_, rfl, rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => rfl⟩
  · rw [qS, qOf, xpow, ordProd]
  · simp only [hs, liftWordS, seed10, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, mul_assoc, show ¬ (10 : ℕ) = 6 by decide, show ¬ (10 : ℕ) = 8 by decide,
      ↓reduceIte]
  · show hs 0 * qS 4194304 = qS 4194304
    rw [show hs 0 = 1 from rfl, one_mul]
  · show hs 0 * qS 1 = qS 1
    rw [show hs 0 = 1 from rfl, one_mul]
  · show hs 0 * qS 3 = qS 3
    rw [show hs 0 = 1 from rfl, one_mul]
  · show hs 0 * qS 7 = qS 7
    rw [show hs 0 = 1 from rfl, one_mul]
  · exact (rfl : hs 6 * qS 43 = hs 6 * qS 43)
  · exact (rfl : hs 6 * qS 61 = hs 6 * qS 61)
  · exact (rfl : hs 6 * qS 10541 = hs 6 * qS 10541)
  · exact (rfl : hs 6 * qS 26925 = hs 6 * qS 26925)
  · exact (rfl : hs 6 * qS 46090 = hs 6 * qS 46090)
  · exact (rfl : hs 8 * qS 0 = hs 8 * qS 0)
  · exact (rfl : hs 8 * qS 128 = hs 8 * qS 128)
  · exact (rfl : hs 8 * qS 35764 = hs 8 * qS 35764)
  · exact (rfl : hs 10 * qS 107 = hs 10 * qS 107)
  · exact (rfl : hs 10 * qS 66038 = hs 10 * qS 66038)

end CFSG.Monster.B.CTIB
