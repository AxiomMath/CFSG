
module

public import Certificates.Kernel.Co1B.IotaData
public import Certificates.Kernel.Co1Cover.Checks
public import CFSG.Certificates.Kernel.Co1BSound
public import CFSG.Sporadic.Co1Block.TwoACheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylData

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo1B

open CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KD.Co1B CFSG.KLie.CT CertificateChecks.KernelCo1Cover
  CFSG.Sporadic.SmallF2.Native

theorem andB_eq_and (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem aR_eq : CFSG.Sporadic.Co1Schreier.Native.aR = unpackR 24 R0 := by
  change rowsOfPayload 24 CFSG.Sporadic.Co1.Native.seedA = _
  rw [SeedA.eq]
  exact bind_sound seedA_bind

theorem bR_eq : CFSG.Sporadic.Co1Schreier.Native.bR = unpackR 24 R1 := by
  change rowsOfPayload 24 CFSG.Sporadic.Co1.Native.seedB = _
  rw [SeedB.eq]
  exact bind_sound seedB_bind

theorem seedInv_chk : andB (andB (andB (canK R0) (canK SAI)) (Nat.beq (mulK R0 SAI) oneK))
    (andB (andB (canK R1) (canK SBI)) (Nat.beq (mulK R1 SBI) oneK)) = true := by quickRfl

theorem h_chk : andB (Nat.beq H0 (wordK [R0, R1] [SAI, SBI]
      (CFSG.Sporadic.Co1Schreier.Data.stabWord0.map Int.ofNat)))
    (Nat.beq H1 (wordK [R0, R1] [SAI, SBI] (CFSG.Sporadic.Co1Schreier.Data.stabWord1.map Int.ofNat))) =
    true := by quickRfl

theorem dag_chk : dagOK [H0, H1] CFSG.Sporadic.Co1Block.iotaDerivs IRS IRIS = true := by quickRfl

theorem hRows_eq : CFSG.Sporadic.Co1Schreier.Native.hRows0 = unpackR 24 H0 ∧
    CFSG.Sporadic.Co1Schreier.Native.hRows1 = unpackR 24 H1 := by
  have hs := seedInv_chk
  simp only [andB_eq_and, Bool.and_eq_true] at hs
  have hh := h_chk
  simp only [andB_eq_and, Bool.and_eq_true] at hh
  have ha := inv_sound' (A := R0) (AI := SAI) (by simp only [andB_eq_and, Bool.and_eq_true]; exact hs.1)
  have hb := inv_sound' (A := R1) (AI := SBI) (by simp only [andB_eq_and, Bool.and_eq_true]; exact hs.2)
  have hw : ∀ w : List Nat, CFSG.Sporadic.Co1Schreier.Native.word
      [CFSG.Sporadic.Co1Schreier.Native.aR, CFSG.Sporadic.Co1Schreier.Native.bR]
      [CFSG.Sporadic.Co1Schreier.Native.inv CFSG.Sporadic.Co1Schreier.Native.aR,
        CFSG.Sporadic.Co1Schreier.Native.inv CFSG.Sporadic.Co1Schreier.Native.bR] (w.map Int.ofNat) =
      unpackR 24 (wordK [R0, R1] [SAI, SBI] (w.map Int.ofNat)) := by
    intro w
    rw [aR_eq, bR_eq, ha, hb]
    exact word_sound [R0, R1] [SAI, SBI] _
  refine ⟨?_, ?_⟩
  · rw [CFSG.Sporadic.Co1Schreier.Native.hRows0, hw, Nat.eq_of_beq_eq_true hh.1]
  · rw [CFSG.Sporadic.Co1Schreier.Native.hRows1, hw, Nat.eq_of_beq_eq_true hh.2]

theorem iotaRows_eq : CFSG.Sporadic.Co1Block.iotaRows = IRS.map (unpackR 24) := by
  have h := dag_sound dag_chk
  rw [CFSG.Sporadic.Co1Block.iotaRows, hRows_eq.1, hRows_eq.2]
  exact congrArg Prod.fst h

theorem getL_eq (x : Nat) : ∀ (l : List Nat) (i : Nat), getL x l i = l.getD i x
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => getL_eq x l i

theorem getD_map_lt {l : List Nat} {i : Nat} (hi : i < l.length) (d : Array Nat) (x : Nat) :
    (l.map (unpackR 24)).getD i d = unpackR 24 (getL x l i) := by
  rw [getL_eq, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    List.getD_eq_getElem _ _ hi]

theorem IRS_len : IRS.length = 52 := rfl

theorem iota_get {k : Nat} (hk : k < 52) :
    CFSG.Sporadic.Co1Block.iotaRows.getD k CFSG.Sporadic.Co1Schreier.Native.one =
      unpackR 24 (getL oneK IRS k) := by
  rw [iotaRows_eq]
  exact getD_map_lt (by rw [IRS_len]; exact hk) _ _

theorem iotaA_eq : CFSG.Sporadic.Co1Block.iotaARows = unpackR 24 (getL oneK IRS 23) :=
  iota_get (by decide)

theorem iotaC_eq : CFSG.Sporadic.Co1Block.iotaCRows = unpackR 24 (getL oneK IRS 51) :=
  iota_get (by decide)

@[expose] noncomputable def IQK : List Nat := (List.range 8).map fun k => getL oneK IRS (36 + k)

theorem twoAQ_eq : CFSG.Sporadic.Co1Block.twoAQRows = IQK.map (unpackR 24) := by
  rw [CFSG.Sporadic.Co1Block.twoAQRows, IQK, List.map_map]
  apply List.map_congr_left
  intro k hk
  exact iota_get (by have := List.mem_range.1 hk; omega)

theorem one_eq : unpackR 24 oneK = CFSG.Sporadic.Co1Schreier.Native.one := by
  have h : (unpackR 24 oneK == CFSG.Sporadic.Co1Schreier.Native.one) = true := by quickRfl
  exact eq_of_beq h

theorem getD_map_u (x : Nat) : ∀ (l : List Nat) (i : Nat),
    (l.map (unpackR 24)).getD i (unpackR 24 x) = unpackR 24 (getL x l i)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => getD_map_u x l i

theorem iotaRows_get (k : Nat) :
    CFSG.Sporadic.Co1Block.iotaRows.getD k CFSG.Sporadic.Co1Schreier.Native.one =
      unpackR 24 (getL oneK IRS k) := by
  rw [iotaRows_eq, ← one_eq]
  exact getD_map_u oneK IRS k

theorem iotaQ_eq (k : Nat) : CFSG.Sporadic.Co1Block.iotaQRows k = unpackR 24 (getL oneK IRS (36 + k)) :=
  iotaRows_get (36 + k)

theorem foldl_mul_unpack (p : Nat → Bool) (f : Nat → Nat) : ∀ (L : List Nat) (a : Nat),
    L.foldl (fun acc i => if p i = true then CFSG.Sporadic.Co1Schreier.Native.mul acc (unpackR 24 (f i))
      else acc) (unpackR 24 a) =
      unpackR 24 (L.foldl (fun acc i => if p i = true then mulK acc (f i) else acc) a)
  | [], _ => rfl
  | i :: L, a => by
    rw [List.foldl_cons, List.foldl_cons]
    by_cases h : p i = true
    · simp only [h, ↓reduceIte]
      rw [mul_unpack]
      exact foldl_mul_unpack p f L _
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      exact foldl_mul_unpack p f L a

end CertificateChecks.KernelCo1B

end
