module

public import CFSG.Sporadic.Co1Patterson.TwistNativeInputs
public import Certificates.Kernel.Co1B.Twist
public import Certificates.Kernel.Co1B.Weyl
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo1B

open CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KD.Co1B CFSG.Sporadic.Co1Schreier.Native
  CFSG.Sporadic.Co1Patterson.TwistNative

theorem bne_unpack (A B : Nat) : (unpackR 24 A != unpackR 24 B) = !eqK A B := by
  rw [bne, beq_unpack]

theorem tw_dagOK : CFSG.Sporadic.Co1Patterson.TwistNative.dagOK = true := by
  simp only [CFSG.Sporadic.Co1Patterson.TwistNative.dagOK, tw_flag, iotaA_eq, yRow_q, yprodRow_q, twRow_get, validRows_unpackR]
  quickRfl

@[expose] noncomputable def yfK (c : Nat) : Bool :=
  (eqK (mulK (ypK c) (ypK c)) oneK == !CFSG.EvenSmallLie.OmegaEight.qNat c) &&
    (List.range 8).all fun i =>
      (eqK (mulK (ypK c) (qwK (yBits.getD ((i + 4) % 8) 0))) (mulK (qwK (yBits.getD ((i + 4) % 8) 0)) (ypK c)) ==
        !c.testBit i)

#j4q_all CFSG.KD.Co1B.YF CertificateChecks.KernelCo1B.yfK 256

theorem tw_yForm : yFormOK = true := by
  unfold yFormOK
  refine List.all_eq_true.2 fun c hc => ?_
  have h := YF.all c (List.mem_range.1 hc)
  simp only [yRow_q, yprodRow_q, mul_unpack, ← one_eq, beq_unpack]
  exact h

theorem tw_elems : elemsOK = true := by
  simp only [elemsOK, conjOK, twRow_get, invTw, iotaA_eq, yRow_q, yprodRow_q, mul_unpack, ← one_eq,
    beq_unpack]
  quickRfl

@[expose] noncomputable def irK (t : Nat) : Bool :=
  (fun x => x == 0 || (wVecs.all fun u => (xorSpan (irrWords.map fun w => actWord w x)).contains u))
    (wVecs.getD t 0)

#j4q_all CFSG.KD.Co1B.IR CertificateChecks.KernelCo1B.irK 64

theorem wVecs_len : wVecs.length = 64 := by
  have h : (wVecs.length == 64) = true := by quickRfl
  exact eq_of_beq h

theorem tw_irr : irrOK = true := by
  unfold irrOK
  refine List.all_eq_true.2 fun x hx => ?_
  obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hx
  have ht' : t < 64 := by
    have := ht
    rwa [wVecs_len] at this
  have h := IR.all t ht'
  rw [irK, List.getD_eq_getElem _ _ ht] at h
  exact h

theorem tw_u : uOK = true := by quickRfl

@[expose] noncomputable def usK (t : Nat) : Bool :=
  (fun bs => (List.range 256).all fun mu => !isoCols (candCols bs mu) || (List.range 64).any fun c =>
    (List.range 8).all fun k => (mprodCols c).getD k 0 == (candCols bs mu).getD k 0) ((allBools 6).getD t [])

#j4q_all CFSG.KD.Co1B.US CertificateChecks.KernelCo1B.usK 64

theorem allBools_len : (allBools 6).length = 64 := rfl

theorem tw_uSet : uSetOK = true := by
  unfold uSetOK
  refine List.all_eq_true.2 fun bs hbs => ?_
  obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hbs
  have ht' : t < 64 := by
    have := ht
    rwa [allBools_len] at this
  have h := US.all t ht'
  rw [usK, List.getD_eq_getElem _ _ ht] at h
  exact h

theorem tw_h4 : h4OK = true := by
  simp only [h4OK, twRow_get, iotaA_eq, yprodRow_q, mul_unpack, ← one_eq, beq_unpack, bne_unpack]
  quickRfl

theorem tw_nwc : nwcOK = true := by
  simp only [nwcOK, twRow_get, invTw, iotaA_eq, yRow_q, mul_unpack, ← one_eq, beq_unpack, bne_unpack]
  quickRfl

theorem all_range_congr' {f g : Nat → Bool} : ∀ {n : Nat}, (∀ i < n, f i = g i) →
    (List.range n).all f = (List.range n).all g
  | 0, _ => rfl
  | n + 1, h => by
    rw [List.range_succ, List.all_append, List.all_append,
      all_range_congr' fun i hi => h i (Nat.lt_succ_of_lt hi), List.all_cons, List.all_cons,
      h n (Nat.lt_succ_self n), List.all_nil, List.all_nil]

theorem sign1 : ((List.range 64).all fun c => Nat.beq (sqK 1 c) NEGP || Nat.beq (sqK 1 c) pidK) = true := by
  quickRfl

theorem sign2 : ((List.range 64).all fun c => Nat.beq (sqK 2 c) NEGP || Nat.beq (sqK 2 c) pidK) = true := by
  quickRfl

theorem tw_sign : signOK = true := by
  unfold signOK
  rw [List.all_cons, List.all_cons, List.all_nil, all_range_congr' (fun c hc => sgn_eq (Or.inl rfl) hc),
    all_range_congr' (fun c hc => sgn_eq (Or.inr rfl) hc), sign1, sign2]
  rfl

open Certificates in
open CFSG.Sporadic.Co1Patterson.TwistNative in
theorem c21141 : (CFSG.Sporadic.Co1Patterson.TwistNative.dagOK = true)
    ∧ (yFormOK = true)
    ∧ (elemsOK = true)
    ∧ (irrOK = true)
    ∧ (uOK = true)
    ∧ (uSetOK = true)
    ∧ (h4OK = true)
    ∧ (nwcOK = true)
    ∧ (signOK = true) :=
  ⟨tw_dagOK, tw_yForm, tw_elems, tw_irr, tw_u, tw_uSet, tw_h4, tw_nwc, tw_sign⟩

end CertificateChecks.KernelCo1B

end
