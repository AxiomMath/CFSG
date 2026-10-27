module

public import CFSG.Sporadic.Co1Patterson.TwistNativeInputs
public import Certificates.Kernel.Co1B.Cnt21142
public import Certificates.Kernel.Co1B.Tab21142
public import Certificates.Kernel.Co1B.Twist
public import Certificates.Kernel.Co1B.Weyl
import CFSG.Certificates.Kernel.Co1BMulSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo1B

open CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KD.Co1B CFSG.KC.Loop CFSG.KLie.CT
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Patterson.TwistNative

theorem code4_eq (A O W V S : Nat) : code4 A O W V S =
    (eqK S A).toNat + 512 * (eqK S O).toNat + 262144 * (eqK S W).toNat +
      134217728 * (eqK S V).toNat := by
  unfold code4
  cases eqK S A <;> cases eqK S O <;> cases eqK S W <;> cases eqK S V <;> rfl

theorem sum_code {α : Type} (A O W V : Nat) (f : α → Nat) : ∀ L : List α,
    (L.map fun x => code4 A O W V (f x)).sum =
      (L.filter fun x => eqK (f x) A).length + 512 * (L.filter fun x => eqK (f x) O).length +
        262144 * (L.filter fun x => eqK (f x) W).length +
        134217728 * (L.filter fun x => eqK (f x) V).length
  | [] => rfl
  | x :: L => by
    rw [List.map_cons, List.sum_cons, sum_code A O W V f L, code4_eq]
    simp only [List.filter_cons]
    cases eqK (f x) A <;> cases eqK (f x) O <;> cases eqK (f x) W <;> cases eqK (f x) V <;>
      simp only [Bool.toNat_true, Bool.toNat_false, ↓reduceIte, Bool.false_eq_true,
        List.length_cons] <;> omega

theorem cnt4_eq (A O W V H : Nat) : ∀ YP : List Nat, cnt4 A O W V H YP =
    ((YP.flatMap fun Y => [mulWK H Y, mulWK H (mulWK Y A)]).map
      fun X => code4 A O W V (mulWK X X)).sum
  | [] => rfl
  | Y :: L => by
    have h : cnt4 A O W V H (Y :: L) = sqCode A O W V (mulWK H Y) +
        (sqCode A O W V (mulWK H (mulWK Y A)) + cnt4 A O W V H L) := rfl
    rw [h, cnt4_eq A O W V H L, List.flatMap_cons, List.map_append, List.sum_append]
    simp only [sqCode, CFSG.KC.F2W.strictN_eq, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    omega

theorem len_sel {α : Type} (l : List α) (f g : α → Bool) (s : Bool) :
    (l.filter fun p => (f p && !s) || (g p && s)).length =
      Bool.rec (motive := fun _ => Nat) (l.filter f).length (l.filter g).length s := by
  cases s <;> simp

theorem mul_unpackWK (A B : Nat) : mul (unpackR 24 A) (unpackR 24 B) = unpackR 24 (mulWK A B) :=
  CFSG.KC.F2W.mul_unpackW A B

theorem AL_eq : getL oneK IRS 23 = AL42 :=
  Nat.eq_of_beq_eq_true (CFSG.KC.Co1B.andB_true consts_chk).1

theorem W0_eq : qwT 1 = W0L42 :=
  Nat.eq_of_beq_eq_true (CFSG.KC.Co1B.andB_true (CFSG.KC.Co1B.andB_true consts_chk).2).1

theorem w0a_K : mulWK W0L42 AL42 = W0AL42 :=
  (CFSG.KC.F2W.mulW_eq 24 _ _).trans
    (Nat.eq_of_beq_eq_true (CFSG.KC.Co1B.andB_true (CFSG.KC.Co1B.andB_true consts_chk).2).2)

theorem iotaA_AL : CFSG.Sporadic.Co1Block.iotaARows = unpackR 24 AL42 := by
  rw [iotaA_eq, AL_eq]

theorem w0_eq : yRow 0 = unpackR 24 W0L42 := by
  rw [yRow_q, ← W0_eq]
  rfl

theorem ypK_eq : ypK = ypT := rfl

theorem yprodRow_T (c : Nat) : yprodRow c = unpackR 24 (ypT c) := by
  rw [yprodRow_q, ypK_eq]

theorem hprodRow_eq (c : Nat) : hprodRow c = unpackR 24 (hpK c) := by
  rw [hprodRow, hpK, ← one_eq]
  simp only [twRow_get]
  exact foldl_mul_unpack (fun i => c.testBit i) (fun i => getL oneK TWS (hIdx.getD i 0 - 1)) _ oneK

@[expose] noncomputable def arK (p : Nat × Nat) : Nat := if p.2 = 1 then mulWK (ypT p.1) AL42 else ypT p.1

theorem aRowOf_eq (p : Nat × Nat) : aRowOf p = unpackR 24 (arK p) := by
  unfold aRowOf arK
  by_cases h : p.2 = 1
  · rw [ite_eq_left h, ite_eq_left h, yprodRow_T, iotaA_AL, mul_unpackWK]
  · rw [ite_eq_right h, ite_eq_right h, yprodRow_T]

theorem ALK_len : ALK42.length = 128 := rfl

theorem YP_len : YP42.length = 128 := rfl

theorem getL_get (x : Nat) {L : List Nat} {i : Nat} (h : i < L.length) : getL x L i = L[i] := by
  rw [CFSG.KC.Co1B.getL_eq, List.getElem?_eq_getElem h, Option.getD_some]

theorem YP_eq : YP42 = ALK42.map ypT := by
  apply List.ext_getElem (by rw [List.length_map, YP_len, ALK_len])
  intro n h1 h2
  have hn : n < 128 := by rwa [YP_len] at h1
  have h := Nat.eq_of_beq_eq_true (YPT42.all n hn)
  rw [getL_get 0 (by rw [ALK_len]; exact hn), getL_get 0 h1] at h
  rw [List.getElem_map, h]

theorem aList_eq : aList = ALK42.flatMap fun c => [(c, 0), (c, 1)] := of_decide_eq_true aList_chk

theorem aList_len : aList.length = 256 := by
  rw [aList_eq]
  rfl

theorem map_arK (H : Nat) : ∀ L : List Nat,
    (L.flatMap fun c => [(c, 0), (c, 1)]).map (fun p => mulWK H (arK p)) =
      (L.map ypT).flatMap fun Y => [mulWK H Y, mulWK H (mulWK Y AL42)]
  | [] => rfl
  | c :: L => by
    simp only [List.map_cons, List.flatMap_cons, List.map_append, map_arK H L]
    rfl

@[expose] noncomputable def sq42 (c : Nat) (p : Nat × Nat) : Nat :=
  mulWK (mulWK (hpK c) (arK p)) (mulWK (hpK c) (arK p))

@[expose] noncomputable def nT (c T : Nat) : Nat := (aList.filter fun p => eqK (sq42 c p) T).length

theorem nT_le (c T : Nat) : nT c T ≤ 256 := by
  rw [nT, ← aList_len]
  exact List.length_filter_le _ _

theorem cnt_eq {c : Nat} (hc : c < 64) : getL 0 CNT42 c =
    nT c AL42 + 512 * nT c oneK + 262144 * nT c W0L42 + 134217728 * nT c W0AL42 := by
  have h := SQ42.all c hc
  rw [cntK] at h
  have h' := Nat.eq_of_beq_eq_true h
  rw [CFSG.KC.F2W.strictN_eq, cnt4_eq, YP_eq, ← map_arK, ← aList_eq, sum_code] at h'
  simp only [List.filter_map, List.length_map] at h'
  exact h'.symm

theorem countTw_0 {k : Nat} (hk : k = 1 ∨ k = 2) : countTw k 0 =
    ((List.range 64).map fun c => Bool.rec (motive := fun _ => Nat) (getL 0 CNT42 c % 512)
      (getL 0 CNT42 c / 512 % 512) (negK k c)).sum := by
  unfold countTw
  congr 1
  apply List.map_congr_left
  intro c hc
  have hc' := List.mem_range.1 hc
  simp only [negSq_eq hk hc', hprodRow_eq, aRowOf_eq, mul_unpackWK, iotaA_AL, ← one_eq, beq_unpack,
    ↓reduceIte]
  refine (len_sel aList (fun p => eqK (sq42 c p) AL42) (fun p => eqK (sq42 c p) oneK) (negK k c)).trans ?_
  have h := cnt_eq hc'
  have h1 := nT_le c AL42
  have h2 := nT_le c oneK
  have h3 := nT_le c W0L42
  have e1 : (aList.filter fun p => eqK (sq42 c p) AL42).length = getL 0 CNT42 c % 512 := by
    change nT c AL42 = _
    omega
  have e2 : (aList.filter fun p => eqK (sq42 c p) oneK).length = getL 0 CNT42 c / 512 % 512 := by
    change nT c oneK = _
    omega
  rw [e1, e2]

theorem countTw_1 {k : Nat} (hk : k = 1 ∨ k = 2) : countTw k 1 =
    ((List.range 64).map fun c => Bool.rec (motive := fun _ => Nat) (getL 0 CNT42 c / 262144 % 512)
      (getL 0 CNT42 c / 134217728 % 512) (negK k c)).sum := by
  unfold countTw
  congr 1
  apply List.map_congr_left
  intro c hc
  have hc' := List.mem_range.1 hc
  simp only [negSq_eq hk hc', hprodRow_eq, aRowOf_eq, mul_unpackWK, iotaA_AL, w0_eq, w0a_K,
    beq_unpack]
  refine (len_sel aList (fun p => eqK (sq42 c p) W0L42) (fun p => eqK (sq42 c p) W0AL42)
    (negK k c)).trans ?_
  have h := cnt_eq hc'
  have h1 := nT_le c AL42
  have h2 := nT_le c oneK
  have h3 := nT_le c W0L42
  have h4 := nT_le c W0AL42
  have e1 : (aList.filter fun p => eqK (sq42 c p) W0L42).length = getL 0 CNT42 c / 262144 % 512 := by
    change nT c W0L42 = _
    omega
  have e2 : (aList.filter fun p => eqK (sq42 c p) W0AL42).length =
      getL 0 CNT42 c / 134217728 % 512 := by
    change nT c W0AL42 = _
    omega
  rw [e1, e2]

open Certificates in
open CFSG.Sporadic.Co1Patterson.TwistNative in
theorem c21142 : countOK = true := by
  unfold countOK
  rw [countTw_0 (Or.inl rfl), countTw_1 (Or.inl rfl), countTw_0 (Or.inr rfl), countTw_1 (Or.inr rfl)]
  quickRfl

end CertificateChecks.KernelCo1B

end
