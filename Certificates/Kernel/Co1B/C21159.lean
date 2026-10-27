module

public import CFSG.Sporadic.Co1Patterson.AmalgamInnerInputs
public import Certificates.Kernel.Co1B.C21142
public import Certificates.Kernel.Co1B.Tab21159
public import Certificates.Kernel.Co1B.Loop21159
import CFSG.Certificates.Kernel.Co1BMulSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo1B

open CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KD.Co1B CFSG.KC.Loop CFSG.KLie.CT
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Patterson.TwistNative
  CFSG.Sporadic.Co1Patterson.Native

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem kRow_eq (j : Nat) : kRow j = unpackR 24 (getL oneK TWS (kIdx.getD j 0 - 1)) := twRow_get _

theorem kRowI_eq (j : Nat) : kRowI j = unpackR 24 (getL oneK TWIS (kIdx.getD j 0 - 1)) := by
  rw [kRowI, kRow_eq, invTw]

theorem kWordR_aux : ∀ (w : List Nat) (a : Nat),
    w.foldl (fun acc j => mul acc (kRow j)) (unpackR 24 a) =
      unpackR 24 (w.foldl (fun acc j => mulK acc (getL oneK TWS (kIdx.getD j 0 - 1))) a)
  | [], _ => rfl
  | j :: w, a => by
    rw [List.foldl_cons, List.foldl_cons, kRow_eq, mul_unpack]
    exact kWordR_aux w _

theorem kWordR_eq (w : List Nat) : kWordR w = unpackR 24 (kwK w) := by
  rw [kWordR, kwK, ← one_eq]
  exact kWordR_aux w oneK

theorem kWordIR_aux : ∀ (w : List Nat) (a : Nat),
    w.foldl (fun acc j => mul (kRowI j) acc) (unpackR 24 a) =
      unpackR 24 (w.foldl (fun acc j => mulK (getL oneK TWIS (kIdx.getD j 0 - 1)) acc) a)
  | [], _ => rfl
  | j :: w, a => by
    rw [List.foldl_cons, List.foldl_cons, kRowI_eq, mul_unpack]
    exact kWordIR_aux w _

theorem kWordIR_eq (w : List Nat) : kWordIR w = unpackR 24 (kwiK w) := by
  rw [kWordIR, kwiK, ← one_eq]
  exact kWordIR_aux w oneK

theorem pow_unpack (M : Nat) : ∀ e : Nat, pow (unpackR 24 M) e = unpackR 24 (powWK M e)
  | 0 => one_eq.symm
  | e + 1 => by
    have h : powWK M (e + 1) = mulWK (powWK M e) M := CFSG.KC.F2W.strictN_eq _ _
    rw [pow, pow_unpack M e, mul_unpackWK, h]

theorem rx_eq : rxRow = unpackR 24 RX59 := by
  rw [rxRow, aRowOf_eq]
  exact congrArg (unpackR 24) (Nat.eq_of_beq_eq_true rx_chk)

theorem ry_eq : ryRow = unpackR 24 RY59 := by
  rw [ryRow, hprodRow_eq, aRowOf_eq, mul_unpackWK]
  exact congrArg (unpackR 24) (Nat.eq_of_beq_eq_true ry_chk)

theorem g1_eq : kWordR (stabWords.getD 0 []) = unpackR 24 G159 := by
  rw [kWordR_eq]
  exact congrArg (unpackR 24) (Nat.eq_of_beq_eq_true g1_chk)

theorem g2_eq : kWordR (stabWords.getD 1 []) = unpackR 24 G259 := by
  rw [kWordR_eq]
  exact congrArg (unpackR 24) (Nat.eq_of_beq_eq_true g2_chk)

theorem k1_eq : kRow 1 = unpackR 24 K159 := by
  rw [kRow_eq]
  exact congrArg (unpackR 24) (Nat.eq_of_beq_eq_true k1_chk)

theorem vRows_eq : vRows = V59.map (unpackR 24) := by
  rw [vRows, V59]
  simp only [List.map_cons, List.map_nil, one_eq, iotaA_AL, w0_eq, mul_unpackWK, w0a_K]

theorem tRow_eq {j : Nat} (hj : j < 12) : tRow j = unpackR 24 (getL 0 T59 j) := by
  have h := TT59.all j hj
  rw [ttChk] at h
  have h' := Nat.eq_of_beq_eq_true h
  rw [tRow, kWordR_eq, kWordIR_eq]
  by_cases h6 : j < 6
  · have hb : Nat.blt j 6 = true := cast Nat.blt_eq.symm h6
    rw [hb] at h'
    rw [ite_eq_left h6, rx_eq, mul_unpack, mul_unpack]
    exact congrArg (unpackR 24) h'
  · have hb : Nat.blt j 6 = false := Bool.eq_false_iff.2 fun h => h6 (cast Nat.blt_eq h)
    rw [hb] at h'
    rw [ite_eq_right h6, ry_eq, mul_unpack, mul_unpack]
    exact congrArg (unpackR 24) h'

theorem T59_len : T59.length = 12 := rfl

theorem TS059_len : TS059.length = 64 := rfl

theorem TS659_len : TS659.length = 64 := rfl

theorem T_eq : (List.range 12).map tRow = T59.map (unpackR 24) := by
  apply List.ext_getElem (by rw [List.length_map, List.length_map, List.length_range, T59_len])
  intro n h1 h2
  have hn : n < 12 := by rwa [List.length_map, List.length_range] at h1
  rw [List.getElem_map, List.getElem_range, List.getElem_map, tRow_eq hn,
    getL_get 0 (by rw [T59_len]; exact hn)]

theorem tSub_eq {b : Nat} (hb : b = 0 ∨ b = 6) (S : Nat) : tSub b S = unpackR 24 (tsK b S) := by
  rw [tSub, tsK, ← one_eq]
  rw [List.foldl_ext _ (fun acc j => if S.testBit j = true then mul acc (unpackR 24 (getL 0 T59 (b + j)))
    else acc) _ ?_]
  · exact foldl_mul_unpack (fun j => S.testBit j) (fun j => getL 0 T59 (b + j)) _ oneK
  · intro acc j hj
    have := List.mem_range.1 hj
    rw [tRow_eq (by omega)]

theorem T0_eq : (List.range 64).map (tSub 0) = TS059.map (unpackR 24) := by
  apply List.ext_getElem (by rw [List.length_map, List.length_map, List.length_range, TS059_len])
  intro n h1 h2
  have hn : n < 64 := by rwa [List.length_map, List.length_range] at h1
  have h := CFSG.KC.Co1B.andB_true (TS59.all n hn)
  rw [List.getElem_map, List.getElem_range, List.getElem_map, tSub_eq (Or.inl rfl),
    Nat.eq_of_beq_eq_true h.1, getL_get 0 (by rw [TS059_len]; exact hn)]

theorem T6_eq : (List.range 64).map (tSub 6) = TS659.map (unpackR 24) := by
  apply List.ext_getElem (by rw [List.length_map, List.length_map, List.length_range, TS659_len])
  intro n h1 h2
  have hn : n < 64 := by rwa [List.length_map, List.length_range] at h1
  have h := CFSG.KC.Co1B.andB_true (TS59.all n hn)
  rw [List.getElem_map, List.getElem_range, List.getElem_map, tSub_eq (Or.inr rfl),
    Nat.eq_of_beq_eq_true h.2, getL_get 0 (by rw [TS659_len]; exact hn)]

theorem map_arK0 : ∀ L : List Nat,
    (L.map ypT).flatMap (fun Y => [Y, mulWK Y AL42]) = (L.flatMap fun c => [(c, 0), (c, 1)]).map arK
  | [] => rfl
  | c :: L => by
    simp only [List.map_cons, List.flatMap_cons, List.map_append, map_arK0 L]
    rfl

theorem AP_eq : AP59 = aList.map arK := by
  rw [of_decide_eq_true ap_chk, YP_eq, aList_eq, map_arK0]

theorem arK_idx {i : Nat} (hi : i < aList.length) : arK aList[i] = getL 0 AP59 i := by
  have hl : i < AP59.length := by rw [AP_eq, List.length_map]; exact hi
  rw [getL_get 0 hl]
  simp only [AP_eq, List.getElem_map]

theorem zip_map_self {α β : Type} (f : α → β) : ∀ l : List α, l.zip (l.map f) = l.map fun p => (p, f p)
  | [] => rfl
  | a :: l => by rw [List.map_cons, List.zip_cons_cons, zip_map_self f l, List.map_cons]

theorem getL_mem0 {L : List Nat} {s : Nat} (h : s < L.length) : getL 0 L s ∈ L := by
  rw [getL_get 0 h]
  exact List.getElem_mem h

theorem inner_elem : innerElemOK = true := by
  unfold innerElemOK stabR
  simp only [kRowI_eq, kRow_eq, validRows_unpackR, ← one_eq, pow_unpack, rx_eq, ry_eq, iotaA_AL, w0_eq,
    vRows_eq, kWordR_eq, List.any_map, Function.comp_def, mul_unpackWK, beq_unpack]
  quickRfl

theorem inner_gen : innerGenOK = true := by
  unfold innerGenOK
  simp only [T0_eq, T6_eq, T_eq, vRows_eq, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine List.all_eq_true.2 fun p hp => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
    have hi' : i < 256 := by rwa [aList_len] at hi
    obtain ⟨hsv, he⟩ := CFSG.KC.Co1B.andB_true (W159.all i hi')
    obtain ⟨hs, hv⟩ := CFSG.KC.Co1B.andB_true hsv
    refine List.any_eq_true.2 ⟨_, List.mem_map_of_mem (getL_mem0 (by rw [TS059_len]; exact cast Nat.blt_eq hs)),
      List.any_eq_true.2 ⟨_, List.mem_map_of_mem (getL_mem0 (cast Nat.blt_eq hv)), ?_⟩⟩
    rw [aRowOf_eq, mul_unpackWK, beq_unpack, arK_idx hi]
    exact he
  · refine List.all_eq_true.2 fun i hi => ?_
    have hi' := List.mem_range.1 hi
    obtain ⟨hsj, he⟩ := CFSG.KC.Co1B.andB_true (W259.all i hi')
    obtain ⟨hs, hj⟩ := CFSG.KC.Co1B.andB_true hsj
    have hj' : getL 0 W2J59 i < aList.length := by rw [aList_len]; exact cast Nat.blt_eq hj
    refine List.any_eq_true.2 ⟨_, List.mem_map_of_mem (getL_mem0 (by rw [TS659_len]; exact cast Nat.blt_eq hs)),
      List.any_eq_true.2 ⟨_, List.getElem_mem hj', ?_⟩⟩
    rw [aRowOf_eq, twRow_get, mul_unpackWK, beq_unpack, arK_idx hj']
    exact he
  · simp only [List.all_map, List.any_map, Function.comp_def, mul_unpackWK, beq_unpack]
    exact comm_chk

theorem loopAt_eq (TT : List Nat) (G1 G2 X1 c : Nat) (p : Nat × Nat) (R : Nat) :
    loopAt (TT.map (unpackR 24)) (unpackR 24 G1) (unpackR 24 G2) (unpackR 24 X1) c p (unpackR 24 R) =
      loopK TT [oneK, AL42, W0L42, W0AL42] AL42 W0L42 G1 G2 X1 RX59 RY59 (isVP c p) R := by
  unfold loopAt loopK stabR stabK vAnyS
  simp only [strictB_eq, vRows_eq, V59, rx_eq, ry_eq, iotaA_AL, w0_eq, List.all_map, List.any_map,
    Function.comp_def, mul_unpackWK, beq_unpack, bne]
  rfl

theorem inner_loop : innerLoopOK = true := by
  unfold innerLoopOK
  refine List.all_eq_true.2 fun c hc => ?_
  have h := LP59.all c (List.mem_range.1 hc)
  have hz : aList.zip AP59 = aList.map fun p => (p, arK p) := by
    rw [AP_eq]
    exact zip_map_self arK aList
  simp only [lpK, strictB_eq, hz, List.all_map, Function.comp_def] at h
  simp only [T_eq, g1_eq, g2_eq, k1_eq, hprodRow_eq, aRowOf_eq, mul_unpackWK, List.all_map,
    Function.comp_def, loopAt_eq]
  exact h

open Certificates in
theorem c21159 : CFSG.Sporadic.Co1Patterson.Native.innerElemOK = true ∧
    CFSG.Sporadic.Co1Patterson.Native.innerGenOK = true ∧
    CFSG.Sporadic.Co1Patterson.Native.innerLoopOK = true := ⟨inner_elem, inner_gen, inner_loop⟩

end CertificateChecks.KernelCo1B

end
