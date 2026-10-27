module

public import Certificates.Kernel.Co1OddB.Cand0
public import Certificates.Kernel.Co1OddB.Cand1
public import Certificates.Kernel.Co1OddB.Cand2
public import Certificates.Kernel.Co1OddB.Cand3
public import Certificates.Kernel.Co1Cover.Bridge
public import Certificates.Kernel.Co1B.C2046
public import CFSG.Certificates.Kernel.Co1OddBSound
public import CFSG.Certificates.Kernel.Co1M.FixListSound
public import CFSG.Sporadic.Schreier.Co1OddBCheckInputs
public meta import CFSG.Sporadic.Schreier.Co1OddData
public meta import CFSG.Sporadic.Schreier.Co1OddACCheck
public meta import CFSG.Sporadic.Co1.Module.TwoBData
public meta import CFSG.Sporadic.Co1.Module.InvData
public meta import CFSG.Sporadic.Co1.Module.Forms
public meta import CFSG.Sporadic.Co1.Module.Orbits
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Odd
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Certificates.Data.CFSGNative.HS.SmallF2
import Certificates.Kernel.Co1OddB.Neg

public section

namespace CertificateChecks.KernelCo1OddB

open CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KC.F2W CFSG.KC.Co1OddB CFSG.KC.Co1Fix CFSG.KC.M1F2
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Schreier.Native

theorem regs_eq : oddBRegs = (RB.map (unpackR 24)).toArray := by
  have hi : CFSG.Sporadic.Co1.Module.TwoB.initRowsB = ((RB.take 3).map (unpackR 24)).toArray := by
    rw [take3, CFSG.Sporadic.Co1.Module.TwoB.initRowsB, CertificateChecks.KernelCo1Cover.rowsA_eq,
      CertificateChecks.KernelCo1Cover.rowsB_eq, CertificateChecks.KernelCo1B.rowsSB_eq]
    rfl
  rw [oddBRegs, hi]
  exact prog_sound prog_ok

theorem reg {i : Nat} (hi : i < 25) : oddReg oddBRegs i = unpackR 24 (RB.getD i 0) := by
  have hl : i < RB.length := by rw [len.1]; exact hi
  rw [oddReg, regs_eq]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]

theorem sB : CFSG.Sporadic.Co1.Module.rowsSB = unpackR 24 CFSG.KD.Co1B.SBK :=
  CertificateChecks.KernelCo1B.rowsSB_eq

theorem map_get {α β γ : Type} [Inhabited α] {f : α → γ} {g : β → γ} {ws : List α} {Vs : List β}
    (d : β) (h : ws.map f = Vs.map g) {i : Nat} (hi : i < ws.length) :
    f ws[i]! = g (Vs.getD i d) := by
  have hl : ws.length = Vs.length := by simpa using congrArg List.length h
  have e := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem (hl ▸ hi : i < Vs.length), Option.map_some] at e
  rw [getElem!_pos ws i hi, Option.some.inj e, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (hl ▸ hi : i < Vs.length), Option.getD_some]

theorem prod_eq {G : Array (Array Nat)} : ∀ (ws : List (List (Nat × Nat))) (Vs : List Nat) (A : Nat),
    ws.map (lineRows G) = Vs.map (unpackR 24) →
    ws.foldl (fun acc w => mulRows 24 acc (lineRows G w)) (unpackR 24 A) =
      unpackR 24 (Vs.foldl (mulW 24) A)
  | [], [], _, _ => rfl
  | w :: ws, V :: Vs, A, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.foldl_cons]
    rw [h.1, mulRows_unpackW]
    exact prod_eq ws Vs _ h.2
  | [], _ :: _, _, h => absurd h (by simp)
  | _ :: _, [], _, h => absurd h (by simp)

theorem hs_eq : oddHsB = (HP.map (unpackR 24)).toArray := by
  rw [oddHsB, oddHs, oddX, oddY, reg (by decide), reg (by decide),
    lines_sound _ _ words.1 (by rw [len.2.2.2.2.1, len.2.1])]

theorem bt_eq : oddBT = unpackR 24 BT := by
  have hb := basis
  simp only [Bool.and_eq_true] at hb
  rw [oddBT, hs_eq, us_eq len.2.1]
  rw [← Nat.eq_of_beq_eq_true hb.1.1.2]
  rfl

theorem bti_eq : inv oddBT = unpackR 24 BTI := by
  have hb := basis
  simp only [Bool.and_eq_true] at hb
  rw [bt_eq]
  exact inv_unpackR (Nat.eq_of_beq_eq_true hb.1.2)

theorem valid_unpack (M : Nat) : validRows (unpackR 24 M) = true := by
  unfold validRows
  rw [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]
  refine ⟨by simp [unpackR], fun i hi => ?_⟩
  simp only [unpackR, Array.getElem_ofFn, decide_eq_true_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos 24)

theorem fixT (M c : Nat) : isFixedN (transposeRows 24 (unpackR 24 M)) c = (vmF 24 (trK 24 M) c == c) := by
  rw [transposeRows_unpackR, isFixed_unpackR]

theorem powE (M e : Nat) : (powRows 24 (unpackR 24 M) e == idRows 24) = eqK (powWK M e) oneK := by
  rw [powRows_eq _ idRows_eq, idRows_eq, beq_unpack]

theorem eq_of_eqK {A B : Nat} (h : eqK A B = true) : unpackR 24 A = unpackR 24 B := by
  rw [← beq_unpack] at h
  exact eq_of_beq h

theorem perfX : oddPerfOK #[unpackR 24 (RB.getD 9 0), unpackR 24 (RB.getD 14 0)] Data.oddPerfX
    (unpackR 24 (RB.getD 9 0)) = true := by
  have hm := lines_sound _ _ words.2.1 (by rw [len.2.2.2.2.2.1, len.2.2.1])
  have hp := perf
  simp only [Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true] at hp
  unfold oddPerfOK oddProdRows
  rw [idRows_eq, prod_eq _ _ _ hm, beq_unpack]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq]
  have hl := len.2.2.2.2.2.1
  rw [map_get 0 hm (by omega), map_get 0 hm (by omega), map_get 0 hm (by omega),
    map_get 0 hm (by omega), map_get 0 hm (by omega), map_get 0 hm (by omega),
    map_get 0 hm (by omega), map_get 0 hm (by omega)]
  rw [mulRows_unpackW, mulRows_unpackW, mulRows_unpackW, mulRows_unpackW]
  exact ⟨⟨hl, hp.1.1⟩, eq_of_eqK hp.2.1.1, eq_of_eqK hp.2.2.1.1, eq_of_eqK hp.2.2.2.1.1,
    eq_of_eqK hp.2.2.2.2.1⟩

theorem perfY : oddPerfOK #[unpackR 24 (RB.getD 9 0), unpackR 24 (RB.getD 14 0)] Data.oddPerfY
    (unpackR 24 (RB.getD 14 0)) = true := by
  have hm := lines_sound _ _ words.2.2 (by rw [len.2.2.2.2.2.2, len.2.2.2.1])
  have hp := perf
  simp only [Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true] at hp
  unfold oddPerfOK oddProdRows
  rw [idRows_eq, prod_eq _ _ _ hm, beq_unpack]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq]
  have hl := len.2.2.2.2.2.2
  rw [map_get 0 hm (by omega), map_get 0 hm (by omega), map_get 0 hm (by omega),
    map_get 0 hm (by omega), map_get 0 hm (by omega), map_get 0 hm (by omega),
    map_get 0 hm (by omega), map_get 0 hm (by omega)]
  rw [mulRows_unpackW, mulRows_unpackW, mulRows_unpackW, mulRows_unpackW]
  exact ⟨⟨hl, hp.1.2⟩, eq_of_eqK hp.2.1.2, eq_of_eqK hp.2.2.1.2, eq_of_eqK hp.2.2.2.1.2,
    eq_of_eqK hp.2.2.2.2.2⟩

theorem check : oddBCheckOf oddBRegs CFSG.Sporadic.Co1.Module.rowsSB = true := by
  have hc := comm_fix
  have ho := orders
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at hc
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at ho
  have hcode : CFSG.Sporadic.Co1.Module.code4 = 10075731 := rfl
  unfold oddBCheckOf
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sB, reg (i := 9) (by decide), reg (i := 14) (by decide), reg (i := 19) (by decide),
    reg (i := 24) (by decide), hcode]
  simp only [Bool.and_eq_true, valid_unpack, mulRows_unpackW, beq_unpack, fixT, powE, bne,
    Bool.not_eq_true', beq_iff_eq, true_and]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨hc, ho.1.1.1.1.1⟩, ho.1.1.1.1.2⟩, ho.1.1.1.2⟩, ho.1.1.2⟩, ho.1.2⟩, ho.2⟩,
    perfX⟩, perfY⟩

theorem basisF : (isFixedN (transposeRows 24 oddY) (Data.oddSeeds.getD 0 0) &&
    isFixedN (transposeRows 24 oddY) (Data.oddSeeds.getD 1 0) &&
    mulRows 24 (inv oddBT) oddBT == idRows 24) = true := by
  have hb := basis
  simp only [Bool.and_eq_true] at hb
  have hs0 : Data.oddSeeds.getD 0 0 = 6217977 := rfl
  have hs1 : Data.oddSeeds.getD 1 0 = 14517350 := rfl
  rw [oddY, reg (by decide), hs0, hs1, fixT, fixT, bti_eq, bt_eq, mulRows_unpackW, idRows_eq,
    beq_unpack]
  simp only [Bool.and_eq_true]
  exact ⟨⟨hb.1.1.1.1, hb.1.1.1.2⟩, hb.2⟩

theorem all_of_blocks {α : Type} (l : List α) (p : α → Bool) (n : Nat) (hl : l.length ≤ 8 * n)
    (h : ∀ k < n, ((l.drop (8 * k)).take 8).all p = true) : l.all p = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hs := List.all_eq_true.1 (h (i / 8) (by omega))
  have hj : i % 8 < ((l.drop (8 * (i / 8))).take 8).length := by
    simp only [List.length_take, List.length_drop]
    omega
  have e : ((l.drop (8 * (i / 8))).take 8)[i % 8] = l[i] := by
    simp only [List.getElem_take, List.getElem_drop, Nat.div_add_mod]
  rw [← e]
  exact hs _ (List.getElem_mem hj)

theorem rows_all : ∀ k < 32, candRow k = true := by
  intro k hk
  have hk' : k = 8 * (k / 8) + k % 8 := (Nat.div_add_mod k 8).symm
  have hr : k % 8 < 8 := Nat.mod_lt _ (by decide)
  have hq : k / 8 < 4 := by omega
  rw [hk']
  generalize k / 8 = q at hq
  generalize k % 8 = s at hr
  match q, hq with
  | 0, _ => have h := Cand0.H.all s hr; rwa [Cand0.f] at h
  | 1, _ => have h := Cand1.H.all s hr; rwa [Cand1.f] at h
  | 2, _ => have h := Cand2.H.all s hr; rwa [Cand2.f] at h
  | 3, _ => have h := Cand3.H.all s hr; rwa [Cand3.f] at h

theorem fixList_one (M : Array Nat) : fixList [M] = fixList [M, M] := by
  unfold fixList
  congr 1
  funext x
  simp

theorem cand : oddCandCheckOf oddX oddY CFSG.Sporadic.Co1.Module.rowsSB oddHsB oddBT (inv oddBT)
    (fixList [transposeRows 24 oddY]) = true := by
  have hW : fixList [transposeRows 24 oddY] = W := by
    rw [oddY, reg (by decide), transposeRows_unpackR, Nat.eq_of_beq_eq_true fixed.1, fixList_one]
    exact fixList_eq_of fixed.2.1 fixed.2.2.1
  rw [hW, oddX, oddY, reg (by decide), reg (by decide), sB, hs_eq, bti_eq, bt_eq]
  unfold oddCandCheckOf
  simp only [cand_eq len.2.1, candK_eq_candM]
  refine all_of_blocks W _ 32 (by rw [fixed.2.2.2]) fun k hk => ?_
  exact rows_all k hk

theorem facts2143 :
    (oddBCheckOf oddBRegs CFSG.Sporadic.Co1.Module.rowsSB = true) ∧
    ((isFixedN (transposeRows 24 oddY) (Data.oddSeeds.getD 0 0) &&
      isFixedN (transposeRows 24 oddY) (Data.oddSeeds.getD 1 0) &&
      mulRows 24 (inv oddBT) oddBT == idRows 24) = true) ∧
    (oddCandCheckOf oddX oddY CFSG.Sporadic.Co1.Module.rowsSB oddHsB oddBT (inv oddBT)
      (fixList [transposeRows 24 oddY]) = true) :=
  ⟨check, basisF, cand⟩

end CertificateChecks.KernelCo1OddB

end
