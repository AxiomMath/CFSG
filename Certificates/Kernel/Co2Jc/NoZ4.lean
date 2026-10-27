module

public import Certificates.Kernel.Co2Jc.NoZ4K
public import Certificates.Kernel.Co2Jc.Gen
public import CFSG.Certificates.Kernel.Co1BMulSound
public import CFSG.Certificates.Kernel.OpsKSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2Jc

open CFSG.KC.Enum CFSG.Sporadic.Co2Jc.Data CFSG.Sporadic.Co2Jc.Native
open CFSG.Sporadic.Co2Jc.Native.NoZ4 CFSG.Sporadic.SmallF2

theorem toM_mul (A B : Nat) : toM (CFSG.KC.M1F2.mulF 10 A B) = toM A * toM B := by
  unfold toM
  rw [← CFSG.KC.F2W.mulRows_unpackR, rowsMatrix_mulRows]

theorem toM_tr (A : Nat) : toM (CFSG.KC.Co1F2.trK 10 A) = (toM A).transpose := by
  unfold toM
  rw [← CFSG.KC.Co1F2.tr_sound (Nat.beq_refl _), rowsMatrix_transposeRows]

theorem toM_id : toM (CFSG.KC.M1F2.idF 10) = 1 := by
  unfold toM
  rw [CFSG.KC.OpsK.unpackR_idF, rowsMatrix_idRows]

theorem toM_apply (X : Nat) (i j : Fin 10) :
    toM X i j = if X.testBit (10 * i.val + j.val) then 1 else 0 := by
  unfold toM
  rw [rowsMatrix_apply, toVecD_apply]
  simp only [CFSG.KC.Co1F2.unpackR, Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some,
    CFSG.KC.OpsK.testBit_field, j.isLt, decide_true, Bool.true_and]

theorem toM_xor (A B : Nat) : toM (A ^^^ B) = toM A + toM B := by
  ext i j
  rw [Matrix.add_apply, toM_apply, toM_apply, toM_apply, Nat.testBit_xor]
  cases A.testBit (10 * i.val + j.val) <;> cases B.testBit (10 * i.val + j.val) <;> decide

theorem toM_zero : toM 0 = 0 := by
  ext i j
  rw [toM_apply, Nat.zero_testBit]
  rfl

theorem G2_eq {k : Nat} (hk : k < 3) : G2 k = toM (GK k) := by
  have h := gen_ok
  simp only [List.all_eq_true, List.mem_range, List.mem_finRange, decide_eq_true_eq,
    true_implies] at h
  ext j i
  exact h k hk j i

theorem chain_facts {t : Nat} (ht : t < 2) : (∀ k ∈ wOf t, k < 3) ∧
    PR t 0 = CFSG.KC.M1F2.idF 10 ∧ SF t (wOf t).length = CFSG.KC.M1F2.idF 10 ∧
    ∀ i < (wOf t).length,
      PR t (i + 1) = CFSG.KC.M1F2.mulF 10 (PR t i) (GK (wOf t)[i]!) ∧
      SF t i = CFSG.KC.M1F2.mulF 10 (GK (wOf t)[i]!) (SF t (i + 1)) := by
  have h := chain_ok
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hw, h0⟩, hn⟩, hi⟩ := h t ht
  exact ⟨hw, Nat.eq_of_beq_eq_true h0, Nat.eq_of_beq_eq_true hn, fun i hi' =>
    ⟨Nat.eq_of_beq_eq_true (hi i hi').1, Nat.eq_of_beq_eq_true (hi i hi').2⟩⟩

theorem G2_get {t i : Nat} (ht : t < 2) (hi : i < (wOf t).length) :
    toM (GK (wOf t)[i]!) = G2 (wOf t)[i] := by
  rw [getElem!_pos _ i hi, G2_eq ((chain_facts ht).1 _ (List.getElem_mem hi))]

theorem pre_eq {t : Nat} (ht : t < 2) :
    ∀ i ≤ (wOf t).length, toM (PR t i) = (((wOf t).take i).map G2).prod := by
  obtain ⟨-, h0, -, hs⟩ := chain_facts ht
  intro i
  induction i with
  | zero => intro _; rw [h0, toM_id]; simp
  | succ i ih =>
    intro hi
    rw [(hs i (by omega)).1, toM_mul, ih (by omega), G2_get ht (i := i) (by omega),
      List.take_succ_eq_append_getElem (by omega), List.map_append, List.prod_append,
      List.map_singleton, List.prod_singleton]

theorem suf_eq {t : Nat} (ht : t < 2) :
    ∀ i ≤ (wOf t).length, toM (SF t i) = (((wOf t).drop i).map G2).prod := by
  obtain ⟨-, -, hn, hs⟩ := chain_facts ht
  have : ∀ d ≤ (wOf t).length, toM (SF t ((wOf t).length - d)) =
      (((wOf t).drop ((wOf t).length - d)).map G2).prod := by
    intro d
    induction d with
    | zero => intro _; rw [Nat.sub_zero, hn, toM_id, List.drop_length]; simp
    | succ d ih =>
      intro hd
      have e : (wOf t).length - d = (wOf t).length - (d + 1) + 1 := by omega
      have hlt : (wOf t).length - (d + 1) < (wOf t).length := by omega
      have key : (((wOf t).drop ((wOf t).length - (d + 1))).map G2).prod =
          G2 (wOf t)[(wOf t).length - (d + 1)] *
            (((wOf t).drop ((wOf t).length - (d + 1) + 1)).map G2).prod := by
        rw [List.drop_eq_getElem_cons hlt, List.map_cons, List.prod_cons]
      rw [(hs _ hlt).2, toM_mul, ← e, ih (by omega), G2_get ht hlt, key, e]
  intro i hi
  have := this ((wOf t).length - i) (by omega)
  rwa [Nat.sub_sub_self hi] at this

theorem csel_eq {r : Nat} (hr : r ∈ noZ4Rels) : (Csel r).toMat = toM (CS r) := by
  have h := csel_ok
  simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq, true_implies] at h
  have e := Tab.toMat_ofMat (R := ZMod 2)
    (fun a b : Fin 10 => if (r, a.val, b.val) ∈ noZ4Sel then (1 : ZMod 2) else 0)
  rw [Csel]
  refine e.trans ?_
  ext a b
  exact h r hr a b

theorem foldl_toM {l : List Nat} {c : Nat → Prop} [DecidablePred c] {T : Nat → M2}
    {f : Nat → Nat} (hT : ∀ i ∈ l, T i = toM (f i)) (a : Nat) :
    l.foldl (fun acc i => if c i then acc + T i else acc) (toM a) =
      toM (l.foldl (fun acc i => if c i then acc ^^^ f i else acc) a) := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons]
    by_cases hx : c x
    · rw [if_pos hx, if_pos hx, hT x List.mem_cons_self, ← toM_xor]
      exact ih (fun i hi => hT i (List.mem_cons_of_mem _ hi)) _
    · rw [if_neg hx, if_neg hx]
      exact ih (fun i hi => hT i (List.mem_cons_of_mem _ hi)) _

theorem term_eq {r t : Nat} (ht : t < 2) (hr : r ∈ noZ4Rels) {i : Nat}
    (hi : i < (wOf t).length) :
    (prefList (wOf t))[i]!.toMat.transpose * (Csel r).toMat *
      (suffList (wOf t))[i + 1]!.toMat.transpose = toM (termK r t i) := by
  have hl1 : i < (prefList (wOf t)).length := by simp [prefList]; omega
  have hl2 : i + 1 < (suffList (wOf t)).length := by simp [suffList]; omega
  rw [getElem!_pos _ i hl1, getElem!_pos _ (i + 1) hl2, prefList_getElem_toMat,
    suffList_getElem_toMat, ← pre_eq ht i (by omega), ← suf_eq ht (i + 1) (by omega), csel_eq hr,
    termK, toM_mul, toM_mul, toM_tr, toM_tr]

theorem coeffT_eq {r t : Nat} (ht : t < 2) (hr : r ∈ noZ4Rels) (k : Nat) :
    (List.range (wOf t).length).foldl (fun acc i =>
      if (wOf t)[i]! = k then
        acc + (prefList (wOf t))[i]!.toMat.transpose * (Csel r).toMat *
          (suffList (wOf t))[i + 1]!.toMat.transpose
      else acc) 0 = toM (coeffT k r t) := by
  rw [← toM_zero, coeffT]
  exact foldl_toM (fun i hi => term_eq ht hr (List.mem_range.1 hi)) 0

theorem coeff2_eq (k : Nat) : (coeff2 k).toMat = toM (coeffK k) := by
  rw [coeff2_toMat]
  have e1 : rels[1]! = wOf 0 := rfl
  have e9 : rels[9]! = wOf 1 := rfl
  simp only [noZ4Rels, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e1, e9]
  rw [coeffT_eq (by norm_num) (by decide), coeffT_eq (by norm_num) (by decide), coeffK, toM_xor,
    toM_xor, toM_zero]

theorem eL_map {f : Nat → Nat → Nat} {i j : Nat} (hi : i < 10) (hj : j < 10) :
    eL ((List.range 10).map fun i => (List.range 10).map fun j => f i j) i j = f i j := by
  simp [eL, List.getD_eq_getElem?_getD, List.getElem?_range, hi, hj]

theorem toM4_mul (A B : List (List Nat)) : toM4 (mul4 A B) = toM4 A * toM4 B := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [toM4, Matrix.of_apply]
  rw [mul4, eL_map i.isLt j.isLt, ZMod.natCast_mod]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_zero]
  simp only [Fin.val_zero, Fin.val_succ]
  ring

theorem G4_eq {k : Nat} (hk : k < 3) : G4 k = toM4 (G4L k) := by
  have h := g4_ok
  simp only [List.all_eq_true, List.mem_range, List.mem_finRange, decide_eq_true_eq,
    true_implies] at h
  ext j i
  exact h k hk j i

theorem P4_eq : ∀ w : List Nat, (∀ k ∈ w, k < 3) → (w.map G4).prod = toM4 (P4 w)
  | [], _ => by
    have h := id4_ok
    simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq, true_implies] at h
    ext i j
    exact h i j
  | k :: w, hw => by
    rw [List.map_cons, List.prod_cons, P4_eq w (fun j hj => hw j (List.mem_cons_of_mem _ hj)),
      G4_eq (hw k List.mem_cons_self), ← toM4_mul]
    rfl

theorem prod4_eq {t : Nat} (ht : t < 2) : (prod4 (wOf t)).toMat = toM4 (QL t) := by
  have hq := q_ok
  simp only [Bool.and_eq_true, beq_iff_eq] at hq
  rw [prod4_toMat, P4_eq _ (chain_facts ht).1]
  rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
  · rw [hq.1]
  · rw [hq.2]

theorem hget (r a b : Nat) :
    (if r = 1 then prod4 rels[1]! else prod4 rels[9]!).get a b = qE r a b := by
  have hg : ∀ T : Tab (ZMod 4), T.get a b =
      T.toMat ⟨a % 10, Nat.mod_lt _ (by norm_num)⟩ ⟨b % 10, Nat.mod_lt _ (by norm_num)⟩ :=
    fun _ => rfl
  have e1 : rels[1]! = wOf 0 := rfl
  have e9 : rels[9]! = wOf 1 := rfl
  rw [hg, qE]
  by_cases hr : r = 1
  · rw [if_pos hr, if_pos hr, e1, prod4_eq (by norm_num)]
    simp only [toM4, Matrix.of_apply, QL]
    rw [eL_map (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))]
  · rw [if_neg hr, if_neg hr, e9, prod4_eq (by norm_num)]
    simp only [toM4, Matrix.of_apply, QL]
    rw [eL_map (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))]

theorem eok_eq : EOK = true := by
  unfold EOK
  simp only [Ebit, hget]
  exact eok_ok

theorem noZ4_ok : noZ4OK = true := by
  have hrel : noZ4Rels.all noZ4RelOK = true := by
    unfold noZ4RelOK
    simp only [wordAct_eq]
    decide +kernel
  have htab : noZ4TabOK = true := by decide +kernel
  have hco : ((List.range 3).all fun k => matZero (coeff2 k).toMat) = true := by
    have h := coeff_ok
    simp only [List.all_eq_true, List.mem_range] at h ⊢
    intro k hk
    rw [coeff2_eq, Nat.eq_of_beq_eq_true (h k hk), toM_zero]
    decide
  unfold noZ4OK
  rw [hrel, htab, hco, eok_eq]
  rfl

end CertificateChecks.KernelCo2Jc
