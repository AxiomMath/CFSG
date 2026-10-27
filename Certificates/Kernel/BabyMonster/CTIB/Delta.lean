module

public import Certificates.Kernel.BabyMonster.CTIB.Signs
public import Certificates.Kernel.BabyMonster.RowChain
public import Certificates.Data.Kernel.BabyMonster.CTIB.DeltaMasks
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelBM.CTIB

open CFSG.KC.BM CFSG.Monster.B.Dyadic CertificateChecks.KernelBM.Pair CFSG.Monster.B.CTIB.Native
open scoped Matrix

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

set_option maxRecDepth 100000
set_option exponentiation.threshold 8192

@[expose] def maskSum (p : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => maskSum p n + if p n then 2 ^ n else 0

theorem maskSum_lt (p : ℕ → Bool) : ∀ n, maskSum p n < 2 ^ n
  | 0 => by simp [maskSum]
  | n + 1 => by
    have := maskSum_lt p n
    rw [maskSum, pow_succ]
    split_ifs <;> omega

theorem testBit_maskSum (p : ℕ → Bool) :
    ∀ n t, (maskSum p n).testBit t = (decide (t < n) && p t)
  | 0, t => by simp [maskSum]
  | n + 1, t => by
    have hlt := maskSum_lt p n
    have e : maskSum p (n + 1) = 2 ^ n * (if p n then 1 else 0) + maskSum p n := by
      rw [maskSum]
      split_ifs <;> ring
    rw [e, Nat.testBit_two_pow_mul_add _ hlt, testBit_maskSum p n t]
    by_cases h : t < n
    · have h' : t < n + 1 := by omega
      simp [h, h']
    · by_cases h' : t = n
      · subst h'
        rw [ite_eq_right h, Nat.sub_self, decide_eq_true (Nat.lt_succ_self t), Bool.true_and]
        cases p t <;> decide
      · have h2 : ¬ t < n + 1 := by omega
        rw [ite_eq_right h, decide_eq_false h2, Bool.false_and]
        split_ifs
        · exact Nat.testBit_eq_false_of_lt (Nat.one_lt_two_pow (by omega))
        · exact Nat.zero_testBit _

@[expose] def Wd (t : ℕ) : List ℤ :=
  if t < 45 then deltaWord t else liftWordZK 10 ++ liftWordZK 10

@[expose] def cls (c : ℕ) (x : ℤ) : Bool :=
  if c = 0 then (x == 1 || x == -1) else if c = 1 then x == 2 else x == -2

@[expose] def entOK (e : ℕ × ℕ × ℕ) (x : ℤ) (t : ℕ) : Bool :=
  e.1.testBit t == cls 0 x && e.2.1.testBit t == cls 1 x && e.2.2.testBit t == cls 2 x

@[expose] def colOK : List ℤ → List (ℕ × ℕ × ℕ) → ℕ → Bool
  | w, [], _ => w.isEmpty
  | w, e :: r, t => entOK e (w.headD 0) t && colOK w.tail r t

@[expose] def entLt (e : ℕ × ℕ × ℕ) : Bool :=
  e.1 < 2 ^ 64 && e.2.1 < 2 ^ 64 && e.2.2 < 2 ^ 64 && Nat.land e.1 e.2.1 == 0 &&
    Nat.land e.1 e.2.2 == 0 && Nat.land e.2.1 e.2.2 == 0

@[expose] def tabOK : Bool :=
  deltaMasksL.all entLt && (List.range 46).all fun t => colOK (Wd t) deltaMasksL t &&
    (Wd t).all fun x => x == 1 || x == -1 || x == 2 || x == -2

theorem tabOK_true : tabOK = true := by quickRfl

theorem colOK_spec {t : ℕ} :
    ∀ (tab : List (ℕ × ℕ × ℕ)) (w : List ℤ), colOK w tab t = true →
      ∀ s, entOK (tab.getD s (0, 0, 0)) (w.getD s 0) t = true
  | [], w, h, s => by
    rw [colOK, List.isEmpty_iff] at h
    subst h
    simp [entOK, cls]
  | e :: r, w, h, s => by
    rw [colOK, Bool.and_eq_true] at h
    cases s with
    | zero => cases w <;> exact h.1
    | succ s =>
      have := colOK_spec r w.tail h.2 s
      cases w <;> exact this

theorem colOK_length {t : ℕ} :
    ∀ (tab : List (ℕ × ℕ × ℕ)) (w : List ℤ), colOK w tab t = true → w.length ≤ tab.length
  | [], w, h => by
    rw [colOK, List.isEmpty_iff] at h
    simp [h]
  | e :: r, w, h => by
    rw [colOK, Bool.and_eq_true] at h
    have := colOK_length r w.tail h.2
    rw [List.length_tail] at this
    rw [List.length_cons]
    omega

theorem entLt_get (s : ℕ) : entLt (deltaMasksL.getD s (0, 0, 0)) = true := by
  have h := tabOK_true
  rw [tabOK, Bool.and_eq_true, List.all_eq_true] at h
  by_cases hs : s < deltaMasksL.length
  · rw [List.getD_eq_getElem _ _ hs]
    exact h.1 _ (List.getElem_mem hs)
  · rw [List.getD_eq_default _ _ (by omega)]
    rfl

theorem word_ok {t : ℕ} (ht : t < 46) : colOK (Wd t) deltaMasksL t = true ∧
    ∀ x ∈ Wd t, x = 1 ∨ x = -1 ∨ x = 2 ∨ x = -2 := by
  have h := tabOK_true
  rw [tabOK, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  have h2 := h.2 t (List.mem_range.2 ht)
  rw [Bool.and_eq_true, List.all_eq_true] at h2
  refine ⟨h2.1, fun x hx => ?_⟩
  have := h2.2 x hx
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  omega

theorem masks_length : deltaMasksL.length = 1960 := by
  have h : (deltaMasksL.length == 1960) = true := by quickRfl
  exact beq_iff_eq.1 h

theorem word_length {t : ℕ} (ht : t < 46) : (Wd t).length ≤ 1960 := by
  have h := colOK_length _ _ (word_ok ht).1
  rwa [masks_length] at h

@[expose] noncomputable def matW (i : ℕ) : List Nat :=
  if i = 0 then Max2.G1 else if i = 1 then Max2.G2 else Max2.Gi2

@[expose] def movesOf (e : ℕ × ℕ × ℕ) : List (ℕ × ℕ) :=
  [(0, e.1), (1, e.2.1), (2, e.2.2)].filter fun p => p.2 != 0

@[expose] def okW (e : ℕ × ℕ × ℕ) (U : ℕ) (l : List (ℕ × ℕ)) : Bool :=
  l == movesOf e && U == (l.map (·.2)).foldl Nat.lor 0

@[expose] def InvW (X : Nat) (s : ℕ) : Prop :=
  ∀ t < 46, vrow (rowOf X t) = e0 ᵥ* prodK (((Wd t).take s).map letterK)

@[expose] def InvT (X : Nat) (s : ℕ) (r : List (ℕ × ℕ × ℕ)) : Prop :=
  InvW X s ∧ ∀ s', deltaMasksL.getD (s + s') (0, 0, 0) = r.getD s' (0, 0, 0)

theorem step_letter (v : Fin 4370 → ZMod 2) {x : ℤ} (hx : x = 1 ∨ x = -1 ∨ x = 2 ∨ x = -2) :
    (if cls 0 x then v ᵥ* stripMat Max2.G1 else if cls 1 x then v ᵥ* stripMat Max2.G2
      else if cls 2 x then v ᵥ* stripMat Max2.Gi2 else v) = v ᵥ* letterK x := by
  rcases hx with rfl | rfl | rfl | rfl
  · have h0 : cls 0 1 = true := by decide
    have hl : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1 := Or.inl rfl
    rw [ite_eq_left h0, letterK, ite_eq_left hl, G1K]
  · have h0 : cls 0 (-1) = true := by decide
    have hl : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1 := Or.inr rfl
    rw [ite_eq_left h0, letterK, ite_eq_left hl, G1K]
  · have h0 : ¬ cls 0 2 = true := by decide
    have h1 : cls 1 2 = true := by decide
    have hl : ¬ ((2 : ℤ) = 1 ∨ (2 : ℤ) = -1) := by decide
    rw [ite_eq_right h0, ite_eq_left h1, letterK, ite_eq_right hl, ite_eq_left rfl, G2K]
  · have h0 : ¬ cls 0 (-2) = true := by decide
    have h1 : ¬ cls 1 (-2) = true := by decide
    have h2 : cls 2 (-2) = true := by decide
    have hl : ¬ ((-2 : ℤ) = 1 ∨ (-2 : ℤ) = -1) := by decide
    have hl2 : ¬ (-2 : ℤ) = 2 := by decide
    rw [ite_eq_right h0, ite_eq_right h1, ite_eq_left h2, letterK, ite_eq_right hl,
      ite_eq_right hl2, ite_eq_left rfl, Gi2K]

theorem step_zero (v : Fin 4370 → ZMod 2) :
    (if cls 0 0 then v ᵥ* stripMat Max2.G1 else if cls 1 0 then v ᵥ* stripMat Max2.G2
      else if cls 2 0 then v ᵥ* stripMat Max2.Gi2 else v) = v := by
  have h0 : ¬ cls 0 0 = true := by decide
  have h1 : ¬ cls 1 0 = true := by decide
  have h2 : ¬ cls 2 0 = true := by decide
  rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right h2]

theorem prodK_take_succ {w : List ℤ} {s : ℕ} (hs : s < w.length) :
    prodK ((w.take (s + 1)).map letterK) =
      prodK ((w.take s).map letterK) * letterK (w.getD s 0) := by
  rw [List.take_add_one,List.map_append, prodK_append, List.getElem?_eq_getElem hs,
    Option.toList_some, List.map_cons, List.map_nil, prodK, prodK, Matrix.mul_one,
    List.getD_eq_getElem _ _ hs]

theorem fold_movesOf (e : ℕ × ℕ × ℕ) (t : ℕ) (v : Fin 4370 → ZMod 2) :
    ((movesOf e).map fun p => (matW p.1, p.2)).foldr
      (fun mv acc => if mv.2.testBit t then v ᵥ* stripMat mv.1 else acc) v =
    if e.1.testBit t then v ᵥ* stripMat Max2.G1 else if e.2.1.testBit t then v ᵥ* stripMat Max2.G2
    else if e.2.2.testBit t then v ᵥ* stripMat Max2.Gi2 else v := by
  obtain ⟨a, b, c⟩ := e
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases hc : c = 0 <;>
    simp [movesOf, ha, hb, hc, matW]

theorem mem_movesOf {e : ℕ × ℕ × ℕ} {p : ℕ × ℕ} (h : p ∈ movesOf e) :
    p = (0, e.1) ∨ p = (1, e.2.1) ∨ p = (2, e.2.2) := by
  rw [movesOf, List.mem_filter, List.mem_cons, List.mem_cons, List.mem_singleton] at h
  exact h.1

theorem wbody (s P R U : ℕ) (l : List (ℕ × ℕ))
    (h : Nat.beq (stepTerm P U (l.map fun p => (matW p.1, p.2))) R = true)
    (hl : l = movesOf (deltaMasksL.getD s (0, 0, 0))) (hU : U = (l.map (·.2)).foldl Nat.lor 0)
    (hP : InvW P s) : InvW R (s + 1) := by
  subst hl
  intro t ht
  have hlt := entLt_get s
  simp only [entLt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hlt
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, d12⟩, d13⟩, d23⟩ := hlt
  have hwf : ∀ mv ∈ (movesOf (deltaMasksL.getD s (0, 0, 0))).map (fun p => (matW p.1, p.2)),
      wfMat mv.1 = true := by
    intro mv hmv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hmv
    rcases mem_movesOf hp with rfl | rfl | rfl
    · exact Max2.wf_G1
    · exact Max2.wf_G2
    · exact Max2.wf_Gi2
  have hlt' : ∀ mv ∈ (movesOf (deltaMasksL.getD s (0, 0, 0))).map (fun p => (matW p.1, p.2)),
      mv.2 < 2 ^ 64 := by
    intro mv hmv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hmv
    rcases mem_movesOf hp with rfl | rfl | rfl <;> assumption
  have hd : ((movesOf (deltaMasksL.getD s (0, 0, 0))).map fun p => (matW p.1, p.2)).Pairwise
      fun a b => Nat.land a.2 b.2 = 0 := by
    rw [List.pairwise_map]
    refine List.Pairwise.filter _ ?_
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.pairwise_singleton _ _))
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact d12
      · rw [List.mem_singleton] at hq
        subst hq
        exact d13
    · intro q hq
      rw [List.mem_singleton] at hq
      subst hq
      exact d23
  rw [← Nat.eq_of_beq_eq_true h, stepTerm_rows _ hwf hlt' hd P U (by rw [hU, List.map_map]; rfl)
    (by omega), fold_movesOf, hP t ht]
  have he := colOK_spec _ _ (word_ok ht).1 s
  simp only [entOK, Bool.and_eq_true, beq_iff_eq] at he
  obtain ⟨⟨e1, e2⟩, e3⟩ := he
  rw [e1, e2, e3]
  by_cases hs : s < (Wd t).length
  · have hm : (Wd t).getD s 0 ∈ Wd t := by
      rw [List.getD_eq_getElem _ _ hs]
      exact List.getElem_mem hs
    have hx := (word_ok ht).2 _ hm
    rw [prodK_take_succ hs, ← Matrix.vecMul_vecMul, step_letter _ hx]
  · have e0' : (Wd t).getD s 0 = 0 := List.getD_eq_default _ _ (by omega)
    have e1' : (Wd t).take (s + 1) = (Wd t).take s := by
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
    rw [e0', e1', step_zero]

theorem wcore (s P R U : ℕ) (l : List (ℕ × ℕ)) (e : ℕ × ℕ × ℕ) (r : List (ℕ × ℕ × ℕ))
    (h : Nat.beq (stepTerm P U (l.map fun p => (matW p.1, p.2))) R = true)
    (hok : okW e U l = true) (hP : InvT P s (e :: r)) : InvT R (s + 1) r := by
  have he : deltaMasksL.getD s (0, 0, 0) = e := by
    have := hP.2 0
    rwa [Nat.add_zero, List.getD_cons_zero] at this
  rw [okW, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hok
  refine ⟨wbody s P R U l h (by rw [he]; exact hok.1) hok.2 hP.1, fun s' => ?_⟩
  have := hP.2 (s' + 1)
  rwa [List.getD_cons_succ, ← Nat.add_assoc, ← Nat.add_right_comm] at this

theorem wstep1 (s P R U : ℕ) (B₁ : List Nat) (m₁ i₁ : ℕ) (e : ℕ × ℕ × ℕ)
    (r : List (ℕ × ℕ × ℕ))
    (h : Nat.beq (Nat.lor (Nat.sub P (Nat.land P (Nat.mul SM U)))
      (mulS B₁ (Nat.land P (Nat.mul SM m₁)))) R = true)
    (hB₁ : B₁ = matW i₁) (hok : okW e U [(i₁, m₁)] = true) (hP : InvT P s (e :: r)) :
    InvT R (s + 1) r := by
  subst hB₁
  exact wcore s P R U [(i₁, m₁)] e r h hok hP

theorem wstep2 (s P R U : ℕ) (B₁ : List Nat) (m₁ i₁ : ℕ) (B₂ : List Nat) (m₂ i₂ : ℕ)
    (e : ℕ × ℕ × ℕ) (r : List (ℕ × ℕ × ℕ))
    (h : Nat.beq (Nat.lor (Nat.lor (Nat.sub P (Nat.land P (Nat.mul SM U)))
      (mulS B₁ (Nat.land P (Nat.mul SM m₁)))) (mulS B₂ (Nat.land P (Nat.mul SM m₂)))) R = true)
    (hB₁ : B₁ = matW i₁) (hB₂ : B₂ = matW i₂) (hok : okW e U [(i₁, m₁), (i₂, m₂)] = true)
    (hP : InvT P s (e :: r)) : InvT R (s + 1) r := by
  subst hB₁ hB₂
  exact wcore s P R U [(i₁, m₁), (i₂, m₂)] e r h hok hP

theorem wstep3 (s P R U : ℕ) (B₁ : List Nat) (m₁ i₁ : ℕ) (B₂ : List Nat) (m₂ i₂ : ℕ)
    (B₃ : List Nat) (m₃ i₃ : ℕ) (e : ℕ × ℕ × ℕ) (r : List (ℕ × ℕ × ℕ))
    (h : Nat.beq (Nat.lor (Nat.lor (Nat.lor (Nat.sub P (Nat.land P (Nat.mul SM U)))
      (mulS B₁ (Nat.land P (Nat.mul SM m₁)))) (mulS B₂ (Nat.land P (Nat.mul SM m₂))))
      (mulS B₃ (Nat.land P (Nat.mul SM m₃)))) R = true)
    (hB₁ : B₁ = matW i₁) (hB₂ : B₂ = matW i₂) (hB₃ : B₃ = matW i₃)
    (hok : okW e U [(i₁, m₁), (i₂, m₂), (i₃, m₃)] = true) (hP : InvT P s (e :: r)) :
    InvT R (s + 1) r := by
  subst hB₁ hB₂ hB₃
  exact wcore s P R U [(i₁, m₁), (i₂, m₂), (i₃, m₃)] e r h hok hP

theorem rows_lit {m : Nat} (hm : m < 2 ^ 64) {t : Nat} (ht : t < 64) :
    vrow (rowOf m t) = if m.testBit t then e0 else 0 := by
  have h := start_rows (m₀ := m) (m₁ := 0) (v := 0) (by simp) hm (by norm_num) (by norm_num) ht
  have e0' : Nat.mul (spreadRow 0) 0 = 0 := Nat.mul_zero _
  have e : Nat.lor m (Nat.mul (spreadRow 0) 0) = m := by
    rw [e0']
    exact Nat.or_zero m
  rw [e, Nat.zero_testBit, ite_eq_right Bool.false_ne_true] at h
  exact h

theorem wstart : InvT 70368744177663 0 deltaMasksL := by
  refine ⟨fun t ht => ?_, fun s' => by rw [Nat.zero_add]⟩
  have h : ∀ t < 46, (70368744177663 : ℕ).testBit t = true := by decide +kernel
  rw [rows_lit (by norm_num) (by omega), ite_eq_left (h t ht), List.take_zero, List.map_nil, prodK,
    Matrix.vecMul_one]

theorem wchain : InvW CTIBRows.S2003 1960 := by
  have h : InvT CTIBRows.S2003 1960 [] := by
    bm_chain [wstep1, wstep2, wstep3] CFSG.KC.BM.CTIBRows.w 1960 wstart
      [CFSG.KC.BM.Max2.G1, CFSG.KC.BM.Max2.G2, CFSG.KC.BM.Max2.Gi2] with deltaMasksL
  exact h.1

@[expose] def dv (t : ℕ) : ℕ := if t < 45 then deltaVals.getD t 0 else 2 ^ 22

@[expose] def maskD (j : ℕ) : ℕ := maskSum (fun t => (dv t).testBit j) 46

@[expose] def okD (j U : ℕ) (l : List (ℕ × ℕ)) : Bool :=
  decide (j < 22) && l == [(j, maskD j)] && U == maskD j

@[expose] def InvD (X : Nat) (j : ℕ) : Prop :=
  ∀ t < 46, vrow (rowOf X t) = rowAcc (if (dv t).testBit 22 then e0 ᵥ* XK else e0) (dv t) j

theorem dcore (j P R U : ℕ) (l : List (ℕ × ℕ))
    (h : Nat.beq (stepTerm P U (l.map fun p => (Elist.getD p.1 [], p.2))) R = true)
    (hok : okD j U l = true) (hP : InvD P j) : InvD R (j + 1) := by
  rw [okD, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, beq_iff_eq] at hok
  obtain ⟨⟨hj, rfl⟩, rfl⟩ := hok
  intro t ht
  have hwf : ∀ mv ∈ [(j, maskD j)].map (fun p => (Elist.getD p.1 [], p.2)),
      wfMat mv.1 = true := by
    intro mv hmv
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmv
    subst hmv
    exact wfE j hj
  have hlt : ∀ mv ∈ [(j, maskD j)].map (fun p => (Elist.getD p.1 [], p.2)), mv.2 < 2 ^ 64 := by
    intro mv hmv
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmv
    subst hmv
    exact lt_trans (maskSum_lt _ 46) (by norm_num)
  have hd : ([(j, maskD j)].map fun p => (Elist.getD p.1 [], p.2)).Pairwise
      fun a b => Nat.land a.2 b.2 = 0 := by
    simp
  have hU : maskD j = (([(j, maskD j)].map fun p => (Elist.getD p.1 [], p.2)).map (·.2)).foldl
      Nat.lor 0 := by
    rw [List.map_cons, List.map_nil, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    exact (Nat.zero_or _).symm
  rw [← Nat.eq_of_beq_eq_true h, stepTerm_rows _ hwf hlt hd P _ hU (by omega)]
  have hb : (maskD j).testBit t = (dv t).testBit j := by
    rw [maskD, testBit_maskSum, decide_eq_true ht, Bool.true_and]
  simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, hb]
  rw [hP t ht, rowAcc.eq_2]
  by_cases hb' : (dv t).testBit j
  · rw [ite_eq_left hb', ite_eq_left hb']
    rfl
  · rw [ite_eq_right hb', ite_eq_right hb', Matrix.vecMul_one]

theorem dstep1 (j P R U : ℕ) (B₁ : List Nat) (m₁ i₁ : ℕ)
    (h : Nat.beq (Nat.lor (Nat.sub P (Nat.land P (Nat.mul SM U)))
      (mulS B₁ (Nat.land P (Nat.mul SM m₁)))) R = true)
    (hB₁ : B₁ = Elist.getD i₁ []) (hok : okD j U [(i₁, m₁)] = true) (hP : InvD P j) :
    InvD R (j + 1) := by
  subst hB₁
  exact dcore j P R U [(i₁, m₁)] h hok hP

theorem dstart : InvD (Nat.lor 22262392524792 (Nat.mul (spreadRow Max2.vx) 48106351652871)) 0 := by
  intro t ht
  have hb1 : ∀ t < 46, (48106351652871 : ℕ).testBit t = (dv t).testBit 22 := by decide +kernel
  have hb0 : ∀ t < 46, (48106351652871 : ℕ).testBit t = false →
      (22262392524792 : ℕ).testBit t = true := by decide +kernel
  rw [start_rows (by decide) (by norm_num) (by norm_num) vecN_vx.1 (by omega), vecN_vx.2,
    hb1 t ht, rowAcc]
  by_cases h : (dv t).testBit 22
  · rw [ite_eq_left h, ite_eq_left h]
  · have h' : (48106351652871 : ℕ).testBit t = false := by
      rw [hb1 t ht]
      exact Bool.eq_false_of_ne_true h
    rw [ite_eq_right h, ite_eq_right h, ite_eq_left (hb0 t ht h')]

theorem dchain : InvD CTIBRows.S2025 22 := by
  bm_chain [dstep1] CFSG.KC.BM.CTIBRows.d 22 dstart
    [CFSG.KC.BM.NativePair.Q0, CFSG.KC.BM.Max2.E1, CFSG.KC.BM.Max2.E2, CFSG.KC.BM.Max2.E3,
      CFSG.KC.BM.Max2.E4, CFSG.KC.BM.Max2.E5, CFSG.KC.BM.Max2.E6, CFSG.KC.BM.Max2.E7,
      CFSG.KC.BM.Max2.E8, CFSG.KC.BM.Max2.E9, CFSG.KC.BM.Max2.E10, CFSG.KC.BM.Max2.E11,
      CFSG.KC.BM.Max2.E12, CFSG.KC.BM.Max2.E13, CFSG.KC.BM.Max2.E14, CFSG.KC.BM.Max2.E15,
      CFSG.KC.BM.Max2.E16, CFSG.KC.BM.Max2.E17, CFSG.KC.BM.Max2.E18, CFSG.KC.BM.Max2.E19,
      CFSG.KC.BM.Max2.E20, CFSG.KC.BM.Max2.E21]

theorem e0_qK_dv (m : ℕ) :
    e0 ᵥ* qK m = rowAcc (if m.testBit 22 then e0 ᵥ* XK else e0) m 22 := by
  rw [qK, ← Matrix.vecMul_vecMul, vecMul_prodK_range]
  by_cases h : m.testBit 22
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, Matrix.vecMul_one]

theorem rows_delta : ∀ t < 46, e0 ᵥ* wordK (Wd t) = e0 ᵥ* qK (dv t) := by
  intro t ht
  have e : CTIBRows.S2003 = CTIBRows.S2025 := Nat.eq_of_beq_eq_true CTIBRows.cm
  have h1 := wchain t ht
  rw [List.take_of_length_le (word_length ht)] at h1
  rw [wordK, ← h1, congrArg (fun X => vrow (rowOf X t)) e, dchain t ht, e0_qK_dv]

theorem factDelta : FactDelta := by
  intro t ht
  have h := rows_delta t (by omega)
  rwa [Wd, ite_eq_left ht, dv, ite_eq_left ht] at h

end CertificateChecks.KernelBM.CTIB

end
