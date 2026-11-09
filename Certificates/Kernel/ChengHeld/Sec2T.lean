module

public import Certificates.Kernel.ChengHeld.Sec2
import CFSG.Certificates.Kernel.Common.Harness
meta import Certificates.Data.ChengHeldSec2Facts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelChengHeld.S2

open CFSG.KC.ChengHeldS2 CFSG.OddStandard.ChengHeldData CFSG.KC.Enum

theorem k0_tw : (twK 256 m0 i0 (aR (AU0 0)) (bR m0 (zGs g0)) &&
    twK 256 m0 i0 (aR (AU0 1)) (bR m0 (zGs g0)) &&
    twK 256 m0 i0 (aR (AU0 2)) (bR m0 (zGs g0))) = true := by decide +kernel

theorem k1_tw : (twK 256 m1 i1 (aR (AU1 0)) (bR m1 (zGs g1)) &&
    twK 256 m1 i1 (aR (AU1 1)) (bR m1 (zGs g1)) &&
    twK 256 m1 i1 (aR (AU1 2)) (bR m1 (zGs g1))) = true := by decide +kernel

theorem k0_sq : sqVK 256 m0 (bR m0 (vGs m0 g0)) = true := by decide +kernel
theorem k1_sq : sqVK 256 m1 (bR m1 (vGs m1 g1)) = true := by decide +kernel

@[expose] def sfStep (p : ℕ → Bool) (acc : List ℕ) (x : ℕ) : List ℕ :=
  match acc with
  | [] => if p x then [x] else []
  | b :: bs => if p x then x :: b :: bs else b :: bs

@[expose] def sfilter (p : ℕ → Bool) (l : List ℕ) : List ℕ := (l.foldl (sfStep p) []).reverse

theorem sfStep_eq (p : ℕ → Bool) (acc : List ℕ) (x : ℕ) :
    sfStep p acc x = if p x then x :: acc else acc := by
  cases acc <;> rfl

theorem foldl_sfStep (p : ℕ → Bool) (l acc : List ℕ) :
    (l.foldl (sfStep p) acc).reverse = acc.reverse ++ l.filter p := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, sfStep_eq]
    by_cases h : p x <;> simp [h]

theorem sfilter_eq (p : ℕ → Bool) (l : List ℕ) : l.filter p = sfilter p l := by
  rw [sfilter, foldl_sfStep, List.reverse_nil, List.nil_append]

@[expose] def eaStepS (m : ℕ → ℕ → ℕ) (E : List ℕ) (st : List ℕ × List (List ℕ)) (a : ℕ) :
    List ℕ × List (List ℕ) :=
  match st with
  | (s1, s2) =>
    if !((maskL E).testBit a) && E.all (fun e => m a e == m e a) then
      if !(s1.contains (maskL (E ++ E.map fun e => m a e))) then
        (maskL (E ++ E.map fun e => m a e) :: s1, (E ++ E.map fun e => m a e) :: s2)
      else (s1, s2)
    else (s1, s2)

@[expose] def eaNextS (m : ℕ → ℕ → ℕ) (invs : List ℕ) (L : List (List ℕ)) : List (List ℕ) :=
  (L.foldl (fun st E => invs.foldl (eaStepS m E) st) ([], [])).2.reverse

theorem eaStepS_rel (m : ℕ → ℕ → ℕ) (E : List ℕ) {s t : List ℕ × List (List ℕ)}
    (h : s.1 = t.1 ∧ s.2 = t.2.reverse) (a : ℕ) :
    (eaStepK m E s a).1 = (eaStepS m E t a).1 ∧
      (eaStepK m E s a).2 = (eaStepS m E t a).2.reverse := by
  obtain ⟨s1, s2⟩ := s
  obtain ⟨t1, t2⟩ := t
  obtain ⟨h1, h2⟩ := h
  dsimp only at h1 h2
  subst h1 h2
  simp only [eaStepK, eaStepS]
  split_ifs <;> simp

theorem eaFold_rel (m : ℕ → ℕ → ℕ) (invs : List ℕ) (L : List (List ℕ))
    {s t : List ℕ × List (List ℕ)} (h : s.1 = t.1 ∧ s.2 = t.2.reverse) :
    (L.foldl (fun st E => invs.foldl (eaStepK m E) st) s).2 =
      (L.foldl (fun st E => invs.foldl (eaStepS m E) st) t).2.reverse := by
  induction L generalizing s t with
  | nil => exact h.2
  | cons E L ih =>
    refine ih ?_
    clear ih
    induction invs generalizing s t with
    | nil => exact h
    | cons a as ih => exact ih (eaStepS_rel m E h a)

theorem eaNextK_eq_eaNextS (m : ℕ → ℕ → ℕ) (invs : List ℕ) (L : List (List ℕ)) :
    eaNextK m invs L = eaNextS m invs L :=
  eaFold_rel m invs L ⟨rfl, rfl⟩

@[expose] def rowK (m : ℕ → ℕ → ℕ) (e : ℕ) : ℕ :=
  (List.range 256).foldl (fun acc x => if m x e == m e x then acc ||| (1 <<< x) else acc) 0

@[expose] def ctB (m : ℕ → ℕ → ℕ) (R : ℕ) (C : ℕ → ℕ) (E : List ℕ) : ℕ :=
  E.foldl (fun acc e =>
    if e < 256 then (if R.testBit e then acc &&& C e else acc &&& rowK m e) else acc) (2 ^ 256 - 1)

@[expose] def ctOK (m : ℕ → ℕ → ℕ) (R : ℕ) (C : ℕ → ℕ) : Bool :=
  (List.range 256).all fun b => !R.testBit b ||
    (List.range 256).all fun x => (C b).testBit x == (m x b == m b x)

theorem ctOK_row {m : ℕ → ℕ → ℕ} {R : ℕ} {C : ℕ → ℕ} (hC : ctOK m R C = true) {e a : ℕ}
    (he : e < 256) (hR : R.testBit e = true) (ha : a < 256) :
    (C e).testBit a = (m a e == m e a) := by
  simp only [ctOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq] at hC
  rcases hC e he with h | h
  · simp [hR] at h
  · exact h a ha

@[expose] def candB (m : ℕ → ℕ → ℕ) (R : ℕ) (C : ℕ → ℕ) (E : List ℕ) : ℕ :=
  ctB m R C E &&& ((2 ^ 256 - 1) ^^^ maskL E)

@[expose] def eaStepC (m : ℕ → ℕ → ℕ) (cb : ℕ) (E : List ℕ) (st : List ℕ × List (List ℕ))
    (a : ℕ) : List ℕ × List (List ℕ) :=
  match st with
  | (s1, s2) =>
    if cb.testBit a then
      if !(s1.contains (maskL (E ++ E.map fun e => m a e))) then
        (maskL (E ++ E.map fun e => m a e) :: s1, (E ++ E.map fun e => m a e) :: s2)
      else (s1, s2)
    else (s1, s2)

@[expose] def eaNextC (m : ℕ → ℕ → ℕ) (R : ℕ) (C : ℕ → ℕ) (invs : List ℕ) (L : List (List ℕ)) :
    List (List ℕ) :=
  (L.foldl (fun st E => if E.all (fun e => decide (e < 256)) then
    invs.foldl (eaStepC m (candB m R C E) E) st else invs.foldl (eaStepS m E) st) ([], [])).2.reverse

theorem invsK_lt (m : ℕ → ℕ → ℕ) : ∀ a ∈ invsK 256 m, a < 256 :=
  fun _ ha => List.mem_range.1 (List.mem_filter.1 ha).1

theorem testBit_foldl_rowK (m : ℕ → ℕ → ℕ) (e : ℕ) (l : List ℕ) (acc a : ℕ) :
    (l.foldl (fun acc x => if m x e == m e x then acc ||| (1 <<< x) else acc) acc).testBit a =
      (acc.testBit a || (l.contains a && (m a e == m e a))) := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    by_cases hx : a = x
    · subst hx
      by_cases h : m a e = m e a
      · simp [h, Nat.one_shiftLeft]
      · simp [beq_eq_false_iff_ne.2 h]
    · by_cases h : m x e = m e x <;> simp [h, hx, Nat.one_shiftLeft, Ne.symm hx]

theorem testBit_rowK (m : ℕ → ℕ → ℕ) (e a : ℕ) :
    (rowK m e).testBit a = (decide (a < 256) && (m a e == m e a)) := by
  rw [rowK, testBit_foldl_rowK]
  simp

theorem testBit_foldl_ctB {m : ℕ → ℕ → ℕ} {R : ℕ} {C : ℕ → ℕ} (hC : ctOK m R C = true)
    (E : List ℕ) (acc a : ℕ) (ha : a < 256) :
    (E.foldl (fun acc e =>
      if e < 256 then (if R.testBit e then acc &&& C e else acc &&& rowK m e) else acc) acc).testBit a =
      (acc.testBit a && E.all fun e => !decide (e < 256) || (m a e == m e a)) := by
  induction E generalizing acc with
  | nil => simp
  | cons e E ih =>
    rw [List.foldl_cons, ih]
    by_cases he : e < 256
    · by_cases h0 : R.testBit e = true
      · simp [he, h0, ctOK_row hC he h0 ha, Bool.and_assoc]
      · simp [he, h0, testBit_rowK, ha, Bool.and_assoc]
    · simp [he]

theorem centK_eq_ctB {m : ℕ → ℕ → ℕ} {R : ℕ} {C : ℕ → ℕ} (hC : ctOK m R C = true) (E : List ℕ)
    {a : ℕ} (ha : a < 256) :
    centK 256 m (fun i => decide (i < 256) && E.contains i) a = (ctB m R C E).testBit a := by
  rw [ctB, testBit_foldl_ctB hC E _ a ha, Nat.testBit_two_pow_sub_one, decide_eq_true ha,
    Bool.true_and, centK, elemsK, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro h e he
    by_cases h2 : e < 256
    · have hm := h e (List.mem_filter.2 ⟨List.mem_range.2 h2, by simp [h2, he]⟩)
      simp only [beq_iff_eq] at hm
      simp [hm]
    · simp [h2]
  · intro h b hb
    obtain ⟨hb1, hb2⟩ := List.mem_filter.1 hb
    have hb1 := List.mem_range.1 hb1
    have hbE : b ∈ E := by simpa [hb1] using hb2
    simpa [hb1] using h b hbE

theorem elemsK_cent_eq {m : ℕ → ℕ → ℕ} {R : ℕ} {C : ℕ → ℕ} (hC : ctOK m R C = true)
    (E : List ℕ) :
    elemsK 256 (centK 256 m fun i => decide (i < 256) && E.contains i) =
      elemsK 256 (fun a => (ctB m R C E).testBit a) := by
  unfold elemsK
  exact List.filter_congr fun a ha => centK_eq_ctB hC E (List.mem_range.1 ha)

theorem testBit_candB {m : ℕ → ℕ → ℕ} {R : ℕ} {C : ℕ → ℕ} (hC : ctOK m R C = true)
    {E : List ℕ} (hE : ∀ e ∈ E, e < 256) {a : ℕ} (ha : a < 256) :
    (candB m R C E).testBit a = (!((maskL E).testBit a) && E.all fun e => m a e == m e a) := by
  rw [candB, Nat.testBit_land, ctB, testBit_foldl_ctB hC E _ a ha, Nat.testBit_xor,
    Nat.testBit_two_pow_sub_one, decide_eq_true ha, Bool.true_and, Bool.true_xor]
  have hA : (E.all fun e => !decide (e < 256) || (m a e == m e a)) =
      E.all fun e => m a e == m e a := by
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    constructor
    · intro h e he
      simpa [hE e he] using h e he
    · intro h e he
      simp [hE e he, h e he]
  rw [hA, Bool.and_comm]

theorem foldl_eaStepC {m : ℕ → ℕ → ℕ} {R : ℕ} {C : ℕ → ℕ} (hC : ctOK m R C = true)
    {E : List ℕ} (hE : ∀ e ∈ E, e < 256) (invs : List ℕ) (h : ∀ a ∈ invs, a < 256)
    (st : List ℕ × List (List ℕ)) :
    invs.foldl (eaStepS m E) st = invs.foldl (eaStepC m (candB m R C E) E) st := by
  induction invs generalizing st with
  | nil => rfl
  | cons a as ih =>
    have hs : eaStepS m E st a = eaStepC m (candB m R C E) E st a := by
      obtain ⟨s1, s2⟩ := st
      simp only [eaStepS, eaStepC, testBit_candB hC hE (h a (by simp))]
    rw [List.foldl_cons, List.foldl_cons, hs, ih (fun b hb => h b (by simp [hb]))]

theorem eaNextS_eq_eaNextC {m : ℕ → ℕ → ℕ} {R : ℕ} {C : ℕ → ℕ} (hC : ctOK m R C = true)
    {invs : List ℕ} (h : ∀ a ∈ invs, a < 256) (L : List (List ℕ)) :
    eaNextS m invs L = eaNextC m R C invs L := by
  have hf : (fun st E => invs.foldl (eaStepS m E) st) = fun st E =>
      if E.all (fun e => decide (e < 256)) then invs.foldl (eaStepC m (candB m R C E) E) st
      else invs.foldl (eaStepS m E) st := by
    funext st E
    by_cases hE : E.all (fun e => decide (e < 256)) = true
    · simp only [hE, ↓reduceIte]
      exact foldl_eaStepC hC (fun e he => by simpa using List.all_eq_true.1 hE e he) invs h st
    · exact (ite_eq_right_of_eq_false _ _ (eq_false hE)).symm
  rw [eaNextS, eaNextC, ← hf]

meta def rbM (M : RegModel) : Array (Array ℕ) :=
  #[#[(List.range 256).foldl (fun acc b => if M.mul[257 * b]! == 0 then acc ||| (1 <<< b) else acc) 0]]
meta def ctM (M : RegModel) : Array (Array ℕ) :=
  #[(Array.range 256).map fun b => if M.mul[257 * b]! != 0 then 0 else
    (List.range 256).foldl (fun acc x =>
      if M.mul[256 * x + b]! == M.mul[256 * b + x]! then acc ||| (1 <<< x) else acc) 0]
meta def ctM0 : Array (Array ℕ) := ctM (mkReg 0)
meta def ctM1 : Array (Array ℕ) := ctM (mkReg 1)
meta def rbM0 : Array (Array ℕ) := rbM (mkReg 0)
meta def rbM1 : Array (Array ℕ) := rbM (mkReg 1)

end CertificateChecks.KernelChengHeld.S2

#kmisc_packarrs CertificateChecks.KernelChengHeld.S2.CT0 CertificateChecks.KernelChengHeld.S2.ctM0 256
#kmisc_packarrs CertificateChecks.KernelChengHeld.S2.CT1 CertificateChecks.KernelChengHeld.S2.ctM1 256
#kmisc_packarrs CertificateChecks.KernelChengHeld.S2.RB0 CertificateChecks.KernelChengHeld.S2.rbM0 256
#kmisc_packarrs CertificateChecks.KernelChengHeld.S2.RB1 CertificateChecks.KernelChengHeld.S2.rbM1 256

namespace CertificateChecks.KernelChengHeld.S2

open CFSG.KC.ChengHeldS2 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim

theorem k0_ct : ctOK m0 (pg 256 (mask 256) (RB0 0) 0) (pg 256 (mask 256) (CT0 0)) = true := by
  decide +kernel
theorem k1_ct : ctOK m1 (pg 256 (mask 256) (RB1 0) 0) (pg 256 (mask 256) (CT1 0)) = true := by
  decide +kernel


theorem k0_ea : eaCentK 256 m0 (bR m0 (vGs m0 g0)) = true := by
  unfold eaCentK ea3K
  rw [eaNextK_eq_eaNextS, eaNextK_eq_eaNextS]
  simp only [eaNextS_eq_eaNextC k0_ct (invsK_lt m0), elemsK_cent_eq k0_ct]
  decide +kernel
theorem k1_ea : eaCentK 256 m1 (bR m1 (vGs m1 g1)) = true := by
  unfold eaCentK ea3K
  rw [eaNextK_eq_eaNextS, eaNextK_eq_eaNextS]
  simp only [eaNextS_eq_eaNextC k1_ct (invsK_lt m1), elemsK_cent_eq k1_ct]
  decide +kernel

theorem k0_nc : (notCentK 256 m0 i0 (aR (AU0 0)) (bR m0 (vGs m0 g0)) &&
    notCentK 256 m0 i0 (aR (AU0 2)) (bR m0 (vGs m0 g0))) = true := by decide +kernel
theorem k1_nc : (notCentK 256 m1 i1 (aR (AU1 0)) (bR m1 (vGs m1 g1)) &&
    notCentK 256 m1 i1 (aR (AU1 2)) (bR m1 (vGs m1 g1))) = true := by decide +kernel

theorem k0_uf : unitFixK 256 (aR (AU0 2)) (bR m0 (u1Gs m0 g0)) (bR m0 (u2Gs m0 g0)) = true := by
  decide +kernel
theorem k1_uf : unitFixK 256 (aR (AU1 2)) (bR m1 (u1Gs m1 g1)) (bR m1 (u2Gs m1 g1)) = true := by
  decide +kernel

theorem k1_gr : graphK 256 m1 i1 (aR (AU1 1)) (bR m1 (vGs m1 g1)) (g1 0) = true := by
  unfold graphK graphCaseK
  simp only [elemsK, sfilter_eq]
  decide +kernel

end CertificateChecks.KernelChengHeld.S2

end
