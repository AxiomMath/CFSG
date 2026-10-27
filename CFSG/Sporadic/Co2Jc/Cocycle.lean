module

public import CFSG.Sporadic.Co2Jc.Linear
public import Certificates.Certificate719050
public import CFSG.Sporadic.Co2Smith.GlNJH1

public section

namespace CFSG.Sporadic.Co2Jc

open CFSG.Sporadic.Co2Smith Subgroup
open CFSG.Sporadic.Co2Jc.Data

private theorem jc_sq_one (x : ↥Jc) : x * x = 1 := by
  obtain ⟨m, hm, rfl⟩ := exists_jcA x
  rw [← jcA_xor, Nat.xor_self, jcA_zero]

private noncomputable def Gam (Γ : Qj → ↥Jc → ↥Jc) (g : MulAut ↥Jc) : ↥Jc → ↥Jc := by
  classical
  exact if h : g ∈ Qj then Γ ⟨g, h⟩ else 1

private theorem Gam_of_mem {Γ : Qj → ↥Jc → ↥Jc} {g : MulAut ↥Jc} (hg : g ∈ Qj) :
    Gam Γ g = Γ ⟨g, hg⟩ := by
  rw [Gam]
  exact dif_pos hg

private theorem Gam_one {Γ : Qj → ↥Jc → ↥Jc}
    (h2 : ∀ g h a, Γ (g * h) a = Γ g a * (g : MulAut ↥Jc) (Γ h ((g : MulAut ↥Jc)⁻¹ a))) :
    Gam Γ 1 = 1 := by
  funext a
  rw [Gam_of_mem Qj.one_mem]
  have h : Γ (1 : Qj) a = Γ (1 : Qj) a * Γ (1 : Qj) a := by
    simpa using h2 (1 : Qj) (1 : Qj) a
  exact h.trans (jc_sq_one (Γ (1 : Qj) a))

private noncomputable def Delta (Γ : Qj → ↥Jc → ↥Jc) (g : MulAut ↥Jc) : ↥Jc → ↥Jc :=
  fun x => Gam Γ g (g x)

private theorem Delta_one (Γ : Qj → ↥Jc → ↥Jc)
    (h2 : ∀ g h a, Γ (g * h) a = Γ g a * (g : MulAut ↥Jc) (Γ h ((g : MulAut ↥Jc)⁻¹ a))) :
    Delta Γ 1 = 1 := by
  funext x
  simp [Delta, Gam_one h2]

private theorem Delta_cocycle {Γ : Qj → ↥Jc → ↥Jc}
    (h2 : ∀ g h a, Γ (g * h) a = Γ g a * (g : MulAut ↥Jc) (Γ h ((g : MulAut ↥Jc)⁻¹ a)))
    {g h : MulAut ↥Jc} (hg : g ∈ Qj) (hh : h ∈ Qj) (x : ↥Jc) :
    Delta Γ (g * h) x = Delta Γ g (h x) * g (Delta Γ h x) := by
  have hgh : g * h ∈ Qj := Qj.mul_mem hg hh
  have hsub : (⟨g * h, hgh⟩ : Qj) = ⟨g, hg⟩ * ⟨h, hh⟩ := Subtype.ext rfl
  have hx : (g * h) x = g (h x) := rfl
  have hinv : ((⟨g, hg⟩ : Qj) : MulAut ↥Jc)⁻¹ (g (h x)) = h x := by
    show (g : MulAut ↥Jc).symm (g (h x)) = h x
    exact MulEquiv.symm_apply_apply g (h x)
  calc
    Delta Γ (g * h) x = Γ ⟨g * h, hgh⟩ (g (h x)) := by rw [Delta, Gam_of_mem hgh, hx]
    _ = Γ (⟨g, hg⟩ * ⟨h, hh⟩) (g (h x)) := by rw [hsub]
    _ = Γ ⟨g, hg⟩ (g (h x)) *
          g (Γ ⟨h, hh⟩ (((⟨g, hg⟩ : Qj) : MulAut ↥Jc)⁻¹ (g (h x)))) := h2 _ _ _
    _ = Γ ⟨g, hg⟩ (g (h x)) * g (Γ ⟨h, hh⟩ (h x)) := by rw [hinv]
    _ = Delta Γ g (h x) * g (Delta Γ h x) := by
      rw [Delta, Delta, Gam_of_mem hg, Gam_of_mem hh]

private theorem Delta_hom {Γ : Qj → ↥Jc → ↥Jc}
    (h1 : ∀ g a b, Γ g (a * b) = Γ g a * Γ g b)
    {g : MulAut ↥Jc} (hg : g ∈ Qj) (a b : ↥Jc) :
    Delta Γ g (a * b) = Delta Γ g a * Delta Γ g b := by
  simp only [Delta, Gam_of_mem hg, map_mul]
  exact h1 ⟨g, hg⟩ (g a) (g b)

private noncomputable def cbit (ρ : ℕ) (x : ↥Jc) : ZMod 2 :=
  if (coord x).testBit ρ then 1 else 0

private theorem cbit_one (ρ : ℕ) : cbit ρ 1 = 0 := by
  simp [cbit, coord_one]

private theorem cbit_mul (ρ : ℕ) (a b : ↥Jc) : cbit ρ (a * b) = cbit ρ a + cbit ρ b := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  simp only [cbit, coord_mul]
  by_cases ha : (coord a).testBit ρ <;> by_cases hb : (coord b).testBit ρ <;>
    simp [ha, hb, h11]

private theorem cbit_jcA {ρ m : ℕ} (hm : m < 1024) (hρ : ρ < 10) :
    cbit ρ (jcA m) = if m.testBit ρ then 1 else 0 := by
  simp only [cbit, coord_jcA hm]

private def rowV : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | k :: w, j, rho =>
      Native.preMask k rho (wordAct w (2 ^ j)) ^^^
        Native.ten.foldr
          (fun rhop acc =>
            if (Native.gl k (2 ^ rhop)).testBit rho then rowV w j rhop ^^^ acc else acc) 0

private theorem mem_ten_lt {rho : ℕ} (h : rho ∈ Native.ten) : rho < 10 := by
  simp [Native.ten] at h
  omega

private theorem ten_map_getElem! (f : ℕ → ℕ) {rho : ℕ} (h : rho < 10) :
    (Native.ten.map f)[rho]! = f rho := by
  interval_cases rho <;> rfl

private theorem foldr_congr {β : Type} (l : List ℕ) (f g : ℕ → β → β)
    (h : ∀ x ∈ l, f x = g x) (init : β) :
    l.foldr f init = l.foldr g init := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldr_cons, List.foldr_cons, h x (by simp)]
    rw [ih (fun y hy => h y (by simp [hy]))]

private theorem rowAll_eq_rowV (w : List ℕ) (j : ℕ) :
    Native.rowAll w j = Native.ten.map (fun rho => rowV w j rho) := by
  induction w with
  | nil => simp [Native.rowAll, rowV, Native.ten, List.replicate]
  | cons k w ih =>
    rw [Native.rowAll, Native.rowStep, Native.preMaskVec]
    rw [ih]
    apply List.map_congr_left
    intro rho hrho
    have h10 : rho < 10 := mem_ten_lt hrho
    rw [ten_map_getElem! _ h10]
    have hfold : Native.ten.foldr
        (fun rhop acc => if (Native.gl k (2 ^ rhop)).testBit rho then
          (Native.ten.map (fun rho => rowV w j rho))[rhop]! ^^^ acc else acc) 0 =
      Native.ten.foldr
        (fun rhop acc => if (Native.gl k (2 ^ rhop)).testBit rho then
          rowV w j rhop ^^^ acc else acc) 0 := by
      apply foldr_congr Native.ten
      intro rhop hrop
      rw [ten_map_getElem! _ (mem_ten_lt hrop)]
    rw [hfold]
    rw [rowV]

private theorem cbit_apply_hom {f : ↥Jc →* ↥Jc} (ρ m : ℕ) (hm : m < 1024) :
    cbit ρ (f (jcA m)) = bsum 10 m (fun b => cbit ρ (f (jcA (2 ^ b)))) :=
  additive_jcA (f := fun x => cbit ρ (f x))
    (fun a b => by rw [map_mul, cbit_mul]) hm

private noncomputable def Vvec (Γ : Qj → ↥Jc → ↥Jc) (i : ℕ) : ZMod 2 :=
  cbit (i % 10) (Delta Γ (qA (i / 100)) (jcA (2 ^ ((i / 10) % 10))))

private theorem ten_sum (f : ℕ → ZMod 2) :
    ((Native.ten.map f).sum) = ∑ i ∈ Finset.range 10, f i := by
  simp [Native.ten, Finset.sum_range_succ]
  abel

private theorem bsum_ten_eq (m : ℕ) (f : ℕ → ZMod 2) :
    bsum 10 m f = (Native.ten.map (fun i => if m.testBit i then f i else 0)).sum := by
  rw [ten_sum]
  simp only [bsum]

private theorem bsum_foldr_ite (l : List ℕ) (g : ℕ → Bool) (m : ℕ → ℕ) (U : ℕ → ZMod 2) :
    bsum 300 (l.foldr (fun b acc => if g b then m b ^^^ acc else acc) 0) U =
      (l.map fun b => if g b then bsum 300 (m b) U else 0).sum := by
  induction l with
  | nil => simp [bsum_zero]
  | cons x xs ih =>
    rw [List.foldr_cons, List.map_cons, List.sum_cons]
    by_cases h : g x
    · rw [if_pos h, if_pos h, bsum_xor, ih]
    · rw [if_neg h, if_neg h, ih, zero_add]

private theorem bsum_preMask (Γ : Qj → ↥Jc → ↥Jc) (k ρ v : ℕ) (hk : k < 3) (hρ : ρ < 10) :
    bsum 300 (Native.preMask k ρ v) (Vvec Γ) =
      bsum 10 v (fun b => Vvec Γ (100 * k + 10 * b + ρ)) := by
  unfold Native.preMask
  rw [bsum_foldr_ite, ten_sum, bsum_ten_eq, ten_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hb10 : b < 10 := by simpa using hb
  by_cases hbit : v.testBit b
  · rw [if_pos hbit, if_pos hbit]
    exact bsum_two_pow (n := 300) (by omega) (Vvec Γ)
  · rw [if_neg hbit, if_neg hbit]

private theorem bsum_congr {n m : ℕ} {f g : ℕ → ZMod 2} (h : ∀ i < n, f i = g i) :
    bsum n m f = bsum n m g := by
  simp only [bsum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i (by simpa using hi)]

private theorem vvec_qA {Γ : Qj → ↥Jc → ↥Jc} (k b ρ : ℕ) (hk : k < 3) (hb : b < 10)
    (hρ : ρ < 10) :
    Vvec Γ (100 * k + 10 * b + ρ) = cbit ρ (Delta Γ (qA k) (jcA (2 ^ b))) := by
  simp only [Vvec]
  rw [show (100 * k + 10 * b + ρ) / 100 = k by omega,
    show (100 * k + 10 * b + ρ) / 10 % 10 = b by omega,
    show (100 * k + 10 * b + ρ) % 10 = ρ by omega]

private theorem cbit_delta_qA {Γ : Qj → ↥Jc → ↥Jc}
    (h1 : ∀ g a b, Γ g (a * b) = Γ g a * Γ g b) {k : ℕ} (hk : k < 3) (ρ m : ℕ)
    (hm : m < 1024) :
    cbit ρ (Delta Γ (qA k) (jcA m)) =
      bsum 10 m (fun b => cbit ρ (Delta Γ (qA k) (jcA (2 ^ b)))) :=
  additive_jcA (f := fun x => cbit ρ (Delta Γ (qA k) x))
    (fun a b => by rw [Delta_hom h1 (qA_mem hk) a b, cbit_mul]) hm

private theorem cbit_qA_apply {k ρ m : ℕ} (hk : k < 3) (hρ : ρ < 10) (hm : m < 1024) :
    cbit ρ (qA k (jcA m)) = bsum 10 m (fun b => cbit ρ (qA k (jcA (2 ^ b)))) :=
  additive_jcA (f := fun x => cbit ρ (qA k x))
    (fun a b => by rw [map_mul, cbit_mul]) hm

private theorem cbit_qA_jcA {k ρ b : ℕ} (hk : k < 3) (hρ : ρ < 10) :
    cbit ρ (qA k (jcA (2 ^ b))) =
      if (Native.gl k (2 ^ b)).testBit ρ then 1 else 0 := by
  rw [qA_jcA hk, cbit_jcA (glNJT_lt hk (2 ^ b)) hρ]
  rfl

private theorem wordAct_lt {w : List ℕ} (hw : ∀ k ∈ w, k < 3) {m : ℕ} (hm : m < 1024) :
    wordAct w m < 1024 := by
  induction w with
  | nil => simpa [wordAct] using hm
  | cons k w ih =>
    have hk : k < 3 := hw k (by simp)
    have hw' : ∀ j ∈ w, j < 3 := fun j hj => hw j (by simp [hj])
    change CFSG.Sporadic.Co2Smith.Native.glNJT k (wordAct w m) < 1024
    exact glNJT_lt hk _

private theorem bsum_rowV {Γ : Qj → ↥Jc → ↥Jc}
    (h1 : ∀ g a b, Γ g (a * b) = Γ g a * Γ g b)
    (h2 : ∀ g h a, Γ (g * h) a = Γ g a * (g : MulAut ↥Jc) (Γ h ((g : MulAut ↥Jc)⁻¹ a))) :
    ∀ (w : List ℕ) (j ρ : ℕ), (∀ k ∈ w, k < 3) → j < 10 → ρ < 10 →
      bsum 300 (rowV w j ρ) (Vvec Γ) =
        cbit ρ (Delta Γ (qWord w) (jcA (2 ^ j)))
  | [], j, ρ, _, _, _ => by
      simp only [rowV, bsum_zero]
      rw [qWord_nil, Delta_one Γ h2]
      exact (cbit_one ρ).symm
  | k :: w, j, ρ, hw, hj, hρ => by
      have hk : k < 3 := hw k (by simp)
      have hw' : ∀ q ∈ w, q < 3 := fun q hq => hw q (by simp [hq])
      have hqk : qA k ∈ Qj := qA_mem hk
      have hmem : qWord w ∈ Qj := qWord_mem hw'
      have hxlt : wordAct w (2 ^ j) < 1024 := wordAct_lt hw' (two_pow_lt_1024 hj)
      have hrow : rowV (k :: w) j ρ =
          Native.preMask k ρ (wordAct w (2 ^ j)) ^^^
            Native.ten.foldr (fun rhop acc =>
              if (Native.gl k (2 ^ rhop)).testBit ρ then rowV w j rhop ^^^ acc else acc) 0 := rfl
      rw [hrow, bsum_xor]
      have hfirst : bsum 300 (Native.preMask k ρ (wordAct w (2 ^ j))) (Vvec Γ) =
          cbit ρ (Delta Γ (qA k) (jcA (wordAct w (2 ^ j)))) := by
        rw [bsum_preMask Γ k ρ _ hk hρ]
        rw [cbit_delta_qA h1 hk ρ (wordAct w (2 ^ j)) hxlt]
        apply bsum_congr
        intro b hb
        exact vvec_qA (Γ := Γ) k b ρ hk hb hρ
      have hsecond : bsum 300
          (Native.ten.foldr (fun rhop acc =>
            if (Native.gl k (2 ^ rhop)).testBit ρ then rowV w j rhop ^^^ acc else acc) 0)
          (Vvec Γ) = cbit ρ (qA k (Delta Γ (qWord w) (jcA (2 ^ j)))) := by
        set y : ↥Jc := Delta Γ (qWord w) (jcA (2 ^ j)) with hy
        rw [bsum_foldr_ite]
        have hmap : (Native.ten.map (fun rhop =>
              if (Native.gl k (2 ^ rhop)).testBit ρ then
                bsum 300 (rowV w j rhop) (Vvec Γ) else 0)).sum =
            (Native.ten.map (fun rhop =>
              if (Native.gl k (2 ^ rhop)).testBit ρ then cbit rhop y else 0)).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro rhop hrop
          rw [bsum_rowV h1 h2 w j rhop hw' hj (mem_ten_lt hrop)]
        rw [hmap]
        rw [show (Native.ten.map (fun rhop =>
              if (Native.gl k (2 ^ rhop)).testBit ρ then cbit rhop y else 0)).sum =
            bsum 10 (coord y) (fun rhop => cbit ρ (qA k (jcA (2 ^ rhop)))) from ?_]
        · rw [← cbit_qA_apply (k := k) (ρ := ρ) (m := coord y) hk hρ (coord_lt y),
            jcA_coord]
        · rw [bsum_ten_eq, ten_sum, ten_sum]
          apply Finset.sum_congr rfl
          intro rhop hrop
          have hr10 : rhop < 10 := by simpa using hrop
          rw [cbit_qA_jcA hk hρ]
          simp only [cbit]
          by_cases hc : (Native.gl k (2 ^ rhop)).testBit ρ <;>
            by_cases hd : (coord y).testBit rhop <;> simp [hc, hd]
      rw [hfirst, hsecond]
      rw [qWord_cons, Delta_cocycle h2 hqk hmem, qWord_jcA hw' (2 ^ j), cbit_mul]

private theorem zmod2_eq_zero_of_ne_one {x : ZMod 2} (h : x ≠ 1) : x = 0 := by
  revert x
  decide

private theorem testBit_eq_false_of_lt_pow {v b w : ℕ} (hv : v < 2 ^ w) (hb : w ≤ b) :
    v.testBit b = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hb))

private noncomputable def xbit (Γ : Qj → ↥Jc → ↥Jc) (pq : ℕ) : ZMod 2 :=
  bsum 300 (Native.xmask[pq]!) (Vvec Γ)

private noncomputable def xb (Γ : Qj → ↥Jc → ↥Jc) (pq : ℕ) : Bool := xbit Γ pq == 1

private noncomputable def Xcol (Γ : Qj → ↥Jc → ↥Jc) (p : ℕ) : ℕ :=
  Native.ten.foldr
    (fun rho acc => if xb Γ (10 * p + rho) then (2 ^ rho) ^^^ acc else acc) 0

private theorem bsum_one_hot {m ρ : ℕ} (hρ : ρ < 10) :
    bsum 10 m (fun i => if i = ρ then (1 : ZMod 2) else 0) =
      if m.testBit ρ then 1 else 0 := by
  rw [bsum, Finset.sum_eq_single ρ]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_range.mpr hρ) h

private theorem bsum_300_eq_10 {m : ℕ} (hm : m < 1024) (f : ℕ → ZMod 2) :
    bsum 300 m f = bsum 10 m f := by
  rw [bsum, bsum]
  symm
  apply Finset.sum_subset
  · intro i hi
    have hi' : i < 10 := Finset.mem_range.mp hi
    exact Finset.mem_range.mpr (by omega)
  · intro i hi hnot
    have hi10 : 10 ≤ i := by
      simp only [Finset.mem_range, not_lt] at hnot
      omega
    rw [testBit_eq_false_of_lt_pow hm hi10]
    simp

private theorem foldr_xor_lt (l : List ℕ) (f : ℕ → ℕ) (g : ℕ → Bool)
    (h : ∀ i ∈ l, f i < 1024) :
    (l.foldr (fun i acc => if g i then f i ^^^ acc else acc) 0) < 1024 := by
  induction l with
  | nil => norm_num
  | cons x xs ih =>
    rw [List.foldr_cons]
    by_cases hg : g x
    · rw [if_pos hg]
      exact Nat.xor_lt_two_pow (n := 10) (by simpa using h x (by simp))
        (by simpa using ih (fun i hi => h i (by simp [hi])))
    · rw [if_neg hg]
      exact ih (fun i hi => h i (by simp [hi]))

private theorem Xcol_lt (Γ : Qj → ↥Jc → ↥Jc) (p : ℕ) : Xcol Γ p < 1024 := by
  unfold Xcol
  apply foldr_xor_lt
  intro rho hrho
  exact two_pow_lt_1024 (mem_ten_lt hrho)

private theorem bsum_Xcol (Γ : Qj → ↥Jc → ↥Jc) (p : ℕ) (f : ℕ → ZMod 2) :
    bsum 300 (Xcol Γ p) f =
      (Native.ten.map (fun rho => if xb Γ (10 * p + rho) then f rho else 0)).sum := by
  unfold Xcol
  rw [bsum_foldr_ite]
  apply congrArg List.sum
  apply List.map_congr_left
  intro rho hrho
  rw [bsum_two_pow (n := 300) (by have := mem_ten_lt hrho; omega)]

private theorem Xcol_testBit (Γ : Qj → ↥Jc → ↥Jc) (p ρ : ℕ) (hρ : ρ < 10) :
    (Xcol Γ p).testBit ρ = xb Γ (10 * p + ρ) := by
  have h := bsum_Xcol Γ p (fun i => if i = ρ then (1 : ZMod 2) else 0)
  rw [bsum_300_eq_10 (Xcol_lt Γ p), bsum_one_hot hρ] at h
  have hrhs : (Native.ten.map (fun rho =>
        if xb Γ (10 * p + rho) then (if rho = ρ then (1 : ZMod 2) else 0)
        else 0)).sum = if xb Γ (10 * p + ρ) then 1 else 0 := by
    rw [ten_sum, Finset.sum_eq_single ρ]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hmem
      exact absurd (Finset.mem_range.mpr hρ) hmem
  rw [hrhs] at h
  by_cases hb : (Xcol Γ p).testBit ρ <;>
    by_cases hx : xb Γ (10 * p + ρ) <;> simp [hb, hx] at h ⊢

private theorem ite_xb (Γ : Qj → ↥Jc → ↥Jc) (pq : ℕ) :
    (if xb Γ pq then (1 : ZMod 2) else 0) = xbit Γ pq := by
  unfold xb
  by_cases h : xbit Γ pq = 1
  · simp [h]
  · have h' : ¬ (xbit Γ pq == 1) := by simpa [beq_iff_eq] using h
    rw [if_neg h', zmod2_eq_zero_of_ne_one h]

private noncomputable def Xfun (Γ : Qj → ↥Jc → ↥Jc) : ↥Jc →* ↥Jc where
  toFun x := jcA (colAct (Xcol Γ) (coord x))
  map_one' := by simp [colAct_zero, jcA_zero, coord_one]
  map_mul' := by
    intro a b
    rw [coord_mul, colAct_xor, jcA_xor]

private theorem Xfun_jcA (Γ : Qj → ↥Jc → ↥Jc) {m : ℕ} (hm : m < 1024) :
    Xfun Γ (jcA m) = jcA (colAct (Xcol Γ) m) := by
  change jcA (colAct (Xcol Γ) (coord (jcA m))) = jcA (colAct (Xcol Γ) m)
  rw [coord_jcA hm]

private theorem cbit_Xfun (Γ : Qj → ↥Jc → ↥Jc) (m ρ : ℕ) (hm : m < 1024) (hρ : ρ < 10) :
    cbit ρ (Xfun Γ (jcA m)) = bsum 10 m (fun p => xbit Γ (10 * p + ρ)) := by
  have h := additive_jcA (f := fun x => cbit ρ (Xfun Γ x))
    (fun a b => by rw [map_mul, cbit_mul]) hm
  rw [h]
  apply bsum_congr
  intro p hp
  have hxp : Xfun Γ (jcA (2 ^ p)) = jcA (Xcol Γ p) := by
    rw [Xfun_jcA Γ (two_pow_lt_1024 hp), colAct_two_pow (Xcol Γ) hp]
  rw [hxp, cbit_jcA (Xcol_lt Γ p) hρ, Xcol_testBit Γ p ρ hρ, ite_xb]

private theorem bsum_cobMask1 (Γ : Qj → ↥Jc → ↥Jc) (k b ρ : ℕ) (hk : k < 3) (hb : b < 10)
    (hρ : ρ < 10) :
    bsum 300 (Native.cobMask1 k b ρ) (Vvec Γ) =
      cbit ρ (Xfun Γ (qA k (jcA (2 ^ b)))) := by
  unfold Native.cobMask1
  rw [bsum_foldr_ite, qA_jcA hk]
  change (Native.ten.map (fun b_1 =>
      if (Native.gl k (2 ^ b)).testBit b_1 then
        bsum 300 (Native.xmask[10 * b_1 + ρ]!) (Vvec Γ) else 0)).sum =
    cbit ρ (Xfun Γ (jcA (Native.gl k (2 ^ b))))
  rw [cbit_Xfun Γ (Native.gl k (2 ^ b)) ρ (glNJT_lt hk (2 ^ b)) hρ, bsum_ten_eq]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [xbit]

private theorem bsum_cobMask2 (Γ : Qj → ↥Jc → ↥Jc) (k b ρ : ℕ) (hk : k < 3) (hb : b < 10)
    (hρ : ρ < 10) :
    bsum 300 (Native.cobMask2 k b ρ) (Vvec Γ) =
      cbit ρ (qA k (Xfun Γ (jcA (2 ^ b)))) := by
  unfold Native.cobMask2
  rw [bsum_foldr_ite]
  have hcoord : coord (Xfun Γ (jcA (2 ^ b))) = Xcol Γ b := by
    rw [Xfun_jcA Γ (two_pow_lt_1024 hb), colAct_two_pow (Xcol Γ) hb,
      coord_jcA (Xcol_lt Γ b)]
  rw [← jcA_coord (Xfun Γ (jcA (2 ^ b)))]
  rw [cbit_qA_apply (k := k) (ρ := ρ) (m := coord (Xfun Γ (jcA (2 ^ b)))) hk hρ
    (coord_lt _)]
  rw [hcoord, bsum_ten_eq]
  apply congrArg List.sum
  apply List.map_congr_left
  intro q hq
  have hq10 : q < 10 := mem_ten_lt hq
  change (if (Native.gl k (2 ^ q)).testBit ρ then xbit Γ (10 * b + q) else 0) =
    (if (Xcol Γ b).testBit q then cbit ρ (qA k (jcA (2 ^ q))) else 0)
  rw [cbit_qA_jcA hk hρ, Xcol_testBit Γ b q hq10, ← ite_xb]
  by_cases h1 : (Native.gl k (2 ^ q)).testBit ρ <;>
    by_cases h2 : xb Γ (10 * b + q) <;> simp [h1, h2]

private theorem all_id_eq_true {l : List Bool} (h : l.all id = true) :
    ∀ b ∈ l, b = true := by
  induction l with
  | nil => intro b hb; simp at hb
  | cons x xs ih =>
    rw [List.all_cons] at h
    have h' := Bool.and_eq_true_iff.mp h
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h'.1
    · exact ih h'.2 b hb

private theorem dualOK_mem : Native.dualOK ∈ Native.cocycleChecks := List.mem_cons_self

private theorem splitOK_mem : Native.splitOK ∈ Native.cocycleChecks :=
  List.mem_cons_of_mem _ List.mem_cons_self

private theorem splitMask_mem : Native.splitMaskOK ∈ Native.splitChecks :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))))))

private theorem splitNoW_mem : Native.noW ∈ Native.splitChecks :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)))))

private theorem relOK_mem : Native.relOK ∈ Native.dualChecks := List.mem_cons_self

private theorem relOK_of_dualOK (h : Native.dualOK = true) : Native.relOK = true :=
  all_id_eq_true h _ relOK_mem

private theorem dualOK_of_cocycle (h : Native.cocycleOK = true) : Native.dualOK = true :=
  all_id_eq_true h _ dualOK_mem

private theorem splitOK_of_cocycle (h : Native.cocycleOK = true) : Native.splitOK = true :=
  all_id_eq_true h _ splitOK_mem

private theorem splitMaskOK_of (h : Native.splitOK = true) : Native.splitMaskOK = true :=
  all_id_eq_true h _ splitMask_mem

private theorem splitNoW_of (h : Native.splitOK = true) : Native.noW = true :=
  all_id_eq_true h _ splitNoW_mem

private theorem splitMask_spec (h : Native.splitOK = true) :
    ∀ u < 300,
      Native.xorRowsByMask Native.splitRows (Native.combSplit[u]!) = Native.splitRes u := by
  have hm := splitMaskOK_of h
  simp only [Native.splitMaskOK, List.all_eq_true] at hm
  intro u hu
  simpa [beq_iff_eq] using hm u (List.mem_range.mpr hu)

private theorem noW_spec (h : Native.splitOK = true) :
    ∀ w < 1024, ¬ ((Native.gcol 0 0 = w ^^^ Native.gl 0 w) ∧
      (Native.gcol 1 0 = w ^^^ Native.gl 1 w)) := by
  have hw := splitNoW_of h
  simp only [Native.noW, List.all_eq_true] at hw
  intro w hlt hc
  have hb : ((Native.gcol 0 0 == w ^^^ Native.gl 0 w) &&
      (Native.gcol 1 0 == w ^^^ Native.gl 1 w)) = true := by
    rw [Bool.and_eq_true_iff]
    exact ⟨by simpa [beq_iff_eq] using hc.1, by simpa [beq_iff_eq] using hc.2⟩
  have h := hw w (List.mem_range.mpr hlt)
  rw [hb] at h
  simpa using h

private theorem bsum_ite {c : Bool} {m : ℕ} (f : ℕ → ZMod 2) :
    bsum 300 (if c then m else 0) f = if c then bsum 300 m f else 0 := by
  cases c <;> simp [bsum_zero]

private theorem ite_mul (c : Bool) (x : ZMod 2) :
    (if c then (1 : ZMod 2) else 0) * x = if c then x else 0 := by
  cases c <;> simp

private theorem add_self_eq_zero' (a : ZMod 2) : a + a = 0 := by
  rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]

private theorem eq_of_add_eq_zero' {a b : ZMod 2} (h : a + b = 0) : a = b := by
  have hbb : b + b = 0 := add_self_eq_zero' b
  exact add_right_cancel (h.trans hbb.symm)

private noncomputable def eps (Γ : Qj → ↥Jc → ↥Jc) : ZMod 2 :=
  bsum 300 Native.emask (Vvec Γ)

private theorem relOK_spec (h : Native.relOK = true) :
    ∀ r ∈ rels, (∀ k ∈ r, k < 3) ∧ ∀ j < 10, wordAct r (2 ^ j) = 2 ^ j := by
  simp only [Native.relOK, List.all_eq_true, Bool.and_eq_true_iff, beq_iff_eq] at h
  intro r hr
  obtain ⟨hr1, hr2⟩ := h r hr
  constructor
  · intro k hk
    simpa using hr1 k hk
  · intro j hj
    simpa using hr2 j (List.mem_range.mpr hj)

private theorem qWord_of_rel {r : List ℕ} (hw : ∀ k ∈ r, k < 3)
    (h : ∀ j < 10, wordAct r (2 ^ j) = 2 ^ j) : qWord r = 1 := by
  apply mulAut_ext_basis
  intro i hi
  rw [qWord_jcA hw, h i hi]
  rfl

private theorem bsum_xorRowsFrom_eq_zero {n : ℕ} {rows : List ℕ} {start : ℕ} {m : ℕ}
    {U : ℕ → ZMod 2} (h : ∀ r ∈ rows, bsum n r U = 0) :
    bsum n (Native.xorRowsFrom start rows m) U = 0 := by
  induction rows generalizing start with
  | nil => simp [Native.xorRowsFrom, bsum_zero]
  | cons r rs ih =>
    rw [show Native.xorRowsFrom start (r :: rs) m =
      (if m.testBit start then r else 0) ^^^ Native.xorRowsFrom (start + 1) rs m from rfl]
    rw [bsum_xor]
    have hr : bsum n r U = 0 := h r (by simp)
    have hrs : ∀ q ∈ rs, bsum n q U = 0 := fun q hq => h q (by simp [hq])
    have hih := ih (start := start + 1) hrs
    by_cases hbit : m.testBit start
    · simp [hbit, hr, hih, bsum_zero]
    · simp [hbit, hih, bsum_zero]

private theorem bsum_rowV_rel {Γ : Qj → ↥Jc → ↥Jc}
    (h1 : ∀ g a b, Γ g (a * b) = Γ g a * Γ g b)
    (h2 : ∀ g h a, Γ (g * h) a = Γ g a * (g : MulAut ↥Jc) (Γ h ((g : MulAut ↥Jc)⁻¹ a)))
    (hrel : Native.relOK = true) {r : List ℕ} (hr : r ∈ rels) {j ρ : ℕ}
    (hj : j < 10) (hρ : ρ < 10) :
    bsum 300 (rowV r j ρ) (Vvec Γ) = 0 := by
  obtain ⟨hw, hact⟩ := relOK_spec hrel r hr
  have hq : qWord r = 1 := qWord_of_rel hw hact
  rw [bsum_rowV h1 h2 r j ρ hw hj hρ, hq, Delta_one Γ h2]
  simpa using cbit_one ρ

private theorem bsum_splitRows_eq_zero {Γ : Qj → ↥Jc → ↥Jc}
    (h1 : ∀ g a b, Γ g (a * b) = Γ g a * Γ g b)
    (h2 : ∀ g h a, Γ (g * h) a = Γ g a * (g : MulAut ↥Jc) (Γ h ((g : MulAut ↥Jc)⁻¹ a)))
    (hrel : Native.relOK = true) (m : ℕ) :
    bsum 300 (Native.xorRowsByMask Native.splitRows m) (Vvec Γ) = 0 := by
  apply bsum_xorRowsFrom_eq_zero
  intro x hx
  simp only [Native.splitRows, List.mem_flatMap, List.mem_map, List.mem_range] at hx
  obtain ⟨r, hr, j, hj, hx⟩ := hx
  rw [rowAll_eq_rowV] at hx
  obtain ⟨rho, hrho, rfl⟩ := List.mem_map.mp hx
  exact bsum_rowV_rel h1 h2 hrel hr hj (mem_ten_lt hrho)

private theorem split_unknown_eq {Γ : Qj → ↥Jc → ↥Jc}
    (h1 : ∀ g a b, Γ g (a * b) = Γ g a * Γ g b)
    (h2 : ∀ g h a, Γ (g * h) a = Γ g a * (g : MulAut ↥Jc) (Γ h ((g : MulAut ↥Jc)⁻¹ a)))
    (hcert : Native.splitOK = true) (hrel : Native.relOK = true)
    {k b ρ : ℕ} (hk : k < 3) (hb : b < 10) (hρ : ρ < 10) :
    Vvec Γ (100 * k + 10 * b + ρ) =
      cbit ρ (Xfun Γ (qA k (jcA (2 ^ b))) * qA k (Xfun Γ (jcA (2 ^ b)))) +
        (if Native.gamma0.testBit (100 * k + 10 * b + ρ) then (1 : ZMod 2) else 0) *
          eps Γ := by
  have hmask := splitMask_spec hcert (100 * k + 10 * b + ρ) (by omega)
  have hzero : bsum 300
      (Native.xorRowsByMask Native.splitRows (Native.combSplit[100 * k + 10 * b + ρ]!))
      (Vvec Γ) = 0 := bsum_splitRows_eq_zero h1 h2 hrel _
  rw [hmask] at hzero
  rw [Native.splitRes, bsum_xor, bsum_xor, bsum_ite] at hzero
  rw [show (100 * k + 10 * b + ρ) / 100 = k by omega,
    show (100 * k + 10 * b + ρ) / 10 % 10 = b by omega,
    show (100 * k + 10 * b + ρ) % 10 = ρ by omega] at hzero
  rw [show Native.unitMask k b ρ = 2 ^ (100 * k + 10 * b + ρ) from rfl,
    bsum_two_pow (by omega)] at hzero
  rw [Native.cobMask, bsum_xor,
    bsum_cobMask1 (Γ := Γ) k b ρ hk hb hρ,
    bsum_cobMask2 (Γ := Γ) k b ρ hk hb hρ] at hzero
  rw [← ite_mul, ← cbit_mul, add_assoc] at hzero
  exact eq_of_add_eq_zero' hzero

private theorem cbit_testBit {ρ : ℕ} (x : ↥Jc) (hρ : ρ < 10) :
    (coord x).testBit ρ = decide (cbit ρ x = 1) := by
  simp only [cbit]
  by_cases h : (coord x).testBit ρ <;> simp [h]

private theorem eq_of_cbit_eq {x y : ↥Jc} (h : ∀ ρ < 10, cbit ρ x = cbit ρ y) : x = y := by
  have hcoord : coord x = coord y := by
    apply Nat.eq_of_testBit_eq
    intro ρ
    by_cases hρ : ρ < 10
    · rw [cbit_testBit x hρ, cbit_testBit y hρ, h ρ hρ]
    · have hx : (coord x).testBit ρ = false := by
        apply Nat.testBit_eq_false_of_lt
        calc
          coord x < 1024 := coord_lt x
          _ = 2 ^ 10 := by norm_num
          _ ≤ 2 ^ ρ := Nat.pow_le_pow_right (n := 2) (i := 10) (by norm_num) (by omega)
      have hy : (coord y).testBit ρ = false := by
        apply Nat.testBit_eq_false_of_lt
        calc
          coord y < 1024 := coord_lt y
          _ = 2 ^ 10 := by norm_num
          _ ≤ 2 ^ ρ := Nat.pow_le_pow_right (n := 2) (i := 10) (by norm_num) (by omega)
      rw [hx, hy]
  rw [← jcA_coord x, ← jcA_coord y, hcoord]

private theorem zmod2_eq_one_of_ne_zero {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  revert x
  decide

private noncomputable def DeltaX (Γ : Qj → ↥Jc → ↥Jc) (g : MulAut ↥Jc) : ↥Jc → ↥Jc :=
  fun x => Xfun Γ (g x) * g (Xfun Γ x)

private theorem DeltaX_hom (Γ : Qj → ↥Jc → ↥Jc) (g : MulAut ↥Jc) (a b : ↥Jc) :
    DeltaX Γ g (a * b) = DeltaX Γ g a * DeltaX Γ g b := by
  apply eq_of_cbit_eq
  intro ρ hρ
  simp only [DeltaX, map_mul, cbit_mul]
  abel

private theorem DeltaX_one (Γ : Qj → ↥Jc → ↥Jc) (x : ↥Jc) : DeltaX Γ 1 x = 1 := by
  simp only [DeltaX]
  rw [show (1 : MulAut ↥Jc) x = x from rfl]
  exact jc_sq_one _

private theorem mul_sq_cancel {A B C : ↥Jc} (hB : B * B = 1) : (A * B) * (B * C) = A * C := by
  rw [mul_assoc, ← mul_assoc B B C, hB, one_mul]

private theorem DeltaX_cocycle (Γ : Qj → ↥Jc → ↥Jc) (g h : MulAut ↥Jc) (x : ↥Jc) :
    DeltaX Γ (g * h) x = DeltaX Γ g (h x) * g (DeltaX Γ h x) := by
  simp only [DeltaX]
  rw [show (g * h) x = g (h x) from rfl]
  rw [show (g * h) (Xfun Γ x) = g (h (Xfun Γ x)) from rfl]
  rw [map_mul]
  have hB : g (Xfun Γ (h x)) * g (Xfun Γ (h x)) = 1 := by
    rw [← map_mul, jc_sq_one, map_one]
  exact (mul_sq_cancel hB).symm

private theorem cbit_DeltaX_bsum (Γ : Qj → ↥Jc → ↥Jc) (g : MulAut ↥Jc) (ρ : ℕ) (x : ↥Jc) :
    cbit ρ (DeltaX Γ g x) =
      bsum 10 (coord x) (fun b => cbit ρ (DeltaX Γ g (jcA (2 ^ b)))) := by
  let f : ↥Jc → ZMod 2 := fun y => cbit ρ (DeltaX Γ g y)
  have hf : ∀ a b, f (a * b) = f a + f b := by
    intro a b
    dsimp only [f]
    rw [DeltaX_hom, cbit_mul]
  have h := additive_jcA (f := f) hf (coord_lt x)
  rw [← jcA_coord x, coord_jcA (coord_lt x)]
  exact h

private theorem Delta_eq_DeltaX_gen {Γ : Qj → ↥Jc → ↥Jc}
    (h1 : ∀ g a b, Γ g (a * b) = Γ g a * Γ g b)
    (h2 : ∀ g h a, Γ (g * h) a = Γ g a * (g : MulAut ↥Jc) (Γ h ((g : MulAut ↥Jc)⁻¹ a)))
    (hsplit : Native.splitOK = true) (hrel : Native.relOK = true)
    (heps : eps Γ = 0) {k : ℕ} (hk : k < 3) :
    Delta Γ (qA k) = DeltaX Γ (qA k) := by
  funext x
  apply eq_of_cbit_eq
  intro ρ hρ
  have hleft := cbit_delta_qA (Γ := Γ) h1 hk ρ (coord x) (coord_lt x)
  rw [← jcA_coord x]
  rw [hleft, cbit_DeltaX_bsum Γ (qA k) ρ (jcA (coord x)), coord_jcA (coord_lt x)]
  apply bsum_congr
  intro b hb
  have hV : cbit ρ (Delta Γ (qA k) (jcA (2 ^ b))) = Vvec Γ (100 * k + 10 * b + ρ) := by
    simp only [Vvec]
    rw [show (100 * k + 10 * b + ρ) / 100 = k by omega,
      show (100 * k + 10 * b + ρ) / 10 % 10 = b by omega,
      show (100 * k + 10 * b + ρ) % 10 = ρ by omega]
  rw [hV, split_unknown_eq h1 h2 hsplit hrel hk hb hρ, heps, mul_zero, add_zero]
  rfl

private theorem Delta_eq_DeltaX_word {Γ : Qj → ↥Jc → ↥Jc}
    (h2 : ∀ g h a, Γ (g * h) a = Γ g a * (g : MulAut ↥Jc) (Γ h ((g : MulAut ↥Jc)⁻¹ a)))
    (hgen : ∀ k < 3, Delta Γ (qA k) = DeltaX Γ (qA k))
    (w : List ℕ) (hw : ∀ k ∈ w, k < 3) :
    Delta Γ (qWord w) = DeltaX Γ (qWord w) := by
  induction w with
  | nil =>
    rw [qWord_nil]
    funext x
    rw [Delta_one Γ h2]
    exact (DeltaX_one Γ x).symm
  | cons k w ih =>
    have hk : k < 3 := hw k (by simp)
    have hw' : ∀ j ∈ w, j < 3 := fun j hj => hw j (by simp [hj])
    rw [qWord_cons]
    funext x
    rw [Delta_cocycle h2 (qA_mem hk) (qWord_mem hw'), DeltaX_cocycle,
      show Delta Γ (qA k) (qWord w x) = DeltaX Γ (qA k) (qWord w x) from
        congrFun (hgen k hk) _,
      show Delta Γ (qWord w) x = DeltaX Γ (qWord w) x from congrFun (ih hw') x]

private theorem Delta_eq_DeltaX_of_mem {Γ : Qj → ↥Jc → ↥Jc}
    (h2 : ∀ g h a, Γ (g * h) a = Γ g a * (g : MulAut ↥Jc) (Γ h ((g : MulAut ↥Jc)⁻¹ a)))
    (hgen : ∀ k < 3, Delta Γ (qA k) = DeltaX Γ (qA k))
    {g : MulAut ↥Jc} (hg : g ∈ Qj) :
    Delta Γ g = DeltaX Γ g := by
  obtain ⟨w, hw, rfl⟩ := exists_qWord hg
  exact Delta_eq_DeltaX_word h2 hgen w hw

private theorem fixT_mem : Native.fixT ∈ Native.splitChecks :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self)))

private theorem fixT_of (h : Native.splitOK = true) : Native.fixT = true :=
  all_id_eq_true h _ fixT_mem

private theorem gl_zero_one (h : Native.splitOK = true) : Native.gl 0 1 = 1 := by
  have hf := fixT_of h
  rw [Native.fixT, Bool.and_eq_true_iff] at hf
  simpa [beq_iff_eq] using hf.1

private theorem gl_one_one (h : Native.splitOK = true) : Native.gl 1 1 = 1 := by
  have hf := fixT_of h
  rw [Native.fixT, Bool.and_eq_true_iff] at hf
  simpa [beq_iff_eq] using hf.2

private theorem gcol_lt (k b : ℕ) : Native.gcol k b < 1024 := by
  unfold Native.gcol
  apply foldr_xor_lt
  intro rho hrho
  exact two_pow_lt_1024 (mem_ten_lt hrho)

private theorem bsum_gcol (k b : ℕ) (f : ℕ → ZMod 2) :
    bsum 300 (Native.gcol k b) f =
      (Native.ten.map (fun rho =>
        if Native.gamma0.testBit (100 * k + 10 * b + rho) then f rho else 0)).sum := by
  unfold Native.gcol
  rw [bsum_foldr_ite]
  apply congrArg List.sum
  apply List.map_congr_left
  intro rho hrho
  rw [bsum_two_pow (n := 300) (by have := mem_ten_lt hrho; omega)]

private theorem gcol_testBit (k b ρ : ℕ) (hρ : ρ < 10) :
    (Native.gcol k b).testBit ρ = Native.gamma0.testBit (100 * k + 10 * b + ρ) := by
  have h := bsum_gcol k b (fun i => if i = ρ then (1 : ZMod 2) else 0)
  rw [bsum_300_eq_10 (gcol_lt k b), bsum_one_hot hρ] at h
  have hrhs : (Native.ten.map (fun rho =>
        if Native.gamma0.testBit (100 * k + 10 * b + rho) then
          (if rho = ρ then (1 : ZMod 2) else 0) else 0)).sum =
      if Native.gamma0.testBit (100 * k + 10 * b + ρ) then 1 else 0 := by
    rw [ten_sum, Finset.sum_eq_single ρ]
    · simp
    · intro c _ hc
      simp [hc]
    · intro hmem
      exact absurd (Finset.mem_range.mpr hρ) hmem
  rw [hrhs] at h
  by_cases hb : (Native.gcol k b).testBit ρ <;>
    by_cases hx : Native.gamma0.testBit (100 * k + 10 * b + ρ) <;> simp [hb, hx] at h ⊢

private noncomputable def G0fun (k : ℕ) : ↥Jc →* ↥Jc where
  toFun x := jcA (colAct (fun b => Native.gcol k b) (coord x))
  map_one' := by simp [colAct_zero, jcA_zero, coord_one]
  map_mul' := by
    intro a b
    rw [coord_mul, colAct_xor, jcA_xor]

private theorem G0fun_jcA (k : ℕ) {m : ℕ} (hm : m < 1024) :
    G0fun k (jcA m) = jcA (colAct (fun b => Native.gcol k b) m) := by
  change jcA (colAct (fun b => Native.gcol k b) (coord (jcA m))) = _
  rw [coord_jcA hm]

private theorem cbit_G0fun (k m ρ : ℕ) (hm : m < 1024) (hρ : ρ < 10) :
    cbit ρ (G0fun k (jcA m)) =
      bsum 10 m (fun b => if Native.gamma0.testBit (100 * k + 10 * b + ρ) then 1 else 0) := by
  have h := cbit_apply_hom (f := G0fun k) ρ m hm
  rw [h]
  apply bsum_congr
  intro b hb
  have hx : G0fun k (jcA (2 ^ b)) = jcA (Native.gcol k b) := by
    rw [G0fun_jcA k (two_pow_lt_1024 hb), colAct_two_pow (fun b => Native.gcol k b) hb]
  rw [hx, cbit_jcA (gcol_lt k b) hρ, gcol_testBit k b ρ hρ]

private theorem bsum_add {n m : ℕ} (f g : ℕ → ZMod 2) :
    bsum n m (fun i => f i + g i) = bsum n m f + bsum n m g := by
  simp only [bsum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : m.testBit i <;> simp [h]

private theorem Delta_eq_DeltaX_G0_gen {Γ : Qj → ↥Jc → ↥Jc}
    (h1 : ∀ g a b, Γ g (a * b) = Γ g a * Γ g b)
    (h2 : ∀ g h a, Γ (g * h) a = Γ g a * (g : MulAut ↥Jc) (Γ h ((g : MulAut ↥Jc)⁻¹ a)))
    (hsplit : Native.splitOK = true) (hrel : Native.relOK = true)
    (heps : eps Γ = 1) {k : ℕ} (hk : k < 3) :
    ∀ x : ↥Jc, Delta Γ (qA k) x = DeltaX Γ (qA k) x * G0fun k x := by
  intro x
  apply eq_of_cbit_eq
  intro ρ hρ
  have hleft := cbit_delta_qA (Γ := Γ) h1 hk ρ (coord x) (coord_lt x)
  rw [← jcA_coord x]
  rw [hleft, cbit_mul, cbit_DeltaX_bsum Γ (qA k) ρ (jcA (coord x)), coord_jcA (coord_lt x),
    cbit_G0fun k (coord x) ρ (coord_lt x) hρ]
  rw [← bsum_add]
  apply bsum_congr
  intro b hb
  have hV : cbit ρ (Delta Γ (qA k) (jcA (2 ^ b))) = Vvec Γ (100 * k + 10 * b + ρ) := by
    simp only [Vvec]
    rw [show (100 * k + 10 * b + ρ) / 100 = k by omega,
      show (100 * k + 10 * b + ρ) / 10 % 10 = b by omega,
      show (100 * k + 10 * b + ρ) % 10 = ρ by omega]
  rw [hV, split_unknown_eq h1 h2 hsplit hrel hk hb hρ, heps, mul_one]
  rfl

private theorem qA_tA_zero (h : Native.splitOK = true) : qA 0 tA = tA := by
  rw [tA, qA_jcA (by norm_num)]
  rw [show CFSG.Sporadic.Co2Smith.Native.glNJT 0 1 = 1 from by
    simpa [Native.gl] using gl_zero_one h]

private theorem qA_tA_one (h : Native.splitOK = true) : qA 1 tA = tA := by
  rw [tA, qA_jcA (by norm_num)]
  rw [show CFSG.Sporadic.Co2Smith.Native.glNJT 1 1 = 1 from by
    simpa [Native.gl] using gl_one_one h]

private theorem colAct_one (c : ℕ → ℕ) : colAct c 1 = c 0 := by
  have h := colAct_two_pow (c := c) (i := 0) (by norm_num : 0 < 10)
  simpa using h

private theorem eq_of_add_eq_add_add {a b c d e : ZMod 2} (h : a + b = c + d + e) :
    e = a + c + b + d := by
  have h0 : (a + b) + (a + b) = 0 := add_self_eq_zero' _
  have hh : (c + d + e) + (a + b) = 0 := by rw [← h]; exact h0
  have hh' : e + (a + b + c + d) = 0 := by
    rw [← hh]
    abel
  have he : e = a + b + c + d := eq_of_add_eq_zero' hh'
  rw [he]
  abel

private theorem G0fun_tA_eq {Γ : Qj → ↥Jc → ↥Jc}
    (h1 : ∀ g a b, Γ g (a * b) = Γ g a * Γ g b)
    (h2 : ∀ g h a, Γ (g * h) a = Γ g a * (g : MulAut ↥Jc) (Γ h ((g : MulAut ↥Jc)⁻¹ a)))
    (hsplit : Native.splitOK = true) (hrel : Native.relOK = true)
    (heps : eps Γ = 1) {k : ℕ} (hk : k < 3) (hfix : qA k tA = tA) {u : ↥Jc}
    (hu : Γ ⟨qA k, qA_mem hk⟩ tA = u * qA k u) :
    G0fun k tA = (u * Xfun Γ tA) * qA k (u * Xfun Γ tA) := by
  have hgen := Delta_eq_DeltaX_G0_gen h1 h2 hsplit hrel heps hk tA
  have hdelta : Delta Γ (qA k) tA = u * qA k u := by
    rw [Delta, Gam_of_mem (qA_mem hk), hfix]
    exact hu
  have hdeltaX : DeltaX Γ (qA k) tA = Xfun Γ tA * qA k (Xfun Γ tA) := by
    rw [DeltaX, hfix]
  rw [hdelta, hdeltaX] at hgen
  apply eq_of_cbit_eq
  intro ρ hρ
  have hc := congrArg (fun z => cbit ρ z) hgen
  simp only [cbit_mul] at hc
  rw [map_mul]
  simp only [cbit_mul]
  simpa [add_assoc] using eq_of_add_eq_add_add hc

private theorem eps_ne_one {Γ : Qj → ↥Jc → ↥Jc}
    (h1 : ∀ g a b, Γ g (a * b) = Γ g a * Γ g b)
    (h2 : ∀ g h a, Γ (g * h) a = Γ g a * (g : MulAut ↥Jc) (Γ h ((g : MulAut ↥Jc)⁻¹ a)))
    (hsplit : Native.splitOK = true) (hrel : Native.relOK = true)
    (h3 : ∃ u : ↥Jc, ∀ g : Qj, (g : MulAut ↥Jc) tA = tA → Γ g tA = u * (g : MulAut ↥Jc) u)
    (heps : eps Γ = 1) : False := by
  obtain ⟨u, hu⟩ := h3
  have hfix0 : qA 0 tA = tA := qA_tA_zero hsplit
  have hfix1 : qA 1 tA = tA := qA_tA_one hsplit
  have hG0 := G0fun_tA_eq h1 h2 hsplit hrel heps (k := 0) (by norm_num) hfix0
    (hu ⟨qA 0, qA_mem (by norm_num)⟩ hfix0)
  have hG1 := G0fun_tA_eq h1 h2 hsplit hrel heps (k := 1) (by norm_num) hfix1
    (hu ⟨qA 1, qA_mem (by norm_num)⟩ hfix1)
  have hc0 : coord (G0fun 0 tA) = Native.gcol 0 0 := by
    rw [tA, G0fun_jcA 0 (by norm_num), colAct_one, coord_jcA (gcol_lt 0 0)]
  have hc1 : coord (G0fun 1 tA) = Native.gcol 1 0 := by
    rw [tA, G0fun_jcA 1 (by norm_num), colAct_one, coord_jcA (gcol_lt 1 0)]
  have hcoord : ∀ k < 3, coord ((u * Xfun Γ tA) * qA k (u * Xfun Γ tA)) =
      coord (u * Xfun Γ tA) ^^^ CFSG.Sporadic.Co2Smith.Native.glNJT k (coord (u * Xfun Γ tA)) := by
    intro k hk
    set m : ℕ := coord (u * Xfun Γ tA) with hm
    have hw : u * Xfun Γ tA = jcA m := (jcA_coord (u * Xfun Γ tA)).symm
    rw [hw, qA_jcA hk, ← jcA_xor]
    exact coord_jcA (Nat.xor_lt_two_pow (n := 10) (coord_lt (u * Xfun Γ tA)) (glNJT_lt hk m))
  have h0 : Native.gcol 0 0 =
      coord (u * Xfun Γ tA) ^^^ CFSG.Sporadic.Co2Smith.Native.glNJT 0 (coord (u * Xfun Γ tA)) := by
    rw [← hc0, hG0, hcoord 0 (by norm_num)]
  have h1eq : Native.gcol 1 0 =
      coord (u * Xfun Γ tA) ^^^ CFSG.Sporadic.Co2Smith.Native.glNJT 1 (coord (u * Xfun Γ tA)) := by
    rw [← hc1, hG1, hcoord 1 (by norm_num)]
  exact noW_spec hsplit (coord (u * Xfun Γ tA)) (coord_lt _) ⟨h0, h1eq⟩

private theorem split_of_fixed_Qj_aux (Γ : Qj → ↥Jc → ↥Jc)
    (h1 : ∀ g a b, Γ g (a * b) = Γ g a * Γ g b)
    (h2 : ∀ g h a, Γ (g * h) a = Γ g a * (g : MulAut ↥Jc) (Γ h ((g : MulAut ↥Jc)⁻¹ a)))
    (h3 : ∃ u : ↥Jc, ∀ g : Qj, (g : MulAut ↥Jc) tA = tA → Γ g tA = u * (g : MulAut ↥Jc) u) :
    ∃ X : ↥Jc →* ↥Jc, ∀ g a, Γ g a = X a * (g : MulAut ↥Jc) (X ((g : MulAut ↥Jc)⁻¹ a)) := by
  have hcert : Native.cocycleOK = true := Certificates.certificate719050
  have hdual := dualOK_of_cocycle hcert
  have hsplit := splitOK_of_cocycle hcert
  have hrel : Native.relOK = true := relOK_of_dualOK hdual
  by_cases heps : eps Γ = 0
  · refine ⟨Xfun Γ, ?_⟩
    intro g a
    have hgen : ∀ k < 3, Delta Γ (qA k) = DeltaX Γ (qA k) :=
      fun k hk => Delta_eq_DeltaX_gen h1 h2 hsplit hrel heps hk
    have hDelta : Delta Γ (g : MulAut ↥Jc) = DeltaX Γ (g : MulAut ↥Jc) :=
      Delta_eq_DeltaX_of_mem h2 hgen g.2
    have hda : Γ g a = Delta Γ (g : MulAut ↥Jc) ((g : MulAut ↥Jc)⁻¹ a) := by
      rw [Delta, Gam_of_mem g.2]
      have hgg : (g : MulAut ↥Jc) ((g : MulAut ↥Jc)⁻¹ a) = a := by
        simpa using MulEquiv.apply_symm_apply (g : MulAut ↥Jc) a
      rw [hgg]
    rw [hda, congrFun hDelta ((g : MulAut ↥Jc)⁻¹ a), DeltaX]
    have hgg : (g : MulAut ↥Jc) ((g : MulAut ↥Jc)⁻¹ a) = a := by
      simpa using MulEquiv.apply_symm_apply (g : MulAut ↥Jc) a
    rw [hgg]
  · exfalso
    exact eps_ne_one h1 h2 hsplit hrel h3 (zmod2_eq_one_of_ne_zero heps)

private noncomputable def gam (γ : Qj → ↥Jc → ZMod 2) (g : MulAut ↥Jc) : ↥Jc → ZMod 2 := by
  classical
  exact if h : g ∈ Qj then γ ⟨g, h⟩ else 0

private theorem gam_of_mem {γ : Qj → ↥Jc → ZMod 2} {g : MulAut ↥Jc} (hg : g ∈ Qj) :
    gam γ g = γ ⟨g, hg⟩ := by
  rw [gam]
  exact dif_pos hg

private noncomputable def del (γ : Qj → ↥Jc → ZMod 2) (g : MulAut ↥Jc) : ↥Jc → ZMod 2 :=
  fun x => gam γ g (g x)

private theorem del_add {γ : Qj → ↥Jc → ZMod 2}
    (h1 : ∀ g a b, γ g (a * b) = γ g a + γ g b)
    {g : MulAut ↥Jc} (hg : g ∈ Qj) (a b : ↥Jc) :
    del γ g (a * b) = del γ g a + del γ g b := by
  simp only [del, gam_of_mem hg, map_mul]
  exact h1 ⟨g, hg⟩ (g a) (g b)

private theorem del_mul {γ : Qj → ↥Jc → ZMod 2}
    (h2 : ∀ g h a, γ (g * h) a = γ g a + γ h ((g : MulAut ↥Jc)⁻¹ a))
    {g h : MulAut ↥Jc} (hg : g ∈ Qj) (hh : h ∈ Qj) (x : ↥Jc) :
    del γ (g * h) x = del γ g (h x) + del γ h x := by
  have hgh : g * h ∈ Qj := Qj.mul_mem hg hh
  have hsub : (⟨g * h, hgh⟩ : Qj) = ⟨g, hg⟩ * ⟨h, hh⟩ := Subtype.ext rfl
  have hx : (g * h) x = g (h x) := rfl
  have hinv : ((⟨g, hg⟩ : Qj) : MulAut ↥Jc)⁻¹ (g (h x)) = h x := by
    show (g : MulAut ↥Jc).symm (g (h x)) = h x
    exact MulEquiv.symm_apply_apply g (h x)
  calc
    del γ (g * h) x = γ ⟨g * h, hgh⟩ (g (h x)) := by rw [del, gam_of_mem hgh, hx]
    _ = γ (⟨g, hg⟩ * ⟨h, hh⟩) (g (h x)) := by rw [hsub]
    _ = γ ⟨g, hg⟩ (g (h x)) + γ ⟨h, hh⟩ (((⟨g,hg⟩ : Qj) : MulAut ↥Jc)⁻¹ (g (h x))) :=
      h2 _ _ _
    _ = γ ⟨g, hg⟩ (g (h x)) + γ ⟨h, hh⟩ (h x) := by rw [hinv]
    _ = del γ g (h x) + del γ h x := by
      rw [del, del, gam_of_mem hg, gam_of_mem hh]

private theorem del_one {γ : Qj → ↥Jc → ZMod 2}
    (h2 : ∀ g h a, γ (g * h) a = γ g a + γ h ((g : MulAut ↥Jc)⁻¹ a))
    (x : ↥Jc) : del γ 1 x = 0 := by
  have h := del_mul (γ := γ) h2 (g := 1) (h := 1) Qj.one_mem Qj.one_mem x
  have h1x : (1 : MulAut ↥Jc) x = x := rfl
  rw [h1x] at h
  simp only [one_mul] at h
  have hzero : del γ 1 x + del γ 1 x = 0 := by
    rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  rw [hzero] at h
  exact h

private noncomputable def Uvec (γ : Qj → ↥Jc → ZMod 2) (i : ℕ) : ZMod 2 :=
  del γ (qA (i / 10)) (jcA (2 ^ (i % 10)))

private theorem bsum_shiftLeft (n m w : ℕ) (hm : m + w ≤ n) {v : ℕ} (hv : v < 2 ^ w)
    (u : ℕ → ZMod 2) :
    bsum n (v <<< m) u = bsum w v (fun b => u (m + b)) := by
  classical
  simp only [bsum]
  set f : ℕ → ZMod 2 := fun j => if (v <<< m).testBit j then u j else 0 with hf
  set g : ℕ → ZMod 2 := fun b => if v.testBit b then u (m + b) else 0 with hg
  have hsub : (Finset.range w).image (fun b => m + b) ⊆ Finset.range n := by
    intro j hj
    simp only [Finset.mem_image, Finset.mem_range] at hj
    obtain ⟨b, hb, rfl⟩ := hj
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Nat.add_lt_add_left hb m) hm)
  have hzero : ∀ j ∈ Finset.range n, j ∉ (Finset.range w).image (fun b => m + b) → f j = 0 := by
    intro j _ hnot
    simp only [Finset.mem_image, Finset.mem_range] at hnot
    have hnot' : ∀ b < w, m + b ≠ j := fun b hb hbj => hnot ⟨b, hb, hbj⟩
    simp only [f, hf]
    rw [Nat.testBit_shiftLeft]
    by_cases hjm : m ≤ j
    · have hw : w ≤ j - m := by
        by_contra h
        exact hnot' (j - m) (by omega) (Nat.add_sub_cancel' hjm)
      rw [decide_eq_true_eq.mpr (by omega : j ≥ m), Bool.true_and,
        testBit_eq_false_of_lt_pow hv hw]
      simp
    · rw [decide_eq_false (by omega : ¬ j ≥ m)]
      simp
  rw [← Finset.sum_subset hsub hzero, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro b hb
    simp only [f, hf, g, hg, Finset.mem_range] at hb ⊢
    rw [Nat.testBit_shiftLeft]
    rw [decide_eq_true_eq.mpr (by omega : m + b ≥ m), Bool.true_and, Nat.add_sub_cancel_left]
  · intro b _ b' _ h
    exact Nat.add_left_cancel h

private theorem del_qWord {γ : Qj → ↥Jc → ZMod 2}
    (h1 : ∀ g a b, γ g (a * b) = γ g a + γ g b)
    (h2 : ∀ g h a, γ (g * h) a = γ g a + γ h ((g : MulAut ↥Jc)⁻¹ a))
    (w : List ℕ) (hw : ∀ k ∈ w, k < 3) (m : ℕ) (hm : m < 1024) :
    del γ (qWord w) (jcA m) = bsum 30 (Native.rowOf w m) (Uvec γ) := by
  induction w generalizing m with
  | nil =>
    simp only [qWord_nil, Native.rowOf, bsum_zero]
    exact del_one h2 _
  | cons k w ih =>
    have hk : k < 3 := hw k (by simp)
    have hw' : ∀ j ∈ w, j < 3 := fun j hj => hw j (by simp [hj])
    have hqk : qA k ∈ Qj := qA_mem hk
    have hmem : qWord w ∈ Qj := qWord_mem hw'
    have hxlt : wordAct w m < 1024 := wordAct_lt hw' hm
    have hUb : ∀ b < 10, del γ (qA k) (jcA (2 ^ b)) = Uvec γ (10 * k + b) := by
      intro b hb
      simp only [Uvec]
      rw [show (10 * k + b) / 10 = k by omega, show (10 * k + b) % 10 = b by omega]
    calc
      del γ (qWord (k :: w)) (jcA m)
          = del γ (qA k) (jcA (wordAct w m)) + del γ (qWord w) (jcA m) := by
            rw [qWord_cons, del_mul h2 hqk hmem, qWord_jcA hw' m]
      _ = bsum 10 (wordAct w m) (fun b => del γ (qA k) (jcA (2 ^ b))) +
            bsum 30 (Native.rowOf w m) (Uvec γ) := by
            rw [additive_jcA (del_add h1 hqk) hxlt, ih hw' m hm]
      _ = bsum 10 (wordAct w m) (fun b => Uvec γ (10 * k + b)) +
            bsum 30 (Native.rowOf w m) (Uvec γ) := by
            congr 1
            simp only [bsum]
            apply Finset.sum_congr rfl
            intro b hb
            rw [hUb b (by simpa using hb)]
      _ = bsum 30 (Native.rowOf (k :: w) m) (Uvec γ) := by
            rw [show Native.rowOf (k :: w) m =
              Native.rowOf w m ^^^ (wordAct w m <<< (10 * k)) from rfl]
            rw [bsum_xor]
            rw [bsum_shiftLeft (n := 30) (m := 10 * k) (w := 10) (by omega) hxlt]
            rw [add_comm]

private theorem bsum_dualTarget_ten (γ : Qj → ↥Jc → ZMod 2) (k b : ℕ) :
    (List.map ((fun m => bsum 30 m (Uvec γ)) ∘ fun bp =>
      if (Native.gl k (2 ^ b)).testBit bp then cocycleDualP[bp]! else 0) Native.ten).sum =
      bsum 10 (Native.gl k (2 ^ b))
        (fun bp => bsum 30 (cocycleDualP[bp]!) (Uvec γ)) := by
  rw [ten_sum]
  simp only [bsum, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro bp _
  by_cases hbit : (Native.gl k (2 ^ b)).testBit bp
  · simp [hbit]
  · simp [hbit, bsum_zero]

private theorem bsum_dualTarget (γ : Qj → ↥Jc → ZMod 2) (k b : ℕ) (hk : k < 3) (hb : b < 10) :
    bsum 30 (Native.dualTarget k b) (Uvec γ) =
      Uvec γ (10 * k + b) + bsum 30 (cocycleDualP[b]!) (Uvec γ) +
        bsum 10 (Native.gl k (2 ^ b))
          (fun bp => bsum 30 (cocycleDualP[bp]!) (Uvec γ)) := by
  rw [Native.dualTarget, bsum_xorList]
  simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_apply]
  rw [bsum_two_pow (by omega)]
  rw [bsum_dualTarget_ten]
  abel

private theorem dualCombOK_mem : Native.dualCombOK ∈ Native.dualChecks :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self)))

private theorem dualOK_spec (h : Native.dualOK = true) :
    Native.relOK = true ∧ ∀ u < 30,
      Native.xorRowsByMask Native.dualRows (cocycleDualComb[u]!) =
        Native.dualTarget (u / 10) (u % 10) := by
  have hrel : Native.relOK = true := all_id_eq_true h _ relOK_mem
  have hcomb : Native.dualCombOK = true := all_id_eq_true h _ dualCombOK_mem
  simp only [Native.dualCombOK, List.all_eq_true] at hcomb
  exact ⟨hrel, fun u hu => by simpa [beq_iff_eq] using hcomb u (List.mem_range.mpr hu)⟩

private theorem bsum_dualRows_eq_zero {γ : Qj → ↥Jc → ZMod 2}
    (h1 : ∀ g a b, γ g (a * b) = γ g a + γ g b)
    (h2 : ∀ g h a, γ (g * h) a = γ g a + γ h ((g : MulAut ↥Jc)⁻¹ a))
    (hrel : Native.relOK = true) (m : ℕ) :
    bsum 30 (Native.xorRowsByMask Native.dualRows m) (Uvec γ) = 0 := by
  apply bsum_xorRowsFrom_eq_zero
  intro x hx
  simp only [Native.dualRows, List.mem_flatMap, List.mem_map, List.mem_range] at hx
  obtain ⟨r, hr, j, hj, rfl⟩ := hx
  obtain ⟨hw, hact⟩ := relOK_spec hrel r hr
  have hq : qWord r = 1 := qWord_of_rel hw hact
  rw [← del_qWord h1 h2 r hw (2 ^ j) (two_pow_lt_1024 hj), hq, del_one h2]

private theorem eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  have hbb : b + b = 0 := by
    rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  exact add_right_cancel (h.trans hbb.symm)

private theorem dual_unknown_eq {γ : Qj → ↥Jc → ZMod 2}
    (h1 : ∀ g a b, γ g (a * b) = γ g a + γ g b)
    (h2 : ∀ g h a, γ (g * h) a = γ g a + γ h ((g : MulAut ↥Jc)⁻¹ a))
    (hcert : Native.dualOK = true) {k b : ℕ} (hk : k < 3) (hb : b < 10) :
    Uvec γ (10 * k + b) = bsum 30 (cocycleDualP[b]!) (Uvec γ) +
      bsum 10 (Native.gl k (2 ^ b))
        (fun bp => bsum 30 (cocycleDualP[bp]!) (Uvec γ)) := by
  obtain ⟨hrel, hcomb⟩ := dualOK_spec hcert
  have hrow : bsum 30
      (Native.xorRowsByMask Native.dualRows (cocycleDualComb[10 * k + b]!)) (Uvec γ) = 0 :=
    bsum_dualRows_eq_zero h1 h2 hrel _
  rw [hcomb (10 * k + b) (by omega)] at hrow
  rw [show (10 * k + b) / 10 = k by omega, show (10 * k + b) % 10 = b by omega] at hrow
  rw [bsum_dualTarget γ k b hk hb] at hrow
  exact eq_of_add_eq_zero (by simpa [add_assoc] using hrow)

private noncomputable def fdual (γ : Qj → ↥Jc → ZMod 2) : ↥Jc → ZMod 2 :=
  fun x => bsum 10 (coord x) (fun b => bsum 30 (cocycleDualP[b]!) (Uvec γ))

private theorem fdual_add (γ : Qj → ↥Jc → ZMod 2) (a b : ↥Jc) :
    fdual γ (a * b) = fdual γ a + fdual γ b := by
  simp only [fdual, coord_mul, bsum_xor]

private theorem fdual_jcA (γ : Qj → ↥Jc → ZMod 2) {b : ℕ} (hb : b < 10) :
    fdual γ (jcA (2 ^ b)) = bsum 30 (cocycleDualP[b]!) (Uvec γ) := by
  simp only [fdual]
  rw [coord_jcA (two_pow_lt_1024 hb), bsum_two_pow hb]

private theorem del_eq_delf_gen {γ : Qj → ↥Jc → ZMod 2}
    (h1 : ∀ g a b, γ g (a * b) = γ g a + γ g b)
    (h2 : ∀ g h a, γ (g * h) a = γ g a + γ h ((g : MulAut ↥Jc)⁻¹ a))
    (hcert : Native.dualOK = true) {k : ℕ} (hk : k < 3) (x : ↥Jc) :
    del γ (qA k) x = fdual γ x + fdual γ (qA k x) := by
  have hqk : qA k ∈ Qj := qA_mem hk
  have hbasis : ∀ b < 10, del γ (qA k) (jcA (2 ^ b)) =
      fdual γ (jcA (2 ^ b)) + fdual γ (qA k (jcA (2 ^ b))) := by
    intro b hb
    have hU : del γ (qA k) (jcA (2 ^ b)) = Uvec γ (10 * k + b) := by
      simp only [Uvec]
      rw [show (10 * k + b) / 10 = k by omega, show (10 * k + b) % 10 = b by omega]
    rw [hU, dual_unknown_eq h1 h2 hcert hk hb, fdual_jcA γ hb]
    rw [fdual, qA_jcA hk, coord_jcA (glNJT_lt hk (2 ^ b))]
    rfl
  let g : ↥Jc → ZMod 2 := fun y => del γ (qA k) y + fdual γ y + fdual γ (qA k y)
  have hgadd : ∀ a b, g (a * b) = g a + g b := by
    intro a b
    simp only [g, map_mul, del_add h1 hqk, fdual_add]
    ac_rfl
  have hgzero : ∀ b < 10, g (jcA (2 ^ b)) = 0 := by
    intro b hb
    simp only [g]
    rw [hbasis b hb]
    rw [show (fdual γ (jcA (2 ^ b)) + fdual γ (qA k (jcA (2 ^ b)))) +
        fdual γ (jcA (2 ^ b)) + fdual γ (qA k (jcA (2 ^ b))) =
        (fdual γ (jcA (2 ^ b)) + fdual γ (qA k (jcA (2 ^ b)))) +
          (fdual γ (jcA (2 ^ b)) + fdual γ (qA k (jcA (2 ^ b)))) from by ac_rfl]
    exact add_self_eq_zero' _
  have hzero : g x = 0 := additive_eq_zero (f := g) hgadd hgzero x
  simp only [g] at hzero
  exact eq_of_add_eq_zero (by simpa [add_assoc] using hzero)

private noncomputable def delf (f : ↥Jc → ZMod 2) (g : MulAut ↥Jc) : ↥Jc → ZMod 2 :=
  fun x => f x + f (g x)

private theorem add_add_add_comm' (a b c : ZMod 2) : (b + c) + (a + b) = a + c := by
  calc
    (b + c) + (a + b) = a + c + (b + b) := by ac_rfl
    _ = a + c := by rw [add_self_eq_zero', add_zero]

private theorem delf_mul (f : ↥Jc → ZMod 2) (g h : MulAut ↥Jc) (x : ↥Jc) :
    delf f (g * h) x = delf f g (h x) + delf f h x := by
  change f x + f (g (h x)) = (f (h x) + f (g (h x))) + (f x + f (h x))
  exact (add_add_add_comm' (f x) (f (h x)) (f (g (h x)))).symm

private theorem delf_one (f : ↥Jc → ZMod 2) (x : ↥Jc) : delf f 1 x = 0 := by
  simp only [delf]
  rw [show (1 : MulAut ↥Jc) x = x from rfl]
  rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]

private theorem del_eq_delf_word {γ : Qj → ↥Jc → ZMod 2}
    (h1 : ∀ g a b, γ g (a * b) = γ g a + γ g b)
    (h2 : ∀ g h a, γ (g * h) a = γ g a + γ h ((g : MulAut ↥Jc)⁻¹ a))
    (hcert : Native.dualOK = true) (w : List ℕ) (hw : ∀ k ∈ w, k < 3) (x : ↥Jc) :
    del γ (qWord w) x = delf (fdual γ) (qWord w) x := by
  induction w with
  | nil => rw [qWord_nil]; exact (del_one h2 x).trans (delf_one (fdual γ) x).symm
  | cons k w ih =>
    have hk : k < 3 := hw k (by simp)
    have hw' : ∀ j ∈ w, j < 3 := fun j hj => hw j (by simp [hj])
    rw [qWord_cons, del_mul h2 (qA_mem hk) (qWord_mem hw'), delf_mul]
    rw [del_eq_delf_gen h1 h2 hcert hk, ih hw']
    simp only [delf]

private theorem dual_cocycle_aux {γ : Qj → ↥Jc → ZMod 2}
    (h1 : ∀ g a b, γ g (a * b) = γ g a + γ g b)
    (h2 : ∀ g h a, γ (g * h) a = γ g a + γ h ((g : MulAut ↥Jc)⁻¹ a))
    (hcert : Native.dualOK = true) :
    ∃ f : ↥Jc → ZMod 2, (∀ a b, f (a * b) = f a + f b) ∧
      ∀ g a, γ g a = f ((g : MulAut ↥Jc)⁻¹ a) + f a := by
  refine ⟨fdual γ, fdual_add γ, ?_⟩
  intro g a
  obtain ⟨w, hw, hqw⟩ := exists_qWord g.2
  have hdel : γ g a = del γ (g : MulAut ↥Jc) ((g : MulAut ↥Jc)⁻¹ a) := by
    rw [del, gam_of_mem g.2]
    simp
  rw [hdel, ← hqw]
  rw [del_eq_delf_word h1 h2 hcert w hw]
  simp only [delf]
  have hgg : (qWord w) ((qWord w)⁻¹ a) = a := by
    simpa using MulEquiv.apply_symm_apply (qWord w) a
  rw [hgg]

theorem dual_cocycle_Qj (γ : Qj → ↥Jc → ZMod 2) (h1 : ∀ g a b, γ g (a * b) = γ g a + γ g b)
    (h2 : ∀ g h a, γ (g * h) a = γ g a + γ h ((g : MulAut ↥Jc)⁻¹ a)) :
    ∃ f : ↥Jc → ZMod 2, (∀ a b, f (a * b) = f a + f b) ∧
      ∀ g a, γ g a = f ((g : MulAut ↥Jc)⁻¹ a) + f a := by
  have hcert : Native.cocycleOK = true := Certificates.certificate719050
  exact dual_cocycle_aux h1 h2 (dualOK_of_cocycle hcert)

theorem split_of_fixed_Qj (Γ : Qj → ↥Jc → ↥Jc) (h1 : ∀ g a b, Γ g (a * b) = Γ g a * Γ g b)
    (h2 : ∀ g h a, Γ (g * h) a = Γ g a * (g : MulAut ↥Jc) (Γ h ((g : MulAut ↥Jc)⁻¹ a)))
    (h3 : ∃ u : ↥Jc, ∀ g : Qj, (g : MulAut ↥Jc) tA = tA → Γ g tA = u * (g : MulAut ↥Jc) u) :
    ∃ X : ↥Jc →* ↥Jc, ∀ g a, Γ g a = X a * (g : MulAut ↥Jc) (X ((g : MulAut ↥Jc)⁻¹ a)) :=
  split_of_fixed_Qj_aux Γ h1 h2 h3

end CFSG.Sporadic.Co2Jc
