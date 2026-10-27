module

public import Certificates.Data.CFSGNative.MonsterB.P0Rank
public import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.Monster.B.TwoA.Sp8.P0Rank

open MonsterB.P0Rank

private theorem xor_mod_two (a b : ℕ) :
    (a ^^^ b) % 2 = (a % 2) ^^^ (b % 2) := by
  have h := Nat.xor_mod_two_pow (a := a) (b := b) (n := 1)
  simpa using h

private theorem xor_mul_two (a b : ℕ) :
    (a ^^^ b) * 2 = a * 2 ^^^ b * 2 := by
  have h : (a ^^^ b) <<< 1 = a <<< 1 ^^^ b <<< 1 := Nat.shiftLeft_xor_distrib
  simpa [Nat.shiftLeft_eq] using h

private theorem two_mul_xor (a b : ℕ) :
    2 * (a ^^^ b) = 2 * a ^^^ 2 * b := by
  rw [Nat.mul_comm 2 (a ^^^ b), Nat.mul_comm 2 a, Nat.mul_comm 2 b]
  exact xor_mul_two a b

private theorem two_mul_div_two_xor_mod_two (x : ℕ) :
    2 * (x / 2) ^^^ (x % 2) = x := by
  have h : 2 ^ 1 * (x / 2) ^^^ (x % 2) = 2 ^ 1 * (x / 2) + x % 2 := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add (x / 2) (by omega) j]
    by_cases hji : j < 1
    · rw [if_pos hji]
      have hz : (2 ^ 1 * (x / 2)).testBit j = false := by
        rw [Nat.testBit_two_pow_mul]
        simp [Nat.not_le.mpr hji]
      rw [hz, Bool.false_xor]
    · rw [if_neg hji]
      have hge : 1 ≤ j := Nat.le_of_not_lt hji
      have h1 : (2 ^ 1 * (x / 2)).testBit j = (x / 2).testBit (j - 1) := by
        rw [Nat.testBit_two_pow_mul]
        simp [hge]
      have hlt : (x % 2).testBit j = false := by
        apply Nat.testBit_lt_two_pow
        calc x % 2 < 2 ^ 1 := by omega
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hge
      rw [h1, hlt, Bool.xor_false]
  have hx : 2 ^ 1 * (x / 2) + x % 2 = x := by
    simpa [Nat.pow_one] using Nat.div_add_mod x 2
  rwa [hx] at h

theorem colsAct_zero (cs : List ℕ) : colsAct cs 0 = 0 := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [colsAct, ih]

theorem colsAct_xor (cs : List ℕ) (a b : ℕ) :
    colsAct cs (a ^^^ b) = colsAct cs a ^^^ colsAct cs b := by
  induction cs generalizing a b with
  | nil => simp [colsAct]
  | cons c cs ih =>
    have hc : (if a % 2 ^^^ b % 2 = 1 then c else 0) =
        (if a % 2 = 1 then c else 0) ^^^ (if b % 2 = 1 then c else 0) := by
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
        rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;> simp [ha, hb]
    rw [colsAct.eq_2, xor_mod_two, Nat.xor_div_two, ih, colsAct.eq_2, colsAct.eq_2, hc]
    ac_rfl

theorem colsAct_lt {cs : List ℕ} {w : ℕ} (h : ∀ c ∈ cs, c < 2 ^ w) (x : ℕ) :
    colsAct cs x < 2 ^ w := by
  induction cs generalizing x with
  | nil => simpa [colsAct] using Nat.two_pow_pos w
  | cons c cs ih =>
    rw [colsAct.eq_2]
    refine Nat.xor_lt_two_pow ?_ ?_
    · split_ifs
      · exact h c (by simp)
      · exact Nat.two_pow_pos w
    · exact ih (fun c' hc' => h c' (by simp [hc'])) (x / 2)

theorem colsAct_colsOf {n : ℕ} {f : ℕ → ℕ} (hf : ∀ a b, f (a ^^^ b) = f a ^^^ f b) {x : ℕ}
    (hx : x < 2 ^ n) : colsAct (colsOf n f) x = f x := by
  have hf0 : f 0 = 0 := by
    have h := hf 0 0
    rw [Nat.zero_xor, Nat.xor_self] at h
    exact h
  induction n generalizing f x with
  | zero =>
    have hx0 : x = 0 := by simpa using hx
    subst hx0
    simp [colsOf, colsAct, hf0]
  | succ n ih =>
    have hcols : colsOf (n + 1) f = f 1 :: colsOf n (fun y => f (2 * y)) := by
      simp [colsOf, List.range_succ_eq_map, Nat.pow_succ, Nat.mul_comm]
    have hbit : (if x % 2 = 1 then f 1 else 0) = f (x % 2) := by
      rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h, hf0]
    have hlin : ∀ a b, (fun y => f (2 * y)) (a ^^^ b) =
        (fun y => f (2 * y)) a ^^^ (fun y => f (2 * y)) b := by
      intro a b
      show f (2 * (a ^^^ b)) = f (2 * a) ^^^ f (2 * b)
      rw [two_mul_xor, hf]
    have hx' : x / 2 < 2 ^ n := by
      rw [Nat.pow_succ] at hx
      have h2 : 0 < 2 ^ n := Nat.two_pow_pos n
      omega
    rw [hcols, colsAct.eq_2, hbit, ih (f := fun y => f (2 * y)) hlin hx' hf0,
      ← hf (x % 2) (2 * (x / 2)),
      Nat.xor_comm (x % 2) (2 * (x / 2)), two_mul_div_two_xor_mod_two]

private theorem bool_xor_swap (a b c d : Bool) :
    ((a ^^ b) ^^ (c ^^ d)) = ((a ^^ c) ^^ (b ^^ d)) := by
  rcases a <;> rcases b <;> rcases c <;> rcases d <;> rfl

theorem par_zero : par 0 = false := by
  rw [par.eq_1]
  simp

private theorem par_step (x : ℕ) : par x = ((x % 2 == 1) ^^ par (x / 2)) := by
  rw [par.eq_1]
  by_cases h : x = 0
  · subst h
    simp [par_zero]
  · simp [h]

theorem par_xor (a b : ℕ) : par (a ^^^ b) = (par a ^^ par b) := by
  have key : ∀ s : ℕ, ∀ a b : ℕ, a + b = s → par (a ^^^ b) = (par a ^^ par b) := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro a b hab
      by_cases hab0 : a + b = 0
      · have ha : a = 0 := by omega
        have hb : b = 0 := by omega
        subst ha; subst hb
        simp [par_zero]
      · have hlt : a / 2 + b / 2 < a + b := by omega
        have hbits : ((a % 2 ^^^ b % 2) == 1) =
            ((a % 2 == 1) ^^ (b % 2 == 1)) := by
          rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
            rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;> simp [ha, hb]
        rw [par_step (a ^^^ b), xor_mod_two, Nat.xor_div_two, par_step a, par_step b, hbits,
          ih (a / 2 + b / 2) (by omega) (a / 2) (b / 2) rfl]
        exact bool_xor_swap _ _ _ _
  exact key (a + b) a b rfl

private theorem par_two_mul (y : ℕ) : par (2 * y) = par y := by
  rw [par_step]
  have h1 : (2 * y) % 2 = 0 := by omega
  have h2 : (2 * y) / 2 = y := by omega
  rw [h1, h2]
  simp

private theorem par_land_two_mul (b m x : ℕ) (hb : b = 0 ∨ b = 1) :
    par ((b + 2 * m) &&& x) = ((((b % 2) &&& (x % 2)) == 1) ^^ par (m &&& (x / 2))) := by
  rw [par_step]
  have hmod : ((b + 2 * m) &&& x) % 2 = ((b % 2) &&& (x % 2)) := by
    have h := Nat.and_mod_two_pow (a := (b + 2 * m)) (b := x) (n := 1)
    simpa using h
    
  have hdiv : ((b + 2 * m) &&& x) / 2 = m &&& (x / 2) := by
    rw [Nat.and_div_two]
    have hb2 : (b + 2 * m) / 2 = m := by omega
    rw [hb2]
  rw [hmod, hdiv]

private theorem par_land_eq (b x : ℕ) (hb : b = 0 ∨ b = 1) :
    ((((b % 2) &&& (x % 2)) == 1)) = ((b == 1) && x.testBit 0) := by
  rcases hb with rfl | rfl
  · simp
  · rw [Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]

theorem testBit_colsAct (cs : List ℕ) (x k : ℕ) :
    (colsAct cs x).testBit k = par (maskT cs k &&& x) := by
  induction cs generalizing x with
  | nil => simp [colsAct, maskT, par_zero]
  | cons c cs ih =>
    have hb : (if c.testBit k then 1 else 0) = 0 ∨ (if c.testBit k then 1 else 0) = 1 := by
      split_ifs <;> simp
    have hlow : ((if x % 2 = 1 then c else 0)).testBit k =
        (((if c.testBit k then 1 else 0) == 1) && decide (x % 2 = 1)) := by
      by_cases hx : x % 2 = 1 <;> by_cases hc : c.testBit k <;> simp [hx, hc]
    rw [colsAct.eq_2, Nat.testBit_xor, ih, maskT.eq_2, par_land_two_mul _ _ _ hb,
      par_land_eq _ _ hb, Nat.testBit_zero, hlow]

private theorem foldr_actK_zero (cols : List (List ℕ)) (κ : ℕ) :
    ∀ l : List ℕ,
      l.foldr (fun k y => if κ.testBit k then colsAct (cols.getD k []) y else y) 0 = 0 := by
  intro l
  induction l with
  | nil => rfl
  | cons k l ih =>
    rw [List.foldr_cons, ih]
    split_ifs with hk
    · exact colsAct_zero _
    · rfl

theorem actK_zero (cols : List (List ℕ)) (κ : ℕ) : actK cols κ 0 = 0 := by
  rw [actK.eq_1]
  exact foldr_actK_zero cols κ (List.range cols.length)

private theorem foldr_actK_xor (cols : List (List ℕ)) (κ : ℕ) :
    ∀ l : List ℕ, ∀ a b : ℕ,
      l.foldr (fun k y => if κ.testBit k then colsAct (cols.getD k []) y else y) (a ^^^ b) =
        l.foldr (fun k y => if κ.testBit k then colsAct (cols.getD k []) y else y) a ^^^
          l.foldr (fun k y => if κ.testBit k then colsAct (cols.getD k []) y else y) b := by
  intro l
  induction l with
  | nil => intro a b; simp
  | cons k l ih =>
    intro a b
    rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, ih]
    split_ifs with hk
    · exact colsAct_xor _ _ _
    · rfl

theorem actK_xor (cols : List (List ℕ)) (κ a b : ℕ) :
    actK cols κ (a ^^^ b) = actK cols κ a ^^^ actK cols κ b := by
  rw [actK.eq_1, actK.eq_1, actK.eq_1]
  exact foldr_actK_xor cols κ (List.range cols.length) a b

private theorem foldr_actK_zero_left (cols : List (List ℕ)) (x : ℕ) :
    ∀ l : List ℕ,
      l.foldr (fun k y => if (0 : ℕ).testBit k then colsAct (cols.getD k []) y else y) x = x := by
  intro l
  induction l with
  | nil => rfl
  | cons k l ih =>
    rw [List.foldr_cons, ih, Nat.zero_testBit]
    simp

theorem actK_zero_left (cols : List (List ℕ)) (x : ℕ) : actK cols 0 x = x := by
  rw [actK.eq_1]
  exact foldr_actK_zero_left cols x (List.range cols.length)

private theorem foldr_actK_lt (cols : List (List ℕ)) (κ : ℕ) {w : ℕ}
    (h : ∀ cs ∈ cols, ∀ c ∈ cs, c < 2 ^ w) (x : ℕ) (hx : x < 2 ^ w) :
    ∀ l : List ℕ, (∀ k ∈ l, k < cols.length) →
      l.foldr (fun k y => if κ.testBit k then colsAct (cols.getD k []) y else y) x < 2 ^ w := by
  intro l
  induction l with
  | nil => intro _; simpa using hx
  | cons k l ih =>
    intro hl
    rw [List.foldr_cons]
    split_ifs with hb
    · apply colsAct_lt
      intro c hc
      refine h (cols.getD k []) ?_ c hc
      rw [List.getD_eq_getElem cols [] (hl k (by simp))]
      exact List.getElem_mem (hl k (by simp))
    · exact ih (fun k' hk' => hl k' (by simp [hk']))

theorem actK_lt {cols : List (List ℕ)} {w : ℕ} (h : ∀ cs ∈ cols, ∀ c ∈ cs, c < 2 ^ w) (κ : ℕ)
    {x : ℕ} (hx : x < 2 ^ w) : actK cols κ x < 2 ^ w := by
  rw [actK.eq_1]
  exact foldr_actK_lt cols κ h x hx (List.range cols.length) (fun k hk => by simpa using hk)

theorem betaN_xor_left (beta : List (List ℕ)) (σ σ' δ : ℕ) :
    betaN beta (σ ^^^ σ') δ = betaN beta σ δ ^^^ betaN beta σ' δ := by
  simp only [betaN]
  exact colsAct_xor _ _ _

private theorem colsAct_map_xor (l : List ℕ) (g₁ g₂ : ℕ → ℕ) (x : ℕ) :
    colsAct (l.map fun i => g₁ i ^^^ g₂ i) x =
      colsAct (l.map g₁) x ^^^ colsAct (l.map g₂) x := by
  induction l generalizing x with
  | nil => simp [colsAct]
  | cons i l ih =>
    have hif : (if x % 2 = 1 then g₁ i ^^^ g₂ i else 0) =
        (if x % 2 = 1 then g₁ i else 0) ^^^ (if x % 2 = 1 then g₂ i else 0) := by
      split_ifs <;> simp
    rw [List.map_cons, List.map_cons, List.map_cons, colsAct.eq_2, colsAct.eq_2,
      colsAct.eq_2, ih, hif]
    ac_rfl

theorem betaN_xor_right (beta : List (List ℕ)) (σ δ δ' : ℕ) :
    betaN beta σ (δ ^^^ δ') = betaN beta σ δ ^^^ betaN beta σ δ' := by
  simp only [betaN]
  have hmap : (List.range 16).map (fun i => colsAct (beta.getD i []) (δ ^^^ δ')) =
      (List.range 16).map
        (fun i => colsAct (beta.getD i []) δ ^^^ colsAct (beta.getD i []) δ') := by
    apply List.map_congr_left
    intro i _
    exact colsAct_xor _ _ _
  rw [hmap]
  exact colsAct_map_xor _ _ _ _

@[expose] def rowVal (X : ℕ → ℕ) (terms : List (ℕ × ℕ)) : Bool :=
  terms.foldr (fun t b => par (t.2 &&& X t.1) ^^ b) false

private theorem foldl_xor_acc {α : Type} (f : α → ℕ) :
    ∀ (l : List α) (m : ℕ), l.foldl (fun m x => m ^^^ f x) m =
      m ^^^ l.foldl (fun m x => m ^^^ f x) 0 := by
  intro l
  induction l with
  | nil => intro m; simp
  | cons x xs ih =>
    intro m
    rw [List.foldl_cons, ih (m ^^^ f x), List.foldl_cons, Nat.zero_xor, ih (f x),
      Nat.xor_assoc]

private theorem foldl_bxor_acc {α : Type} (f : α → Bool) :
    ∀ (l : List α) (b : Bool), l.foldl (fun b x => b ^^ f x) b =
      (b ^^ l.foldl (fun b x => b ^^ f x) false) := by
  intro l
  induction l with
  | nil => intro b; simp
  | cons x xs ih =>
    intro b
    rw [List.foldl_cons, ih (b ^^ f x), List.foldl_cons, Bool.false_xor, ih (f x),
      Bool.xor_assoc]

private theorem rowVal_eq_par_foldl (X : ℕ → ℕ) (terms : List (ℕ × ℕ)) :
    rowVal X terms = par (terms.foldl (fun m t => m ^^^ (t.2 &&& X t.1)) 0) := by
  induction terms with
  | nil => simp [rowVal, par_zero]
  | cons t ts ih =>
    rw [rowVal, List.foldr_cons]
    rw [show ts.foldr (fun t b => par (t.2 &&& X t.1) ^^ b) false =
        par (ts.foldl (fun m t => m ^^^ (t.2 &&& X t.1)) 0) from by
      simpa only [rowVal] using ih]
    rw [← par_xor]
    congr 1
    rw [List.foldl_cons, Nat.zero_xor,
      foldl_xor_acc (fun t => t.2 &&& X t.1) ts (t.2 &&& X t.1)]

private theorem par_foldl_rows (X : ℕ → ℕ) :
    ∀ (l : List (List (ℕ × ℕ) × Bool)) (m : ℕ),
      par (l.foldl (fun m r => r.1.foldl (fun m t => m ^^^ (t.2 &&& X t.1)) m) m) =
        (par m ^^ l.foldl (fun b r => b ^^ rowVal X r.1) false) := by
  intro l
  induction l with
  | nil => intro m; simp
  | cons r rs ih =>
    intro m
    rw [List.foldl_cons, List.foldl_cons, ih]
    rw [foldl_bxor_acc (fun r => rowVal X r.1) rs (false ^^ rowVal X r.1), Bool.false_xor]
    rw [foldl_xor_acc (fun t => t.2 &&& X t.1) r.1 m, par_xor, ← rowVal_eq_par_foldl]
    rw [Bool.xor_assoc]

private theorem par_rows_eq (X : ℕ → ℕ) (l : List (List (ℕ × ℕ) × Bool)) :
    par (l.foldl (fun m r => r.1.foldl (fun m t => m ^^^ (t.2 &&& X t.1)) m) 0) =
      l.foldl (fun b r => b ^^ rowVal X r.1) false := by
  rw [par_foldl_rows, par_zero, Bool.false_xor]

private theorem foldl_rows_flatMap (l : List (List (ℕ × ℕ) × Bool))
    (g : ℕ → (ℕ × ℕ) → ℕ) (a : ℕ) :
    l.foldl (fun m r => r.1.foldl g m) a = (l.flatMap (·.1)).foldl g a := by
  rw [List.foldl_flatMap]

private theorem foldl_congr_mem {α β : Type} (l : List α) (f g : β → α → β) (a : β)
    (h : ∀ x ∈ l, ∀ b, f b x = g b x) : l.foldl f a = l.foldl g a := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, List.foldl_cons, h x (by simp) a]
    exact ih _ (fun y hy b => h y (by simp [hy]) b)

private theorem foldl_zero (l : List ℕ) (f : ℕ → ℕ) (hf : ∀ a ∈ l, f a = 0) :
    l.foldl (fun m a => m ^^^ f a) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.foldl_cons, hf a (by simp), Nat.zero_xor]
    exact ih (fun a ha => hf a (by simp [ha]))

private theorem foldl_xor_split (l : List ℕ) (a b : ℕ → ℕ) :
    l.foldl (fun m v => m ^^^ (a v ^^^ b v)) 0 =
      (l.foldl (fun m v => m ^^^ a v) 0 ^^^ l.foldl (fun m v => m ^^^ b v) 0) := by
  induction l with
  | nil => simp
  | cons v vs ih =>
    simp only [List.foldl_cons, Nat.zero_xor]
    rw [foldl_xor_acc (fun v => a v ^^^ b v) vs (a v ^^^ b v),
      foldl_xor_acc (fun v => a v) vs (a v),
      foldl_xor_acc (fun v => b v) vs (b v), ih]
    ac_rfl

private theorem foldl_range_delta (X : ℕ → ℕ) :
    ∀ (nv t₁ t₂ : ℕ), t₁ < nv →
      (List.range nv).foldl (fun m v => m ^^^ ((if t₁ = v then t₂ else 0) &&& X v)) 0 =
        t₂ &&& X t₁ := by
  intro nv
  induction nv with
  | zero => intro t₁ t₂ h; omega
  | succ n ih =>
    intro t₁ t₂ h
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases hlt : t₁ < n
    · rw [ih t₁ t₂ hlt]
      have h0 : (if t₁ = n then t₂ else 0) &&& X n = 0 := by
        rw [if_neg (by omega), Nat.zero_and]
      rw [h0, Nat.xor_zero]
    · have heq : t₁ = n := by omega
      rw [heq]
      have hz : (List.range n).foldl
          (fun m v => m ^^^ ((if n = v then t₂ else 0) &&& X v)) 0 = 0 := by
        apply foldl_zero
        intro v hv
        rw [List.mem_range] at hv
        rw [if_neg (by omega), Nat.zero_and]
      rw [hz, Nat.zero_xor]
      simp

private theorem foldl_var_acc (v : ℕ) :
    ∀ (ts : List (ℕ × ℕ)) (m : ℕ),
      ts.foldl (fun m t => if t.1 = v then m ^^^ t.2 else m) m =
        (m ^^^ ts.foldl (fun m t => if t.1 = v then m ^^^ t.2 else m) 0) := by
  intro ts
  induction ts with
  | nil => intro m; simp
  | cons t ts ih =>
    intro m
    rw [List.foldl_cons, ih]
    by_cases h : t.1 = v
    · rw [if_pos h, List.foldl_cons, if_pos h, Nat.zero_xor, ih t.2, Nat.xor_assoc]
    · rw [if_neg h, List.foldl_cons, if_neg h]

private theorem foldl_terms_group (X : ℕ → ℕ) :
    ∀ (ts : List (ℕ × ℕ)) (nv : ℕ), (∀ t ∈ ts, t.1 < nv) →
      ts.foldl (fun m t => m ^^^ (t.2 &&& X t.1)) 0 =
        (List.range nv).foldl (fun m v =>
          m ^^^ (ts.foldl (fun m t => if t.1 = v then m ^^^ t.2 else m) 0 &&& X v)) 0 := by
  intro ts
  induction ts with
  | nil =>
    intro nv _
    rw [show (List.range nv).foldl (fun m v => m ^^^
        ((([] : List (ℕ × ℕ)).foldl (fun m t => if t.1 = v then m ^^^ t.2 else m) 0) &&& X v)) 0
        = 0 from by
      apply foldl_zero
      intro v _
      simp only [List.foldl_nil, Nat.zero_and]]
    rfl
  | cons t ts ih =>
    intro nv hmem
    have ht : t.1 < nv := hmem t (by simp)
    have hts : ∀ t' ∈ ts, t'.1 < nv := fun t' ht' => hmem t' (by simp [ht'])
    rw [List.foldl_cons, Nat.zero_xor,
      foldl_xor_acc (fun t => t.2 &&& X t.1) ts (t.2 &&& X t.1), ih nv hts]
    have hvar : ∀ v ∈ List.range nv,
        (t :: ts).foldl (fun m t => if t.1 = v then m ^^^ t.2 else m) 0 =
          ((if t.1 = v then t.2 else 0) ^^^
            ts.foldl (fun m t => if t.1 = v then m ^^^ t.2 else m) 0) := by
      intro v _
      rw [List.foldl_cons, Nat.zero_xor, foldl_var_acc]
    have hcong : (List.range nv).foldl (fun m v =>
        m ^^^ ((t :: ts).foldl (fun m t => if t.1 = v then m ^^^ t.2 else m) 0 &&& X v)) 0 =
        (List.range nv).foldl (fun m v => m ^^^ (((if t.1 = v then t.2 else 0) ^^^
          ts.foldl (fun m t => if t.1 = v then m ^^^ t.2 else m) 0) &&& X v)) 0 := by
      apply foldl_congr_mem
      intro v hv m
      rw [hvar v hv, Nat.and_xor_distrib_right]
    rw [hcong]
    simp only [Nat.and_xor_distrib_right]
    rw [foldl_xor_split, foldl_range_delta X nv t.1 t.2 ht]

private def farkasCh (rows : List (List (ℕ × ℕ) × Bool)) (sel : List Bool) :
    List (List (ℕ × ℕ) × Bool) :=
  (rows.zip sel).filterMap fun p => if p.2 then some p.1 else none

private theorem farkasOK_eq (nv : ℕ) (rows : List (List (ℕ × ℕ) × Bool)) (sel : List Bool) :
    farkasOK nv rows sel =
      ((farkasCh rows sel).foldl (fun b r => b ^^ r.2) false &&
        (rows.all fun r => r.1.all fun t => t.1 < nv) &&
        (List.range nv).all fun v =>
          ((farkasCh rows sel).foldl
            (fun m r => r.1.foldl (fun m t => if t.1 = v then m ^^^ t.2 else m) m) 0 == 0)) := rfl

theorem farkasOK_sound {nv : ℕ} {rows : List (List (ℕ × ℕ) × Bool)} {sel : List Bool}
    (h : farkasOK nv rows sel = true) (X : ℕ → ℕ) : ¬ ∀ r ∈ rows, rowVal X r.1 = r.2 := by
  intro hX
  rw [farkasOK_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [List.all_eq_true] at h2 h3
  have h2' : ∀ r ∈ rows, ∀ t ∈ r.1, t.1 < nv := by
    intro r hr t ht
    have h := h2 r hr
    rw [List.all_eq_true] at h
    simpa using h t ht
  have h3' : ∀ v ∈ List.range nv,
      (farkasCh rows sel).foldl
        (fun m r => r.1.foldl (fun m t => if t.1 = v then m ^^^ t.2 else m) m) 0 = 0 := by
    intro v hv
    have h := h3 v hv
    simpa [beq_iff_eq] using h
  have hch_mem : ∀ r ∈ farkasCh rows sel, r ∈ rows := by
    intro r hr
    rw [farkasCh, List.mem_filterMap] at hr
    obtain ⟨p, hp, hpr⟩ := hr
    obtain ⟨r0, b⟩ := p
    obtain ⟨hp1, -⟩ := List.of_mem_zip hp
    by_cases hb : b
    · simp [hb] at hpr
      rw [← hpr]
      exact hp1
    · simp [hb] at hpr
  have hrowval : ∀ r ∈ farkasCh rows sel, rowVal X r.1 = r.2 :=
    fun r hr => hX r (hch_mem r hr)
  have h1' : (farkasCh rows sel).foldl (fun b r => b ^^ rowVal X r.1) false = true := by
    rw [← h1]
    apply foldl_congr_mem
    intro r hr b
    rw [hrowval r hr]
  have hpar : par ((farkasCh rows sel).foldl
      (fun m r => r.1.foldl (fun m t => m ^^^ (t.2 &&& X t.1)) m) 0) = true := by
    rw [par_rows_eq, h1']
  have hmem : ∀ t ∈ (farkasCh rows sel).flatMap (·.1), t.1 < nv := by
    intro t ht
    rw [List.mem_flatMap] at ht
    obtain ⟨r, hr, ht⟩ := ht
    exact h2' r (hch_mem r hr) t ht
  have hM : ∀ v ∈ List.range nv,
      ((farkasCh rows sel).flatMap (·.1)).foldl
        (fun m t => if t.1 = v then m ^^^ t.2 else m) 0 = 0 := by
    intro v hv
    rw [← foldl_rows_flatMap]
    exact h3' v hv
  have hzero : (farkasCh rows sel).foldl
      (fun m r => r.1.foldl (fun m t => m ^^^ (t.2 &&& X t.1)) m) 0 = 0 := by
    rw [foldl_rows_flatMap,
      foldl_terms_group X ((farkasCh rows sel).flatMap (·.1)) nv hmem]
    apply foldl_zero
    intro v hv
    rw [hM v hv, Nat.zero_and]
  rw [hzero, par_zero] at hpar
  exact Bool.noConfusion hpar

private theorem foldr_testBit (terms : List (ℕ × List ℕ)) (f : ℕ × List ℕ → ℕ) (k : ℕ) :
    terms.foldr (fun t b => (f t).testBit k ^^ b) false =
      (terms.foldr (fun t acc => f t ^^^ acc) 0).testBit k := by
  induction terms with
  | nil => simp
  | cons t ts ih =>
    rw [List.foldr_cons, List.foldr_cons, ih, Nat.testBit_xor]

theorem blockRows_holds {X : ℕ → ℕ} {w : ℕ} {terms : List (ℕ × List ℕ)} {rhs : ℕ}
    (h : terms.foldr (fun t acc => colsAct t.2 (X t.1) ^^^ acc) 0 = rhs) :
    ∀ r ∈ blockRows w terms rhs, rowVal X r.1 = r.2 := by
  intro r hr
  simp only [blockRows, List.mem_map, List.mem_range] at hr
  obtain ⟨k, hk, rfl⟩ := hr
  show rowVal X (terms.map fun t => (t.1, maskT t.2 k)) = rhs.testBit k
  unfold rowVal
  rw [List.foldr_map]
  have hpar : ∀ t : ℕ × List ℕ, par (maskT t.2 k &&& X t.1) = (colsAct t.2 (X t.1)).testBit k :=
    fun t => (testBit_colsAct t.2 (X t.1) k).symm
  simp only [hpar]
  rw [foldr_testBit (f := fun t => colsAct t.2 (X t.1)), h]

structure LiftSol (dat : Data) (F : List Fact) (ds ks : List ℕ) (X : ℕ → ℕ) : Prop where
  lt16 : ∀ j < ks.length, X j < 2 ^ 16
  lt9 : ∀ i < ds.length, X (ks.length + i) < 2 ^ 9
  sq : ∀ j < ks.length, ∀ s, findSq F (ks.getD j 0) = some s →
    X j ^^^ actK dat.aCols (ks.getD j 0) (X j) = s
  comm : ∀ j k, j < k → k < ks.length → ∀ s,
    findComm F (ks.getD j 0) (ks.getD k 0) = some s →
    (X j ^^^ actK dat.aCols (ks.getD k 0) (X j)) ^^^
      (X k ^^^ actK dat.aCols (ks.getD j 0) (X k)) = s
  conj : ∀ i < ds.length, ∀ j < ks.length, ∀ c,
    findConj F (ks.getD j 0) (ds.getD i 0) = some c →
    betaN dat.beta (X j) (ds.getD i 0) ^^^
      (X (ks.length + i) ^^^ actK dat.uConjT (ks.getD j 0) (X (ks.length + i))) = c

private theorem linear_add_actK (cols : List (List ℕ)) (κ : ℕ) :
    ∀ a b, (fun x => x ^^^ actK cols κ x) (a ^^^ b) =
      (fun x => x ^^^ actK cols κ x) a ^^^ (fun x => x ^^^ actK cols κ x) b := by
  intro a b
  show a ^^^ b ^^^ actK cols κ (a ^^^ b) =
    (a ^^^ actK cols κ a) ^^^ (b ^^^ actK cols κ b)
  rw [actK_xor]
  ac_rfl

private theorem linear_betaN (dat : Data) (δ : ℕ) :
    ∀ a b, (fun x => betaN dat.beta x δ) (a ^^^ b) =
      (fun x => betaN dat.beta x δ) a ^^^ (fun x => betaN dat.beta x δ) b :=
  fun a b => betaN_xor_left dat.beta a b δ

private def sysE1 (dat : Data) (F : List Fact) (ks : List ℕ) :
    List ((ℕ × ℕ × ℕ) × List (List (ℕ × ℕ) × Bool)) :=
  (List.range ks.length).flatMap fun j =>
    match findSq F (ks.getD j 0) with
    | some s => [((0, j, 0), blockRows 16 [(j, c1 dat (ks.getD j 0))] s)]
    | none => []

private def sysE2 (dat : Data) (F : List Fact) (ks : List ℕ) :
    List ((ℕ × ℕ × ℕ) × List (List (ℕ × ℕ) × Bool)) :=
  (List.range ks.length).flatMap fun j =>
    ((List.range ks.length).filter (j < ·)).flatMap fun k =>
      match findComm F (ks.getD j 0) (ks.getD k 0) with
      | some s =>
        [((1, j, k), blockRows 16 [(j, c1 dat (ks.getD k 0)), (k, c1 dat (ks.getD j 0))] s)]
      | none => []

private def sysE3 (dat : Data) (F : List Fact) (ds ks : List ℕ) :
    List ((ℕ × ℕ × ℕ) × List (List (ℕ × ℕ) × Bool)) :=
  (List.range ds.length).flatMap fun i => (List.range ks.length).flatMap fun j =>
    match findConj F (ks.getD j 0) (ds.getD i 0) with
    | some c => [((2, i, j), blockRows 9
        [(j, colsOf 16 fun x => betaN dat.beta x (ds.getD i 0)),
          (ks.length + i, colsOf 9 fun x => x ^^^ actK dat.uConjT (ks.getD j 0) x)] c)]
    | none => []

private theorem sysBlocks_eq (dat : Data) (F : List Fact) (ds ks : List ℕ) :
    sysBlocks dat F ds ks = sysE1 dat F ks ++ sysE2 dat F ks ++ sysE3 dat F ds ks := by
  simp only [sysBlocks, sysE1, sysE2, sysE3]
  rfl

private theorem e1_block_holds {dat : Data} {F : List Fact} {ds ks : List ℕ} {X : ℕ → ℕ}
    (hX : LiftSol dat F ds ks X) :
    ∀ b ∈ sysE1 dat F ks, ∀ r ∈ b.2, rowVal X r.1 = r.2 := by
  intro b hb r hr
  rw [sysE1] at hb
  rw [List.mem_flatMap] at hb
  obtain ⟨j, hj, hb⟩ := hb
  rw [List.mem_range] at hj
  cases h : findSq F (ks.getD j 0) with
  | none => rw [h] at hb; simp at hb
  | some s =>
    rw [h] at hb
    rw [List.mem_singleton] at hb
    subst hb
    refine blockRows_holds ?_ r hr
    show colsAct (c1 dat (ks.getD j 0)) (X j) ^^^ 0 = s
    rw [Nat.xor_zero]
    show colsAct (colsOf 16 fun x => x ^^^ actK dat.aCols (ks.getD j 0) x) (X j) = s
    rw [colsAct_colsOf (f := fun x => x ^^^ actK dat.aCols (ks.getD j 0) x)
      (linear_add_actK dat.aCols (ks.getD j 0)) (hX.lt16 j hj)]
    exact hX.sq j hj s h

private theorem e2_block_holds {dat : Data} {F : List Fact} {ds ks : List ℕ} {X : ℕ → ℕ}
    (hX : LiftSol dat F ds ks X) :
    ∀ b ∈ sysE2 dat F ks, ∀ r ∈ b.2, rowVal X r.1 = r.2 := by
  intro b hb r hr
  rw [sysE2] at hb
  rw [List.mem_flatMap] at hb
  obtain ⟨j, hj, hb⟩ := hb
  rw [List.mem_range] at hj
  rw [List.mem_flatMap] at hb
  obtain ⟨k, hk, hb⟩ := hb
  rw [List.mem_filter, List.mem_range] at hk
  obtain ⟨hk, hjk⟩ := hk
  rw [decide_eq_true_eq] at hjk
  cases h : findComm F (ks.getD j 0) (ks.getD k 0) with
  | none => rw [h] at hb; simp at hb
  | some s =>
    rw [h] at hb
    rw [List.mem_singleton] at hb
    subst hb
    refine blockRows_holds ?_ r hr
    show colsAct (c1 dat (ks.getD k 0)) (X j) ^^^
      (colsAct (c1 dat (ks.getD j 0)) (X k) ^^^ 0) = s
    rw [Nat.xor_zero]
    simp only [c1]
    rw [colsAct_colsOf (f := fun x => x ^^^ actK dat.aCols (ks.getD k 0) x)
        (linear_add_actK dat.aCols (ks.getD k 0)) (hX.lt16 j hj),
      colsAct_colsOf (f := fun x => x ^^^ actK dat.aCols (ks.getD j 0) x)
        (linear_add_actK dat.aCols (ks.getD j 0)) (hX.lt16 k hk)]
    exact hX.comm j k hjk hk s h

private theorem e3_block_holds {dat : Data} {F : List Fact} {ds ks : List ℕ} {X : ℕ → ℕ}
    (hX : LiftSol dat F ds ks X) :
    ∀ b ∈ sysE3 dat F ds ks, ∀ r ∈ b.2, rowVal X r.1 = r.2 := by
  intro b hb r hr
  rw [sysE3] at hb
  rw [List.mem_flatMap] at hb
  obtain ⟨i, hi, hb⟩ := hb
  rw [List.mem_range] at hi
  rw [List.mem_flatMap] at hb
  obtain ⟨j, hj, hb⟩ := hb
  rw [List.mem_range] at hj
  cases h : findConj F (ks.getD j 0) (ds.getD i 0) with
  | none => rw [h] at hb; simp at hb
  | some c =>
    rw [h] at hb
    rw [List.mem_singleton] at hb
    subst hb
    refine blockRows_holds ?_ r hr
    show colsAct (colsOf 16 fun x => betaN dat.beta x (ds.getD i 0)) (X j) ^^^
      (colsAct (colsOf 9 fun x => x ^^^ actK dat.uConjT (ks.getD j 0) x)
        (X (ks.length + i)) ^^^ 0) = c
    rw [Nat.xor_zero]
    rw [colsAct_colsOf (f := fun x => betaN dat.beta x (ds.getD i 0))
        (linear_betaN dat (ds.getD i 0)) (hX.lt16 j hj),
      colsAct_colsOf (f := fun x => x ^^^ actK dat.uConjT (ks.getD j 0) x)
        (linear_add_actK dat.uConjT (ks.getD j 0)) (hX.lt9 i hi)]
    exact hX.conj i hi j hj c h

theorem sysRows_holds {dat : Data} {F : List Fact} {ds ks : List ℕ} {X : ℕ → ℕ}
    (hX : LiftSol dat F ds ks X) : ∀ r ∈ sysRows dat F ds ks, rowVal X r.1 = r.2 := by
  intro r hr
  rw [sysRows, List.mem_flatMap] at hr
  obtain ⟨b, hb, hr⟩ := hr
  have hb' : b ∈ sysE1 dat F ks ++ sysE2 dat F ks ++ sysE3 dat F ds ks := by
    rw [← sysBlocks_eq]
    exact hb
  rw [List.mem_append] at hb'
  rcases hb' with hb' | hb'
  · rw [List.mem_append] at hb'
    rcases hb' with hb' | hb'
    · exact e1_block_holds hX b hb' r hr
    · exact e2_block_holds hX b hb' r hr
  · exact e3_block_holds hX b hb' r hr

theorem farkasCase_sound {dat : Data} {F : List Fact} {node ks : List ℕ}
    (h : farkasCase dat F node ks = true) (X : ℕ → ℕ) :
    ¬ LiftSol dat F (basisIn node) (basisIn ks) X := by
  intro hX
  unfold farkasCase at h
  dsimp only at h
  split at h
  · rename_i sel _
    exact farkasOK_sound h X (sysRows_holds hX)
  · exact Bool.noConfusion h

theorem mem_of_mem_basisIn {l : List ℕ} {x : ℕ} (hx : x ∈ basisIn l) : x ∈ l := by
  simp only [basisIn, List.mem_filter] at hx
  exact List.contains_iff.mp hx.2

end CFSG.Monster.B.TwoA.Sp8.P0Rank
