module

public import CFSG.Quasithin.H13.A6S1372L76C
public import CFSG.Quasithin.H13.A6S1372L76B
public import CFSG.Quasithin.H13.A6S1372L19a
public import CFSG.Quasithin.H13.A6S1372L76EK

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Quasithin

namespace A6L76E

@[expose] def cyc3 {n : ℕ} (a b c : Fin n) : Perm (Fin n) := swap a b * swap b c

theorem sign_cyc3 {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) :
    Perm.sign (cyc3 a b c) = 1 := by
  rw [cyc3, Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hbc]
  decide

@[expose] def supp (n : ℕ) (m : G6.PermMod n) : List (Fin n) :=
  (List.finRange n).filter fun i => Multiplicative.toAdd m i = 1

@[expose] def cosupp (n : ℕ) (m : G6.PermMod n) : List (Fin n) :=
  (List.finRange n).filter fun i => Multiplicative.toAdd m i = 0

@[expose] def pick3 {n : ℕ} (l : List (Fin n)) (k : ℕ) : Perm (Fin n) :=
  match l.drop k with
  | a :: b :: c :: _ => cyc3 a b c
  | _ => 1

theorem sign_pick3 {n : ℕ} {l : List (Fin n)} (hl : l.Nodup) (k : ℕ) :
    Perm.sign (pick3 l k) = 1 := by
  unfold pick3
  have hd : (l.drop k).Nodup := hl.sublist (List.drop_sublist k l)
  split
  · rename_i a b c t h
    rw [h] at hd
    have hab : a ≠ b := fun e => by simp [e] at hd
    have hbc : b ≠ c := fun e => by simp [e] at hd
    exact sign_cyc3 hab hbc
  · exact Perm.sign_one

@[expose] def wit (n : ℕ) (m : G6.PermMod n) : Perm (Fin n) × Perm (Fin n) :=
  if 6 ≤ (cosupp n m).length then (pick3 (cosupp n m) 0, pick3 (cosupp n m) 3)
  else if 6 ≤ (supp n m).length then (pick3 (supp n m) 0, pick3 (supp n m) 3)
  else (pick3 (supp n m) 0, pick3 (cosupp n m) 0)

theorem sign_wit (n : ℕ) (m : G6.PermMod n) :
    Perm.sign (wit n m).1 = 1 ∧ Perm.sign (wit n m).2 = 1 := by
  have h1 : (supp n m).Nodup := (List.nodup_finRange n).filter _
  have h2 : (cosupp n m).Nodup := (List.nodup_finRange n).filter _
  unfold wit
  split_ifs
  · exact ⟨sign_pick3 h2 0, sign_pick3 h2 3⟩
  · exact ⟨sign_pick3 h1 0, sign_pick3 h1 3⟩
  · exact ⟨sign_pick3 h1 0, sign_pick3 h2 0⟩

@[expose] def WitOK (n : ℕ) (m : G6.PermMod n) : Prop :=
  A6L76B.E9Pair (wit n m).1 (wit n m).2 ∧ A6L76C.FixCls n (wit n m).1 m ∧
    A6L76C.FixCls n (wit n m).2 m

instance (n : ℕ) (m : G6.PermMod n) : Decidable (WitOK n m) := by unfold WitOK; infer_instance

theorem check8 : ∀ m : G6.PermMod 8, ∑ i, Multiplicative.toAdd m i = 0 → WitOK 8 m := by
  decide +kernel

theorem check7 : ∀ m : G6.PermMod 7, ∑ i, Multiplicative.toAdd m i = 0 →
    WitOK 7 m ∨ (supp 7 m).length = 2 := by
  decide +kernel

@[expose] def common (n : ℕ) (x y : G6.PermMod n) : List (Fin n) :=
  (List.finRange n).filter fun i => Multiplicative.toAdd x i = 1 ∧ Multiplicative.toAdd y i = 1

@[expose] def tau3 (a b c : Fin 7) : Perm (Fin 7) :=
  swap ((swap ((swap a 4) b) 5) ((swap a 4) c)) 6 * swap ((swap a 4) b) 5 * swap a 4

@[expose] def tau7 (x y : G6.PermMod 7) : Perm (Fin 7) :=
  match common 7 x y, (supp 7 x).filter (fun i => Multiplicative.toAdd y i = 0),
    (supp 7 y).filter (fun i => Multiplicative.toAdd x i = 0) with
  | [a], [b], [c] => tau3 a b c
  | _, _, _ => 1

@[expose] def TriOK (x y : G6.PermMod 7) : Prop :=
  (supp 7 x).length = 2 → (supp 7 y).length = 2 → (supp 7 (x * y)).length = 2 → x ≠ y →
    G6.permAct 7 (tau7 x y) x = A6L76.vecS 7 {4, 5} ∧
      G6.permAct 7 (tau7 x y) y = A6L76.vecS 7 {4, 6}

instance (x y : G6.PermMod 7) : Decidable (TriOK x y) := by unfold TriOK; infer_instance

theorem tri7 : ∀ x y : G6.PermMod 7, TriOK x y := by
  decide +kernel

theorem vecS_injective {n : ℕ} {s t : Finset (Fin n)} (h : A6L76.vecS n s = A6L76.vecS n t) :
    s = t := by
  ext i
  have h1 := congrArg (fun x : G6.PermMod n => Multiplicative.toAdd x i) h
  simp only [A6L76.vecS, toAdd_ofAdd] at h1
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all

theorem permAct_vecS {n : ℕ} (σ : Perm (Fin n)) (s : Finset (Fin n)) :
    G6.permAct n σ (A6L76.vecS n s) = A6L76.vecS n (s.map σ.toEmbedding) := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [G6.permAct_apply]
  simp only [A6L76.vecS, toAdd_ofAdd, Finset.mem_map_equiv]
  rfl

theorem pairs7 : ∀ a b c : Fin 7, ({a, b} : Finset (Fin 7)) = {4, 6} →
    ({a, c} : Finset (Fin 7)) = {5, 6} → a = 6 ∧ b = 4 ∧ c = 5 := by
  decide

theorem eps7_points {γ : Perm (Fin 7)}
    (h1 : G6.permAct 7 γ (A6L76.vecS 7 {4, 5}) = A6L76.vecS 7 {4, 6})
    (h2 : G6.permAct 7 γ (A6L76.vecS 7 {4, 6}) = A6L76.vecS 7 {5, 6}) :
    γ 4 = 6 ∧ γ 5 = 4 ∧ γ 6 = 5 := by
  rw [permAct_vecS] at h1 h2
  have e1 := vecS_injective h1
  have e2 := vecS_injective h2
  simp only [Finset.map_insert, Finset.map_singleton, Equiv.coe_toEmbedding] at e1 e2
  exact pairs7 _ _ _ e1 e2

abbrev Low4 : Type := {x : Fin 7 // (x : ℕ) < 4}

theorem alt4_cases : ∀ σ : Perm Low4, Perm.sign σ = 1 → σ ^ 3 = 1 ∨ σ ^ 2 = 1 := by
  decide

theorem alt4_cases' {δ : Perm (Fin 7)} (hs : Perm.sign δ = 1) (h4 : δ 4 = 4) (h5 : δ 5 = 5)
    (h6 : δ 6 = 6) : δ ^ 3 = 1 ∨ δ ^ 2 = 1 := by
  have hp : ∀ x, (fun y : Fin 7 => (y : ℕ) < 4) (δ x) ↔ (fun y : Fin 7 => (y : ℕ) < 4) x := by
    intro x
    show ((δ x : Fin 7) : ℕ) < 4 ↔ (x : ℕ) < 4
    constructor
    · intro hx
      by_contra h
      have hx4 : x = 4 ∨ x = 5 ∨ x = 6 := by omega
      rcases hx4 with rfl | rfl | rfl
      · rw [h4] at hx; exact absurd hx (by decide)
      · rw [h5] at hx; exact absurd hx (by decide)
      · rw [h6] at hx; exact absurd hx (by decide)
    · intro hx
      by_contra h
      have hδ : δ x = 4 ∨ δ x = 5 ∨ δ x = 6 := by omega
      rcases hδ with e | e | e
      · rw [← h4] at e; have := δ.injective e; rw [this] at hx; exact absurd hx (by decide)
      · rw [← h5] at e; have := δ.injective e; rw [this] at hx; exact absurd hx (by decide)
      · rw [← h6] at e; have := δ.injective e; rw [this] at hx; exact absurd hx (by decide)
  have hsupp : ∀ x, δ x ≠ x → (fun y : Fin 7 => (y : ℕ) < 4) x := by
    intro x hx
    show (x : ℕ) < 4
    by_contra h
    have hx4 : x = 4 ∨ x = 5 ∨ x = 6 := by omega
    rcases hx4 with rfl | rfl | rfl
    · exact hx h4
    · exact hx h5
    · exact hx h6
  set σ : Perm Low4 := δ.subtypePerm hp with hσ
  have hδσ : Perm.ofSubtype σ = δ := Perm.ofSubtype_subtypePerm hp hsupp
  have hsσ : Perm.sign σ = 1 := by rw [← Perm.sign_ofSubtype, hδσ, hs]
  rcases alt4_cases σ hsσ with h | h
  · left
    rw [← hδσ, ← map_pow, h, map_one]
  · right
    rw [← hδσ, ← map_pow, h, map_one]

theorem comm_c465 {δ : Perm (Fin 7)} (h4 : δ 4 = 4) (h5 : δ 5 = 5) (h6 : δ 6 = 6) :
    cyc3 4 6 5 * δ = δ * cyc3 4 6 5 := by
  have key : ∀ x : Fin 7, x = 4 ∨ x = 5 ∨ x = 6 ∨ cyc3 4 6 5 x = x := by decide
  have key' : ∀ x : Fin 7, cyc3 4 6 5 x = x → x ≠ 4 ∧ x ≠ 5 ∧ x ≠ 6 := by decide
  refine Equiv.ext fun x => ?_
  simp only [Perm.mul_apply]
  rcases key x with rfl | rfl | rfl | hx
  · rw [h4, show cyc3 (4 : Fin 7) 6 5 4 = 6 from by decide, h6]
  · rw [h5, show cyc3 (4 : Fin 7) 6 5 5 = 4 from by decide, h4]
  · rw [h6, show cyc3 (4 : Fin 7) 6 5 6 = 5 from by decide, h5]
  · rw [hx]
    obtain ⟨hx4, hx5, hx6⟩ := key' x hx
    have hδ4 : δ x ≠ 4 := fun e => hx4 (δ.injective (e.trans h4.symm))
    have hδ5 : δ x ≠ 5 := fun e => hx5 (δ.injective (e.trans h5.symm))
    have hδ6 : δ x ≠ 6 := fun e => hx6 (δ.injective (e.trans h6.symm))
    have key2 : ∀ y : Fin 7, y ≠ 4 → y ≠ 5 → y ≠ 6 → cyc3 4 6 5 y = y := by decide
    exact key2 _ hδ4 hδ5 hδ6

theorem e9_7 : A6L76B.E9Pair (cyc3 (0 : Fin 7) 1 2) (cyc3 4 6 5) ∧
    cyc3 (0 : Fin 7) 1 2 4 = 4 ∧ cyc3 (0 : Fin 7) 1 2 5 = 5 ∧ cyc3 (0 : Fin 7) 1 2 6 = 6 ∧
    (cyc3 (4 : Fin 7) 6 5) ^ 3 = 1 := by
  decide

@[expose] def InL0 (x : P6) : Prop := x = dv 0 2 ∨ x = dv 1 3 ∨ x = e0123

instance : DecidablePred InL0 := fun x => by unfold InL0; infer_instance

@[expose] def Inv3 (σ : Perm (Fin 6)) (x y : P6) : Prop :=
  (act4f σ x = x ∨ act4f σ x = y ∨ act4f σ x = x * y) ∧
    (act4f σ y = x ∨ act4f σ y = y ∨ act4f σ y = x * y)

instance (σ : Perm (Fin 6)) (x y : P6) : Decidable (Inv3 σ x y) := by
  unfold Inv3; infer_instance

@[expose] def FpfOK (γ : Perm (Fin 6)) : Prop :=
  Perm.sign γ = 1 → γ ^ 3 = 1 → InL0 (act4f γ (dv 0 2)) → InL0 (act4f γ (dv 1 3)) →
    act4f γ e0123 ≠ e0123 → ∀ w : P6, InW4 w → act4f γ w = w → w = 1

instance (γ : Perm (Fin 6)) : Decidable (FpfOK γ) := by unfold FpfOK; infer_instance

theorem fpf6 : ∀ γ : Perm (Fin 6), FpfOK γ := by decide +kernel

@[expose] def PresL0 (σ : Perm (Fin 6)) : Prop :=
  InL0 (act4f σ (dv 0 2)) ∧ InL0 (act4f σ (dv 1 3))

instance (σ : Perm (Fin 6)) : Decidable (PresL0 σ) := by unfold PresL0; infer_instance

theorem L0_facts : (∀ x y : P6, InL0 x → InL0 y → x ≠ y → InL0 (x * y)) ∧
    dv 0 2 * dv 1 3 = e0123 ∧ dv (0 : Fin 6) 2 ≠ dv 1 3 ∧ (∀ x : P6, InL0 x → InW4 x) := by
  decide +kernel

theorem presL0_all {σ : Perm (Fin 6)} (h : PresL0 σ) {x : P6} (hx : InL0 x) :
    InL0 (act4f σ x) := by
  obtain ⟨hmul, he, hne, hW⟩ := L0_facts
  rcases hx with rfl | rfl | rfl
  · exact h.1
  · exact h.2
  · rw [← he, act4f_mul_apply]
    refine hmul _ _ h.1 h.2 fun e => hne ?_
    have h1 : act4 σ ⟨dv 0 2, hW _ (Or.inl rfl)⟩ = act4 σ ⟨dv 1 3, hW _ (Or.inr (Or.inl rfl))⟩ :=
      Subtype.ext e
    exact congrArg Subtype.val ((act4 σ).injective h1)

@[expose] def stabL0 : Subgroup (Perm (Fin 6)) :=
  { carrier := {σ | PresL0 σ ∧ Perm.sign σ = 1}
    one_mem' := by decide
    mul_mem' := fun {a b} ha hb => by
      refine ⟨⟨?_, ?_⟩, by rw [Perm.sign_mul, ha.2, hb.2, one_mul]⟩
      · rw [act4f_mul]; exact presL0_all ha.1 hb.1.1
      · rw [act4f_mul]; exact presL0_all ha.1 hb.1.2
    inv_mem' := fun {a} ha => by
      have hpow : ∀ k : ℕ, PresL0 (a ^ k) := by
        intro k
        induction k with
        | zero =>
          rw [pow_zero]
          decide
        | succ k ih =>
          rw [pow_succ]
          refine ⟨?_, ?_⟩
          · rw [act4f_mul]; exact presL0_all ih (ha.1.1)
          · rw [act4f_mul]; exact presL0_all ih (ha.1.2)
      have hinv : a⁻¹ = a ^ (orderOf a - 1) := by
        apply inv_eq_of_mul_eq_one_right
        rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos a), pow_orderOf_eq_one]
      refine ⟨by rw [hinv]; exact hpow _, by rw [Perm.sign_inv, ha.2]⟩ }

instance : DecidablePred (· ∈ stabL0) := fun σ =>
  decidable_of_iff (PresL0 σ ∧ Perm.sign σ = 1) Iff.rfl

theorem card_stabL0 : Nat.card ↥stabL0 = 24 := by
  have : Fintype.card {σ : Perm (Fin 6) // PresL0 σ ∧ Perm.sign σ = 1} = 24 := by
    decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

theorem pRank_stabL0_le_one : CFSG.Open.pRank 3 stabL0 ≤ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.SectionRank.pRank_le (by norm_num) fun E hEX hE => ?_
  have hEp : IsPGroup 3 ↥E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 _ g.2)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have hdvd : 3 ^ k ∣ 24 := by
    rw [← hk, ← card_stabL0]
    exact Subgroup.card_dvd_of_le hEX
  have hk1 : k ≤ 1 := by
    by_contra h
    push Not at h
    have h9 : 3 ^ 2 ∣ 24 := (pow_dvd_pow 3 h).trans hdvd
    norm_num at h9
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) hk1

@[expose] def Good (x y : P6) : Prop := InW4 x ∧ InW4 y ∧ x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y

instance (x y : P6) : Decidable (Good x y) := by unfold Good; infer_instance

@[expose] def In3 (x y z : P6) : Prop := z = x ∨ z = y ∨ z = x * y

theorem p6_mul_self (x : P6) : x * x = 1 := G6.permMod_mul_self x

theorem in3_mul {x y a b : P6} (ha : In3 x y a) (hb : In3 x y b) (hab : a ≠ b) :
    In3 x y (a * b) := by
  have hxx := p6_mul_self x
  have hyy := p6_mul_self y
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact absurd rfl hab
  · right; right; rfl
  · right; left
    rw [← mul_assoc, hxx, one_mul]
  · right; right; exact mul_comm _ _
  · exact absurd rfl hab
  · left
    rw [mul_comm, mul_assoc, hyy, mul_one]
  · right; left
    rw [mul_comm, ← mul_assoc, hxx, one_mul]
  · left
    rw [mul_assoc, hyy, mul_one]
  · exact absurd rfl hab

@[expose] def Pres3 (σ : Perm (Fin 6)) (x y : P6) : Prop :=
  In3 x y (act4f σ x) ∧ In3 x y (act4f σ y)

instance (σ : Perm (Fin 6)) (x y : P6) : Decidable (Pres3 σ x y) := by
  unfold Pres3 In3; infer_instance

theorem pres3_all {x y : P6} (hg : Good x y) {σ : Perm (Fin 6)} (h : Pres3 σ x y) {z : P6}
    (hz : In3 x y z) : In3 x y (act4f σ z) := by
  obtain ⟨hx, hy, -, -, hxy⟩ := hg
  rcases hz with rfl | rfl | rfl
  · exact h.1
  · exact h.2
  · rw [act4f_mul_apply]
    refine in3_mul h.1 h.2 fun e => hxy ?_
    have h1 : act4 σ ⟨x, hx⟩ = act4 σ ⟨y, hy⟩ := Subtype.ext e
    exact congrArg Subtype.val ((act4 σ).injective h1)

@[expose] def stabW {x y : P6} (hg : Good x y) : Subgroup (Perm (Fin 6)) :=
  { carrier := {σ | Pres3 σ x y ∧ Perm.sign σ = 1}
    one_mem' := by
      refine ⟨⟨Or.inl (act4f_one _ hg.1), Or.inr (Or.inl (act4f_one _ hg.2.1))⟩, Perm.sign_one⟩
    mul_mem' := fun {a b} ha hb => by
      refine ⟨⟨?_, ?_⟩, by rw [Perm.sign_mul, ha.2, hb.2, one_mul]⟩
      · rw [act4f_mul]; exact pres3_all hg ha.1 hb.1.1
      · rw [act4f_mul]; exact pres3_all hg ha.1 hb.1.2
    inv_mem' := fun {a} ha => by
      have hpow : ∀ k : ℕ, Pres3 (a ^ k) x y := by
        intro k
        induction k with
        | zero =>
          rw [pow_zero]
          exact ⟨Or.inl (act4f_one _ hg.1), Or.inr (Or.inl (act4f_one _ hg.2.1))⟩
        | succ k ih =>
          rw [pow_succ]
          refine ⟨?_, ?_⟩
          · rw [act4f_mul]; exact pres3_all hg ih ha.1.1
          · rw [act4f_mul]; exact pres3_all hg ih ha.1.2
      have hinv : a⁻¹ = a ^ (orderOf a - 1) := by
        apply inv_eq_of_mul_eq_one_right
        rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos a), pow_orderOf_eq_one]
      refine ⟨by rw [hinv]; exact hpow _, by rw [Perm.sign_inv, ha.2]⟩ }

@[expose] def stabCard (x y : P6) : ℕ :=
  (Finset.univ.filter fun σ : Perm (Fin 6) => Pres3 σ x y ∧ Perm.sign σ = 1).card

theorem card_stabW {x y : P6} (hg : Good x y) : Nat.card ↥(stabW hg) = stabCard x y := by
  rw [stabCard, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  rfl

@[expose] def duad6 (x : P6) : List (Fin 6) :=
  if (supp 6 x).length = 2 then supp 6 x else cosupp 6 x

@[expose] def tau4 (a b c d : Fin 6) : Perm (Fin 6) :=
  let s₁ := swap a 4
  let s₂ := swap (s₁ b) 5
  let s₃ := swap (s₂ (s₁ c)) 0
  let s₄ := swap (s₃ (s₂ (s₁ d))) 2
  s₄ * s₃ * s₂ * s₁

@[expose] def tau6 (x y : P6) : Perm (Fin 6) :=
  match duad6 x, duad6 y with
  | [a, b], [c, d] => tau4 a b c d
  | _, _ => 1

@[expose] def SynOK (x y : P6) : Prop :=
  Good x y → 8 ∣ stabCard x y → act4f (tau6 x y) x = e0123 ∧ InL0 (act4f (tau6 x y) y)

instance (x y : P6) : Decidable (SynOK x y) := by unfold SynOK; infer_instance

open CFSG.Permutation in
theorem stabCard_eq (x y : P6) :
    stabCard x y = FinPack.cntK 6 (A6L76EK.qS (A6L76EK.vc6 x) (A6L76EK.vc6 y)
      (A6L76EK.vc6 (x * y))) 6 0 0 0 := by
  rw [stabCard, FinPack.card_filter_inv, ← FinPack.card_filter_eq_cntK]
  refine congrArg Finset.card (Finset.filter_congr fun τ _ => ?_)
  rw [A6L76EK.qS.eq_1, Bool.and_eq_true, Bool.and_eq_true,
    ← FinPack.sign_eq_one_iff_evenK A6L76EK.h16, Perm.sign_inv, ← A6L76EK.vc6_act_inv,
    ← A6L76EK.vc6_act_inv, A6L76EK.in3K_iff, A6L76EK.in3K_iff]
  rfl

theorem syn6C : ∀ a ∈ A6L76EK.W4C, ∀ b ∈ A6L76EK.W4C,
    CFSG.Permutation.FinPack.memK (A6L76EK.pairC a b) A6L76EK.Lsyn = true →
      act4f (tau6 (A6L76EK.dec6 a) (A6L76EK.dec6 b)) (A6L76EK.dec6 a) = e0123 ∧
        InL0 (act4f (tau6 (A6L76EK.dec6 a) (A6L76EK.dec6 b)) (A6L76EK.dec6 b)) := by
  decide +kernel

theorem syn6 : ∀ x y : P6, SynOK x y := by
  intro x y hg h8
  obtain ⟨hx, hy, h1, h2, h3⟩ := hg
  have hxW := A6L76EK.vc6_mem x hx
  have hyW := A6L76EK.vc6_mem y hy
  have h := CFSG.Permutation.FinPack.allK_iff.1 (CFSG.Permutation.FinPack.allK_iff.1
    A6L76EK.synB_check _ (CFSG.Permutation.FinPack.memK_iff.1 hxW)) _
    (CFSG.Permutation.FinPack.memK_iff.1 hyW)
  rw [stabCard_eq, A6L76EK.vc6_mul hx hy] at h8
  rw [A6L76EK.goodC_of h1 h2 h3] at h
  generalize CFSG.Permutation.FinPack.cntK 6 (A6L76EK.qS (A6L76EK.vc6 x) (A6L76EK.vc6 y)
    (Nat.xor (A6L76EK.vc6 x) (A6L76EK.vc6 y))) 6 0 0 0 = N at h h8
  have h0 : Nat.beq (Nat.mod N 8) 0 = true := by
    rw [Nat.beq_eq]
    exact Nat.dvd_iff_mod_eq_zero.1 h8
  rw [h0] at h
  simp only [Bool.not_true, Bool.false_or] at h
  have hc := syn6C _ (CFSG.Permutation.FinPack.memK_iff.1 hxW) _
    (CFSG.Permutation.FinPack.memK_iff.1 hyW) h
  rwa [A6L76EK.dec6_vc6, A6L76EK.dec6_vc6] at hc

@[expose] def Fix5 (a b : Perm (Fin 5)) (x : G6.PermMod 5) : Prop :=
  ∑ i, Multiplicative.toAdd x i = 0 ∧ x ≠ 1 ∧ G6.permAct 5 a x = x ∧ G6.permAct 5 b x = x

instance (a b : Perm (Fin 5)) (x : G6.PermMod 5) : Decidable (Fix5 a b x) := by
  unfold Fix5; infer_instance

@[expose] def Fix5Eq (a b : Perm (Fin 5)) : Prop :=
  ∀ x y : G6.PermMod 5, Fix5 a b x → Fix5 a b y → x = y

instance (a b : Perm (Fin 5)) : Decidable (Fix5Eq a b) := by unfold Fix5Eq; infer_instance

@[expose] def KlOK (a b : Perm (Fin 5)) : Prop := A6L19.IsKl a b → Fix5Eq a b

instance (a b : Perm (Fin 5)) : Decidable (KlOK a b) := by unfold KlOK; infer_instance

theorem kl5 : ∀ a b : Perm (Fin 5), KlOK a b := by decide +kernel

theorem kl5_eq {a b : Perm (Fin 5)} (h : A6L19.IsKl a b) {x y : G6.PermMod 5}
    (hx0 : ∑ i, Multiplicative.toAdd x i = 0) (hy0 : ∑ i, Multiplicative.toAdd y i = 0)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hax : G6.permAct 5 a x = x) (hbx : G6.permAct 5 b x = x)
    (hay : G6.permAct 5 a y = y) (hby : G6.permAct 5 b y = y) : x = y :=
  kl5 a b h x y ⟨hx0, hx1, hax, hbx⟩ ⟨hy0, hy1, hay, hby⟩

@[expose] def Comm5OK (a b : Perm (Fin 5)) : Prop :=
  Perm.sign a = 1 → Perm.sign b = 1 → a * a = 1 → b * b = 1 → (a * b) ^ 8 = 1 → a * b = b * a

instance (a b : Perm (Fin 5)) : Decidable (Comm5OK a b) := by unfold Comm5OK; infer_instance

theorem comm5 : ∀ a b : Perm (Fin 5), Comm5OK a b := by decide +kernel

theorem pow_mod_three {X : Type*} [Monoid X] {x : X} (hx : x ^ 3 = 1) (k : ℕ) :
    x ^ (k % 3) = x ^ k := by
  conv_rhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, hx, one_pow, one_mul]

theorem pow_val_add {X : Type*} [Monoid X] {x : X} (hx : x ^ 3 = 1) (u v : ZMod 3) :
    x ^ (u + v).val = x ^ u.val * x ^ v.val := by
  rw [ZMod.val_add, pow_mod_three hx, pow_add]

theorem cyc9_facts : cyc3 (0 : Fin 9) 1 2 * cyc3 3 4 5 = cyc3 3 4 5 * cyc3 0 1 2 ∧
    cyc3 (0 : Fin 9) 1 2 * cyc3 6 7 8 = cyc3 6 7 8 * cyc3 0 1 2 ∧
    cyc3 (3 : Fin 9) 4 5 * cyc3 6 7 8 = cyc3 6 7 8 * cyc3 3 4 5 ∧
    cyc3 (0 : Fin 9) 1 2 ^ 3 = 1 ∧ cyc3 (3 : Fin 9) 4 5 ^ 3 = 1 ∧ cyc3 (6 : Fin 9) 7 8 ^ 3 = 1 := by
  decide

theorem cyc9_indep : ∀ i j k : ZMod 3,
    cyc3 (0 : Fin 9) 1 2 ^ i.val * cyc3 3 4 5 ^ j.val * cyc3 6 7 8 ^ k.val = 1 →
      i = 0 ∧ j = 0 ∧ k = 0 := by
  decide

@[expose] noncomputable def f9 : Multiplicative (Fin 3 → ZMod 3) →* Perm (Fin 9) where
  toFun v := cyc3 0 1 2 ^ (Multiplicative.toAdd v 0).val *
    cyc3 3 4 5 ^ (Multiplicative.toAdd v 1).val * cyc3 6 7 8 ^ (Multiplicative.toAdd v 2).val
  map_one' := by simp
  map_mul' v w := by
    obtain ⟨hab, hac, hbc, ha, hb, hc⟩ := cyc9_facts
    simp only [toAdd_mul, Pi.add_apply]
    rw [pow_val_add ha, pow_val_add hb, pow_val_add hc]
    set A := cyc3 (0 : Fin 9) 1 2 ^ (Multiplicative.toAdd v 0).val
    set A' := cyc3 (0 : Fin 9) 1 2 ^ (Multiplicative.toAdd w 0).val
    set B := cyc3 (3 : Fin 9) 4 5 ^ (Multiplicative.toAdd v 1).val
    set B' := cyc3 (3 : Fin 9) 4 5 ^ (Multiplicative.toAdd w 1).val
    set C := cyc3 (6 : Fin 9) 7 8 ^ (Multiplicative.toAdd v 2).val
    set C' := cyc3 (6 : Fin 9) 7 8 ^ (Multiplicative.toAdd w 2).val
    have h1 : A' * B = B * A' :=
      (Commute.pow_pow (show Commute (cyc3 (0 : Fin 9) 1 2) (cyc3 3 4 5) from hab)
        (Multiplicative.toAdd w 0).val (Multiplicative.toAdd v 1).val).eq
    have h2 : A' * C = C * A' :=
      (Commute.pow_pow (show Commute (cyc3 (0 : Fin 9) 1 2) (cyc3 6 7 8) from hac)
        (Multiplicative.toAdd w 0).val (Multiplicative.toAdd v 2).val).eq
    have h3 : B' * C = C * B' :=
      (Commute.pow_pow (show Commute (cyc3 (3 : Fin 9) 4 5) (cyc3 6 7 8) from hbc)
        (Multiplicative.toAdd w 1).val (Multiplicative.toAdd v 2).val).eq
    calc A * A' * (B * B') * (C * C') = A * (A' * B) * B' * C * C' := by group
      _ = A * B * (A' * B') * C * C' := by rw [h1]; group
      _ = A * B * A' * (B' * C) * C' := by group
      _ = A * B * A' * C * B' * C' := by rw [h3]; group
      _ = A * B * (A' * C) * B' * C' := by group
      _ = A * B * C * A' * B' * C' := by rw [h2]; group
      _ = A * B * C * (A' * B' * C') := by group

theorem f9_injective : Function.Injective f9 := by
  rw [injective_iff_map_eq_one]
  intro v hv
  have hv' : cyc3 (0 : Fin 9) 1 2 ^ (Multiplicative.toAdd v 0).val *
      cyc3 3 4 5 ^ (Multiplicative.toAdd v 1).val *
      cyc3 6 7 8 ^ (Multiplicative.toAdd v 2).val = 1 := hv
  obtain ⟨h0, h1, h2⟩ := cyc9_indep _ _ _ hv'
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem sign_f9 (v : Multiplicative (Fin 3 → ZMod 3)) : Perm.sign (f9 v) = 1 := by
  show Perm.sign (cyc3 0 1 2 ^ _ * cyc3 3 4 5 ^ _ * cyc3 6 7 8 ^ _) = 1
  rw [map_mul, map_mul, map_pow, map_pow, map_pow, sign_cyc3 (by decide) (by decide),
    sign_cyc3 (by decide) (by decide), sign_cyc3 (by decide) (by decide)]
  simp

@[expose] noncomputable def emb9 {n : ℕ} (hn : 9 ≤ n) : Perm (Fin 9) →* Perm (Fin n) :=
  Perm.viaEmbeddingHom (Fin.castLEEmb hn)

theorem sign_emb9 {n : ℕ} (hn : 9 ≤ n) (σ : Perm (Fin 9)) :
    Perm.sign (emb9 hn σ) = Perm.sign σ := by
  classical
  rw [emb9, Perm.viaEmbeddingHom_apply, Perm.viaEmbedding]
  convert Perm.sign_extendDomain σ (Equiv.ofInjective (Fin.castLEEmb hn).1 (Fin.castLEEmb hn).2)

theorem three_le_pRank_alt {n : ℕ} (hn : 9 ≤ n) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(alternatingGroup (Fin n))) := by
  set f : Multiplicative (Fin 3 → ZMod 3) →* ↥(alternatingGroup (Fin n)) :=
    ((emb9 hn).comp f9).codRestrict _ fun v => by
      rw [Perm.mem_alternatingGroup, MonoidHom.comp_apply, sign_emb9]
      exact sign_f9 v with hf
  have hfi : Function.Injective f := fun a b h =>
    f9_injective (Perm.viaEmbeddingHom_injective (Fin.castLEEmb hn) (congrArg Subtype.val h))
  refine CFSG.SectionRank.le_pRank_of_injective (by norm_num) (fun a b => mul_comm a b)
    (fun a => ?_) ?_ f hfi le_top
  · apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i
    rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul,
      show ((3 : ℕ) : ZMod 3) = 0 from rfl, zero_mul]
  · rw [Nat.card_eq_fintype_card]
    rfl

end A6L76E

end CFSG.Quasithin.H13.A6
