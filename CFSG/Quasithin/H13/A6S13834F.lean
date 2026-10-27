module

public import CFSG.Quasithin.H13.A6Assembly
public import CFSG.Sporadic.Schreier.J4SSylowBase
import CFSG.Quasithin.H13.A6S13834FK

public section

namespace CFSG.Quasithin.H13.A6

open Equiv
open CFSG.Permutation.FinPack (enc mulK invPK memK allK_iff enc_mem_of_beq mem_of_memKL mul_mem_of_K
  sub_of_KL comm_enc_iff enc_inv enc_mul beq_enc_iff beq_enc_false walkK_sound)

@[expose] def vp (σ : Perm (Fin 6)) (v : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 := fun i => v (σ⁻¹ i)

theorem vp_add (σ : Perm (Fin 6)) (v w : Fin 6 → ZMod 2) : vp σ (v + w) = vp σ v + vp σ w := rfl

theorem vp_mul (σ τ : Perm (Fin 6)) (v : Fin 6 → ZMod 2) : vp (σ * τ) v = vp σ (vp τ v) := by
  funext i
  simp only [vp, mul_inv_rev, Perm.mul_apply]

theorem vp_one (v : Fin 6 → ZMod 2) : vp 1 v = v := rfl

theorem vp_zero (σ : Perm (Fin 6)) : vp σ 0 = 0 := rfl

theorem vp_const (σ : Perm (Fin 6)) : vp σ (fun _ => 1) = fun _ => 1 := rfl

theorem vadd_self (v : Fin 6 → ZMod 2) : v + v = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize v i = c
  revert c
  decide

@[expose] def InL (a b v : Fin 6 → ZMod 2) : Prop := v = 0 ∨ v = a ∨ v = b ∨ v = a + b

instance (a b v : Fin 6 → ZMod 2) : Decidable (InL a b v) := by unfold InL; infer_instance

theorem inL_add {a b x y : Fin 6 → ZMod 2} (hx : InL a b x) (hy : InL a b y) :
    InL a b (x + y) := by
  have h := vadd_self
  unfold InL at hx hy ⊢
  rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy]
  · exact Or.inl (add_zero 0)
  · exact Or.inr (Or.inl (zero_add a))
  · exact Or.inr (Or.inr (Or.inl (zero_add b)))
  · exact Or.inr (Or.inr (Or.inr (zero_add _)))
  · exact Or.inr (Or.inl (add_zero a))
  · exact Or.inl (h a)
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inr (Or.inl (by rw [← add_assoc, h, zero_add])))
  · exact Or.inr (Or.inr (Or.inl (add_zero b)))
  · exact Or.inr (Or.inr (Or.inr (add_comm b a)))
  · exact Or.inl (h b)
  · exact Or.inr (Or.inl (by rw [add_left_comm, h, add_zero]))
  · exact Or.inr (Or.inr (Or.inr (add_zero _)))
  · exact Or.inr (Or.inr (Or.inl (by rw [add_right_comm, h, zero_add])))
  · exact Or.inr (Or.inl (by rw [add_assoc, h, add_zero]))
  · exact Or.inl (h _)

@[expose] def InLn (a b v : Fin 6 → ZMod 2) : Prop := InL a b v ∨ InL a b (v + fun _ => 1)

instance (a b v : Fin 6 → ZMod 2) : Decidable (InLn a b v) := by unfold InLn; infer_instance

theorem inLn_add {a b x y : Fin 6 → ZMod 2} (hx : InLn a b x) (hy : InLn a b y) :
    InLn a b (x + y) := by
  have h := vadd_self (fun _ => (1 : ZMod 2))
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact Or.inl (inL_add hx hy)
  · right
    have := inL_add hx hy
    rwa [← add_assoc] at this
  · right
    have := inL_add hx hy
    rwa [add_right_comm] at this
  · left
    have := inL_add hx hy
    rwa [add_add_add_comm, h, add_zero] at this

@[expose] def StabL (a b : Fin 6 → ZMod 2) (σ : Perm (Fin 6)) : Prop :=
  InL a b (vp σ a) ∧ InL a b (vp σ b)

instance (a b : Fin 6 → ZMod 2) : DecidablePred (StabL a b) := fun σ => by
  unfold StabL; infer_instance

@[expose] def StabLn (a b : Fin 6 → ZMod 2) (σ : Perm (Fin 6)) : Prop :=
  InLn a b (vp σ a) ∧ InLn a b (vp σ b)

instance (a b : Fin 6 → ZMod 2) : DecidablePred (StabLn a b) := fun σ => by
  unfold StabLn; infer_instance

theorem stabL_maps {a b : Fin 6 → ZMod 2} {σ : Perm (Fin 6)} (h : StabL a b σ) {v : Fin 6 → ZMod 2}
    (hv : InL a b v) : InL a b (vp σ v) := by
  rcases hv with hv | hv | hv | hv <;> rw [hv]
  · exact Or.inl rfl
  · exact h.1
  · exact h.2
  · rw [vp_add]; exact inL_add h.1 h.2

theorem stabLn_maps {a b : Fin 6 → ZMod 2} {σ : Perm (Fin 6)} (h : StabLn a b σ)
    {v : Fin 6 → ZMod 2} (hv : InLn a b v) : InLn a b (vp σ v) := by
  have key : ∀ w, InL a b w → InLn a b (vp σ w) := by
    intro w hw
    rcases hw with hw | hw | hw | hw <;> rw [hw]
    · exact Or.inl (Or.inl rfl)
    · exact h.1
    · exact h.2
    · rw [vp_add]; exact inLn_add h.1 h.2
  rcases hv with hv | hv
  · exact key v hv
  · have h1 := key _ hv
    rw [vp_add, vp_const] at h1
    have h2 : InLn a b (fun _ => (1 : ZMod 2)) := Or.inr (Or.inl (vadd_self _))
    have := inLn_add h1 h2
    rwa [add_assoc, vadd_self, add_zero] at this

theorem stabL_inv {a b : Fin 6 → ZMod 2} {σ : Perm (Fin 6)} (h : StabL a b σ) :
    StabL a b σ⁻¹ := by
  have hk : ∀ k : ℕ, ∀ v, InL a b v → InL a b (vp (σ ^ k) v) := by
    intro k
    induction k with
    | zero => intro v hv; exact hv
    | succ k ih => intro v hv; rw [pow_succ, vp_mul]; exact ih _ (stabL_maps h hv)
  have e : σ⁻¹ = σ ^ (orderOf σ - 1) := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel (orderOf_pos σ),
      pow_orderOf_eq_one]
  rw [e]
  exact ⟨hk _ _ (Or.inr (Or.inl rfl)), hk _ _ (Or.inr (Or.inr (Or.inl rfl)))⟩

theorem stabLn_inv {a b : Fin 6 → ZMod 2} {σ : Perm (Fin 6)} (h : StabLn a b σ) :
    StabLn a b σ⁻¹ := by
  have hk : ∀ k : ℕ, ∀ v, InLn a b v → InLn a b (vp (σ ^ k) v) := by
    intro k
    induction k with
    | zero => intro v hv; exact hv
    | succ k ih => intro v hv; rw [pow_succ, vp_mul]; exact ih _ (stabLn_maps h hv)
  have e : σ⁻¹ = σ ^ (orderOf σ - 1) := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel (orderOf_pos σ),
      pow_orderOf_eq_one]
  rw [e]
  exact ⟨hk _ _ (Or.inl (Or.inr (Or.inl rfl))), hk _ _ (Or.inl (Or.inr (Or.inr (Or.inl rfl))))⟩

@[expose] def stabSub (a b : Fin 6 → ZMod 2) : Subgroup (Perm (Fin 6)) where
  carrier := {σ | StabL a b σ}
  one_mem' := ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl))⟩
  mul_mem' := fun {σ τ} hσ hτ => by
    refine ⟨?_, ?_⟩ <;> rw [vp_mul]
    · exact stabL_maps hσ hτ.1
    · exact stabL_maps hσ hτ.2
  inv_mem' := fun {σ} hσ => stabL_inv hσ

@[expose] def stabSubN (a b : Fin 6 → ZMod 2) : Subgroup (Perm (Fin 6)) where
  carrier := {σ | StabLn a b σ}
  one_mem' := ⟨Or.inl (Or.inr (Or.inl rfl)), Or.inl (Or.inr (Or.inr (Or.inl rfl)))⟩
  mul_mem' := fun {σ τ} hσ hτ => by
    refine ⟨?_, ?_⟩ <;> rw [vp_mul]
    · exact stabLn_maps hσ hτ.1
    · exact stabLn_maps hσ hτ.2
  inv_mem' := fun {σ} hσ => stabLn_inv hσ

instance (a b : Fin 6 → ZMod 2) : DecidablePred (· ∈ stabSub a b) := fun σ =>
  (inferInstance : Decidable (StabL a b σ))

instance (a b : Fin 6 → ZMod 2) : DecidablePred (· ∈ stabSubN a b) := fun σ =>
  (inferInstance : Decidable (StabLn a b σ))

theorem card_stabSub (a b : Fin 6 → ZMod 2) :
    Nat.card (stabSub a b) = (Finset.univ.filter (StabL a b)).card := by
  rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  rfl

theorem card_stabSubN (a b : Fin 6 → ZMod 2) :
    Nat.card (stabSubN a b) = (Finset.univ.filter (StabLn a b)).card := by
  rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  rfl

theorem natCard_eq_length {X : Subgroup (Perm (Fin 6))} {l : List (Perm (Fin 6))} (hl : l.Nodup)
    (h : ∀ σ, σ ∈ X ↔ σ ∈ l) : Nat.card X = l.length := by
  rw [← List.toFinset_card_of_nodup hl, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun σ => by rw [List.mem_toFinset]; exact h σ)

@[expose] def iota0 : Perm (Fin 6) := swap 0 1 * swap 2 3 * swap 4 5

@[expose] def c0 : Perm (Fin 6) := swap 0 2 * swap 2 4 * (swap 1 3 * swap 3 5)

@[expose] def tC : Perm (Fin 6) := swap 0 2 * swap 1 3

@[expose] def e8List : List (Perm (Fin 6)) :=
  [1, swap 0 1, swap 2 3, swap 0 1 * swap 2 3, swap 4 5, swap 0 1 * swap 4 5,
    swap 2 3 * swap 4 5, swap 0 1 * swap 2 3 * swap 4 5]

@[expose] def e0List : List (Perm (Fin 6)) :=
  [1, swap 0 1 * swap 2 3, swap 0 1 * swap 4 5, swap 2 3 * swap 4 5]

@[expose] def s3List : List (Perm (Fin 6)) := [1, c0, c0 * c0, tC, tC * c0, tC * (c0 * c0)]

@[expose] def cList : List (Perm (Fin 6)) := e8List.flatMap fun x => s3List.map fun y => x * y

@[expose] def a4List : List (Perm (Fin 6)) :=
  [1, c0, c0 * c0].flatMap fun y => e0List.map fun x => y * x

private theorem hn6 : 6 ≤ 16 := by norm_num

private theorem hC : (cList.map enc == A6K.CC) = true := by decide +kernel

private theorem hA4 : (a4List.map enc == A6K.A4C) = true := by decide +kernel

private theorem hE0 : (e0List.map enc == A6K.E0C) = true := by decide +kernel

private theorem hE8 : (e8List.map enc == A6K.E8C) = true := by decide +kernel

private theorem hI : enc iota0 = A6K.IC := by decide +kernel

theorem mem_cList : ∀ σ : Perm (Fin 6), σ * iota0 = iota0 * σ → σ ∈ cList := by
  intro σ hσ
  have h := walkK_sound A6K.walk_CC σ
  rw [← hI, (comm_enc_iff hn6).2 hσ, Bool.not_true, Bool.false_or] at h
  exact mem_of_memKL hn6 hC h

theorem cList_comm : ∀ σ ∈ cList, σ * iota0 = iota0 * σ := by
  intro σ hσ
  have h := allK_iff.1 A6K.comm_CC _ (enc_mem_of_beq hC hσ)
  rw [← hI] at h
  exact (comm_enc_iff hn6).1 h

theorem list_nodup : cList.Nodup ∧ a4List.Nodup ∧ e8List.Nodup := by
  decide +kernel

theorem e0_sub_e8 : ∀ σ ∈ e0List, σ ∈ e8List :=
  sub_of_KL hn6 e0List e8List _ _ hE0 hE8 A6K.sub_E0E8

theorem a4_mul : ∀ σ ∈ a4List, ∀ τ ∈ a4List, σ * τ ∈ a4List :=
  mul_mem_of_K hn6 a4List a4List _ _ hA4 hA4 A6K.mul_A4

theorem a4_inv : ∀ σ ∈ a4List, σ⁻¹ ∈ a4List := by
  intro σ hσ
  have h := allK_iff.1 A6K.inv_A4 _ (enc_mem_of_beq hA4 hσ)
  rw [← enc_inv hn6] at h
  exact mem_of_memKL hn6 hA4 h

theorem a4_normal_e0 : ∀ a ∈ a4List, ∀ x ∈ e0List, a * x * a⁻¹ ∈ e0List := by
  intro a ha x hx
  have h := allK_iff.1 (allK_iff.1 A6K.norm_A4E0 _ (enc_mem_of_beq hA4 ha)) _
    (enc_mem_of_beq hE0 hx)
  simp only [← enc_inv hn6, ← enc_mul hn6] at h
  exact mem_of_memKL hn6 hE0 h

theorem a4_exp : ∀ a ∈ a4List, a ^ 6 = 1 := fun a ha =>
  A6K.eq_of_beq_pow hn6 A6K.enc_one6 (allK_iff.1 A6K.exp_A4 _ (enc_mem_of_beq hA4 ha))

theorem a4_two : ∀ a ∈ a4List, a ^ 2 = 1 → a ∈ e0List := by
  intro a ha h2
  have h := allK_iff.1 A6K.two_A4 _ (enc_mem_of_beq hA4 ha)
  rw [A6K.beq_pow_of_eq hn6 A6K.enc_one6 h2, Bool.not_true, Bool.false_or] at h
  exact mem_of_memKL hn6 hE0 h

theorem e8_mul : ∀ σ ∈ e8List, ∀ τ ∈ e8List, σ * τ ∈ e8List :=
  mul_mem_of_K hn6 e8List e8List _ _ hE8 hE8 A6K.mul_E8

theorem e8_inv : ∀ σ ∈ e8List, σ⁻¹ ∈ e8List := by
  intro σ hσ
  have h := allK_iff.1 A6K.inv_E8 _ (enc_mem_of_beq hE8 hσ)
  rw [← enc_inv hn6] at h
  exact mem_of_memKL hn6 hE8 h

theorem c3_mem_a4 : ∀ σ ∈ cList, σ ^ 3 = 1 → σ ∈ a4List := by
  intro σ hσ h3
  have h := allK_iff.1 A6K.c3_CC _ (enc_mem_of_beq hC hσ)
  rw [A6K.beq_pow_of_eq hn6 A6K.enc_one6 h3, Bool.not_true, Bool.false_or] at h
  exact mem_of_memKL hn6 hA4 h

theorem cList_exp : ∀ σ ∈ cList, σ ^ 12 = 1 := fun σ hσ =>
  A6K.eq_of_beq_pow hn6 A6K.enc_one6 (allK_iff.1 A6K.exp_CC _ (enc_mem_of_beq hC hσ))

theorem card_normalizer_c3 : ∀ c ∈ a4List, c ^ 3 = 1 → c ≠ 1 →
    (cList.filter fun σ => decide (σ * c * σ⁻¹ = c ∨ σ * c * σ⁻¹ = c⁻¹)).length = 12 := by
  intro c hc h3 h1
  have h := allK_iff.1 A6K.norm_A4 _ (enc_mem_of_beq hA4 hc)
  rw [A6K.beq_pow_of_eq hn6 A6K.enc_one6 h3, A6K.beq_one_false hn6 A6K.enc_one6 h1] at h
  simp only [Bool.not_true, Bool.false_or] at h
  rw [A6K.length_filter_enc hC (fun σ => decide (σ * c * σ⁻¹ = c ∨ σ * c * σ⁻¹ = c⁻¹))
    (fun s => Nat.beq (mulK 6 (mulK 6 s (enc c)) (invPK 6 s)) (enc c) ||
      Nat.beq (mulK 6 (mulK 6 s (enc c)) (invPK 6 s)) (invPK 6 (enc c))) fun σ => by
      simp only [← enc_inv hn6, ← enc_mul hn6]
      rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.or_eq_true, beq_enc_iff hn6, beq_enc_iff hn6]]
  exact Nat.eq_of_beq_eq_true h

theorem card_C_A6 : (cList.filter fun σ => decide (Perm.sign σ = 1)).length = 24 := by
  decide +kernel

theorem E0_of_two_c3 : ∀ c ∈ a4List, ∀ d ∈ a4List, c ^ 3 = 1 → c ≠ 1 → d ^ 3 = 1 → d ≠ 1 →
    d ≠ c → d ≠ c⁻¹ → c * d * c⁻¹ * d⁻¹ ∈ e0List ∧ ∀ x ∈ e0List, x = 1 ∨
      x = c * d * c⁻¹ * d⁻¹ ∨ x = c * (c * d * c⁻¹ * d⁻¹) * c⁻¹ ∨
      x = c⁻¹ * (c * d * c⁻¹ * d⁻¹) * c := by
  intro c hc d hd hc3 hc1 hd3 hd1 hdc hdci
  have h1 := allK_iff.1 A6K.e0two_A4 _ (enc_mem_of_beq hA4 hc)
  rw [A6K.beq_pow_of_eq hn6 A6K.enc_one6 hc3, A6K.beq_one_false hn6 A6K.enc_one6 hc1] at h1
  simp only [Bool.not_true, Bool.false_or] at h1
  have h2 := allK_iff.1 h1 _ (enc_mem_of_beq hA4 hd)
  rw [A6K.beq_pow_of_eq hn6 A6K.enc_one6 hd3, A6K.beq_one_false hn6 A6K.enc_one6 hd1,
    beq_enc_false hn6 hdc, ← enc_inv hn6 c, beq_enc_false hn6 hdci] at h2
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, A6K.commC, ← enc_inv hn6,
    ← enc_mul hn6] at h2
  obtain ⟨hk, hall⟩ := h2
  refine ⟨mem_of_memKL hn6 hE0 hk, fun x hx => ?_⟩
  have h3 := allK_iff.1 hall _ (enc_mem_of_beq hE0 hx)
  rw [← A6K.enc_one6] at h3
  simp only [Bool.or_eq_true, beq_enc_iff hn6] at h3
  rcases h3 with ((h | h) | h) | h
  exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inr (Or.inr h))]

@[expose] def e2345 : Fin 6 → ZMod 2 := ![0, 0, 1, 1, 1, 1]

@[expose] def e0145 : Fin 6 → ZMod 2 := ![1, 1, 0, 0, 1, 1]

@[expose] def e01 : Fin 6 → ZMod 2 := ![1, 1, 0, 0, 0, 0]

@[expose] def e23 : Fin 6 → ZMod 2 := ![0, 0, 1, 1, 0, 0]

@[expose] def e0123v : Fin 6 → ZMod 2 := ![1, 1, 1, 1, 0, 0]

@[expose] def e45v : Fin 6 → ZMod 2 := ![0, 0, 0, 0, 1, 1]

theorem iota0_stab : ∀ σ ∈ cList, StabL e2345 e0145 σ ∧ StabLn e01 e23 σ := by
  decide +kernel

theorem stab_iota0 : ∀ σ : Perm (Fin 6), StabL e2345 e0145 σ → σ * iota0 = iota0 * σ := by
  decide +kernel

theorem stabN_iota0 : ∀ σ : Perm (Fin 6), StabLn e01 e23 σ → σ * iota0 = iota0 * σ := by
  decide +kernel

@[expose] def wtv (v : Fin 6 → ZMod 2) : ℕ := ∑ i, (v i).val

theorem wtv_vp (σ : Perm (Fin 6)) (v : Fin 6 → ZMod 2) : wtv (vp σ v) = wtv v :=
  Equiv.sum_comp σ⁻¹ (fun i => (v i).val)

@[expose] def relabelList : List (Perm (Fin 6)) :=
  [swap 0 4 * swap 1 5, swap 0 4 * swap 2 5, swap 1 4 * swap 2 5, swap 0 4 * swap 3 5,
    swap 1 4 * swap 3 5, swap 2 4 * swap 3 5, 1, swap 0 5, swap 1 5, swap 2 5, swap 3 4,
    swap 3 5, swap 2 4, swap 1 4, swap 0 4]

theorem relabel_nat : ∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 → v ≠ 0 → v ≠ (fun _ => 1) →
    ∃ τ ∈ relabelList, vp τ⁻¹ v = e0123v ∨ vp τ⁻¹ v = e0123v + fun _ => 1 := by
  decide +kernel

theorem relabel_cover : ∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 → v ≠ 0 → v ≠ (fun _ => 1) →
    ∃ τ ∈ relabelList, vp τ⁻¹ v = e45v ∨ vp τ⁻¹ v = e0123v := by
  decide +kernel

@[expose] def HypN (b : Fin 6 → ZMod 2) : Prop :=
  ∑ i, b i = 0 ∧ b 5 = 0 ∧ b ≠ 0 ∧ b ≠ e0123v

instance (b : Fin 6 → ZMod 2) : Decidable (HypN b) := by unfold HypN; infer_instance

@[expose] def ConclN (b : Fin 6 → ZMod 2) : Prop :=
  ∃ τ : Perm (Fin 6), InLn e0123v b (vp τ e01) ∧ InLn e0123v b (vp τ e23) ∧
    InLn e01 e23 (vp τ⁻¹ e0123v) ∧ InLn e01 e23 (vp τ⁻¹ b)

instance (b : Fin 6 → ZMod 2) : Decidable (ConclN b) := by unfold ConclN; infer_instance

@[expose] def ClsN (b : Fin 6 → ZMod 2) : Prop :=
  HypN b → 8 ∣ (Finset.univ.filter (StabLn e0123v b)).card → ConclN b

instance (b : Fin 6 → ZMod 2) : Decidable (ClsN b) := by unfold ClsN; infer_instance

theorem cls_nat : ∀ b : Fin 6 → ZMod 2, ClsN b := by
  decide +kernel

@[expose] def HypC (d b : Fin 6 → ZMod 2) : Prop :=
  ∑ i, b i = 0 ∧ b ≠ 0 ∧ b ≠ d ∧ wtv b = wtv d ∧ wtv (d + b) = wtv d

instance (d b : Fin 6 → ZMod 2) : Decidable (HypC d b) := by unfold HypC; infer_instance

@[expose] def ConclC (b : Fin 6 → ZMod 2) : Prop :=
  ∃ τ : Perm (Fin 6), InL e0123v b (vp τ e2345) ∧ InL e0123v b (vp τ e0145) ∧
    InL e2345 e0145 (vp τ⁻¹ e0123v) ∧ InL e2345 e0145 (vp τ⁻¹ b)

instance (b : Fin 6 → ZMod 2) : Decidable (ConclC b) := by unfold ConclC; infer_instance

@[expose] def ClsC (b : Fin 6 → ZMod 2) : Prop :=
  HypC e0123v b → 8 ∣ (Finset.univ.filter (StabL e0123v b)).card → ConclC b

instance (b : Fin 6 → ZMod 2) : Decidable (ClsC b) := by unfold ClsC; infer_instance

theorem cls_cover : ∀ b : Fin 6 → ZMod 2, ClsC b := by
  decide +kernel

@[expose] def ClsC45 (b : Fin 6 → ZMod 2) : Prop :=
  HypC e45v b → ¬ 8 ∣ (Finset.univ.filter (StabL e45v b)).card

instance (b : Fin 6 → ZMod 2) : Decidable (ClsC45 b) := by unfold ClsC45; infer_instance

theorem cls_cover45 : ∀ b : Fin 6 → ZMod 2, ClsC45 b := by
  decide +kernel

theorem e0_mul : ∀ σ ∈ e0List, ∀ τ ∈ e0List, σ * τ ∈ e0List :=
  CFSG.Permutation.FinPack.mul_mem_of_K hn6 e0List e0List _ _ hE0 hE0 A6K.mul_E0

theorem e0_sq : ∀ σ ∈ e0List, σ * σ = 1 :=
  CFSG.Permutation.FinPack.sq_of_KL hn6 e0List _ _ hE0 A6K.enc_one6 A6K.sq_E0

theorem one_mem_lists : (1 : Perm (Fin 6)) ∈ e0List ∧ (1 : Perm (Fin 6)) ∈ a4List ∧
    (1 : Perm (Fin 6)) ∈ e8List := by
  decide +kernel

@[expose] def a4Sub : Subgroup (Perm (Fin 6)) where
  carrier := {σ | σ ∈ a4List}
  mul_mem' := fun {σ τ} hσ hτ => a4_mul σ hσ τ hτ
  one_mem' := one_mem_lists.2.1
  inv_mem' := fun {σ} hσ => a4_inv σ hσ

@[expose] def e0Sub : Subgroup (Perm (Fin 6)) where
  carrier := {σ | σ ∈ e0List}
  mul_mem' := fun {σ τ} hσ hτ => e0_mul σ hσ τ hτ
  one_mem' := one_mem_lists.1
  inv_mem' := fun {σ} hσ => by
    have e : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right (e0_sq σ hσ)
    show σ⁻¹ ∈ e0List
    rw [e]
    exact hσ

@[expose] def e8Sub : Subgroup (Perm (Fin 6)) where
  carrier := {σ | σ ∈ e8List}
  mul_mem' := fun {σ τ} hσ hτ => e8_mul σ hσ τ hτ
  one_mem' := one_mem_lists.2.2
  inv_mem' := fun {σ} hσ => e8_inv σ hσ

theorem card_e8Sub : Nat.card e8Sub = 8 :=
  natCard_eq_length list_nodup.2.2 fun _ => Iff.rfl

@[expose] def normC3 (c : Perm (Fin 6)) : Subgroup (Perm (Fin 6)) where
  carrier := {σ | σ * iota0 = iota0 * σ ∧ (σ * c * σ⁻¹ = c ∨ σ * c * σ⁻¹ = c⁻¹)}
  mul_mem' := fun {σ τ} hσ hτ => by
    refine ⟨by rw [mul_assoc, hτ.1, ← mul_assoc, hσ.1, mul_assoc], ?_⟩
    have e : σ * τ * c * (σ * τ)⁻¹ = σ * (τ * c * τ⁻¹) * σ⁻¹ := by group
    rw [e]
    rcases hτ.2 with h | h <;> rw [h]
    · exact hσ.2
    · rcases hσ.2 with h' | h'
      · right
        rw [show σ * c⁻¹ * σ⁻¹ = (σ * c * σ⁻¹)⁻¹ by group, h']
      · left
        rw [show σ * c⁻¹ * σ⁻¹ = (σ * c * σ⁻¹)⁻¹ by group, h', inv_inv]
  one_mem' := ⟨by rw [one_mul, mul_one], Or.inl (by rw [one_mul, inv_one, mul_one])⟩
  inv_mem' := fun {σ} hσ => by
    refine ⟨?_, ?_⟩
    · calc σ⁻¹ * iota0 = σ⁻¹ * (iota0 * σ) * σ⁻¹ := by group
        _ = σ⁻¹ * (σ * iota0) * σ⁻¹ := by rw [hσ.1]
        _ = iota0 * σ⁻¹ := by group
    · rcases hσ.2 with h | h
      · left
        calc σ⁻¹ * c * σ⁻¹⁻¹ = σ⁻¹ * (σ * c * σ⁻¹) * σ⁻¹⁻¹ := by rw [h]
          _ = c := by group
      · right
        have e : σ⁻¹ * c⁻¹ * σ = c := by rw [← h]; group
        calc σ⁻¹ * c * σ⁻¹⁻¹ = (σ⁻¹ * c⁻¹ * σ)⁻¹ := by group
          _ = c⁻¹ := by rw [e]

theorem card_normC3 {c : Perm (Fin 6)} (hc : c ∈ a4List) (h3 : c ^ 3 = 1) (h1 : c ≠ 1) :
    Nat.card (normC3 c) = 12 := by
  rw [natCard_eq_length (l := cList.filter fun σ => decide (σ * c * σ⁻¹ = c ∨ σ * c * σ⁻¹ = c⁻¹))
    (list_nodup.1.filter _) ?_]
  · exact card_normalizer_c3 c hc h3 h1
  · intro σ
    simp only [List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨mem_cList σ h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨cList_comm σ h1, h2⟩

@[expose] def cA6 : Subgroup (Perm (Fin 6)) where
  carrier := {σ | σ * iota0 = iota0 * σ ∧ Perm.sign σ = 1}
  mul_mem' := fun {σ τ} hσ hτ =>
    ⟨by rw [mul_assoc, hτ.1, ← mul_assoc, hσ.1, mul_assoc], by rw [map_mul, hσ.2, hτ.2, one_mul]⟩
  one_mem' := ⟨by rw [one_mul, mul_one], map_one _⟩
  inv_mem' := fun {σ} hσ =>
    ⟨calc σ⁻¹ * iota0 = σ⁻¹ * (iota0 * σ) * σ⁻¹ := by group
        _ = σ⁻¹ * (σ * iota0) * σ⁻¹ := by rw [hσ.1]
        _ = iota0 * σ⁻¹ := by group, by rw [map_inv, hσ.2, inv_one]⟩

theorem card_cA6 : Nat.card cA6 = 24 := by
  rw [natCard_eq_length (l := cList.filter fun σ => decide (Perm.sign σ = 1))
    (list_nodup.1.filter _) ?_]
  · exact card_C_A6
  · intro σ
    simp only [List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨mem_cList σ h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨cList_comm σ h1, h2⟩

theorem oddOrder_mem_A4 {σ : Perm (Fin 6)} (hσ : σ ∈ cList) {m : ℕ} (hm : Odd m)
    (h : σ ^ m = 1) : σ ∈ a4List := by
  have h1 : orderOf σ ∣ m := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf σ ∣ 4 * 3 := orderOf_dvd_of_pow_eq_one (cList_exp σ hσ)
  have hodd : ¬ 2 ∣ orderOf σ := fun h2 => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr
    (h2.trans h1))
  have hcop : Nat.Coprime (orderOf σ) 4 := by
    have : Nat.Coprime 2 (orderOf σ) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
    exact (Nat.Coprime.pow_left 2 this).symm
  have h3 : orderOf σ ∣ 3 := hcop.dvd_of_dvd_mul_left h2
  exact c3_mem_a4 σ hσ (orderOf_dvd_iff_pow_eq_one.mp h3)

theorem pow_four_of_two {σ : Perm (Fin 6)} (hσ : σ ∈ cList) {k : ℕ} (h : σ ^ (2 ^ k) = 1) :
    σ ^ 4 = 1 := by
  have h1 : orderOf σ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf σ ∣ 3 * 4 := orderOf_dvd_of_pow_eq_one (cList_exp σ hσ)
  have hcop : Nat.Coprime (orderOf σ) 3 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    rw [hj]
    exact Nat.Coprime.pow_left j (by norm_num)
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_left h2)

theorem mem_e0_of_two {σ : Perm (Fin 6)} (hσ : σ ∈ a4List) {k : ℕ} (h : σ ^ (2 ^ k) = 1) :
    σ ∈ e0List := by
  have h1 : orderOf σ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf σ ∣ 3 * 2 := orderOf_dvd_of_pow_eq_one (a4_exp σ hσ)
  have hcop : Nat.Coprime (orderOf σ) 3 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    rw [hj]
    exact Nat.Coprime.pow_left j (by norm_num)
  exact a4_two σ hσ (orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_left h2))

theorem mem_E8_of_c3 : ∀ c ∈ a4List, c ^ 3 = 1 → c ≠ 1 → ∀ x ∈ cList, x ^ 4 = 1 → x ∉ e8List →
    (x * (c * x * c⁻¹)) ^ 4 ≠ 1 := by
  intro c hc hc3 hc1 x hx hx4 hx8 h4
  have h1 := allK_iff.1 A6K.e8c3_A4 _ (enc_mem_of_beq hA4 hc)
  rw [A6K.beq_pow_of_eq hn6 A6K.enc_one6 hc3, A6K.beq_one_false hn6 A6K.enc_one6 hc1] at h1
  simp only [Bool.not_true, Bool.false_or] at h1
  have h2 := allK_iff.1 h1 _ (enc_mem_of_beq hC hx)
  have hm : memK (enc x) A6K.E8C = false :=
    Bool.eq_false_iff.2 fun h => hx8 (mem_of_memKL hn6 hE8 h)
  rw [A6K.beq_pow_of_eq hn6 A6K.enc_one6 hx4, hm] at h2
  simp only [← enc_inv hn6, ← enc_mul hn6] at h2
  rw [A6K.beq_pow_of_eq hn6 A6K.enc_one6 h4] at h2
  exact absurd h2 (by decide)

theorem alt6_le_of_overgroup {X : Subgroup (Perm (Fin 6))} (hC : cA6 ≤ X) {s : Perm (Fin 6)}
    (hs : s ∈ X) (hs1 : Perm.sign s = 1) (hsC : s * iota0 ≠ iota0 * s) :
    alternatingGroup (Fin 6) ≤ X := by
  set A := alternatingGroup (Fin 6) with hAdef
  have hsimp : IsSimpleGroup ↥A := alternatingGroup.isSimpleGroup (by simp)
  have hCA : cA6 ≤ X ⊓ A := le_inf hC fun σ hσ => Equiv.Perm.mem_alternatingGroup.mpr hσ.2
  have h24 : 24 ∣ Nat.card ↥(X ⊓ A) := card_cA6 ▸ Subgroup.card_dvd_of_le hCA
  have hne : Nat.card ↥(X ⊓ A) ≠ 24 := by
    intro h
    have e : cA6 = X ⊓ A := Subgroup.eq_of_le_of_card_ge hCA (by rw [h, card_cA6])
    have hsXA : s ∈ X ⊓ A := ⟨hs, Equiv.Perm.mem_alternatingGroup.mpr hs1⟩
    rw [← e] at hsXA
    exact hsC hsXA.1
  set Y := (X ⊓ A).subgroupOf A with hYdef
  have hcY : Nat.card Y = Nat.card ↥(X ⊓ A) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hmul := Subgroup.card_mul_index Y
  rw [hcY, card_alt6] at hmul
  obtain ⟨k, hk⟩ := h24
  have hki : k * Y.index = 15 := by
    rw [hk, mul_assoc] at hmul
    omega
  have hi5 : Y.index ≤ 5 := by
    have hpos : 0 < Y.index := Nat.pos_of_ne_zero (by intro h; rw [h, mul_zero] at hki; omega)
    have hle : Y.index ≤ 15 := Nat.le_of_dvd (by norm_num) ⟨k, by rw [mul_comm]; exact hki.symm⟩
    have hk1 : k ≠ 1 := fun h => hne (by rw [hk, h])
    interval_cases h : Y.index <;> omega
  have hcore := Subgroup.index_normalCore_le_factorial_index Y
  rcases (Subgroup.normalCore_normal Y).eq_bot_or_eq_top with h | h
  · rw [h, Subgroup.index_bot, card_alt6] at hcore
    have : Nat.factorial Y.index ≤ Nat.factorial 5 := Nat.factorial_le hi5
    have h120 : Nat.factorial 5 = 120 := rfl
    omega
  · intro σ hσ
    have hm : (⟨σ, hσ⟩ : ↥A) ∈ Y := Y.normalCore_le (h ▸ Subgroup.mem_top _)
    exact (Subgroup.mem_subgroupOf.mp hm).1

theorem cert_pts :
    Perm.sign (swap 1 2 * swap 3 4 : Perm (Fin 6)) = 1 ∧
    (swap 1 2 * swap 3 4 : Perm (Fin 6)) * iota0 ≠ iota0 * (swap 1 2 * swap 3 4) ∧
    (swap 0 1 * swap 2 3 : Perm (Fin 6)) ∈ e0List ∧ (swap 0 1 * swap 4 5 : Perm (Fin 6)) ∈ e0List ∧
    ((swap 0 1 * swap 4 5) * (swap 0 1 * swap 2 3) * (swap 1 2 * swap 3 4))⁻¹ *
      ((swap 1 2 * swap 3 4) * (swap 0 1 * swap 2 3) * (swap 1 2 * swap 3 4)⁻¹) ∈ cList ∧
    ((swap 0 1 * swap 4 5) * (swap 1 2 * swap 3 4))⁻¹ *
      ((swap 1 2 * swap 3 4) * (swap 0 1 * swap 4 5) * (swap 1 2 * swap 3 4)⁻¹) ∈ cList ∧
    ((swap 0 1 * swap 2 3) * (swap 1 2 * swap 3 4))⁻¹ *
      ((swap 1 2 * swap 3 4) * (swap 0 1 * swap 4 5) * (swap 0 1 * swap 2 3) *
        (swap 1 2 * swap 3 4)⁻¹) ∈ cList := by
  decide +kernel

end CFSG.Quasithin.H13.A6
