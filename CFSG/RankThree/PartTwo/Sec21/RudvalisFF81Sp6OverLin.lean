module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over

open Matrix

abbrev V7 : Type := Fin 7 → ZMod 2

abbrev M7 : Type := Matrix (Fin 7) (Fin 7) (ZMod 2)

@[expose] def conv (a b : Fin 7 → ZMod 2) : Fin 7 → ZMod 2 :=
  fun k => ∑ i : Fin 7, a i * b (k - i)

@[expose] def sig3 (a : Fin 7 → ZMod 2) : Fin 7 → ZMod 2 := fun k => a (5 * k)

@[expose] def eU : Fin 7 → ZMod 2 := ![1, 0, 0, 0, 0, 0, 0]

@[expose] def e0v : Fin 7 → ZMod 2 := ![1, 1, 1, 1, 1, 1, 1]

@[expose] def e1v : Fin 7 → ZMod 2 := ![1, 1, 1, 0, 1, 0, 0]

@[expose] def e2v : Fin 7 → ZMod 2 := ![1, 0, 0, 1, 0, 1, 1]

noncomputable def ev (M : M7) (a : Fin 7 → ZMod 2) : M7 :=
  ∑ k : Fin 7, a k • M ^ (k : ℕ)

theorem e_sum : e0v + e1v + e2v = eU := by decide

theorem e0_idem : conv e0v e0v = e0v := by decide

theorem e1_idem : conv e1v e1v = e1v := by decide

theorem e2_idem : conv e2v e2v = e2v := by decide

theorem e01 : conv e0v e1v = 0 := by decide

theorem e02 : conv e0v e2v = 0 := by decide

theorem e12 : conv e1v e2v = 0 := by decide

theorem conv_comm (a b : Fin 7 → ZMod 2) : conv a b = conv b a := by
  funext k
  simp only [conv]
  refine Fintype.sum_equiv (Equiv.subLeft k) _ _ fun i => ?_
  simp only [Equiv.subLeft_apply, sub_sub_cancel]
  ring

theorem sig3_e1 : sig3 e1v = e2v := by decide

theorem sig3_e2 : sig3 e2v = e1v := by decide

theorem k0_rel : conv ![1, 1, 0, 0, 0, 0, 0] e0v = 0 := by decide

theorem k1_rel : conv ![1, 1, 0, 1, 0, 0, 0] e1v = 0 := by decide

theorem k2_rel : conv ![1, 0, 1, 1, 0, 0, 0] e2v = 0 := by decide

theorem k1_rel6 : conv ![1, 0, 1, 0, 0, 0, 1] e1v = 0 := by decide

theorem k2_rel6 : conv ![0, 1, 1, 0, 0, 0, 1] e2v = 0 := by decide

@[expose] def q3 (c₀ c₁ c₂ : ZMod 2) : Fin 7 → ZMod 2 := ![c₀, c₁, c₂, 0, 0, 0, 0]

theorem q3_inv : ∀ c₀ c₁ c₂ : ZMod 2, q3 c₀ c₁ c₂ ≠ 0 →
    (∃ a, conv (conv a (q3 c₀ c₁ c₂)) e1v = e1v) ∧ ∃ a, conv (conv a (q3 c₀ c₁ c₂)) e2v = e2v := by
  intro c₀ c₁ c₂ h
  fin_cases c₀ <;> fin_cases c₁ <;> fin_cases c₂
  · exact absurd (by decide) h
  · exact ⟨⟨q3 1 1 1, by decide⟩, ⟨q3 1 1 0, by decide⟩⟩
  · exact ⟨⟨q3 1 0 1, by decide⟩, ⟨q3 0 1 1, by decide⟩⟩
  · exact ⟨⟨q3 1 1 0, by decide⟩, ⟨q3 0 1 0, by decide⟩⟩
  · exact ⟨⟨q3 1 0 0, by decide⟩, ⟨q3 1 0 0, by decide⟩⟩
  · exact ⟨⟨q3 0 1 0, by decide⟩, ⟨q3 1 1 1, by decide⟩⟩
  · exact ⟨⟨q3 0 1 1, by decide⟩, ⟨q3 0 0 1, by decide⟩⟩
  · exact ⟨⟨q3 0 0 1, by decide⟩, ⟨q3 1 0 1, by decide⟩⟩

section Ev

variable {M : M7}

theorem pow_eq_pow_mod (hM : M ^ 7 = 1) (n : ℕ) : M ^ n = M ^ (n % 7) := by
  conv_lhs => rw [← Nat.div_add_mod n 7, pow_add, pow_mul, hM, one_pow, one_mul]

theorem ev_add (a b : Fin 7 → ZMod 2) : ev M (a + b) = ev M a + ev M b := by
  simp only [ev, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem ev_zero : ev M 0 = 0 := by
  simp [ev]

theorem ev_eU : ev M eU = 1 := by
  simp [ev, eU, Fin.sum_univ_seven]

theorem ev_conv (hM : M ^ 7 = 1) (a b : Fin 7 → ZMod 2) :
    ev M (conv a b) = ev M a * ev M b := by
  simp only [ev, conv, Finset.sum_smul, Fintype.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp (Equiv.addLeft i)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Equiv.coe_addLeft, add_sub_cancel_left, smul_mul_smul_comm, ← pow_add, Fin.val_add,
    ← pow_eq_pow_mod hM]

theorem ev_comm (hM : M ^ 7 = 1) (a b : Fin 7 → ZMod 2) : ev M a * ev M b = ev M b * ev M a := by
  rw [← ev_conv hM, ← ev_conv hM, conv_comm]

theorem mul_pow_of_twist {N : M7} (hNM : N * M = M ^ 3 * N) (k : ℕ) :
    N * M ^ k = M ^ (3 * k) * N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, hNM, ← mul_assoc, ← pow_add,
      show 3 * k + 3 = 3 * (k + 1) by ring]

def mul3 : Fin 7 ≃ Fin 7 := ⟨(3 * ·), (5 * ·), by decide, by decide⟩

theorem mul_ev_of_twist {N : M7} (hM : M ^ 7 = 1) (hNM : N * M = M ^ 3 * N)
    (a : Fin 7 → ZMod 2) : N * ev M a = ev M (sig3 a) * N := by
  simp only [ev, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    mul_pow_of_twist hNM]
  conv_rhs => rw [← Equiv.sum_comp mul3]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h53 : ∀ k : Fin 7, 5 * (3 * k) = k := by decide
  have hv : ∀ k : Fin 7, ((3 * k : Fin 7) : ℕ) = 3 * (k : ℕ) % 7 := by decide
  simp only [sig3, mul3, Equiv.coe_fn_mk, h53, hv, ← pow_eq_pow_mod hM]

end Ev

@[expose] def nG : M7 :=
  !![1, 0, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 1, 1]

@[expose] def nH : M7 :=
  !![1, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 1;
    0, 1, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0; 0, 0, 1, 1, 0, 0, 0]

section Decomp

variable {M N : M7}

private theorem eq_add_of_add_add (x y z : V7) (h : x + y + z = 0) : z = y + x := by
  funext i
  have h' := congrFun h i
  simp only [Pi.add_apply, Pi.zero_apply] at h' ⊢
  generalize x i = a at *
  generalize y i = b at *
  generalize z i = c at *
  revert a b c
  decide

theorem E_sum : ev M e0v + ev M e1v + ev M e2v = 1 := by
  rw [← ev_add, ← ev_add, e_sum, ev_eU]

theorem E_mulVec_sum (v : V7) : ev M e0v *ᵥ v + ev M e1v *ᵥ v + ev M e2v *ᵥ v = v := by
  rw [← add_mulVec, ← add_mulVec, E_sum, one_mulVec]

theorem E_mul (hM : M ^ 7 = 1) {a b c : Fin 7 → ZMod 2} (h : conv a b = c) :
    ev M a * ev M b = ev M c := by
  rw [← ev_conv hM, h]

theorem E_mulVec_mulVec (hM : M ^ 7 = 1) {a b c : Fin 7 → ZMod 2} (h : conv a b = c) (v : V7) :
    ev M a *ᵥ (ev M b *ᵥ v) = ev M c *ᵥ v := by
  rw [mulVec_mulVec, E_mul hM h]

theorem ev_mulVec_comm (hM : M ^ 7 = 1) (a b : Fin 7 → ZMod 2) (v : V7) :
    ev M a *ᵥ (ev M b *ᵥ v) = ev M b *ᵥ (ev M a *ᵥ v) := by
  rw [mulVec_mulVec, mulVec_mulVec, ev_comm hM]

theorem ev_k0 : ev M ![1, 1, 0, 0, 0, 0, 0] = 1 + M := by
  simp [ev, Fin.sum_univ_seven]

theorem ev_k1 : ev M ![1, 1, 0, 1, 0, 0, 0] = 1 + M + M ^ 3 := by
  simp [ev, Fin.sum_univ_seven]

theorem ev_k2 : ev M ![1, 0, 1, 1, 0, 0, 0] = 1 + M ^ 2 + M ^ 3 := by
  simp [ev, Fin.sum_univ_seven]

theorem ev_k16 : ev M ![1, 0, 1, 0, 0, 0, 1] = 1 + M ^ 2 + M ^ 6 := by
  simp [ev, Fin.sum_univ_seven]

theorem ev_k26 : ev M ![0, 1, 1, 0, 0, 0, 1] = M + M ^ 2 + M ^ 6 := by
  simp [ev, Fin.sum_univ_seven]

theorem ev_q3 (c₀ c₁ c₂ : ZMod 2) : ev M (q3 c₀ c₁ c₂) = c₀ • 1 + c₁ • M + c₂ • M ^ 2 := by
  simp [ev, q3, Fin.sum_univ_seven]

theorem K1_rel (hM : M ^ 7 = 1) {v : V7} (hv : ev M e1v *ᵥ v = v) :
    M ^ 3 *ᵥ v = M *ᵥ v + v := by
  have h := E_mulVec_mulVec hM k1_rel v
  rw [hv, ev_k1, ev_zero, zero_mulVec, add_mulVec, add_mulVec, one_mulVec] at h
  exact eq_add_of_add_add _ _ _ h

theorem K1_rel6 (hM : M ^ 7 = 1) {v : V7} (hv : ev M e1v *ᵥ v = v) :
    M ^ 6 *ᵥ v = M ^ 2 *ᵥ v + v := by
  have h := E_mulVec_mulVec hM k1_rel6 v
  rw [hv, ev_k16, ev_zero, zero_mulVec, add_mulVec, add_mulVec, one_mulVec] at h
  exact eq_add_of_add_add _ _ _ h

theorem K2_rel (hM : M ^ 7 = 1) {v : V7} (hv : ev M e2v *ᵥ v = v) :
    M ^ 3 *ᵥ v = M ^ 2 *ᵥ v + v := by
  have h := E_mulVec_mulVec hM k2_rel v
  rw [hv, ev_k2, ev_zero, zero_mulVec, add_mulVec, add_mulVec, one_mulVec] at h
  have := eq_add_of_add_add _ _ _ h
  rw [this, add_comm]

theorem K2_rel6 (hM : M ^ 7 = 1) {v : V7} (hv : ev M e2v *ᵥ v = v) :
    M ^ 6 *ᵥ v = M ^ 2 *ᵥ v + M *ᵥ v := by
  have h := E_mulVec_mulVec hM k2_rel6 v
  rw [hv, ev_k26, ev_zero, zero_mulVec, add_mulVec, add_mulVec] at h
  have := eq_add_of_add_add _ _ _ h
  rw [this]

@[expose] def Kset (A : M7) : Finset V7 := Finset.univ.filter fun v => A *ᵥ v = v

theorem mem_Kset {A : M7} {v : V7} : v ∈ Kset A ↔ A *ᵥ v = v := by
  simp [Kset]

theorem E_idem_mulVec (hM : M ^ 7 = 1) {a : Fin 7 → ZMod 2} (ha : conv a a = a) (v : V7) :
    ev M a *ᵥ v ∈ Kset (ev M a) := by
  rw [mem_Kset, E_mulVec_mulVec hM ha]

set_option linter.constructorNameAsVariable false in
theorem card_K_mul (hM : M ^ 7 = 1) :
    (Kset (ev M e0v)).card * (Kset (ev M e1v)).card * (Kset (ev M e2v)).card = 128 := by
  rw [← Finset.card_product, ← Finset.card_product]
  have hcard : (Finset.univ : Finset V7).card = 128 := by
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    norm_num
  rw [← hcard]
  symm
  refine Finset.card_nbij' (fun v => ((ev M e0v *ᵥ v, ev M e1v *ᵥ v), ev M e2v *ᵥ v))
    (fun x => x.1.1 + x.1.2 + x.2) ?_ ?_ ?_ ?_
  · intro v _
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe]
    exact ⟨⟨E_idem_mulVec hM e0_idem v, E_idem_mulVec hM e1_idem v⟩,
      E_idem_mulVec hM e2_idem v⟩
  · intro _ _
    exact Finset.mem_coe.mpr (Finset.mem_univ _)
  · intro v _
    exact E_mulVec_sum v
  · rintro ⟨⟨a, b⟩, c⟩ hx
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_Kset] at hx
    obtain ⟨⟨ha, hb⟩, hc⟩ := hx
    have e01' : conv e0v e1v = 0 := e01
    have e10' : conv e1v e0v = 0 := by rw [conv_comm]; exact e01
    have e02' : conv e0v e2v = 0 := e02
    have e20' : conv e2v e0v = 0 := by rw [conv_comm]; exact e02
    have e12' : conv e1v e2v = 0 := e12
    have e21' : conv e2v e1v = 0 := by rw [conv_comm]; exact e12
    have z : ∀ {x y : Fin 7 → ZMod 2} {u : V7}, conv x y = 0 → ev M y *ᵥ u = u →
        ev M x *ᵥ u = 0 := fun hxy hu => by
      rw [← hu, E_mulVec_mulVec hM hxy, ev_zero, zero_mulVec]
    simp only [mulVec_add, ha, hb, hc, z e01' hb, z e02' hc, z e10' ha, z e12' hc, z e20' ha,
      z e21' hb, add_zero, zero_add]

theorem N_E1 (hM : M ^ 7 = 1) (hNM : N * M = M ^ 3 * N) : N * ev M e1v = ev M e2v * N := by
  rw [mul_ev_of_twist hM hNM, sig3_e1]

theorem N_E2 (hM : M ^ 7 = 1) (hNM : N * M = M ^ 3 * N) : N * ev M e2v = ev M e1v * N := by
  rw [mul_ev_of_twist hM hNM, sig3_e2]

theorem N2_E1 (hM : M ^ 7 = 1) (hNM : N * M = M ^ 3 * N) :
    N ^ 2 * ev M e1v = ev M e1v * N ^ 2 := by
  rw [pow_two, mul_assoc, N_E1 hM hNM, ← mul_assoc, N_E2 hM hNM, mul_assoc]

theorem N_mulVec_injective (hN : N ^ 6 = 1) : Function.Injective (N *ᵥ ·) := by
  intro v v' h
  have h' := congrArg (N ^ 5 *ᵥ ·) h
  simp only [mulVec_mulVec, ← pow_succ, hN, one_mulVec] at h'
  exact h'

theorem N_K1 (hM : M ^ 7 = 1) (hNM : N * M = M ^ 3 * N) {v : V7} (hv : ev M e1v *ᵥ v = v) :
    ev M e2v *ᵥ (N *ᵥ v) = N *ᵥ v := by
  rw [mulVec_mulVec, ← N_E1 hM hNM, ← mulVec_mulVec, hv]

theorem N_K2 (hM : M ^ 7 = 1) (hNM : N * M = M ^ 3 * N) {v : V7} (hv : ev M e2v *ᵥ v = v) :
    ev M e1v *ᵥ (N *ᵥ v) = N *ᵥ v := by
  rw [mulVec_mulVec, ← N_E2 hM hNM, ← mulVec_mulVec, hv]

theorem card_K1_eq (hM : M ^ 7 = 1) (hN : N ^ 6 = 1) (hNM : N * M = M ^ 3 * N) :
    (Kset (ev M e1v)).card = (Kset (ev M e2v)).card := by
  apply le_antisymm
  · refine Finset.card_le_card_of_injOn (N *ᵥ ·) (fun v hv => ?_)
      (fun v _ v' _ h => N_mulVec_injective hN h)
    rw [Finset.mem_coe, mem_Kset] at hv ⊢
    exact N_K1 hM hNM hv
  · refine Finset.card_le_card_of_injOn (N *ᵥ ·) (fun v hv => ?_)
      (fun v _ v' _ h => N_mulVec_injective hN h)
    rw [Finset.mem_coe, mem_Kset] at hv ⊢
    exact N_K2 hM hNM hv

private theorem q3_add (c₀ c₁ c₂ d₀ d₁ d₂ : ZMod 2) :
    q3 c₀ c₁ c₂ + q3 d₀ d₁ d₂ = q3 (c₀ + d₀) (c₁ + d₁) (c₂ + d₂) := by
  revert c₀ c₁ c₂ d₀ d₁ d₂
  decide

private theorem q3_eq_zero : ∀ c₀ c₁ c₂ d₀ d₁ d₂ : ZMod 2,
    q3 (c₀ + d₀) (c₁ + d₁) (c₂ + d₂) = 0 → c₀ = d₀ ∧ c₁ = d₁ ∧ c₂ = d₂ := by
  decide

private theorem add_self_V7 (v : V7) : v + v = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize v i = a
  revert a
  decide

theorem q3_inj (hM : M ^ 7 = 1) {e : Fin 7 → ZMod 2} (he : e = e1v ∨ e = e2v) {w : V7}
    (hw : ev M e *ᵥ w = w) (hw0 : w ≠ 0) {c₀ c₁ c₂ d₀ d₁ d₂ : ZMod 2}
    (h : ev M (q3 c₀ c₁ c₂) *ᵥ w = ev M (q3 d₀ d₁ d₂) *ᵥ w) :
    c₀ = d₀ ∧ c₁ = d₁ ∧ c₂ = d₂ := by
  have h0 : ev M (q3 (c₀ + d₀) (c₁ + d₁) (c₂ + d₂)) *ᵥ w = 0 := by
    rw [← q3_add, ev_add, add_mulVec, h, add_self_V7]
  by_contra hne
  have hr : q3 (c₀ + d₀) (c₁ + d₁) (c₂ + d₂) ≠ 0 := fun h' => hne (q3_eq_zero _ _ _ _ _ _ h')
  obtain ⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩⟩ := q3_inv _ _ _ hr
  have key : ∀ a, conv (conv a (q3 (c₀ + d₀) (c₁ + d₁) (c₂ + d₂))) e = e → w = 0 := by
    intro a ha
    rw [← hw, ← ha, ev_conv hM, ev_conv hM, ← mulVec_mulVec, hw, ← mulVec_mulVec, h0,
      mulVec_zero]
  rcases he with rfl | rfl
  · exact hw0 (key a₁ ha₁)
  · exact hw0 (key a₂ ha₂)

theorem eight_le_card (hM : M ^ 7 = 1) {e : Fin 7 → ZMod 2} (he : e = e1v ∨ e = e2v)
    {w : V7} (hw : ev M e *ᵥ w = w) (hw0 : w ≠ 0) : 8 ≤ (Kset (ev M e)).card := by
  have hidem : conv e e = e := by rcases he with rfl | rfl <;> decide
  let F : ZMod 2 × ZMod 2 × ZMod 2 → V7 := fun c => ev M (q3 c.1 c.2.1 c.2.2) *ᵥ w
  have hF : Function.Injective F := by
    rintro ⟨c₀, c₁, c₂⟩ ⟨d₀, d₁, d₂⟩ h
    obtain ⟨h₀, h₁, h₂⟩ := q3_inj hM he hw hw0 h
    simp only at h₀ h₁ h₂
    rw [h₀, h₁, h₂]
  have hsub : Finset.univ.image F ⊆ Kset (ev M e) := by
    intro v hv
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hv
    rw [mem_Kset]
    show ev M e *ᵥ (ev M (q3 c.1 c.2.1 c.2.2) *ᵥ w) = ev M (q3 c.1 c.2.1 c.2.2) *ᵥ w
    rw [ev_mulVec_comm hM, hw]
  have := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injective _ hF, Finset.card_univ] at this

private theorem pow_mulVec_fix {x : V7} (hx : M *ᵥ x = x) (k : ℕ) : M ^ k *ᵥ x = x := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← mulVec_mulVec, hx, ih]

theorem E0_fix {x : V7} (hx : M *ᵥ x = x) : ev M e0v *ᵥ x = x := by
  have h7 : ∀ v : V7, v + v + v + v + v + v + v = v := by
    intro v
    funext i
    simp only [Pi.add_apply]
    generalize v i = a
    revert a
    decide
  simp only [ev, e0v, Fin.sum_univ_seven, add_mulVec, smul_mulVec, pow_mulVec_fix hx]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul]
  exact h7 x

private theorem N_mul_N5 (hN : N ^ 6 = 1) : N * N ^ 5 = 1 := by
  rw [← pow_succ']
  exact hN

theorem exists_K1 (hM : M ^ 7 = 1) (hN : N ^ 6 = 1) (hNM : N * M = M ^ 3 * N) (hM1 : M ≠ 1) :
    ∃ w : V7, ev M e1v *ᵥ w = w ∧ w ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hE1 : ev M e1v = 0 := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    rw [zero_mulVec]
    exact hcon _ (E_mulVec_mulVec hM e1_idem _)
  have hE2 : ev M e2v = 0 := by
    have h := N_E1 hM hNM
    rw [hE1, mul_zero] at h
    calc ev M e2v = ev M e2v * (N * N ^ 5) := by rw [N_mul_N5 hN, mul_one]
      _ = 0 := by rw [← mul_assoc, ← h, zero_mul]
  have hE0 : ev M e0v = 1 := by
    have := E_sum (M := M)
    rwa [hE1, hE2, add_zero, add_zero] at this
  apply hM1
  have h := E_mul hM k0_rel
  rw [ev_k0, hE0, mul_one, ev_zero] at h
  ext i j
  have h' := congrFun (congrFun h i) j
  simp only [Matrix.add_apply, Matrix.zero_apply] at h'
  generalize M i j = a at *
  generalize (1 : M7) i j = b at *
  revert a b
  decide

theorem card_K1 (hM : M ^ 7 = 1) (hN : N ^ 6 = 1) (hNM : N * M = M ^ 3 * N) (hM1 : M ≠ 1)
    {x₀ : V7} (hx₀ : x₀ ≠ 0) (hMx : M *ᵥ x₀ = x₀) : (Kset (ev M e1v)).card = 8 := by
  obtain ⟨w, hw, hw0⟩ := exists_K1 hM hN hNM hM1
  have h8 := eight_le_card hM (Or.inl rfl) hw hw0
  have h2 : 2 ≤ (Kset (ev M e0v)).card := by
    have hsub : ({0, x₀} : Finset V7) ⊆ Kset (ev M e0v) := by
      intro v hv
      rw [Finset.mem_insert, Finset.mem_singleton] at hv
      rw [mem_Kset]
      rcases hv with rfl | rfl
      · exact mulVec_zero _
      · exact E0_fix hMx
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair (Ne.symm hx₀)] at this
  have hmul := card_K_mul hM
  rw [← card_K1_eq hM hN hNM] at hmul
  generalize (Kset (ev M e0v)).card = a at *
  generalize (Kset (ev M e1v)).card = b at *
  refine le_antisymm ?_ h8
  by_contra hlt
  have hb : 9 ≤ b := by omega
  have : 2 * 9 * 9 ≤ a * b * b := Nat.mul_le_mul (Nat.mul_le_mul h2 hb) hb
  omega

theorem exists_fix_N2 (hM : M ^ 7 = 1) (hN : N ^ 6 = 1) (hNM : N * M = M ^ 3 * N) (hM1 : M ≠ 1)
    {x₀ : V7} (hx₀ : x₀ ≠ 0) (hMx : M *ᵥ x₀ = x₀) :
    ∃ w₁ : V7, ev M e1v *ᵥ w₁ = w₁ ∧ w₁ ≠ 0 ∧ N ^ 2 *ᵥ w₁ = w₁ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set S := (Kset (ev M e1v)).erase 0 with hS
  have hcard : S.card = 7 := by
    rw [hS, Finset.card_erase_of_mem (by rw [mem_Kset]; exact mulVec_zero _),
      card_K1 hM hN hNM hM1 hx₀ hMx]
  have hinj : ∀ k : ℕ, ∀ v : V7, N ^ k *ᵥ v = 0 → v = 0 := by
    intro k v h
    have h6 : N ^ (6 * k) = 1 := by rw [pow_mul, hN, one_pow]
    have : N ^ (6 * k - k) * N ^ k = 1 := by
      rw [← pow_add, Nat.sub_add_cancel (by omega), h6]
    rw [← one_mulVec v, ← this, ← mulVec_mulVec, h, mulVec_zero]
  have hcomm : ∀ k : ℕ, N ^ (2 * k) * ev M e1v = ev M e1v * N ^ (2 * k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, mul_assoc, N2_E1 hM hNM,
        ← mul_assoc, ih, mul_assoc]
  have hmem : ∀ k : ℕ, ∀ v ∈ S, N ^ (2 * k) *ᵥ v ∈ S := by
    intro k v hv
    rw [hS, Finset.mem_erase, mem_Kset] at hv ⊢
    refine ⟨fun h => hv.1 (hinj _ v h), ?_⟩
    rw [mulVec_mulVec, ← hcomm, ← mulVec_mulVec, hv.2]
  let σ : Equiv.Perm S :=
    { toFun := fun v => ⟨N ^ (2 * 1) *ᵥ v.1, hmem 1 v.1 v.2⟩
      invFun := fun v => ⟨N ^ (2 * 2) *ᵥ v.1, hmem 2 v.1 v.2⟩
      left_inv := fun v => Subtype.ext (by
        simp only [mulVec_mulVec, ← pow_add]
        rw [show 2 * 2 + 2 * 1 = 6 by rfl, hN, one_mulVec])
      right_inv := fun v => Subtype.ext (by
        simp only [mulVec_mulVec, ← pow_add]
        rw [show 2 * 1 + 2 * 2 = 6 by rfl, hN, one_mulVec]) }
  have hσ : σ ^ 3 ^ 1 = 1 := by
    ext v
    simp only [pow_one, pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    simp only [σ, Equiv.coe_fn_mk, mulVec_mulVec, ← pow_add]
    rw [show 2 * 1 + (2 * 1 + 2 * 1) = 6 by rfl, hN, one_mulVec]
  have h3 : ¬ 3 ∣ Fintype.card S := by
    rw [Fintype.card_coe, hcard]
    decide
  obtain ⟨⟨w, hw⟩, hfix⟩ := Equiv.Perm.exists_fixed_point_of_prime h3 hσ
  rw [hS, Finset.mem_erase, mem_Kset] at hw
  refine ⟨w, hw.2, hw.1, ?_⟩
  have := congrArg Subtype.val hfix
  exact this

end Decomp

@[expose] def basisMat (M : M7) (x₀ w₁ w₂ : V7) : M7 :=
  Matrix.of fun i j => (![x₀, w₁, M *ᵥ w₁, M ^ 2 *ᵥ w₁, w₂, M *ᵥ w₂, M ^ 2 *ᵥ w₂] j) i

theorem ofCols_mulVec (v : Fin 7 → V7) (c : V7) :
    (Matrix.of fun i j => v j i) *ᵥ c = ∑ j, c j • v j := by
  funext i
  simp only [mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    mul_comm]

theorem basisMat_mulVec (M : M7) (x₀ w₁ w₂ c : V7) : basisMat M x₀ w₁ w₂ *ᵥ c =
    c 0 • x₀ + c 1 • w₁ + c 2 • (M *ᵥ w₁) + c 3 • (M ^ 2 *ᵥ w₁) + c 4 • w₂ +
      c 5 • (M *ᵥ w₂) + c 6 • (M ^ 2 *ᵥ w₂) := by
  rw [basisMat, ofCols_mulVec, Fin.sum_univ_seven]
  simp only [Matrix.cons_val]

theorem nG_mulVec (c : V7) : nG *ᵥ c = ![c 0, c 3, c 1 + c 3, c 2, c 6, c 4, c 5 + c 6] := by
  funext i
  fin_cases i <;> simp [nG, mulVec, dotProduct, Fin.sum_univ_seven]

theorem nH_mulVec (c : V7) :
    nH *ᵥ c = ![c 0, c 4 + c 5 + c 6, c 5, c 6, c 1 + c 2, c 3, c 2 + c 3] := by
  funext i
  fin_cases i <;> simp [nH, mulVec, dotProduct, Fin.sum_univ_seven]

private theorem ev_q3_mulVec (M : M7) (a b c : ZMod 2) (w : V7) :
    ev M (q3 a b c) *ᵥ w = a • w + b • (M *ᵥ w) + c • (M ^ 2 *ᵥ w) := by
  rw [ev_q3, add_mulVec, add_mulVec, smul_mulVec, smul_mulVec, smul_mulVec, one_mulVec]

theorem basisMat_ker {M : M7} {x₀ w₁ w₂ : V7} (hM : M ^ 7 = 1) (hx₀ : x₀ ≠ 0)
    (hMx : M *ᵥ x₀ = x₀) (hw₁ : ev M e1v *ᵥ w₁ = w₁) (hw₁0 : w₁ ≠ 0)
    (hw₂ : ev M e2v *ᵥ w₂ = w₂) (hw₂0 : w₂ ≠ 0) (c : V7)
    (hc : basisMat M x₀ w₁ w₂ *ᵥ c = 0) : c = 0 := by
  rw [basisMat_mulVec] at hc
  have hsum : c 0 • x₀ + ev M (q3 (c 1) (c 2) (c 3)) *ᵥ w₁ +
      ev M (q3 (c 4) (c 5) (c 6)) *ᵥ w₂ = 0 := by
    rw [ev_q3_mulVec, ev_q3_mulVec]
    calc _ = c 0 • x₀ + c 1 • w₁ + c 2 • (M *ᵥ w₁) + c 3 • (M ^ 2 *ᵥ w₁) + c 4 • w₂ +
          c 5 • (M *ᵥ w₂) + c 6 • (M ^ 2 *ᵥ w₂) := by abel
      _ = 0 := hc
  have hx0 : ev M e0v *ᵥ x₀ = x₀ := E0_fix hMx
  have z : ∀ {x y : Fin 7 → ZMod 2} {u : V7}, conv x y = 0 → ev M y *ᵥ u = u →
      ev M x *ᵥ u = 0 := fun hxy hu => by
    rw [← hu, E_mulVec_mulVec hM hxy, ev_zero, zero_mulVec]
  have e10' : conv e1v e0v = 0 := by rw [conv_comm]; exact e01
  have e20' : conv e2v e0v = 0 := by rw [conv_comm]; exact e02
  have e21' : conv e2v e1v = 0 := by rw [conv_comm]; exact e12
  have hBK : ev M e1v *ᵥ (ev M (q3 (c 1) (c 2) (c 3)) *ᵥ w₁) =
      ev M (q3 (c 1) (c 2) (c 3)) *ᵥ w₁ := by rw [ev_mulVec_comm hM, hw₁]
  have hCK : ev M e2v *ᵥ (ev M (q3 (c 4) (c 5) (c 6)) *ᵥ w₂) =
      ev M (q3 (c 4) (c 5) (c 6)) *ᵥ w₂ := by rw [ev_mulVec_comm hM, hw₂]
  have hB0 : ev M (q3 (c 1) (c 2) (c 3)) *ᵥ w₁ = 0 := by
    have h1 := congrArg (ev M e1v *ᵥ ·) hsum
    simp only [mulVec_add, mulVec_smul, mulVec_zero, z e10' hx0, z e12 hCK, hBK, smul_zero,
      zero_add, add_zero] at h1
    exact h1
  have hC0 : ev M (q3 (c 4) (c 5) (c 6)) *ᵥ w₂ = 0 := by
    have h2 := congrArg (ev M e2v *ᵥ ·) hsum
    simp only [mulVec_add, mulVec_smul, mulVec_zero, z e20' hx0, z e21' hBK, hCK, smul_zero,
      zero_add, add_zero] at h2
    exact h2
  have hq0 : ∀ w : V7, ev M (q3 0 0 0) *ᵥ w = 0 := fun w => by
    rw [ev_q3_mulVec]
    simp
  have hq1 := q3_inj hM (Or.inl rfl) hw₁ hw₁0 (hB0.trans (hq0 w₁).symm)
  have hq2 := q3_inj hM (Or.inr rfl) hw₂ hw₂0 (hC0.trans (hq0 w₂).symm)
  rw [hB0, hC0, add_zero, add_zero] at hsum
  have hc0 : c 0 = 0 := by
    by_contra hne
    have key : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
    rw [key _ hne, one_smul] at hsum
    exact hx₀ hsum
  funext i
  fin_cases i
  · exact hc0
  · exact hq1.1
  · exact hq1.2.1
  · exact hq1.2.2
  · exact hq2.1
  · exact hq2.2.1
  · exact hq2.2.2

theorem normal_form {M N : M7} {x₀ : V7} (hM : M ^ 7 = 1) (hN : N ^ 6 = 1)
    (hNM : N * M = M ^ 3 * N) (hM1 : M ≠ 1) (hx₀ : x₀ ≠ 0) (hMx : M *ᵥ x₀ = x₀)
    (hNx : N *ᵥ x₀ = x₀) :
    ∃ P : M7, IsUnit P ∧ P *ᵥ Pi.single 0 1 = x₀ ∧ M * P = P * nG ∧ N * P = P * nH := by
  obtain ⟨w₁, hw₁, hw₁0, hNw₁⟩ := exists_fix_N2 hM hN hNM hM1 hx₀ hMx
  obtain ⟨w₂, hw₂def⟩ : ∃ w₂ : V7, N *ᵥ w₁ = w₂ := ⟨_, rfl⟩
  have hw₂ : ev M e2v *ᵥ w₂ = w₂ := hw₂def ▸ N_K1 hM hNM hw₁
  have hw₂0 : w₂ ≠ 0 := by
    rintro rfl
    exact hw₁0 (N_mulVec_injective hN (hw₂def.trans (mulVec_zero N).symm))
  have hNw₂ : N *ᵥ w₂ = w₁ := by rw [← hw₂def, mulVec_mulVec, ← pow_two, hNw₁]
  have h31 := K1_rel hM hw₁
  have h61 := K1_rel6 hM hw₁
  have h32 := K2_rel hM hw₂
  have h62 := K2_rel6 hM hw₂
  have hM2 : ∀ v : V7, M *ᵥ (M *ᵥ v) = M ^ 2 *ᵥ v := fun v => by rw [mulVec_mulVec, ← pow_two]
  have hM3 : ∀ v : V7, M *ᵥ (M ^ 2 *ᵥ v) = M ^ 3 *ᵥ v := fun v => by
    rw [mulVec_mulVec, ← pow_succ']
  have hNM1 : ∀ v : V7, N *ᵥ (M *ᵥ v) = M ^ 3 *ᵥ (N *ᵥ v) := fun v => by
    rw [mulVec_mulVec, hNM, ← mulVec_mulVec]
  have hNM2 : ∀ v : V7, N *ᵥ (M ^ 2 *ᵥ v) = M ^ 6 *ᵥ (N *ᵥ v) := fun v => by
    rw [mulVec_mulVec, mul_pow_of_twist hNM 2, ← mulVec_mulVec]
  refine ⟨basisMat M x₀ w₁ w₂, ?_, ?_, ?_, ?_⟩
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hker := basisMat_ker hM hx₀ hMx hw₁ hw₁0 hw₂ hw₂0
    refine (Matrix.mulVec_injective_iff_isUnit (K := ZMod 2)).mp fun c c' h => ?_
    have h0 := hker (c - c') (by rw [mulVec_sub, h, sub_self])
    exact sub_eq_zero.mp h0
  · rw [basisMat_mulVec]
    simp
  · refine Matrix.ext_iff_mulVec.mpr fun c => ?_
    rw [← mulVec_mulVec, ← mulVec_mulVec, nG_mulVec, basisMat_mulVec, basisMat_mulVec]
    simp only [mulVec_add, mulVec_smul, hMx, hM2, hM3, h31, h32]
    simp only [Matrix.cons_val]
    module
  · refine Matrix.ext_iff_mulVec.mpr fun c => ?_
    rw [← mulVec_mulVec, ← mulVec_mulVec, nH_mulVec, basisMat_mulVec, basisMat_mulVec]
    simp only [mulVec_add, mulVec_smul, hNx, hNM1, hNM2, hw₂def, hNw₂, h31, h61, h32, h62]
    simp only [Matrix.cons_val]
    module

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Over
