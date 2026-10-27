module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5zz
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Group.Subgroup.Ker

public section

namespace CFSG.Quasithin.H13.S127.FourA

open Equiv Equiv.Perm S127.Mod

@[expose] def pp (a b : Fin 6) : Perm (Fin 6) := swap (swap 0 a 1) b * swap 0 a

theorem pp_spec : ∀ a b : Fin 6, a ≠ b → pp a b 0 = a ∧ pp a b 1 = b := by decide

theorem pp_zero_one : pp 0 1 = 1 := by decide

@[expose] def qq (a b : Fin 6) : Perm (Fin 6) := swap (swap 2 a 3) b * swap 2 a

theorem qq_spec : ∀ a b : Fin 6, a ≠ 0 → a ≠ 1 → b ≠ 0 → b ≠ 1 → a ≠ b →
    swap 0 1 * qq a b = qq a b * swap 0 1 ∧ swap a b * qq a b = qq a b * swap 2 3 := by
  decide

@[expose] def rr (a b : Fin 6) : Perm (Fin 6) := swap (swap 1 a 2) b * swap 1 a

theorem rr_spec : ∀ a b : Fin 6, a ≠ 0 → b ≠ 0 → a ≠ b →
    rr a b 0 = 0 ∧ rr a b 1 = a ∧ rr a b 2 = b := by decide

theorem act4_trans : ∀ m < 16, m ≠ 0 → ∃ a b : Fin 6, act4 ⇑(swap 0 a * swap 1 b) m = 1 := by
  decide

@[expose] def NotZO (i : Fin 6) : Prop := i ≠ 0 ∧ i ≠ 1

instance : DecidablePred NotZO := fun _ => inferInstanceAs (Decidable (_ ∧ _))

theorem mem_closure_of_fix {σ : Perm (Fin 6)} (h0 : σ 0 = 0) (h1 : σ 1 = 1) :
    σ ∈ Subgroup.closure {τ : Perm (Fin 6) | ∃ a b : Fin 6, NotZO a ∧ NotZO b ∧ a ≠ b ∧
      τ = swap a b} := by
  have hp : ∀ x, NotZO (σ x) ↔ NotZO x := by
    intro x
    constructor
    · rintro ⟨hx0, hx1⟩
      exact ⟨fun h => hx0 (by rw [h, h0]), fun h => hx1 (by rw [h, h1])⟩
    · rintro ⟨hx0, hx1⟩
      exact ⟨fun h => hx0 (σ.injective (h.trans h0.symm)),
        fun h => hx1 (σ.injective (h.trans h1.symm))⟩
  have hfix : ∀ x, σ x ≠ x → NotZO x := fun x hx =>
    ⟨fun h => hx (by rw [h, h0]), fun h => hx (by rw [h, h1])⟩
  rw [← ofSubtype_subtypePerm hp hfix]
  have htop : σ.subtypePerm hp ∈ Subgroup.closure {τ : Perm (Subtype NotZO) | τ.IsSwap} := by
    rw [closure_isSwap]
    trivial
  have hmap := Subgroup.mem_map_of_mem (ofSubtype (p := NotZO)) htop
  rw [MonoidHom.map_closure] at hmap
  refine Subgroup.closure_mono ?_ hmap
  rintro _ ⟨τ, ⟨x, y, hxy, rfl⟩, rfl⟩
  exact ⟨x, y, x.2, y.2, fun h => hxy (Subtype.ext h), ofSubtype_swap_eq x y⟩

variable {W : Type*} [CommGroup W]

@[expose] def bpow (w : W) (b : Bool) : W := if b then w else 1

theorem inv_eq (hW : ∀ w : W, w * w = 1) (w : W) : w⁻¹ = w :=
  inv_eq_of_mul_eq_one_right (hW w)

theorem bpow_xor (hW : ∀ w : W, w * w = 1) (w : W) (b b' : Bool) :
    bpow w (b ^^ b') = bpow w b * bpow w b' := by
  cases b <;> cases b' <;> simp [bpow, hW]

variable (ρ : Perm (Fin 6) →* MulAut W)

theorem rho_mul_apply (σ τ : Perm (Fin 6)) (w : W) : ρ (σ * τ) w = ρ σ (ρ τ w) := by
  rw [map_mul, MulAut.mul_apply]

theorem rho_inv_apply (σ : Perm (Fin 6)) (w : W) : ρ σ⁻¹ (ρ σ w) = w := by
  rw [← rho_mul_apply, inv_mul_cancel, map_one, MulAut.one_apply]

theorem rho_apply_inv (σ : Perm (Fin 6)) (w : W) : ρ σ (ρ σ⁻¹ w) = w := by
  rw [← rho_mul_apply, mul_inv_cancel, map_one, MulAut.one_apply]

theorem bpow_apply (σ : Perm (Fin 6)) (w : W) (b : Bool) : ρ σ (bpow w b) = bpow (ρ σ w) b := by
  cases b <;> simp [bpow]

variable {ρ}

theorem quad_symm (hQ : ∀ w, ρ (swap 0 1) (ρ (swap 2 3) w * w⁻¹) = ρ (swap 2 3) w * w⁻¹)
    (w : W) : ρ (swap 2 3) (ρ (swap 0 1) w * w⁻¹) = ρ (swap 0 1) w * w⁻¹ := by
  have hc : (swap (2 : Fin 6) 3) * swap 0 1 = swap 0 1 * swap 2 3 := by decide
  have h1 : ρ (swap 2 3) (ρ (swap 0 1) w) = ρ (swap 0 1) (ρ (swap 2 3) w) := by
    rw [← rho_mul_apply, hc, rho_mul_apply]
  have h2 := hQ w
  rw [map_mul, map_inv] at h2
  have h3 : ρ (swap 0 1) (ρ (swap 2 3) w) = ρ (swap 2 3) w * w⁻¹ * ρ (swap 0 1) w := by
    rw [← h2, inv_mul_cancel_right]
  rw [map_mul, map_inv, h1, h3]
  calc ρ (swap 2 3) w * w⁻¹ * ρ (swap 0 1) w * (ρ (swap 2 3) w)⁻¹
      = w⁻¹ * ρ (swap 0 1) w * ρ (swap 2 3) w * (ρ (swap 2 3) w)⁻¹ := by
        rw [mul_assoc (ρ (swap 2 3) w), mul_comm (ρ (swap 2 3) w), mul_assoc w⁻¹]
    _ = ρ (swap 0 1) w * w⁻¹ := by rw [mul_inv_cancel_right, mul_comm]

theorem swap_fix (hQ : ∀ w, ρ (swap 0 1) (ρ (swap 2 3) w * w⁻¹) = ρ (swap 2 3) w * w⁻¹)
    {a b : Fin 6} (ha : NotZO a) (hb : NotZO b) (hab : a ≠ b) (w : W) :
    ρ (swap a b) (ρ (swap 0 1) w * w⁻¹) = ρ (swap 0 1) w * w⁻¹ := by
  obtain ⟨hc1, hc2⟩ := qq_spec a b ha.1 ha.2 hb.1 hb.2 hab
  obtain ⟨w', rfl⟩ : ∃ w', w = ρ (qq a b) w' := ⟨_, (rho_apply_inv ρ _ w).symm⟩
  have key : ρ (swap 0 1) (ρ (qq a b) w') * (ρ (qq a b) w')⁻¹ =
      ρ (qq a b) (ρ (swap 0 1) w' * w'⁻¹) := by
    rw [← rho_mul_apply, hc1, rho_mul_apply, map_mul (ρ (qq a b)), map_inv]
  rw [key, ← rho_mul_apply, hc2, rho_mul_apply, quad_symm hQ]

theorem stab_fix (hW : ∀ w : W, w * w = 1)
    (hQ : ∀ w, ρ (swap 0 1) (ρ (swap 2 3) w * w⁻¹) = ρ (swap 2 3) w * w⁻¹) (w₀ : W)
    {σ : Perm (Fin 6)} (h0 : σ 0 = 0 ∨ σ 0 = 1) (h1 : σ 1 = 0 ∨ σ 1 = 1) :
    ρ σ (ρ (swap 0 1) w₀ * w₀⁻¹) = ρ (swap 0 1) w₀ * w₀⁻¹ := by
  set c := ρ (swap 0 1) w₀ * w₀⁻¹ with hc
  let F : Subgroup (Perm (Fin 6)) :=
    { carrier := {τ | ρ τ c = c}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ρ a c = c := ha
        have hb' : ρ b c = c := hb
        show ρ (a * b) c = c
        rw [rho_mul_apply, hb', ha']
      one_mem' := by
        show ρ 1 c = c
        rw [map_one, MulAut.one_apply]
      inv_mem' := fun {a} ha => by
        have ha' : ρ a c = c := ha
        show ρ a⁻¹ c = c
        calc ρ a⁻¹ c = ρ a⁻¹ (ρ a c) := by rw [ha']
          _ = c := rho_inv_apply ρ a c }
  have hτ : ρ (swap 0 1) c = c := by
    rw [hc, map_mul (ρ (swap 0 1)), map_inv, ← rho_mul_apply, swap_mul_self, map_one,
      MulAut.one_apply, inv_eq hW, inv_eq hW, mul_comm]
  have hK : ∀ τ : Perm (Fin 6), τ 0 = 0 → τ 1 = 1 → ρ τ c = c := by
    intro τ h0 h1
    have hle : Subgroup.closure {τ : Perm (Fin 6) | ∃ a b : Fin 6, NotZO a ∧ NotZO b ∧ a ≠ b ∧
        τ = swap a b} ≤ F := by
      rw [Subgroup.closure_le]
      rintro _ ⟨a, b, ha, hb, hab, rfl⟩
      exact swap_fix hQ ha hb hab w₀
    exact hle (mem_closure_of_fix h0 h1)
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exact absurd (σ.injective (h0.trans h1.symm)) (by decide)
  · exact hK σ h0 h1
  · have e : σ = swap 0 1 * (swap 0 1 * σ) := by rw [← mul_assoc, swap_mul_self, one_mul]
    have h0' : (swap 0 1 * σ : Perm (Fin 6)) 0 = 0 := by rw [Perm.mul_apply, h0]; decide
    have h1' : (swap 0 1 * σ : Perm (Fin 6)) 1 = 1 := by rw [Perm.mul_apply, h1]; decide
    rw [e, rho_mul_apply, hK _ h0' h1', hτ]
  · exact absurd (σ.injective (h0.trans h1.symm)) (by decide)

variable (ρ) in
@[expose] def cc (c : W) (a b : Fin 6) : W := ρ (pp a b) c

variable {c : W}

section Stab

variable (hstab : ∀ σ : Perm (Fin 6), (σ 0 = 0 ∨ σ 0 = 1) → (σ 1 = 0 ∨ σ 1 = 1) → ρ σ c = c)
include hstab

theorem cc_apply (σ : Perm (Fin 6)) {a b : Fin 6} (hab : a ≠ b) :
    ρ σ (cc ρ c a b) = cc ρ c (σ a) (σ b) := by
  have hσab : σ a ≠ σ b := fun h => hab (σ.injective h)
  obtain ⟨ha, hb⟩ := pp_spec a b hab
  obtain ⟨ha', hb'⟩ := pp_spec (σ a) (σ b) hσab
  have h0 : ((pp (σ a) (σ b))⁻¹ * σ * pp a b) 0 = 0 := by
    rw [Perm.mul_apply, Perm.mul_apply, ha, Perm.inv_eq_iff_eq, ha']
  have h1 : ((pp (σ a) (σ b))⁻¹ * σ * pp a b) 1 = 1 := by
    rw [Perm.mul_apply, Perm.mul_apply, hb, Perm.inv_eq_iff_eq, hb']
  have e : σ * pp a b = pp (σ a) (σ b) * ((pp (σ a) (σ b))⁻¹ * σ * pp a b) := by group
  unfold cc
  rw [← rho_mul_apply, e, rho_mul_apply, hstab _ (Or.inl h0) (Or.inr h1)]

theorem cc_symm {a b : Fin 6} (hab : a ≠ b) : cc ρ c a b = cc ρ c b a := by
  obtain ⟨ha, hb⟩ := pp_spec a b hab
  obtain ⟨ha', hb'⟩ := pp_spec b a hab.symm
  have h0 : ((pp b a)⁻¹ * pp a b) 0 = 1 := by
    rw [Perm.mul_apply, ha, Perm.inv_eq_iff_eq, hb']
  have h1 : ((pp b a)⁻¹ * pp a b) 1 = 0 := by
    rw [Perm.mul_apply, hb, Perm.inv_eq_iff_eq, ha']
  have e : pp a b = pp b a * ((pp b a)⁻¹ * pp a b) := by group
  unfold cc
  rw [e, rho_mul_apply, hstab _ (Or.inr h0) (Or.inl h1)]

omit hstab in
theorem cc_zero_one : cc ρ c 0 1 = c := by
  rw [cc, pp_zero_one, map_one, MulAut.one_apply]

theorem rho_tri (σ : Perm (Fin 6)) :
    ρ σ (cc ρ c 0 1 * cc ρ c 1 2 * cc ρ c 0 2) =
      cc ρ c (σ 0) (σ 1) * cc ρ c (σ 1) (σ 2) * cc ρ c (σ 0) (σ 2) := by
  rw [map_mul, map_mul, cc_apply hstab σ (by decide), cc_apply hstab σ (by decide),
    cc_apply hstab σ (by decide)]

theorem rho_prod (σ : Perm (Fin 6)) :
    ρ σ (cc ρ c 0 1 * cc ρ c 0 2 * cc ρ c 0 3 * cc ρ c 0 4 * cc ρ c 0 5) =
      cc ρ c (σ 0) (σ 1) * cc ρ c (σ 0) (σ 2) * cc ρ c (σ 0) (σ 3) * cc ρ c (σ 0) (σ 4) *
        cc ρ c (σ 0) (σ 5) := by
  rw [map_mul, map_mul, map_mul, map_mul, cc_apply hstab σ (by decide),
    cc_apply hstab σ (by decide), cc_apply hstab σ (by decide), cc_apply hstab σ (by decide),
    cc_apply hstab σ (by decide)]

variable (hW : ∀ w : W, w * w = 1)
  (hQ : ∀ w, ρ (swap 0 1) (ρ (swap 2 3) w * w⁻¹) = ρ (swap 2 3) w * w⁻¹)
  (hF : ∀ w, (∀ σ, ρ σ w = w) → w = 1)
include hW hQ hF

theorem tri : cc ρ c 0 1 * cc ρ c 1 2 * cc ρ c 0 2 = 1 := by
  apply hF
  intro σ
  have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin 5 => swap i.castSucc i.succ) := by
    rw [mclosure_swap_castSucc_succ]
    trivial
  induction hσ using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [rho_tri hstab]
    fin_cases i
    · show cc ρ c 1 0 * cc ρ c 0 2 * cc ρ c 1 2 = _
      rw [cc_symm hstab (by decide : (1 : Fin 6) ≠ 0), mul_right_comm]
    · show cc ρ c 0 2 * cc ρ c 2 1 * cc ρ c 0 1 = _
      rw [cc_symm hstab (by decide : (2 : Fin 6) ≠ 1)]
      ac_rfl
    · show cc ρ c 0 1 * cc ρ c 1 3 * cc ρ c 0 3 = _
      have h := hQ (cc ρ c 0 2)
      rw [cc_apply hstab _ (by decide), map_mul, map_inv, cc_apply hstab _ (by decide),
        cc_apply hstab _ (by decide)] at h
      change cc ρ c 1 3 * (cc ρ c 1 2)⁻¹ = cc ρ c 0 3 * (cc ρ c 0 2)⁻¹ at h
      rw [inv_eq hW, inv_eq hW] at h
      have h13 : cc ρ c 1 3 = cc ρ c 0 3 * cc ρ c 0 2 * cc ρ c 1 2 := by
        rw [← h, mul_assoc, hW, mul_one]
      rw [h13]
      calc cc ρ c 0 1 * (cc ρ c 0 3 * cc ρ c 0 2 * cc ρ c 1 2) * cc ρ c 0 3
          = cc ρ c 0 1 * cc ρ c 1 2 * cc ρ c 0 2 * (cc ρ c 0 3 * cc ρ c 0 3) := by ac_rfl
        _ = _ := by rw [hW, mul_one]
    · rfl
    · rfl
  | one => rw [map_one, MulAut.one_apply]
  | mul x y _ _ hx hy => rw [rho_mul_apply, hy, hx]

theorem cc_eq {a b : Fin 6} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    cc ρ c a b = cc ρ c 0 a * cc ρ c 0 b := by
  obtain ⟨h0, h1, h2⟩ := rr_spec a b ha hb hab
  have h := congrArg (ρ (rr a b)) (tri hstab hW hQ hF)
  rw [rho_tri hstab, h0, h1, h2, map_one] at h
  calc cc ρ c a b = cc ρ c 0 a * cc ρ c 0 a * cc ρ c a b * (cc ρ c 0 b * cc ρ c 0 b) := by
        rw [hW, hW, one_mul, mul_one]
    _ = cc ρ c 0 a * cc ρ c a b * cc ρ c 0 b * (cc ρ c 0 a * cc ρ c 0 b) := by ac_rfl
    _ = cc ρ c 0 a * cc ρ c 0 b := by rw [h, one_mul]

theorem prod_eq : cc ρ c 0 1 * cc ρ c 0 2 * cc ρ c 0 3 * cc ρ c 0 4 * cc ρ c 0 5 = 1 := by
  apply hF
  intro σ
  have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin 5 => swap i.castSucc i.succ) := by
    rw [mclosure_swap_castSucc_succ]
    trivial
  induction hσ using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [rho_prod hstab]
    fin_cases i
    · show cc ρ c 1 0 * cc ρ c 1 2 * cc ρ c 1 3 * cc ρ c 1 4 * cc ρ c 1 5 = _
      rw [cc_symm hstab (by decide : (1 : Fin 6) ≠ 0),
        cc_eq hstab hW hQ hF (by decide) (by decide) (by decide : (1 : Fin 6) ≠ 2),
        cc_eq hstab hW hQ hF (by decide) (by decide) (by decide : (1 : Fin 6) ≠ 3),
        cc_eq hstab hW hQ hF (by decide) (by decide) (by decide : (1 : Fin 6) ≠ 4),
        cc_eq hstab hW hQ hF (by decide) (by decide) (by decide : (1 : Fin 6) ≠ 5)]
      calc cc ρ c 0 1 * (cc ρ c 0 1 * cc ρ c 0 2) * (cc ρ c 0 1 * cc ρ c 0 3) *
            (cc ρ c 0 1 * cc ρ c 0 4) * (cc ρ c 0 1 * cc ρ c 0 5)
          = (cc ρ c 0 1 * cc ρ c 0 1) * (cc ρ c 0 1 * cc ρ c 0 1) *
              (cc ρ c 0 1 * cc ρ c 0 2 * cc ρ c 0 3 * cc ρ c 0 4 * cc ρ c 0 5) := by ac_rfl
        _ = _ := by simp only [hW, one_mul]
    · show cc ρ c 0 2 * cc ρ c 0 1 * cc ρ c 0 3 * cc ρ c 0 4 * cc ρ c 0 5 = _
      ac_rfl
    · show cc ρ c 0 1 * cc ρ c 0 3 * cc ρ c 0 2 * cc ρ c 0 4 * cc ρ c 0 5 = _
      ac_rfl
    · show cc ρ c 0 1 * cc ρ c 0 2 * cc ρ c 0 4 * cc ρ c 0 3 * cc ρ c 0 5 = _
      ac_rfl
    · show cc ρ c 0 1 * cc ρ c 0 2 * cc ρ c 0 3 * cc ρ c 0 5 * cc ρ c 0 4 = _
      ac_rfl
  | one => rw [map_one, MulAut.one_apply]
  | mul x y _ _ hx hy => rw [rho_mul_apply, hy, hx]

end Stab

variable (ρ) in
@[expose] def theta (c : W) (m : ℕ) : W :=
  bpow (cc ρ c 0 1) (m.testBit 0) * bpow (cc ρ c 0 2) (m.testBit 1) *
    bpow (cc ρ c 0 3) (m.testBit 2) * bpow (cc ρ c 0 4) (m.testBit 3)

theorem theta_xor (hW : ∀ w : W, w * w = 1) (m m' : ℕ) :
    theta ρ c (m ^^^ m') = theta ρ c m * theta ρ c m' := by
  simp only [theta, Nat.testBit_xor, bpow_xor hW]
  ac_rfl

theorem theta_val {m : ℕ} {b0 b1 b2 b3 : Bool}
    (h : m.testBit 0 = b0 ∧ m.testBit 1 = b1 ∧ m.testBit 2 = b2 ∧ m.testBit 3 = b3) :
    theta ρ c m = bpow (cc ρ c 0 1) b0 * bpow (cc ρ c 0 2) b1 * bpow (cc ρ c 0 3) b2 *
      bpow (cc ρ c 0 4) b3 := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  rw [theta, h0, h1, h2, h3]

theorem theta_zero : theta ρ c 0 = 1 := by
  rw [theta_val (b0 := false) (b1 := false) (b2 := false) (b3 := false) (by decide)]
  simp [bpow]

theorem theta_one : theta ρ c 1 = cc ρ c 0 1 := by
  rw [theta_val (b0 := true) (b1 := false) (b2 := false) (b3 := false) (by decide)]
  simp [bpow]

theorem bpow_theta (k : ℕ) (b : Bool) :
    bpow (theta ρ c k) b = theta ρ c (if b then k else 0) := by
  cases b
  · simp only [bpow, Bool.false_eq_true, ↓reduceIte, theta_zero]
  · simp only [bpow, ↓reduceIte]

section Main

variable (hstab : ∀ σ : Perm (Fin 6), (σ 0 = 0 ∨ σ 0 = 1) → (σ 1 = 0 ∨ σ 1 = 1) → ρ σ c = c)
  (hW : ∀ w : W, w * w = 1)
  (hQ : ∀ w, ρ (swap 0 1) (ρ (swap 2 3) w * w⁻¹) = ρ (swap 2 3) w * w⁻¹)
  (hF : ∀ w, (∀ σ, ρ σ w = w) → w = 1)
include hstab hW hQ hF

theorem theta_ex_of_ne {a : Fin 6} (ha : a ≠ 0) : theta ρ c (ex a) = cc ρ c 0 a := by
  fin_cases a
  · exact absurd rfl ha
  · rw [theta_val (b0 := true) (b1 := false) (b2 := false) (b3 := false) (by decide)]
    simp [bpow]
  · rw [theta_val (b0 := false) (b1 := true) (b2 := false) (b3 := false) (by decide)]
    simp [bpow]
  · rw [theta_val (b0 := false) (b1 := false) (b2 := true) (b3 := false) (by decide)]
    simp [bpow]
  · rw [theta_val (b0 := false) (b1 := false) (b2 := false) (b3 := true) (by decide)]
    simp [bpow]
  · rw [theta_val (b0 := true) (b1 := true) (b2 := true) (b3 := true) (by decide)]
    simp only [bpow, ↓reduceIte]
    have h := prod_eq hstab hW hQ hF
    show cc ρ c 0 1 * cc ρ c 0 2 * cc ρ c 0 3 * cc ρ c 0 4 = cc ρ c 0 5
    calc cc ρ c 0 1 * cc ρ c 0 2 * cc ρ c 0 3 * cc ρ c 0 4
        = cc ρ c 0 1 * cc ρ c 0 2 * cc ρ c 0 3 * cc ρ c 0 4 * cc ρ c 0 5 * cc ρ c 0 5 := by
          rw [mul_assoc _ (cc ρ c 0 5), hW, mul_one]
      _ = cc ρ c 0 5 := by rw [h, one_mul]

theorem cc_eq_theta {a b : Fin 6} (hab : a ≠ b) : cc ρ c a b = theta ρ c (ex a ^^^ ex b) := by
  rw [theta_xor hW]
  have he0 : theta ρ c (ex 0) = 1 := theta_zero
  by_cases ha : a = 0
  · subst ha
    rw [he0, one_mul, theta_ex_of_ne hstab hW hQ hF (Ne.symm hab)]
  by_cases hb : b = 0
  · subst hb
    rw [he0, mul_one, theta_ex_of_ne hstab hW hQ hF ha, cc_symm hstab hab]
  rw [theta_ex_of_ne hstab hW hQ hF ha, theta_ex_of_ne hstab hW hQ hF hb,
    cc_eq hstab hW hQ hF ha hb hab]

theorem theta_apply (σ : Perm (Fin 6)) (m : ℕ) : ρ σ (theta ρ c m) = theta ρ c (act4 σ m) := by
  have hne : ∀ j : Fin 6, j ≠ 0 → σ 0 ≠ σ j := fun j hj h => hj (σ.injective h).symm
  simp only [theta, map_mul, bpow_apply]
  rw [cc_apply hstab σ (by decide), cc_apply hstab σ (by decide), cc_apply hstab σ (by decide),
    cc_apply hstab σ (by decide), cc_eq_theta hstab hW hQ hF (hne 1 (by decide)),
    cc_eq_theta hstab hW hQ hF (hne 2 (by decide)), cc_eq_theta hstab hW hQ hF (hne 3 (by decide)),
    cc_eq_theta hstab hW hQ hF (hne 4 (by decide)), bpow_theta, bpow_theta, bpow_theta,
    bpow_theta, ← theta_xor hW, ← theta_xor hW, ← theta_xor hW]
  rfl

theorem theta_inj (hc : c ≠ 1) {m : ℕ} (hm : m < 16) (h : theta ρ c m = 1) : m = 0 := by
  by_contra hm0
  obtain ⟨a, b, hab⟩ := act4_trans m hm hm0
  have h' := theta_apply hstab hW hQ hF (swap 0 a * swap 1 b) m
  rw [h, map_one, hab, theta_one, cc_zero_one] at h'
  exact hc h'.symm

end Main

theorem exists_theta (hW : ∀ w : W, w * w = 1)
    (hQ : ∀ w, ρ (swap 0 1) (ρ (swap 2 3) w * w⁻¹) = ρ (swap 2 3) w * w⁻¹)
    (hF : ∀ w, (∀ σ, ρ σ w = w) → w = 1) (hN : ∃ w : W, w ≠ 1) :
    ∃ Θ : ℕ → W, Θ 0 = 1 ∧ (∀ m m', Θ (m ^^^ m') = Θ m * Θ m') ∧
      (∀ m < 16, Θ m = 1 → m = 0) ∧ ∀ σ m, ρ σ (Θ m) = Θ (act4 σ m) := by
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, ρ (swap 0 1) w₀ ≠ w₀ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨w, hw⟩ := hN
    apply hw
    apply hF
    intro σ
    have hle : Subgroup.closure {τ : Perm (Fin 6) | τ.IsSwap} ≤ ρ.ker := by
      rw [Subgroup.closure_le]
      rintro _ ⟨x, y, hxy, rfl⟩
      obtain ⟨h0, h1⟩ := pp_spec x y hxy
      have e : swap x y = pp x y * swap 0 1 * (pp x y)⁻¹ := by
        rw [← swap_apply_apply, h0, h1]
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      refine MulEquiv.ext fun v => ?_
      rw [e, rho_mul_apply, rho_mul_apply, hcon, rho_apply_inv, MulAut.one_apply]
    have hσ : σ ∈ ρ.ker := hle (by rw [closure_isSwap]; trivial)
    rw [MonoidHom.mem_ker] at hσ
    rw [hσ, MulAut.one_apply]
  have hc : ρ (swap 0 1) w₀ * w₀⁻¹ ≠ 1 := fun h => hw₀ (mul_inv_eq_one.mp h)
  have hstab : ∀ σ : Perm (Fin 6), (σ 0 = 0 ∨ σ 0 = 1) → (σ 1 = 0 ∨ σ 1 = 1) →
      ρ σ (ρ (swap 0 1) w₀ * w₀⁻¹) = ρ (swap 0 1) w₀ * w₀⁻¹ :=
    fun σ h0 h1 => stab_fix hW hQ w₀ h0 h1
  exact ⟨theta ρ _, theta_zero, theta_xor hW, fun m hm h => theta_inj hstab hW hQ hF hc hm h,
    theta_apply hstab hW hQ hF⟩

end CFSG.Quasithin.H13.S127.FourA
