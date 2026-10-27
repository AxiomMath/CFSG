module

public import CFSG.Quasithin.Background.G6Natural
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.H13.A7.LinCode

open Equiv

abbrev Vec := Fin 8 → ZMod 2

@[expose] def act (π : Perm (Fin 8)) (x : Vec) : Vec := fun i => x (π⁻¹ i)

@[expose] def jVec : Vec := fun _ => 1

@[expose] def wt (x : Vec) : ℕ := (Finset.univ.filter (fun i => x i = 1)).card

theorem act_mul (π ρ : Perm (Fin 8)) (x : Vec) : act (π * ρ) x = act π (act ρ x) := by
  funext i
  simp [act, mul_inv_rev]

theorem act_one (x : Vec) : act 1 x = x := by
  funext i
  simp [act]

theorem act_pow_of_fix {g : Perm (Fin 8)} {x : Vec} (hx : act g x = x) (n : ℕ) :
    act (g ^ n) x = x := by
  induction n with
  | zero => exact act_one x
  | succ n ih => rw [pow_succ, act_mul, hx, ih]

theorem wt_act (π : Perm (Fin 8)) (x : Vec) : wt (act π x) = wt x := by
  unfold wt act
  have : (Finset.univ.filter (fun i => x (π⁻¹ i) = 1)) =
      (Finset.univ.filter (fun i => x i = 1)).map π.toEmbedding := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv]
    rfl
  rw [this, Finset.card_map]

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem wt_add_jVec (x : Vec) : wt (x + jVec) = 8 - wt x := by
  unfold wt
  have h : ∀ i, ((x + jVec) i = 1 ↔ ¬ x i = 1) := fun i => by
    simp only [Pi.add_apply, jVec]
    rcases zmod2_cases (x i) with h | h <;> rw [h] <;> decide
  rw [Finset.filter_congr (fun i _ => h i)]
  have := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => x i = 1)
  rw [Finset.card_univ, Fintype.card_fin] at this
  omega


theorem exists_fixed_of_order_seven {g : Perm (Fin 8)} (hg : orderOf g = 7) :
    g.IsCycle ∧ ∃ p, g.supportᶜ = {p} := by
  have hcyc : g.IsCycle := Perm.isCycle_of_prime_order (by rw [hg]; norm_num) (by
    rw [hg]
    have : g.support.card ≤ 8 := (Finset.card_le_univ _).trans (by simp)
    omega)
  have hsupp : g.support.card = 7 := by rw [← hcyc.orderOf, hg]
  have hcompl : (g.supportᶜ).card = 1 := by
    rw [Finset.card_compl, hsupp]
    simp
  exact ⟨hcyc, Finset.card_eq_one.1 hcompl⟩

theorem eq_zero_or_jVec_of_fix {g : Perm (Fin 8)} (hg : orderOf g = 7) {x : Vec}
    (hx : act g x = x) (hev : ∑ i, x i = 0) : x = 0 ∨ x = jVec := by
  obtain ⟨hcyc, p, hp⟩ := exists_fixed_of_order_seven hg
  have hsupp : g.support.card = 7 := by rw [← hcyc.orderOf, hg]
  have hx' : ∀ i, x (g i) = x i := fun i => by
    have := congrFun hx (g i)
    simp only [act] at this
    rw [show g⁻¹ (g i) = i from by simp] at this
    exact this.symm
  have hpow : ∀ (n : ℕ) i, x ((g ^ n) i) = x i := by
    intro n
    induction n with
    | zero => intro i; rfl
    | succ n ih =>
      intro i
      rw [pow_succ', Perm.mul_apply, hx', ih]
  obtain ⟨i₀, hi₀⟩ : g.support.Nonempty := Finset.card_pos.1 (by omega)
  have hconst : ∀ i ∈ g.support, x i = x i₀ := fun i hi => by
    obtain ⟨n, hn⟩ := hcyc.exists_pow_eq (Perm.mem_support.1 hi₀) (Perm.mem_support.1 hi)
    rw [← hn, hpow]
  have hsum : ∑ i, x i = ∑ i ∈ g.support, x i + ∑ i ∈ g.supportᶜ, x i :=
    (Finset.sum_add_sum_compl _ _).symm
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, hsupp, hp, Finset.sum_singleton, hev]
    at hsum
  have hp' : x p = x i₀ := by
    have h7 : (7 : ℕ) • x i₀ = x i₀ := by
      rw [nsmul_eq_mul]
      have : ((7 : ℕ) : ZMod 2) = 1 := by decide
      rw [this, one_mul]
    rw [h7] at hsum
    rcases zmod2_cases (x i₀) with h | h <;> rcases zmod2_cases (x p) with h' | h' <;>
      rw [h, h'] at hsum ⊢ <;> revert hsum <;> decide
  have hall : ∀ i, x i = x i₀ := fun i => by
    by_cases hi : i ∈ g.support
    · exact hconst i hi
    · have : i ∈ g.supportᶜ := Finset.mem_compl.2 hi
      rw [hp, Finset.mem_singleton] at this
      rw [this, hp']
  rcases zmod2_cases (x i₀) with h | h
  · left
    funext i
    rw [hall i, h]
    rfl
  · right
    funext i
    rw [hall i, h]
    rfl

theorem fix_of_pow_fix {g : Perm (Fin 8)} (hg : orderOf g = 7) {x : Vec} {m : ℕ} (hm0 : 0 < m)
    (hm7 : m < 7) (hx : act (g ^ m) x = x) : act g x = x := by
  obtain ⟨m', hm'⟩ : ∃ m', m * m' % 7 = 1 := by
    interval_cases m
    exacts [⟨1, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨6, rfl⟩]
  have hgg : g = (g ^ m) ^ m' := by
    rw [← pow_mul, ← pow_mod_orderOf, hg, hm', pow_one]
  rw [hgg]
  exact act_pow_of_fix hx m'

abbrev Tri := ZMod 2 × ZMod 2 × ZMod 2

@[expose] def dot (b e : Tri) : ZMod 2 := b.1 * e.1 + b.2.1 * e.2.1 + b.2.2 * e.2.2

theorem univ_zmod2 : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide

@[expose] def comb (v₁ v₂ v₃ : Vec) (b : Tri) : Vec := b.1 • v₁ + b.2.1 • v₂ + b.2.2 • v₃

@[expose] def coord (v₁ v₂ v₃ : Vec) (i : Fin 8) : Tri := (v₁ i, v₂ i, v₃ i)

theorem comb_apply (v₁ v₂ v₃ : Vec) (b : Tri) (i : Fin 8) :
    comb v₁ v₂ v₃ b i = dot b (coord v₁ v₂ v₃ i) := by
  simp [comb, dot, coord]

theorem smul_mem_of {A : AddSubgroup Vec} {x : Vec} (hx : x ∈ A) (a : ZMod 2) : a • x ∈ A := by
  rcases zmod2_cases a with h | h
  · rw [h, zero_smul]
    exact A.zero_mem
  · rw [h, one_smul]
    exact hx

theorem comb_mem {A : AddSubgroup Vec} {v₁ v₂ v₃ : Vec} (h₁ : v₁ ∈ A) (h₂ : v₂ ∈ A) (h₃ : v₃ ∈ A)
    (b : Tri) : comb v₁ v₂ v₃ b ∈ A :=
  A.add_mem (A.add_mem (smul_mem_of h₁ _) (smul_mem_of h₂ _)) (smul_mem_of h₃ _)

theorem card_filter_coord (c : Fin 8 → Tri) (P : Tri → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun i => P (c i))).card =
      ∑ e : Tri, if P e then (Finset.univ.filter (fun i => c i = e)).card else 0 := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := c) (t := Finset.univ) (by simp)]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases hP : P e
  · simp only [hP, ↓reduceIte]
    rw [Finset.filter_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨h ▸ hP, h⟩
  · simp only [hP, ↓reduceIte]
    rw [Finset.card_eq_zero, Finset.filter_filter]
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
      not_and]
    intro h he
    exact hP (he ▸ h)

section Code

variable {A : AddSubgroup Vec}

open Classical in
@[expose] noncomputable def finA (A : AddSubgroup Vec) : Finset Vec := Finset.univ.filter (· ∈ A)

theorem mem_finA {x : Vec} : x ∈ finA A ↔ x ∈ A := by
  classical
  simp [finA]

theorem card_finA (hA : Nat.card A = 16) : (finA A).card = 16 := by
  classical
  rw [← hA, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [finA]

theorem zmod2_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  rcases zmod2_cases a with h' | h'
  · exact absurd h' h
  · exact h'

theorem add_self_vec (x : Vec) : x + x = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  rcases zmod2_cases (x i) with h | h <;> rw [h] <;> decide

theorem card_finA_zero (hA : Nat.card A = 16) (hj : jVec ∈ A) (p : Fin 8) :
    ((finA A).filter (fun x => x p = 0)).card = 8 := by
  have h1 := Finset.card_filter_add_card_filter_not (s := finA A) (fun x => x p = 0)
  rw [card_finA hA] at h1
  have h2 : ((finA A).filter (fun x => x p = 0)).card =
      ((finA A).filter (fun x => ¬ x p = 0)).card := by
    refine Finset.card_nbij' (· + jVec) (· + jVec) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_finA] at hx ⊢
      refine ⟨A.add_mem hx.1 hj, ?_⟩
      simp [hx.2, jVec]
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_finA] at hx ⊢
      refine ⟨A.add_mem hx.1 hj, ?_⟩
      have := zmod2_ne_zero hx.2
      simp only [Pi.add_apply, this, jVec]
      decide
    · intro x _
      simp only
      rw [add_assoc, add_self_vec, add_zero]
    · intro x _
      simp only
      rw [add_assoc, add_self_vec, add_zero]
  omega

theorem eq_zero_of_wt_eq_zero {x : Vec} (h : wt x = 0) : x = 0 := by
  unfold wt at h
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  funext i
  have := h (Finset.mem_univ i)
  rcases zmod2_cases (x i) with h' | h'
  · exact h'
  · exact absurd h' this

theorem wt_le_seven {x : Vec} {p : Fin 8} (hp : x p = 0) : wt x ≤ 7 := by
  unfold wt
  have : Finset.univ.filter (fun i => x i = 1) ⊆ Finset.univ.erase p := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    refine Finset.mem_erase.2 ⟨fun hip => ?_, Finset.mem_univ _⟩
    rw [hip, hp] at hi
    exact absurd hi (by decide)
  have h := Finset.card_le_card this
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h
  exact h

theorem four_dvd_sum_wt (A : AddSubgroup Vec) (p : Fin 8)
    (h8 : ((finA A).filter (fun x => x p = 0)).card = 8) :
    4 ∣ ∑ x ∈ (finA A).filter (fun x => x p = 0), wt x := by
  classical
  set B := (finA A).filter (fun x => x p = 0) with hB
  have hBmem : ∀ {x}, x ∈ B ↔ x ∈ A ∧ x p = 0 := by
    intro x
    simp [hB, mem_finA]
  have hsum : ∑ x ∈ B, wt x = ∑ i, (B.filter (fun x => x i = 1)).card := by
    unfold wt
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [hsum]
  refine Finset.dvd_sum fun i _ => ?_
  by_cases hex : ∃ y ∈ B, y i = 1
  · obtain ⟨y, hyB, hyi⟩ := hex
    have h1 := Finset.card_filter_add_card_filter_not (s := B) (fun x => x i = 1)
    have h2 : (B.filter (fun x => x i = 1)).card = (B.filter (fun x => ¬ x i = 1)).card := by
      refine Finset.card_nbij' (· + y) (· + y) ?_ ?_ ?_ ?_
      · intro x hx
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx ⊢
        obtain ⟨hxA, hxp⟩ := hBmem.1 hx.1
        obtain ⟨hyA, hyp⟩ := hBmem.1 hyB
        refine ⟨hBmem.2 ⟨A.add_mem hxA hyA, by simp [hxp, hyp]⟩, ?_⟩
        simp only [Pi.add_apply, hx.2, hyi]
        decide
      · intro x hx
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx ⊢
        obtain ⟨hxA, hxp⟩ := hBmem.1 hx.1
        obtain ⟨hyA, hyp⟩ := hBmem.1 hyB
        refine ⟨hBmem.2 ⟨A.add_mem hxA hyA, by simp [hxp, hyp]⟩, ?_⟩
        have : x i = 0 := by
          rcases zmod2_cases (x i) with h | h
          · exact h
          · exact absurd h hx.2
        simp only [Pi.add_apply, this, hyi]
        decide
      · intro x _
        simp only
        rw [add_assoc, add_self_vec, add_zero]
      · intro x _
        simp only
        rw [add_assoc, add_self_vec, add_zero]
    rw [h8] at h1
    exact ⟨1, by omega⟩
  · push Not at hex
    rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun x hx => hex x hx)]
    exact dvd_zero 4

end Code

section Weight

variable {A : AddSubgroup Vec}

theorem eq_zero_of_act_eq_zero {π : Perm (Fin 8)} {x : Vec} (h : act π x = 0) : x = 0 := by
  funext i
  have := congrFun h (π i)
  simpa [act] using this

theorem act_pow_apply_of_fix {g : Perm (Fin 8)} {p : Fin 8} (hgp : g p = p) (n : ℕ) (x : Vec) :
    act (g ^ n) x p = x p := by
  have h1 : (g ^ n) p = p := by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', Perm.mul_apply, ih, hgp]
  have h2 : (g ^ n)⁻¹ p = p := by
    rw [Perm.inv_eq_iff_eq]
    exact h1.symm
  simp only [act, h2]

theorem wt_eq_four (hA : Nat.card A = 16) (hj : jVec ∈ A) (hev : ∀ x ∈ A, ∑ i, x i = 0)
    {g : Perm (Fin 8)} (hg : orderOf g = 7) (hgA : ∀ x ∈ A, act g x ∈ A) :
    ∀ x ∈ A, x ≠ 0 → x ≠ jVec → wt x = 4 := by
  classical
  obtain ⟨-, p, hp⟩ := exists_fixed_of_order_seven hg
  have hgp : g p = p := by
    have : p ∈ g.supportᶜ := by rw [hp]; exact Finset.mem_singleton_self p
    exact Perm.notMem_support.1 (Finset.mem_compl.1 this)
  have hpowA : ∀ (n : ℕ) (x : Vec), x ∈ A → act (g ^ n) x ∈ A := by
    intro n
    induction n with
    | zero => intro x hx; rwa [pow_zero, act_one]
    | succ n ih => intro x hx; rw [pow_succ, act_mul]; exact ih _ (hgA x hx)
  set B := (finA A).filter (fun x => x p = 0) with hBdef
  have hBmem : ∀ {x}, x ∈ B ↔ x ∈ A ∧ x p = 0 := by
    intro x
    simp [hBdef, mem_finA]
  have hB8 : B.card = 8 := card_finA_zero hA hj p
  have h0B : (0 : Vec) ∈ B := hBmem.2 ⟨A.zero_mem, rfl⟩
  have hBe : (B.erase 0).card = 7 := by rw [Finset.card_erase_of_mem h0B, hB8]
  have horb : ∀ x ∈ B, x ≠ 0 → ∀ y ∈ B, y ≠ 0 → wt y = wt x := by
    intro x hx hx0 y hy hy0
    obtain ⟨hxA, hxp⟩ := hBmem.1 hx
    set O := (Finset.range 7).image (fun k => act (g ^ k) x) with hOdef
    have hOsub : O ⊆ B.erase 0 := by
      intro z hz
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hz
      refine Finset.mem_erase.2 ⟨fun h => hx0 (eq_zero_of_act_eq_zero h), ?_⟩
      exact hBmem.2 ⟨hpowA k x hxA, by rw [act_pow_apply_of_fix hgp, hxp]⟩
    have hinj : Set.InjOn (fun k => act (g ^ k) x) (Finset.range 7 : Set ℕ) := by
      have key : ∀ a b, a < b → b < 7 → act (g ^ a) x = act (g ^ b) x → False := by
        intro a b hab hb7 h
        have hfix : act (g ^ (b - a)) (act (g ^ a) x) = act (g ^ a) x := by
          rw [← act_mul, pow_sub_mul_pow g hab.le, h]
        have h1 := fix_of_pow_fix hg (by omega) (by omega) hfix
        have hyA := hpowA a x hxA
        rcases eq_zero_or_jVec_of_fix hg h1 (hev _ hyA) with h0 | hjv
        · exact hx0 (eq_zero_of_act_eq_zero h0)
        · have := congrFun hjv p
          rw [act_pow_apply_of_fix hgp, hxp] at this
          simp [jVec] at this
      intro a ha b hb hab
      simp only [Finset.coe_range, Set.mem_Iio] at ha hb
      rcases lt_trichotomy a b with h | h | h
      · exact (key a b h hb hab).elim
      · exact h
      · exact (key b a h ha hab.symm).elim
    have hOcard : O.card = 7 := by
      rw [hOdef, Finset.card_image_of_injOn hinj, Finset.card_range]
    have hOeq : O = B.erase 0 := Finset.eq_of_subset_of_card_le hOsub (by omega)
    have hyO : y ∈ O := hOeq ▸ Finset.mem_erase.2 ⟨hy0, hy⟩
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hyO
    exact wt_act _ _
  obtain ⟨x₀, hx₀B, hx₀0⟩ : ∃ x₀ ∈ B, x₀ ≠ 0 := Finset.exists_mem_ne (by omega) 0
  have hwt0 : wt 0 = 0 := by simp [wt]
  have hsum : ∑ x ∈ B, wt x = 7 * wt x₀ := by
    rw [← Finset.add_sum_erase B wt h0B, hwt0, zero_add]
    rw [Finset.sum_congr rfl (fun y hy => horb x₀ hx₀B hx₀0 y (Finset.mem_of_mem_erase hy)
      (Finset.ne_of_mem_erase hy)), Finset.sum_const, hBe, smul_eq_mul]
  have h4 := four_dvd_sum_wt A p hB8
  rw [hsum] at h4
  have hw0 : wt x₀ ≠ 0 := fun h => hx₀0 (eq_zero_of_wt_eq_zero h)
  have hw7 : wt x₀ ≤ 7 := wt_le_seven (hBmem.1 hx₀B).2
  have hw4 : wt x₀ = 4 := by omega
  intro x hxA hx0 hxj
  by_cases hxp : x p = 0
  · exact (horb x₀ hx₀B hx₀0 x (hBmem.2 ⟨hxA, hxp⟩) hx0).trans hw4
  · have hxj' : x + jVec ∈ B := by
      refine hBmem.2 ⟨A.add_mem hxA hj, ?_⟩
      have := zmod2_ne_zero hxp
      simp only [Pi.add_apply, this, jVec]
      decide
    have hne : x + jVec ≠ 0 := fun h => hxj (by
      have := congrArg (· + jVec) h
      simpa [add_assoc, add_self_vec] using this)
    have h1 := (horb x₀ hx₀B hx₀0 _ hxj' hne).trans hw4
    have h8 := wt_add_jVec (x + jVec)
    rw [add_assoc, add_self_vec, add_zero] at h8
    omega

end Weight

section Structure

variable {A : AddSubgroup Vec}

theorem eq_of_add_eq_zero {x y : Vec} (h : x + y = 0) : x = y := by
  have := congrArg (· + y) h
  simpa [add_assoc, add_self_vec] using this

theorem sum_tri (f : Tri → ℕ) : ∑ e, f e = f (0, 0, 0) + f (0, 0, 1) + f (0, 1, 0) + f (0, 1, 1) +
    f (1, 0, 0) + f (1, 0, 1) + f (1, 1, 0) + f (1, 1, 1) := by
  simp only [Fintype.sum_prod_type, univ_zmod2,
    Finset.sum_insert (show (0 : ZMod 2) ∉ ({1} : Finset (ZMod 2)) by decide),
    Finset.sum_singleton]
  ring

theorem tri_cases (e : Tri) : e = (0, 0, 0) ∨ e = (0, 0, 1) ∨ e = (0, 1, 0) ∨ e = (0, 1, 1) ∨
    e = (1, 0, 0) ∨ e = (1, 0, 1) ∨ e = (1, 1, 0) ∨ e = (1, 1, 1) := by
  revert e
  decide

theorem rm_structure (hA : Nat.card A = 16) (hj : jVec ∈ A) (hev : ∀ x ∈ A, ∑ i, x i = 0)
    {g : Perm (Fin 8)} (hg : orderOf g = 7) (hgA : ∀ x ∈ A, act g x ∈ A) :
    ∃ c : Fin 8 ≃ Tri, ∀ x : Vec, x ∈ A ↔ ∃ (a : ZMod 2) (b : Tri), ∀ i, x i = a + dot b (c i) := by
  classical
  have hw4 := wt_eq_four hA hj hev hg hgA
  obtain ⟨-, p, -⟩ := exists_fixed_of_order_seven hg
  set B := (finA A).filter (fun x => x p = 0) with hBdef
  have hBmem : ∀ {x}, x ∈ B ↔ x ∈ A ∧ x p = 0 := by
    intro x
    simp [hBdef, mem_finA]
  have hB8 : B.card = 8 := card_finA_zero hA hj p
  obtain ⟨v₁, hv₁B, hv₁0⟩ := Finset.exists_mem_ne (by omega : 1 < B.card) 0
  obtain ⟨v₂, hv₂B, hv₂⟩ : ∃ v₂ ∈ B, v₂ ∉ ({0, v₁} : Finset Vec) :=
    Finset.exists_mem_notMem_of_card_lt_card (lt_of_le_of_lt (Finset.card_le_two) (by omega))
  obtain ⟨v₃, hv₃B, hv₃⟩ : ∃ v₃ ∈ B, v₃ ∉ ({0, v₁, v₂, v₁ + v₂} : Finset Vec) :=
    Finset.exists_mem_notMem_of_card_lt_card (lt_of_le_of_lt (Finset.card_le_four) (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv₂ hv₃
  obtain ⟨hv₁A, hv₁p⟩ := hBmem.1 hv₁B
  obtain ⟨hv₂A, hv₂p⟩ := hBmem.1 hv₂B
  obtain ⟨hv₃A, hv₃p⟩ := hBmem.1 hv₃B
  have hcomb0 : ∀ b : Tri, b ≠ 0 → comb v₁ v₂ v₃ b ≠ 0 := by
    intro b hb h
    obtain ⟨b₁, b₂, b₃⟩ := b
    rcases zmod2_cases b₁ with rfl | rfl <;> rcases zmod2_cases b₂ with rfl | rfl <;>
      rcases zmod2_cases b₃ with rfl | rfl <;> simp only [comb, zero_smul, one_smul, add_zero,
        zero_add] at h
    · exact hb rfl
    · exact hv₃.1 h
    · exact hv₂.1 h
    · exact hv₃.2.2.1 (eq_of_add_eq_zero h).symm
    · exact hv₁0 h
    · exact hv₃.2.1 (eq_of_add_eq_zero h).symm
    · exact hv₂.2 (eq_of_add_eq_zero h).symm
    · exact hv₃.2.2.2 (eq_of_add_eq_zero h).symm
  have hcoordp : coord v₁ v₂ v₃ p = 0 := by simp [coord, hv₁p, hv₂p, hv₃p]
  have hwt : ∀ b : Tri, b ≠ 0 → wt (comb v₁ v₂ v₃ b) = 4 := by
    intro b hb
    refine hw4 _ (comb_mem hv₁A hv₂A hv₃A b) (hcomb0 b hb) fun h => ?_
    have := congrFun h p
    rw [comb_apply, hcoordp] at this
    simp [dot, jVec] at this
  set c := coord v₁ v₂ v₃ with hcdef
  set N : Tri → ℕ := fun e => (Finset.univ.filter (fun i => c i = e)).card with hNdef
  have hwtN : ∀ b : Tri, b ≠ 0 → 4 = ∑ e, if dot b e = 1 then N e else 0 := by
    intro b hb
    rw [← hwt b hb, ← card_filter_coord c (fun e => dot b e = 1)]
    unfold wt
    simp only [comb_apply, hcdef]
  have htot : 8 = ∑ e, N e := by
    have := Finset.card_eq_sum_card_fiberwise (f := c) (s := Finset.univ) (t := Finset.univ)
      (by simp)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this
  have e1 := hwtN (1, 0, 0) (by decide)
  have e2 := hwtN (0, 1, 0) (by decide)
  have e3 := hwtN (1, 1, 0) (by decide)
  have e4 := hwtN (0, 0, 1) (by decide)
  have e5 := hwtN (1, 0, 1) (by decide)
  have e6 := hwtN (0, 1, 1) (by decide)
  have e7 := hwtN (1, 1, 1) (by decide)
  simp (config := { decide := true }) only [sum_tri, dot, ↓reduceIte] at e1 e2 e3 e4 e5 e6 e7
  rw [sum_tri] at htot
  have hN : ∀ e, N e = 1 := by
    intro e
    rcases tri_cases e with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hinj : Function.Injective c := by
    intro i i' h
    have h1 := hN (c i)
    rw [hNdef, Finset.card_eq_one] at h1
    obtain ⟨k, hk⟩ := h1
    have hi : i ∈ Finset.univ.filter (fun j => c j = c i) := by simp
    have hi' : i' ∈ Finset.univ.filter (fun j => c j = c i) := by simp [h]
    rw [hk, Finset.mem_singleton] at hi hi'
    rw [hi, hi']
  have hbij : Function.Bijective c :=
    (Fintype.bijective_iff_injective_and_card c).2 ⟨hinj, by simp⟩
  set e := Equiv.ofBijective c hbij with hedef
  refine ⟨e, fun x => ⟨fun hx => ?_, ?_⟩⟩
  ·
    set Ψ : ZMod 2 × Tri → Vec := fun ab => ab.1 • jVec + comb v₁ v₂ v₃ ab.2 with hΨ
    have hΨapp : ∀ ab i, Ψ ab i = ab.1 + dot ab.2 (c i) := by
      intro ab i
      simp [hΨ, comb_apply, jVec, hcdef]
    have hΨinj : Function.Injective Ψ := by
      intro ab ab' h
      have hval : ∀ t : Tri, ab.1 + dot ab.2 t = ab'.1 + dot ab'.2 t := by
        intro t
        obtain ⟨i, hi⟩ := hbij.2 t
        have := congrFun h i
        rwa [hΨapp, hΨapp, hi] at this
      obtain ⟨a, b₁, b₂, b₃⟩ := ab
      obtain ⟨a', b₁', b₂', b₃'⟩ := ab'
      have h0 := hval (0, 0, 0)
      have h1 := hval (1, 0, 0)
      have h2 := hval (0, 1, 0)
      have h3 := hval (0, 0, 1)
      simp only [dot, mul_zero, mul_one, add_zero, zero_add] at h0 h1 h2 h3
      rw [h0] at h1 h2 h3
      simp only [add_right_inj] at h1 h2 h3
      rw [h0, h1, h2, h3]
    have hsub : Finset.univ.image Ψ ⊆ finA A := by
      intro y hy
      obtain ⟨ab, -, rfl⟩ := Finset.mem_image.1 hy
      exact mem_finA.2 (A.add_mem (smul_mem_of hj _) (comb_mem hv₁A hv₂A hv₃A _))
    have hcard : (Finset.univ.image Ψ).card = 16 := by
      rw [Finset.card_image_of_injective _ hΨinj]
      simp
    have heq : Finset.univ.image Ψ = finA A :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard, card_finA hA])
    have hx' : x ∈ Finset.univ.image Ψ := heq ▸ mem_finA.2 hx
    obtain ⟨⟨a, b⟩, -, hab⟩ := Finset.mem_image.1 hx'
    refine ⟨a, b, fun i => ?_⟩
    rw [← hab, hΨapp]
    rfl
  · rintro ⟨a, b, hab⟩
    have : x = a • jVec + comb v₁ v₂ v₃ b := by
      funext i
      rw [hab i]
      simp [comb_apply, jVec, hedef, hcdef]
    rw [this]
    exact A.add_mem (smul_mem_of hj _) (comb_mem hv₁A hv₂A hv₃A _)

end Structure

section Translation

variable {A : AddSubgroup Vec}

theorem dot_add_left_one (b t : Tri) : dot b (t + (1, 0, 0)) = dot b t + b.1 := by
  simp only [dot, Prod.fst_add, Prod.snd_add]
  ring

theorem exists_translation (hA : Nat.card A = 16) (hj : jVec ∈ A) (hev : ∀ x ∈ A, ∑ i, x i = 0)
    {g : Perm (Fin 8)} (hg : orderOf g = 7) (hgA : ∀ x ∈ A, act g x ∈ A) :
    ∃ σ : Perm (Fin 8), σ ∈ alternatingGroup (Fin 8) ∧
      (∀ x ∈ A, act σ x ∈ A ∧ (act σ x = x ∨ act σ x = x + jVec)) ∧ ∃ x ∈ A, act σ x ≠ x := by
  classical
  obtain ⟨c, hc⟩ := rm_structure hA hj hev hg hgA
  set σ : Perm (Fin 8) := c.symm.permCongr (Equiv.addRight ((1, 0, 0) : Tri)) with hσ
  have hσapp : ∀ i, σ i = c.symm (c i + (1, 0, 0)) := fun i => by
    rw [hσ, Equiv.permCongr_apply]
    simp
  have hσinv : ∀ i, c (σ⁻¹ i) = c i + (1, 0, 0) := by
    intro i
    have h := hσapp (σ⁻¹ i)
    rw [show σ (σ⁻¹ i) = i from by simp] at h
    have h' := congrArg c h
    rw [Equiv.apply_symm_apply] at h'
    rw [h']
    have : ((1, 0, 0) : Tri) + (1, 0, 0) = 0 := by decide
    rw [add_assoc, this, add_zero]
  have hσx : ∀ x ∈ A, ∃ t : ZMod 2, act σ x = x + t • jVec := by
    intro x hx
    obtain ⟨a, b, hab⟩ := (hc x).1 hx
    refine ⟨b.1, funext fun i => ?_⟩
    simp only [act, Pi.add_apply, Pi.smul_apply, jVec, smul_eq_mul, mul_one]
    rw [hab, hab, hσinv, dot_add_left_one, add_assoc]
  refine ⟨σ, ?_, fun x hx => ?_, ?_⟩
  · rw [Perm.mem_alternatingGroup, hσ, Perm.sign_permCongr]
    decide
  · obtain ⟨t, ht⟩ := hσx x hx
    refine ⟨ht ▸ A.add_mem hx (smul_mem_of hj t), ?_⟩
    rcases zmod2_cases t with rfl | rfl
    · left
      rw [ht, zero_smul, add_zero]
    · right
      rw [ht, one_smul]
  · set x₁ : Vec := fun i => (c i).1 with hx₁
    have hx₁A : x₁ ∈ A := (hc x₁).2 ⟨0, (1, 0, 0), fun i => by simp [hx₁, dot]⟩
    refine ⟨x₁, hx₁A, fun h => ?_⟩
    have := congrFun h (c.symm 0)
    simp only [act, hx₁, hσinv, Equiv.apply_symm_apply] at this
    revert this
    decide

theorem eq_one_of_fix (hA : Nat.card A = 16) (hj : jVec ∈ A) (hev : ∀ x ∈ A, ∑ i, x i = 0)
    {g : Perm (Fin 8)} (hg : orderOf g = 7) (hgA : ∀ x ∈ A, act g x ∈ A) {τ : Perm (Fin 8)}
    (hτ : ∀ x ∈ A, act τ x = x) : τ = 1 := by
  classical
  obtain ⟨c, hc⟩ := rm_structure hA hj hev hg hgA
  have hcoord : ∀ b : Tri, (fun i => dot b (c i)) ∈ A := fun b =>
    (hc _).2 ⟨0, b, fun i => by simp⟩
  have hfix : ∀ i, c (τ⁻¹ i) = c i := by
    intro i
    have h1 := congrFun (hτ _ (hcoord (1, 0, 0))) i
    have h2 := congrFun (hτ _ (hcoord (0, 1, 0))) i
    have h3 := congrFun (hτ _ (hcoord (0, 0, 1))) i
    simp only [act, dot, one_mul, zero_mul, add_zero, zero_add] at h1 h2 h3
    exact Prod.ext h1 (Prod.ext h2 h3)
  have hinv : τ⁻¹ = 1 := Equiv.ext fun i => c.injective (hfix i)
  rw [← inv_inv τ, hinv, inv_one]

end Translation

section Fixed

theorem eq_zero_or_jVec_of_alt {x : Vec} (hx : ∀ σ ∈ alternatingGroup (Fin 8), act σ x = x) :
    x = 0 ∨ x = jVec := by
  classical
  have hconst : ∀ i j, x i = x j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({i, j} : Finset (Fin 8))) (t := Finset.univ)
      (lt_of_le_of_lt Finset.card_le_two (by simp))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    set σ : Perm (Fin 8) := swap i k * swap i j with hσ
    have hσA : σ ∈ alternatingGroup (Fin 8) := by
      rw [Perm.mem_alternatingGroup, hσ, map_mul, Perm.sign_swap (Ne.symm hk.1),
        Perm.sign_swap hij]
      decide
    have hσi : σ i = j := by
      rw [hσ, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hij) (Ne.symm hk.2)]
    have h1 := congrFun (hx σ hσA) j
    have hσj : σ⁻¹ j = i := by rw [Perm.inv_eq_iff_eq]; exact hσi.symm
    simp only [act, hσj] at h1
    exact h1
  rcases zmod2_cases (x 0) with h | h
  · left
    funext i
    rw [hconst i 0, h]
    rfl
  · right
    funext i
    rw [hconst i 0, h]
    rfl

end Fixed

section PermMod

@[expose] def toAdd8 (S : Subgroup (G6.PermMod 8)) : AddSubgroup Vec where
  carrier := {x | Multiplicative.ofAdd x ∈ S}
  zero_mem' := S.one_mem
  add_mem' := fun ha hb => S.mul_mem ha hb
  neg_mem' := fun ha => S.inv_mem ha

theorem card_toAdd8 (S : Subgroup (G6.PermMod 8)) : Nat.card (toAdd8 S) = Nat.card S :=
  Nat.card_congr
    { toFun := fun x => ⟨Multiplicative.ofAdd (x : Vec), x.2⟩
      invFun := fun s => ⟨Multiplicative.toAdd (s : G6.PermMod 8), s.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem exists_translation_permMod {S : Subgroup (G6.PermMod 8)} (hS : Nat.card S = 16)
    (hj : G6.allOnes 8 ∈ S) (hev : S ≤ G6.coreMod 8) {g : Perm (Fin 8)} (hg : orderOf g = 7)
    (hgS : ∀ s ∈ S, G6.permAct 8 g s ∈ S) :
    ∃ σ ∈ alternatingGroup (Fin 8),
      (∀ s ∈ S, G6.permAct 8 σ s ∈ S ∧
        (G6.permAct 8 σ s = s ∨ G6.permAct 8 σ s = s * G6.allOnes 8)) ∧
          ∃ s ∈ S, G6.permAct 8 σ s ≠ s := by
  obtain ⟨σ, hσ, h1, x, hx, hx'⟩ := exists_translation (A := toAdd8 S)
    (by rw [card_toAdd8]; exact hS) hj (fun x hx => hev hx) hg (fun x hx => hgS _ hx)
  refine ⟨σ, hσ, fun s hs => ?_, Multiplicative.ofAdd x, hx,
    fun h => hx' (congrArg Multiplicative.toAdd h)⟩
  obtain ⟨h2, h3⟩ := h1 (Multiplicative.toAdd s) hs
  refine ⟨h2, ?_⟩
  rcases h3 with h | h
  · exact Or.inl (congrArg Multiplicative.ofAdd h)
  · exact Or.inr (congrArg Multiplicative.ofAdd h)

theorem eq_one_of_fix_permMod {S : Subgroup (G6.PermMod 8)} (hS : Nat.card S = 16)
    (hj : G6.allOnes 8 ∈ S) (hev : S ≤ G6.coreMod 8) {g : Perm (Fin 8)} (hg : orderOf g = 7)
    (hgS : ∀ s ∈ S, G6.permAct 8 g s ∈ S) {τ : Perm (Fin 8)}
    (hτ : ∀ s ∈ S, G6.permAct 8 τ s = s) : τ = 1 :=
  eq_one_of_fix (A := toAdd8 S) (by rw [card_toAdd8]; exact hS) hj (fun x hx => hev hx) hg
    (fun x hx => hgS _ hx) fun x hx => congrArg Multiplicative.toAdd (hτ _ hx)

theorem eq_one_or_allOnes_of_fix {x : G6.PermMod 8}
    (hx : ∀ σ ∈ alternatingGroup (Fin 8), G6.permAct 8 σ x = x) : x = 1 ∨ x = G6.allOnes 8 := by
  rcases eq_zero_or_jVec_of_alt (x := Multiplicative.toAdd x)
    (fun σ hσ => congrArg Multiplicative.toAdd (hx σ hσ)) with h | h
  · exact Or.inl (congrArg Multiplicative.ofAdd h)
  · exact Or.inr (congrArg Multiplicative.ofAdd h)

end PermMod

end CFSG.Quasithin.H13.A7.LinCode
