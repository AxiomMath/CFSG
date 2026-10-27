module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitTvLinAlg
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLTvALinAlg
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic.Ring

public section

namespace CFSG.StandardType.UnitTv

open LinTvA

variable {p d : ℕ}

theorem pairVec_add (i j l k : Fin d) :
    pairVec p i j k + pairVec p j l k = pairVec p i l k := by
  simp only [pairVec]
  ring

theorem pairVec_perm (σ : Equiv.Perm (Fin d)) (i j k : Fin d) :
    pairVec p (σ i) (σ j) k = pairVec p i j (σ⁻¹ k) := by
  simp only [pairVec, Equiv.Perm.inv_eq_iff_eq]

@[expose] def pairCob (p : ℕ) {d : ℕ} (i j : Fin d) : Fin d → Fin d → ZMod p :=
  fun k l => pairVec p i j k - pairVec p i j l

structure CobData (p d : ℕ) (G : Type*) [AddCommGroup G] where
  lam : G →+ (Fin d → Fin d → ZMod p)
  inj : Function.Injective lam
  coc : ∀ a k l m, lam a k l + lam a l m = lam a k m
  m : Fin d → Fin d → G
  hm : ∀ i j, lam (m i j) = pairCob p i j
  ρ : Equiv.Perm (Fin d) → G →+ G
  hρ : ∀ σ a k l, lam (ρ σ a) k l = lam a (σ⁻¹ k) (σ⁻¹ l)

@[expose] def kap (p d : ℕ) : ZMod p := 1 - ((d : ZMod p)⁻¹) * (d : ZMod p)

theorem kap_mul_d [Fact p.Prime] : kap p d * (d : ZMod p) = 0 := by
  unfold kap
  by_cases h : (d : ZMod p) = 0
  · rw [h]
    ring
  · rw [inv_mul_cancel₀ h]
    ring

theorem sum_shift_mul (u v : Fin d → ZMod p) (σ : Equiv.Perm (Fin d)) (uj vj : ZMod p) :
    ∑ k, (u (σ k) - uj) * (v (σ k) - vj) =
      ∑ k, u k * v k - uj * ∑ k, v k - vj * ∑ k, u k + (d : ZMod p) * uj * vj := by
  have h1 : ∑ k, (u (σ k) - uj) * (v (σ k) - vj) =
      ∑ k, (u (σ k) * v (σ k) - uj * v (σ k) - vj * u (σ k) + uj * vj) :=
    Finset.sum_congr rfl fun k _ => by ring
  have e1 : ∑ k, u (σ k) * v (σ k) = ∑ k, u k * v k :=
    Fintype.sum_equiv σ (fun k => u (σ k) * v (σ k)) (fun k => u k * v k) fun _ => rfl
  have e2 : ∑ k, v (σ k) = ∑ k, v k := Fintype.sum_equiv σ (fun k => v (σ k)) v fun _ => rfl
  have e3 : ∑ k, u (σ k) = ∑ k, u k := Fintype.sum_equiv σ (fun k => u (σ k)) u fun _ => rfl
  rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, e1, e2, e3, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

theorem two_ne_zero_zmod [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h')

theorem sum_pairVec (i j : Fin d) : ∑ k, pairVec p i j k = 0 := by
  simp only [pairVec, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem sum_mul_pairVec (f : Fin d → ZMod p) (i j : Fin d) :
    ∑ k, f k * pairVec p i j k = f i - f j := by
  simp only [pairVec, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sum_mul_pairVec_base (w : Fin d → ZMod p) (k₀ l : Fin d) :
    ∑ k, w k * pairVec p k k₀ l = w l - (if l = k₀ then ∑ k, w k else 0) := by
  by_cases hl : l = k₀
  · simp [pairVec, hl, mul_sub, Finset.sum_sub_distrib]
  · simp [pairVec, hl, mul_sub, Finset.sum_sub_distrib]

namespace CobData

variable {G : Type*} [AddCommGroup G] (C : CobData p d G)

include C

theorem lam_self (a : G) (k : Fin d) : C.lam a k k = 0 := by
  have h := C.coc a k k k
  linear_combination h

theorem lam_swap (a : G) (k l : Fin d) : C.lam a l k = - C.lam a k l := by
  have h := C.coc a k l k
  rw [C.lam_self] at h
  linear_combination h

theorem lam_sub (a : G) (k l k₀ : Fin d) : C.lam a k l = C.lam a k k₀ - C.lam a l k₀ := by
  have h := C.coc a k k₀ l
  have h' := C.lam_swap a k₀ l
  linear_combination (-1 : ZMod p) * h + h'

theorem exp_p (a : G) : p • a = 0 := by
  apply C.inj
  rw [map_nsmul, map_zero]
  funext k l
  simp [nsmul_eq_mul]

theorem m_add (i j k : Fin d) : C.m i j + C.m j k = C.m i k := by
  apply C.inj
  rw [map_add, C.hm, C.hm, C.hm]
  funext a b
  simp only [pairCob, Pi.add_apply]
  have h1 := pairVec_add (p := p) i j k a
  have h2 := pairVec_add (p := p) i j k b
  linear_combination h1 - h2

theorem m_self (i : Fin d) : C.m i i = 0 := by
  have h := C.m_add i i i
  exact add_eq_right.mp h

theorem ρ_m (σ : Equiv.Perm (Fin d)) (i j : Fin d) : C.ρ σ (C.m i j) = C.m (σ i) (σ j) := by
  apply C.inj
  funext k l
  rw [C.hρ, C.hm, C.hm]
  simp only [pairCob, pairVec_perm]

variable (k₀ : Fin d)

@[expose] def scHom : G →+ ZMod p :=
  AddMonoidHom.mk' (fun a => ∑ k, C.lam a k k₀) fun a b => by
    simp only [map_add, Pi.add_apply, Finset.sum_add_distrib]

theorem scHom_apply (a : G) : C.scHom k₀ a = ∑ k, C.lam a k k₀ := rfl

@[expose] def Bc (a b : G) : ZMod p :=
  ∑ k, C.lam a k k₀ * C.lam b k k₀ - ((d : ZMod p)⁻¹) * C.scHom k₀ a * C.scHom k₀ b

theorem Bc_add_left (a a' b : G) : C.Bc k₀ (a + a') b = C.Bc k₀ a b + C.Bc k₀ a' b := by
  unfold Bc
  simp only [map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

theorem Bc_add_right (a b b' : G) : C.Bc k₀ a (b + b') = C.Bc k₀ a b + C.Bc k₀ a b' := by
  unfold Bc
  simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem Bc_symm (a b : G) : C.Bc k₀ a b = C.Bc k₀ b a := by
  unfold Bc
  simp only [mul_comm (C.lam a _ k₀), mul_comm (C.scHom k₀ a)]
  ring

theorem scHom_ρ (σ : Equiv.Perm (Fin d)) (a : G) :
    C.scHom k₀ (C.ρ σ a) = C.scHom k₀ a - (d : ZMod p) * C.lam a (σ⁻¹ k₀) k₀ := by
  have h : ∀ k, C.lam (C.ρ σ a) k k₀ = C.lam a (σ⁻¹ k) k₀ - C.lam a (σ⁻¹ k₀) k₀ := fun k => by
    rw [C.hρ, C.lam_sub a (σ⁻¹ k) (σ⁻¹ k₀) k₀]
  rw [scHom_apply, scHom_apply]
  simp only [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [Fintype.sum_equiv σ⁻¹ (fun k => C.lam a (σ⁻¹ k) k₀) (fun k => C.lam a k k₀) fun _ => rfl]

theorem Bc_ρ [Fact p.Prime] (σ : Equiv.Perm (Fin d)) (a b : G) :
    C.Bc k₀ (C.ρ σ a) (C.ρ σ b) = C.Bc k₀ a b -
      kap p d * (C.lam a (σ⁻¹ k₀) k₀ * C.scHom k₀ b + C.lam b (σ⁻¹ k₀) k₀ * C.scHom k₀ a) +
        (d : ZMod p) * kap p d * C.lam a (σ⁻¹ k₀) k₀ * C.lam b (σ⁻¹ k₀) k₀ := by
  have h : ∀ (c : G) k, C.lam (C.ρ σ c) k k₀ = C.lam c (σ⁻¹ k) k₀ - C.lam c (σ⁻¹ k₀) k₀ :=
    fun c k => by rw [C.hρ, C.lam_sub c (σ⁻¹ k) (σ⁻¹ k₀) k₀]
  have hs := C.scHom_ρ k₀ σ a
  have hs' := C.scHom_ρ k₀ σ b
  unfold Bc
  simp only [h]
  rw [sum_shift_mul (fun k => C.lam a k k₀) (fun k => C.lam b k k₀) σ⁻¹, hs, hs']
  have e1 := C.scHom_apply k₀ a
  have e2 := C.scHom_apply k₀ b
  unfold kap
  rw [← e1, ← e2]
  ring

@[expose] def Msub : AddSubgroup G :=
  ((AddMonoidHom.mulLeft (kap p d)).comp (C.scHom k₀)).ker

theorem mem_Msub {a : G} : a ∈ C.Msub k₀ ↔ kap p d * C.scHom k₀ a = 0 :=
  AddMonoidHom.mem_ker

theorem ρ_mem [Fact p.Prime] (σ : Equiv.Perm (Fin d)) {a : G} (ha : a ∈ C.Msub k₀) :
    C.ρ σ a ∈ C.Msub k₀ := by
  rw [mem_Msub] at ha ⊢
  rw [C.scHom_ρ k₀ σ a]
  linear_combination ha - (C.lam a (σ⁻¹ k₀) k₀) * kap_mul_d (p := p) (d := d)

theorem ρ_sub_mem [Fact p.Prime] (σ : Equiv.Perm (Fin d)) (a : G) :
    C.ρ σ a - a ∈ C.Msub k₀ := by
  rw [mem_Msub, map_sub, C.scHom_ρ k₀ σ a]
  linear_combination -(C.lam a (σ⁻¹ k₀) k₀) * kap_mul_d (p := p) (d := d)

theorem Bc_ρ_M [Fact p.Prime] (σ : Equiv.Perm (Fin d)) {a b : G} (ha : a ∈ C.Msub k₀)
    (hb : b ∈ C.Msub k₀) : C.Bc k₀ (C.ρ σ a) (C.ρ σ b) = C.Bc k₀ a b := by
  rw [mem_Msub] at ha hb
  rw [C.Bc_ρ k₀ σ a b]
  linear_combination -(C.lam a (σ⁻¹ k₀) k₀) * hb - (C.lam b (σ⁻¹ k₀) k₀) * ha +
    (C.lam a (σ⁻¹ k₀) k₀ * C.lam b (σ⁻¹ k₀) k₀) * kap_mul_d (p := p) (d := d)

theorem scHom_m [Fact p.Prime] (i j : Fin d) :
    C.scHom k₀ (C.m i j) = - (d : ZMod p) * pairVec p i j k₀ := by
  rw [scHom_apply]
  simp only [hm, pairCob, Finset.sum_sub_distrib, sum_pairVec, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

theorem m_mem [Fact p.Prime] (i j : Fin d) : C.m i j ∈ C.Msub k₀ := by
  rw [mem_Msub, C.scHom_m k₀ i j]
  linear_combination -(pairVec p i j k₀) * kap_mul_d (p := p) (d := d)

theorem gen_mem [Fact p.Prime] {a : G} (ha : a ∈ C.Msub k₀) :
    a ∈ AddSubgroup.closure (Set.range fun k : Fin d => C.m k k₀) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hka := (C.mem_Msub k₀).mp ha
  set w : Fin d → ZMod p := fun k => C.lam a k k₀ - ((d : ZMod p)⁻¹) * C.scHom k₀ a with hw
  have hwsum : ∑ k, w k = 0 := by
    simp only [hw, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← scHom_apply]
    unfold kap at hka
    linear_combination hka
  have key : a = ∑ k, (w k).val • C.m k k₀ := by
    apply C.inj
    funext l l'
    rw [map_sum]
    simp only [map_nsmul, C.hm, Finset.sum_apply, Pi.smul_apply]
    simp only [pairCob, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_sub, Finset.sum_sub_distrib,
      sum_mul_pairVec_base, hwsum, ite_self, sub_zero]
    simp only [hw]
    rw [C.lam_sub a l l' k₀]
    ring
  rw [key]
  exact AddSubgroup.sum_mem _ fun k _ =>
    AddSubgroup.nsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self k)) _

theorem Bc_m_base [Fact p.Prime] {a : G} (ha : a ∈ C.Msub k₀) {k : Fin d} (hk : k ≠ k₀) :
    C.Bc k₀ a (C.m k k₀) = C.lam a k k₀ := by
  have hx : ∀ l, C.lam (C.m k k₀) l k₀ = pairVec p k k₀ l + 1 := by
    intro l
    simp only [C.hm, pairCob]
    rw [pairVec_right hk]
    ring
  have hs : C.scHom k₀ (C.m k k₀) = (d : ZMod p) := by
    rw [scHom_apply]
    simp only [hx, Finset.sum_add_distrib, sum_pairVec, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, zero_add]
  have h1 : ∑ l, C.lam a l k₀ * (pairVec p k k₀ l + 1) =
      (C.lam a k k₀ - C.lam a k₀ k₀) + C.scHom k₀ a := by
    simp only [mul_add, mul_one, Finset.sum_add_distrib, sum_mul_pairVec]
    rw [scHom_apply]
  unfold Bc
  simp only [hx, hs]
  rw [h1, C.lam_self]
  have h2 := (C.mem_Msub k₀).mp ha
  unfold kap at h2
  linear_combination h2

theorem Bc_m_m [Fact p.Prime] {i j : Fin d} (hij : i ≠ j) (hi : k₀ ≠ i) (hj : k₀ ≠ j) :
    C.Bc k₀ (C.m i j) (C.m i j) = 2 := by
  have hx : ∀ l, C.lam (C.m i j) l k₀ = pairVec p i j l := by
    intro l
    simp only [C.hm, pairCob]
    rw [pairVec_of_ne hi hj]
    ring
  have hs : C.scHom k₀ (C.m i j) = 0 := by
    rw [scHom_apply]
    simp only [hx, sum_pairVec]
  unfold Bc
  simp only [hx, hs]
  rw [sum_mul_pairVec, pairVec_left hij, pairVec_right hij]
  ring

theorem nondeg [Fact p.Prime] {a : G} (ha : a ∈ C.Msub k₀)
    (h : ∀ b ∈ C.Msub k₀, C.Bc k₀ a b = 0) : a = 0 := by
  apply C.inj
  have hx : ∀ k, C.lam a k k₀ = 0 := by
    intro k
    by_cases hk : k = k₀
    · rw [hk, C.lam_self]
    · rw [← C.Bc_m_base k₀ ha hk]
      exact h _ (C.m_mem k₀ k k₀)
  funext k l
  rw [C.lam_sub a k l k₀, hx, hx, map_zero]
  simp

section Transvection

variable [Fact p.Prime] (hp2 : p ≠ 2) (T : G →+ G)
  (hT : ∀ σ : Equiv.Perm (Fin d), ∃ π : Equiv.Perm (Fin d), ∀ a, T (C.ρ σ a) = C.ρ π (T a))

include hp2 hT

theorem T_m_mem (i j : Fin d) : T (C.m i j) ∈ C.Msub k₀ := by
  by_cases hij : i = j
  · rw [hij, C.m_self, map_zero]
    exact (C.Msub k₀).zero_mem
  obtain ⟨e, he⟩ : ∃ e : ℕ, 2 * e = p + 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd' with h | h
    · exact absurd h hp2
    · obtain ⟨t, ht⟩ := h
      exact ⟨t + 1, by omega⟩
  have hneg : C.m j i = - C.m i j := by
    have h := C.m_add i j i
    rw [C.m_self] at h
    exact eq_neg_of_add_eq_zero_right h
  set σ : Equiv.Perm (Fin d) := Equiv.swap i j with hσ
  have h1 : C.ρ σ (C.m i j) = - C.m i j := by
    rw [C.ρ_m, hσ, Equiv.swap_apply_left, Equiv.swap_apply_right, hneg]
  have hb : C.ρ σ (-(e • C.m i j)) - -(e • C.m i j) = C.m i j := by
    rw [map_neg, map_nsmul, h1, smul_neg, neg_neg, sub_neg_eq_add, ← add_nsmul, ← two_mul, he,
      add_nsmul, C.exp_p, zero_add, one_nsmul]
  obtain ⟨π, hπ⟩ := hT σ
  have : T (C.m i j) = C.ρ π (T (-(e • C.m i j))) - T (-(e • C.m i j)) := by
    conv_lhs => rw [← hb]
    rw [map_sub, hπ]
  rw [this]
  exact C.ρ_sub_mem k₀ π _

theorem T_mem {a : G} (ha : a ∈ C.Msub k₀) : T a ∈ C.Msub k₀ := by
  have hTm : ∀ i j, T (C.m i j) ∈ C.Msub k₀ := C.T_m_mem k₀ hp2 T hT
  refine AddSubgroup.closure_induction (p := fun x _ => T x ∈ C.Msub k₀) ?_ ?_ ?_ ?_
    (C.gen_mem k₀ ha)
  · rintro _ ⟨k, rfl⟩
    exact hTm k k₀
  · rw [map_zero]
    exact (C.Msub k₀).zero_mem
  · intro x y _ _ hx hy
    rw [map_add]
    exact (C.Msub k₀).add_mem hx hy
  · intro x _ hx
    rw [map_neg]
    exact (C.Msub k₀).neg_mem hx

omit hT in
theorem eq_of_ρ_eq (hd : 5 ≤ d) {σ π : Equiv.Perm (Fin d)}
    (h : ∀ a ∈ C.Msub k₀, C.ρ σ a = C.ρ π a) : σ = π := by
  refine Equiv.ext fun i => ?_
  by_contra hne
  obtain ⟨j, hji, -⟩ := exists_ne_two (by omega : 3 ≤ d) i i
  have h1 := h _ (C.m_mem k₀ i j)
  rw [C.ρ_m, C.ρ_m] at h1
  have h2 := congrArg C.lam h1
  rw [C.hm, C.hm] at h2
  obtain ⟨l, hl1, hl2, hl3, hl4⟩ := exists_ne_four hd (σ i) (σ j) (π i) (π j)
  have h3 : ∀ k, pairVec p (σ i) (σ j) k = pairVec p (π i) (π j) k := by
    intro k
    have h5 := congrFun (congrFun h2 k) l
    simp only [pairCob, pairVec_of_ne hl1 hl2, pairVec_of_ne hl3 hl4, sub_zero] at h5
    exact h5
  have h4 := h3 (σ i)
  rw [pairVec_left (σ.injective.ne hji.symm)] at h4
  have h6 : pairVec p (π i) (π j) (σ i) = - (if σ i = π j then 1 else 0) := by
    simp [pairVec, hne]
  by_cases hh : σ i = π j
  · rw [h6, if_pos hh] at h4
    exact two_ne_zero_zmod hp2 (by linear_combination h4)
  · rw [h6, if_neg hh, neg_zero] at h4
    exact one_ne_zero h4

theorem false_of_transvection [Finite G] (hd : 5 ≤ d)
    (hfix : Nat.card {a // T a = a} * p = Nat.card G) (hN : ∀ a, T (T a - a) = T a - a) :
    False := by
  classical
  have hp : p.Prime := Fact.out
  have h2 := two_ne_zero_zmod (p := p) hp2
  set k₀ : Fin d := ⟨2, by omega⟩ with hk₀
  set i₀ : Fin d := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin d := ⟨1, by omega⟩ with hi₁
  have hi01 : i₀ ≠ i₁ := by simp [hi₀, hi₁, Fin.ext_iff]
  have hk0 : k₀ ≠ i₀ := by simp [hk₀, hi₀, Fin.ext_iff]
  have hk1 : k₀ ≠ i₁ := by simp [hk₀, hi₁, Fin.ext_iff]
  have hTM : ∀ a ∈ C.Msub k₀, T a ∈ C.Msub k₀ := fun a ha => C.T_mem k₀ hp2 T hT ha
  set c₀ : ZMod p := C.Bc k₀ (T (C.m i₀ i₁)) (T (C.m i₀ i₁)) * (2 : ZMod p)⁻¹ with hc₀
  set D : G → G → ZMod p := fun a b => C.Bc k₀ (T a) (T b) - c₀ * C.Bc k₀ a b with hD
  have hDl : ∀ a a' b, D (a + a') b = D a b + D a' b := by
    intro a a' b
    simp only [hD, map_add, C.Bc_add_left]
    ring
  have hDr : ∀ a b b', D a (b + b') = D a b + D a b' := by
    intro a b b'
    simp only [hD, map_add, C.Bc_add_right]
    ring
  have hDs : ∀ a b, D a b = D b a := by
    intro a b
    simp only [hD]
    rw [C.Bc_symm k₀ (T a), C.Bc_symm k₀ a]
  have hDinv : ∀ σ : Equiv.Perm (Fin d), ∀ a ∈ C.Msub k₀, ∀ b ∈ C.Msub k₀,
      D (C.ρ σ a) (C.ρ σ b) = D a b := by
    intro σ a ha b hb
    obtain ⟨π, hπ⟩ := hT σ
    simp only [hD]
    rw [hπ a, hπ b, C.Bc_ρ_M k₀ π (hTM a ha) (hTM b hb), C.Bc_ρ_M k₀ σ ha hb]
  have hD01 : D (C.m i₀ i₁) (C.m i₀ i₁) = 0 := by
    simp only [hD]
    rw [C.Bc_m_m k₀ hi01 hk0 hk1, hc₀, mul_assoc, inv_mul_cancel₀ h2, mul_one, sub_self]
  have hvan := form_vanish hp2 (C.Msub k₀) C.m k₀ i₀ i₁ hi01 C.m_add
    (fun a ha => C.gen_mem k₀ ha) C.ρ C.ρ_m (C.m_mem k₀) D hDl hDr hDs hDinv hD01
  have hsim : ∀ a ∈ C.Msub k₀, ∀ b ∈ C.Msub k₀,
      C.Bc k₀ (T a) (T b) = c₀ * C.Bc k₀ a b := by
    intro a ha b hb
    have h := hvan a ha b hb
    simp only [hD] at h
    linear_combination h
  by_cases hne : ∃ u ∈ C.Msub k₀, T u - u ≠ 0
  · exact false_of_similitude_transvection hp2 (C.Msub k₀) (C.Bc k₀) (C.Bc_add_left k₀)
      (C.Bc_add_right k₀) (C.Bc_symm k₀) (fun a ha h => C.nondeg k₀ ha h) T hTM c₀ hsim
      (fun a _ => hN a)
      (fun a _ b _ ha => exists_nsmul_of_card_fix C.exp_p T hfix a b ha) hne
  push Not at hne
  have hTid : ∀ a ∈ C.Msub k₀, T a = a := fun a ha => sub_eq_zero.mp (hne a ha)
  have hcomm : ∀ σ a, T (C.ρ σ a) = C.ρ σ (T a) := by
    intro σ a
    obtain ⟨π, hπ⟩ := hT σ
    have hπσ : σ = π := C.eq_of_ρ_eq k₀ hp2 hd fun b hb => by
      have h1 := hπ b
      rw [hTid _ (C.ρ_mem k₀ σ hb), hTid b hb] at h1
      exact h1
    rw [hπ a, hπσ]
  have hall : ∀ a, T a = a := by
    intro a
    have hfixu : ∀ σ, C.ρ σ (T a - a) = T a - a := by
      intro σ
      have h1 := hTid _ (C.ρ_sub_mem k₀ σ a)
      rw [map_sub, hcomm] at h1
      rw [map_sub]
      exact sub_eq_sub_iff_sub_eq_sub.mp h1
    have hu : T a - a = 0 := by
      apply C.inj
      funext k l
      by_cases hkl : k = l
      · rw [hkl, C.lam_self, map_zero]
        rfl
      · have h5 := C.hρ (Equiv.swap k l) (T a - a) k l
        rw [hfixu, Equiv.swap_inv, Equiv.swap_apply_left, Equiv.swap_apply_right,
          C.lam_swap _ k l] at h5
        have h6 : 2 * C.lam (T a - a) k l = 0 := by linear_combination h5
        have h7 := (mul_eq_zero.mp h6).resolve_left h2
        rw [h7, map_zero]
        rfl
    exact sub_eq_zero.mp hu
  have hcard : Nat.card {a // T a = a} = Nat.card G :=
    Nat.card_congr (Equiv.subtypeUnivEquiv hall)
  rw [hcard] at hfix
  have hpos : 0 < Nat.card G := Nat.card_pos
  have h8 : Nat.card G * p = Nat.card G * 1 := by rw [hfix, mul_one]
  exact hp.one_lt.ne' (Nat.eq_of_mul_eq_mul_left hpos h8)

end Transvection

end CobData

end CFSG.StandardType.UnitTv

end
