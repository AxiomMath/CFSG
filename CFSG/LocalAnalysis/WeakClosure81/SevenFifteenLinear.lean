module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.WeakClosure81

private def zmodFinEquiv (p : ℕ) [NeZero p] : ZMod p ≃ Fin p where
  toFun b := ⟨b.val, ZMod.val_lt b⟩
  invFun j := (j.val : ZMod p)
  left_inv b := ZMod.natCast_zmod_val b
  right_inv j := by
    apply Fin.ext
    change ((j.val : ZMod p)).val = j.val
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt j.isLt]

private lemma sum_zmod_eq_sum_range {M : Type*} [AddCommMonoid M] {p : ℕ} [NeZero p]
    (f : ℕ → M) : ∑ b : ZMod p, f b.val = ∑ j ∈ Finset.range p, f j := by
  rw [Finset.sum_range]
  exact Equiv.sum_comp (zmodFinEquiv p) (fun j : Fin p => f j.val)

private lemma sum_zmod_pow_mul_eq {R : Type*} [Ring R] {p : ℕ} [Fact p.Prime] {τ : R}
    (hτ : τ ^ p = 1) {c : ℕ} (h0 : 0 < c) (hc : c < p) :
    ∑ b : ZMod p, τ ^ (b.val * c) = ∑ j ∈ Finset.range p, τ ^ j := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hc' : (c : ZMod p) ≠ 0 := by
    intro h
    have hpdc : p ∣ c := (ZMod.natCast_eq_zero_iff c p).mp h
    exact absurd (Nat.le_of_dvd h0 hpdc) (not_le.mpr hc)
  have h1 : ∀ b : ZMod p, τ ^ (b.val * c) = τ ^ ((b * (c : ZMod p)).val) := by
    intro b
    rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_eq_of_lt hc]
    exact pow_eq_pow_mod (b.val * c) hτ
  calc
    ∑ b : ZMod p, τ ^ (b.val * c)
        = ∑ b : ZMod p, τ ^ ((b * (c : ZMod p)).val) :=
          Finset.sum_congr rfl fun b _ => h1 b
    _ = ∑ b : ZMod p, τ ^ (((c : ZMod p) * b).val) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [mul_comm]
    _ = ∑ b : ZMod p, τ ^ b.val :=
          Equiv.sum_comp (Equiv.mulLeft₀ (c : ZMod p) hc') (fun b : ZMod p => τ ^ b.val)
    _ = ∑ j ∈ Finset.range p, τ ^ j := sum_zmod_eq_sum_range (fun j => τ ^ j)

private lemma sum_range_pow_mul_eq {R : Type*} [Ring R] {p : ℕ} [Fact p.Prime] {τ : R}
    (hτ : τ ^ p = 1) {c : ℕ} (h0 : 0 < c) (hc : c < p) :
    ∑ j ∈ Finset.range p, τ ^ (c * j) = ∑ j ∈ Finset.range p, τ ^ j := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [← sum_zmod_eq_sum_range (fun j => τ ^ (c * j))]
  rw [Finset.sum_congr rfl (fun b _ => by rw [mul_comm])]
  exact sum_zmod_pow_mul_eq hτ h0 hc

private lemma pred_mul_mod_eq {p j : ℕ} (hp : 0 < p) (hj : j ≤ p) :
    ((p - 1) * j) % p = (p - j) % p := by
  haveI : NeZero p := ⟨hp.ne'⟩
  have hpc : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  have hp1 : ((p - 1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub (show 1 ≤ p from hp), hpc]
    ring
  have hsub : ((p - j : ℕ) : ZMod p) = -((j : ℕ) : ZMod p) := by
    rw [Nat.cast_sub hj, hpc]
    ring
  have h1 : (((p - 1) * j : ℕ) : ZMod p) = ((p - j : ℕ) : ZMod p) := by
    rw [Nat.cast_mul, hp1, hsub]
    ring
  rw [← ZMod.val_natCast p ((p - 1) * j), ← ZMod.val_natCast p (p - j), h1]

private lemma pow_pred_mul_eq {R : Type*} [Monoid R] {p j : ℕ} (hp : 0 < p) {σ : R}
    (hσ : σ ^ p = 1) (hj : j ≤ p) : σ ^ ((p - 1) * j) = σ ^ (p - j) := by
  haveI : NeZero p := ⟨hp.ne'⟩
  rw [pow_eq_pow_mod ((p - 1) * j) hσ, pow_eq_pow_mod (p - j) hσ]
  rw [pred_mul_mod_eq hp hj]

theorem sum_geom_sum_mul_pow_add_geom_sum {R : Type*} [Ring R] {p : ℕ} [Fact p.Prime] {σ τ : R}
    (hστ : Commute σ τ) (hτ : τ ^ p = 1) :
    ∑ b : ZMod p, ∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j + ∑ j ∈ Finset.range p, τ ^ j =
      (p : R) + (∑ i ∈ Finset.range p, σ ^ i) * ∑ j ∈ Finset.range p, τ ^ j := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hterm : ∀ b : ZMod p, ∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j =
      ∑ j ∈ Finset.range p, σ ^ j * τ ^ (b.val * j) := by
    intro b
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(hστ.pow_right b.val).mul_pow j, ← pow_mul τ b.val j]
  have hkey : ∀ j : ℕ, 0 < j → j < p → ∑ b : ZMod p, τ ^ (b.val * j) =
      ∑ j ∈ Finset.range p, τ ^ j := fun j hj0 hjp => sum_zmod_pow_mul_eq hτ hj0 hjp
  have hmain : ∑ b : ZMod p, ∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j =
      (∑ j ∈ Finset.range (p-1), σ ^ (j+1)) * (∑ j ∈ Finset.range p, τ ^ j) + (p : R) := by
    rw [Finset.sum_congr rfl (fun b _ => hterm b), Finset.sum_comm]
    have hstep : ∑ j ∈ Finset.range p, ∑ b : ZMod p, σ ^ j * τ ^ (b.val * j) =
        ∑ j ∈ Finset.range p, σ ^ j * ∑ b : ZMod p, τ ^ (b.val * j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
    rw [hstep]
    have hsplit := Finset.sum_range_succ'
      (fun j => σ ^ j * ∑ b : ZMod p, τ ^ (b.val * j)) (p-1)
    rw [show p - 1 + 1 = p from Nat.succ_pred_eq_of_pos hp0] at hsplit
    rw [hsplit]
    have hF0 : σ ^ 0 * ∑ b : ZMod p, τ ^ (b.val * 0) = (p : R) := by
      rw [pow_zero, one_mul]
      simp only [Nat.mul_zero, pow_zero, Finset.sum_const, Finset.card_univ, ZMod.card,
        nsmul_eq_mul, mul_one]
    have hFpos : ∑ j ∈ Finset.range (p-1), σ ^ (j+1) * ∑ b : ZMod p, τ ^ (b.val * (j+1)) =
        (∑ j ∈ Finset.range (p-1), σ ^ (j+1)) * (∑ j ∈ Finset.range p, τ ^ j) := by
      have hc : ∀ j ∈ Finset.range (p-1), σ ^ (j+1) * ∑ b : ZMod p, τ ^ (b.val * (j+1)) =
          σ ^ (j+1) * (∑ j ∈ Finset.range p, τ ^ j) := by
        intro j hj
        rw [hkey (j+1) (Nat.succ_pos j) (Nat.lt_of_le_of_lt
          (Nat.lt_iff_add_one_le.mp (Finset.mem_range.mp hj))
          (Nat.sub_one_lt (Fact.out : p.Prime).ne_zero))]
      rw [Finset.sum_congr rfl hc, ← Finset.sum_mul]
    rw [hFpos, hF0]
  have hNσ : ∑ i ∈ Finset.range p, σ ^ i = (∑ j ∈ Finset.range (p-1), σ ^ (j+1)) + 1 := by
    have h := Finset.sum_range_succ' (fun k : ℕ => σ ^ k) (p-1)
    rw [show p - 1 + 1 = p from Nat.succ_pred_eq_of_pos hp0, pow_zero] at h
    exact h
  rw [hmain, hNσ, add_mul, one_mul]
  abel

theorem mul_geom_sum_eq_geom_sum {R : Type*} [Ring R] {p : ℕ} (hp : 0 < p) {φ : R}
    (hφ : φ ^ p = 1) : φ * ∑ j ∈ Finset.range p, φ ^ j = ∑ j ∈ Finset.range p, φ ^ j := by
  have hcomm : Commute φ (∑ j ∈ Finset.range p, φ ^ j) :=
    Commute.sum_right _ _ _ fun j _ => (Commute.refl φ).pow_right j
  have hN : (∑ j ∈ Finset.range p, φ ^ j) * (φ - 1) = 0 := by
    rw [geom_sum_mul, hφ, sub_self]
  rw [hcomm.eq]
  rw [mul_sub, mul_one, sub_eq_zero] at hN
  exact hN

private lemma geom_sum_mul_self_eq {R : Type*} [Ring R] {p : ℕ} (hp : 0 < p) {φ : R}
    (hφ : φ ^ p = 1) (hpR : (p : R) = 1) :
    (∑ j ∈ Finset.range p, φ ^ j) * (∑ j ∈ Finset.range p, φ ^ j) =
      ∑ j ∈ Finset.range p, φ ^ j := by
  have hNφ : (∑ j ∈ Finset.range p, φ ^ j) * φ = ∑ j ∈ Finset.range p, φ ^ j := by
    have hcomm : Commute (∑ j ∈ Finset.range p, φ ^ j) φ :=
      Commute.sum_left _ _ _ fun j _ => (Commute.refl φ).pow_left j
    rw [hcomm.eq, mul_geom_sum_eq_geom_sum hp hφ]
  have hNφpow : ∀ j : ℕ, (∑ j ∈ Finset.range p, φ ^ j) * φ ^ j =
      ∑ j ∈ Finset.range p, φ ^ j := by
    intro j
    induction j with
    | zero => rw [pow_zero, mul_one]
    | succ j ih => rw [pow_succ, ← mul_assoc, ih, hNφ]
  calc (∑ j ∈ Finset.range p, φ ^ j) * (∑ j ∈ Finset.range p, φ ^ j)
      = ∑ j ∈ Finset.range p, (∑ j ∈ Finset.range p, φ ^ j) * φ ^ j := by
        rw [Finset.mul_sum]
    _ = ∑ j ∈ Finset.range p, (∑ j ∈ Finset.range p, φ ^ j) := by
        refine Finset.sum_congr rfl fun j _ => hNφpow j
    _ = p • (∑ j ∈ Finset.range p, φ ^ j) := by
        rw [Finset.sum_const, Finset.card_range]
    _ = (p : R) * (∑ j ∈ Finset.range p, φ ^ j) := by rw [nsmul_eq_mul]
    _ = ∑ j ∈ Finset.range p, φ ^ j := by rw [hpR, one_mul]

section FTwo

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

private lemma natCast_zmod_two_of_odd {p : ℕ} (hp : Odd p) : (p : ZMod 2) = 1 := by
  obtain ⟨m, rfl⟩ := hp
  have h2 : (2 : ZMod 2) = 0 := by decide
  push_cast
  rw [h2, zero_mul, zero_add]

private lemma finrank_eq_sum_finrank_range_of_orthogonal [Finite M] {ι : Type*} [Fintype ι]
    {e : ι → Module.End (ZMod 2) M} (hsum : ∑ i, e i = 1) (hidem : ∀ i, e i * e i = e i)
    (horth : ∀ i j, i ≠ j → e i * e j = 0) :
    Module.finrank (ZMod 2) M =
      ∑ i, Module.finrank (ZMod 2) (LinearMap.range (e i)) := by
  classical
  let Φ : M →ₗ[ZMod 2] (∀ i, LinearMap.range (e i)) :=
    { toFun := fun m i => ⟨e i m, m, rfl⟩
      map_add' := fun m n => by ext i; simp
      map_smul' := fun c m => by ext i; simp }
  let Ψ : (∀ i, LinearMap.range (e i)) →ₗ[ZMod 2] M :=
    { toFun := fun f => ∑ i, (f i : M)
      map_add' := fun f g => by simp [Finset.sum_add_distrib]
      map_smul' := fun c f => by simp [Finset.smul_sum] }
  have hΨΦ : ∀ m, Ψ (Φ m) = m := by
    intro m
    show (∑ i, e i m) = m
    rw [← LinearMap.sum_apply, hsum, Module.End.one_apply]
  have hΦΨ : ∀ f, Φ (Ψ f) = f := by
    intro f
    ext i
    show e i (∑ j, (f j : M)) = (f i : M)
    rw [map_sum, Finset.sum_eq_single i]
    · obtain ⟨x, hx⟩ := (f i).2
      rw [← hx, ← Module.End.mul_apply, hidem i]
    · intro j _ hji
      obtain ⟨x, hx⟩ := (f j).2
      rw [← hx, ← Module.End.mul_apply, horth i j (Ne.symm hji), LinearMap.zero_apply]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hbij : Function.Bijective Φ :=
    ⟨fun m n h => by rw [← hΨΦ m, ← hΨΦ n, h], fun f => ⟨Ψ f, hΦΨ f⟩⟩
  calc Module.finrank (ZMod 2) M
      = Module.finrank (ZMod 2) (∀ i, LinearMap.range (e i)) :=
        (LinearEquiv.ofBijective Φ hbij).finrank_eq
    _ = ∑ i, Module.finrank (ZMod 2) (LinearMap.range (e i)) :=
        Module.finrank_pi_fintype (ZMod 2)

theorem exists_eq_sum_of_commute {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {σ τ : Module.End (ZMod 2) M} (hστ : Commute σ τ) (hσ : σ ^ p = 1) (hτ : τ ^ p = 1)
    (hfix : ∀ a : M, σ a = a → τ a = a → a = 0) (a : M) :
    ∃ (f : ZMod p → M) (c : M), (∀ b : ZMod p, (σ * τ ^ b.val) (f b) = f b) ∧ τ c = c ∧
      a = ∑ b, f b + c := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hpsmul : p • a = a := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2) p a,
      natCast_zmod_two_of_odd ((Fact.out : p.Prime).odd_of_ne_two hp), one_smul]
  have hphip : ∀ b : ZMod p, (σ * τ ^ b.val) ^ p = 1 := by
    intro b
    rw [(hστ.pow_right b.val).mul_pow p, hσ, one_mul, ← pow_mul τ b.val p, mul_comm b.val p,
      pow_mul τ p b.val, hτ, one_pow]
  have hf : ∀ b : ZMod p, (σ * τ ^ b.val)
      ((∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j) a) =
      (∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j) a := by
    intro b
    rw [← Module.End.mul_apply, mul_geom_sum_eq_geom_sum hp0 (hphip b)]
  have hc : τ ((∑ j ∈ Finset.range p, τ ^ j) a) = (∑ j ∈ Finset.range p, τ ^ j) a := by
    rw [← Module.End.mul_apply, mul_geom_sum_eq_geom_sum hp0 hτ]
  have hw0 : (∑ i ∈ Finset.range p, σ ^ i) ((∑ j ∈ Finset.range p, τ ^ j) a) = 0 := by
    apply hfix
    · rw [← Module.End.mul_apply, mul_geom_sum_eq_geom_sum hp0 hσ]
    · have hcomm : Commute τ (∑ i ∈ Finset.range p, σ ^ i) :=
        Commute.sum_right _ _ _ fun i _ => hστ.symm.pow_right i
      calc τ ((∑ i ∈ Finset.range p, σ ^ i) ((∑ j ∈ Finset.range p, τ ^ j) a))
          = (τ * (∑ i ∈ Finset.range p, σ ^ i)) ((∑ j ∈ Finset.range p, τ ^ j) a) :=
            (Module.End.mul_apply _ _ _).symm
        _ = ((∑ i ∈ Finset.range p, σ ^ i) * τ) ((∑ j ∈ Finset.range p, τ ^ j) a) := by
            rw [hcomm.eq]
        _ = (∑ i ∈ Finset.range p, σ ^ i) (τ ((∑ j ∈ Finset.range p, τ ^ j) a)) :=
            Module.End.mul_apply _ _ _
        _ = (∑ i ∈ Finset.range p, σ ^ i)
              ((τ * (∑ j ∈ Finset.range p, τ ^ j)) a) := by
            rw [Module.End.mul_apply]
        _ = (∑ i ∈ Finset.range p, σ ^ i) ((∑ j ∈ Finset.range p, τ ^ j) a) := by
            rw [mul_geom_sum_eq_geom_sum hp0 hτ]
  let f : ZMod p → M := fun b => (∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j) a
  let c : M := (∑ j ∈ Finset.range p, τ ^ j) a
  have hf' : ∀ b : ZMod p, (σ * τ ^ b.val) (f b) = f b := by
    intro b
    change (σ * τ ^ b.val) ((∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j) a) =
      (∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j) a
    rw [← Module.End.mul_apply, mul_geom_sum_eq_geom_sum hp0 (hphip b)]
  have hc' : τ c = c := by
    change τ ((∑ j ∈ Finset.range p, τ ^ j) a) = (∑ j ∈ Finset.range p, τ ^ j) a
    rw [← Module.End.mul_apply, mul_geom_sum_eq_geom_sum hp0 hτ]
  have happ : (∑ b : ZMod p, f b) + c = a := by
    have h1 := congr_arg (fun e : Module.End (ZMod 2) M => e a)
      (sum_geom_sum_mul_pow_add_geom_sum (σ := σ) (τ := τ) hστ hτ)
    have hsa : (∑ b : ZMod p, (∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j)) a =
        ∑ b : ZMod p, (∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j) a :=
      LinearMap.sum_apply Finset.univ _ a
    rw [LinearMap.add_apply, LinearMap.add_apply, hsa, Module.End.natCast_apply,
      Module.End.mul_apply] at h1
    rw [hpsmul, hw0, add_zero] at h1
    exact h1
  exact ⟨f, c, hf', hc', happ.symm⟩

theorem finrank_eq_mul_finrank_ker [Finite M] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {σ τ γ : Module.End (ZMod 2) M} (hστ : Commute σ τ) (hσ : σ ^ p = 1) (hτ : τ ^ p = 1)
    (hτfix : ∀ a : M, τ a = a → a = 0) (hγ : Function.Injective γ)
    (hγσ : γ * σ = σ * τ * γ) (hγτ : γ * τ = τ * γ) :
    Module.finrank (ZMod 2) M = p * Module.finrank (ZMod 2) (LinearMap.ker (σ - 1)) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  have hpsmul : ∀ a : M, p • a = a := fun a => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2) p a, natCast_zmod_two_of_odd hpodd, one_smul]
  have hpE : (p : Module.End (ZMod 2) M) = 1 := by
    ext a
    rw [Module.End.natCast_apply, Module.End.one_apply]
    exact hpsmul a
  have hphip : ∀ b : ZMod p, (σ * τ ^ b.val) ^ p = 1 := by
    intro b
    rw [(hστ.pow_right b.val).mul_pow p, hσ, one_mul, ← pow_mul τ b.val p, mul_comm b.val p,
      pow_mul τ p b.val, hτ, one_pow]
  let e : ZMod p → Module.End (ZMod 2) M := fun b => ∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j
  have hNτ : (∑ j ∈ Finset.range p, τ ^ j : Module.End (ZMod 2) M) = 0 := by
    ext a
    rw [LinearMap.zero_apply]
    exact hτfix _ (by rw [← Module.End.mul_apply, mul_geom_sum_eq_geom_sum hp0 hτ])
  have hsumN : (∑ b : ZMod p, e b) = 1 := by
    change (∑ b : ZMod p, ∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j) = 1
    have h1 := sum_geom_sum_mul_pow_add_geom_sum (σ := σ) (τ := τ) hστ hτ
    rw [hNτ, mul_zero, add_zero, hpE, add_zero] at h1
    exact h1
  have hNidem : ∀ b : ZMod p, e b * e b = e b := by
    intro b
    change (∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j) *
      (∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j) =
      ∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j
    exact geom_sum_mul_self_eq hp0 (hphip b) hpE
  have hNφ : ∀ b : ZMod p, (∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j) * (σ * τ ^ b.val) =
      ∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j := by
    intro b
    have hcomm : Commute (∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j) (σ * τ ^ b.val) :=
      Commute.sum_left _ _ _ fun j _ => (Commute.refl _).pow_left j
    rw [hcomm.eq, mul_geom_sum_eq_geom_sum hp0 (hphip b)]
  have hNφpow : ∀ (b : ZMod p) (j : ℕ), (∑ i ∈ Finset.range p, (σ * τ ^ b.val) ^ i) *
      (σ * τ ^ b.val) ^ j = ∑ i ∈ Finset.range p, (σ * τ ^ b.val) ^ i := by
    intro b j
    induction j with
    | zero => rw [pow_zero, mul_one]
    | succ j ih => rw [pow_succ, ← mul_assoc, ih, hNφ b]
  have horth : ∀ b b' : ZMod p, b ≠ b' → e b * e b' = 0 := by
    intro b b' hbb'
    change (∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j) *
      (∑ j ∈ Finset.range p, (σ * τ ^ b'.val) ^ j) = 0
    set c : ℕ := (b' - b).val with hcdef
    have hcpos : 0 < c := by
      rw [hcdef]
      exact ZMod.val_pos.mpr (sub_ne_zero.mpr (Ne.symm hbb'))
    have hclt : c < p := by rw [hcdef]; exact ZMod.val_lt _
    have hval : τ ^ b'.val = τ ^ (b.val + c) := by
      have hb' : b' = b + (c : ZMod p) := by
        rw [hcdef, ZMod.natCast_zmod_val]; abel
      rw [hb', ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt hclt]
      exact (pow_eq_pow_mod (b.val + c) hτ).symm
    have hphi : σ * τ ^ b'.val = (σ * τ ^ b.val) * τ ^ c := by
      rw [hval, pow_add, mul_assoc]
    have hNpow : ∀ j : ℕ, (σ * τ ^ b'.val) ^ j = (σ * τ ^ b.val) ^ j * τ ^ (c * j) := by
      intro j
      rw [hphi]
      have hcomm : Commute (σ * τ ^ b.val) (τ ^ c) :=
        (hστ.pow_right c).mul_left ((Commute.refl τ).pow_pow b.val c)
      rw [hcomm.mul_pow j, pow_mul]
    calc (∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j) *
            (∑ j ∈ Finset.range p, (σ * τ ^ b'.val) ^ j)
        = ∑ j ∈ Finset.range p, (∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j) *
            (σ * τ ^ b'.val) ^ j := by rw [Finset.mul_sum]
      _ = ∑ j ∈ Finset.range p, (∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j) *
            ((σ * τ ^ b.val) ^ j * τ ^ (c * j)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hNpow j]
      _ = ∑ j ∈ Finset.range p, ((∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j) *
            (σ * τ ^ b.val) ^ j) * τ ^ (c * j) := by
          refine Finset.sum_congr rfl fun j _ => by rw [mul_assoc]
      _ = ∑ j ∈ Finset.range p, (∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j) *
            τ ^ (c * j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hNφpow b j]
      _ = (∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j) *
            ∑ j ∈ Finset.range p, τ ^ (c * j) := by rw [Finset.mul_sum]
      _ = (∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j) *
            (∑ j ∈ Finset.range p, τ ^ j) := by rw [sum_range_pow_mul_eq hτ hcpos hclt]
      _ = 0 := by rw [hNτ, mul_zero]
  have hrange : ∀ b : ZMod p, LinearMap.range (∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j) =
      LinearMap.ker (σ * τ ^ b.val - 1) := by
    intro b
    ext a
    constructor
    · intro ha
      obtain ⟨x, rfl⟩ := ha
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.End.one_apply,
        ← Module.End.mul_apply, mul_geom_sum_eq_geom_sum hp0 (hphip b)]
    · intro ha
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.End.one_apply] at ha
      have hfixpow : ∀ j : ℕ, ((σ * τ ^ b.val) ^ j) a = a := by
        intro j
        induction j with
        | zero => rw [pow_zero, Module.End.one_apply]
        | succ j ih => rw [pow_succ', Module.End.mul_apply, ih, ha]
      refine ⟨a, ?_⟩
      calc (∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j) a
          = ∑ j ∈ Finset.range p, ((σ * τ ^ b.val) ^ j) a := LinearMap.sum_apply _ _ _
        _ = ∑ j ∈ Finset.range p, a := by
              refine Finset.sum_congr rfl fun j _ => hfixpow j
        _ = p • a := by rw [Finset.sum_const, Finset.card_range]
        _ = a := hpsmul a
  have hγpow : ∀ b : ZMod p, γ * (σ * τ ^ b.val) = (σ * τ ^ (b + 1).val) * γ := by
    intro b
    have hval : τ ^ (b + 1).val = τ ^ (b.val + 1) := by
      haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
      have hb1 : (b + 1).val = (b.val + 1) % p := by rw [ZMod.val_add, ZMod.val_one]
      rw [hb1]
      exact (pow_eq_pow_mod (b.val + 1) hτ).symm
    calc γ * (σ * τ ^ b.val)
        = (γ * σ) * τ ^ b.val := (mul_assoc _ _ _).symm
      _ = (σ * τ * γ) * τ ^ b.val := by rw [hγσ]
      _ = σ * τ * (γ * τ ^ b.val) := mul_assoc _ _ _
      _ = σ * τ * (τ ^ b.val * γ) := by rw [Commute.eq (Commute.pow_right hγτ b.val)]
      _ = σ * (τ * τ ^ b.val) * γ := by noncomm_ring
      _ = σ * τ ^ (b.val + 1) * γ := by rw [← pow_succ']
      _ = (σ * τ ^ (b + 1).val) * γ := by rw [hval]
  let f : ZMod p → ℕ := fun b => Module.finrank (ZMod 2) (LinearMap.ker (σ * τ ^ b.val - 1))
  have hstep : ∀ b : ZMod p, f b ≤ f (b + 1) := by
    intro b
    have hmap : ∀ x ∈ LinearMap.ker (σ * τ ^ b.val - 1),
        γ x ∈ LinearMap.ker (σ * τ ^ (b + 1).val - 1) := by
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.End.one_apply] at hx ⊢
      rw [← Module.End.mul_apply, ← hγpow b, Module.End.mul_apply, hx]
    have hinj : Function.Injective (γ.restrict hmap) := by
      intro x y hxy
      exact Subtype.ext (hγ (Subtype.ext_iff.mp hxy))
    exact LinearMap.finrank_le_finrank_of_injective hinj
  have hmono : ∀ n : ℕ, ∀ b : ZMod p, f b ≤ f (b + (n : ZMod p)) := by
    intro n
    induction n with
    | zero => intro b; simp
    | succ n ih =>
        intro b
        calc f b ≤ f (b + (n : ZMod p)) := ih b
          _ ≤ f ((b + (n : ZMod p)) + 1) := hstep (b + (n : ZMod p))
          _ = f (b + ((n + 1 : ℕ) : ZMod p)) := by
              rw [Nat.cast_add, Nat.cast_one, add_assoc]
  have hf_eq : ∀ b : ZMod p, f b = f 0 := by
    intro b
    refine le_antisymm ?_ ?_
    · have h := hmono ((-b).val) b
      rw [ZMod.natCast_zmod_val, add_neg_cancel] at h
      exact h
    · have h := hmono b.val 0
      rw [ZMod.natCast_zmod_val, zero_add] at h
      exact h
  have hf0 : f 0 = Module.finrank (ZMod 2) (LinearMap.ker (σ - 1)) := by
    change Module.finrank (ZMod 2) (LinearMap.ker (σ * τ ^ (0 : ZMod p).val - 1)) =
      Module.finrank (ZMod 2) (LinearMap.ker (σ - 1))
    rw [ZMod.val_zero, pow_zero, mul_one]
  have hfin : ∀ b : ZMod p, Module.finrank (ZMod 2) (LinearMap.range (e b)) =
      Module.finrank (ZMod 2) (LinearMap.ker (σ - 1)) := by
    intro b
    change Module.finrank (ZMod 2) (LinearMap.range
      (∑ j ∈ Finset.range p, (σ * τ ^ b.val) ^ j)) = _
    rw [hrange b, ← hf0]
    exact hf_eq b
  calc Module.finrank (ZMod 2) M
      = ∑ b : ZMod p, Module.finrank (ZMod 2) (LinearMap.range (e b)) :=
        finrank_eq_sum_finrank_range_of_orthogonal hsumN hNidem horth
    _ = ∑ b : ZMod p, Module.finrank (ZMod 2) (LinearMap.ker (σ - 1)) := by
        refine Finset.sum_congr rfl fun b _ => hfin b
    _ = p * Module.finrank (ZMod 2) (LinearMap.ker (σ - 1)) := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, Nat.nsmul_eq_mul]

theorem finrank_eq_add_two_mul_finrank_range [Finite M] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {σ ν : Module.End (ZMod 2) M} (hσ : σ ^ p = 1) (hν : ν * ν = 1)
    (hνσ : ν * σ = σ ^ (p - 1) * ν) (hfix : ∀ a : M, σ a = a → ν a = a) :
    Module.finrank (ZMod 2) M = Module.finrank (ZMod 2) (LinearMap.ker (σ - 1)) +
      2 * Module.finrank (ZMod 2) (LinearMap.range (ν - 1)) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  have hpsmul : ∀ a : M, p • a = a := fun a => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2) p a, natCast_zmod_two_of_odd hpodd, one_smul]
  have h2zmod : ((2 : ℕ) : ZMod 2) = 0 := ZMod.natCast_self 2
  have hxx : ∀ x : M, x + x = 0 := fun x => by
    rw [← two_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 2) 2 x, h2zmod, zero_smul]
  have hneg : ∀ x : M, -x = x := fun x => neg_eq_iff_add_eq_zero.mpr (hxx x)
  have h2E : (2 : Module.End (ZMod 2) M) = 0 := by
    ext x
    show ((2 : ℕ) : Module.End (ZMod 2) M) x = (0 : Module.End (ZMod 2) M) x
    rw [Module.End.natCast_apply, LinearMap.zero_apply]
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2) 2 x, h2zmod, zero_smul]
  have hNσ : σ * (∑ j ∈ Finset.range p, σ ^ j : Module.End (ZMod 2) M) =
      ∑ j ∈ Finset.range p, σ ^ j := mul_geom_sum_eq_geom_sum hp0 hσ
  have hNa : ∀ a : M, σ a = a → (∑ j ∈ Finset.range p, σ ^ j) a = a := by
    intro a ha
    have hfixpow : ∀ j : ℕ, (σ ^ j) a = a := by
      intro j
      induction j with
      | zero => rw [pow_zero, Module.End.one_apply]
      | succ j ih => rw [pow_succ', Module.End.mul_apply, ih, ha]
    calc (∑ j ∈ Finset.range p, σ ^ j) a
        = ∑ j ∈ Finset.range p, (σ ^ j) a := LinearMap.sum_apply _ _ _
      _ = ∑ j ∈ Finset.range p, a := by refine Finset.sum_congr rfl fun j _ => hfixpow j
      _ = p • a := by rw [Finset.sum_const, Finset.card_range]
      _ = a := hpsmul a
  have hNaC : ∀ a : M, (∑ j ∈ Finset.range p, σ ^ j) a ∈ LinearMap.ker (σ - 1) := by
    intro a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.End.one_apply,
      ← Module.End.mul_apply, hNσ]
  have hνσpow : ∀ j : ℕ, ν * σ ^ j = σ ^ ((p - 1) * j) * ν := by
    intro j
    induction j with
    | zero => rw [Nat.mul_zero, pow_zero, mul_one, one_mul]
    | succ j ih =>
        rw [pow_succ, ← mul_assoc, ih, mul_assoc, hνσ, ← mul_assoc, ← pow_add, Nat.mul_succ]
  have hνN : ν * (∑ j ∈ Finset.range p, σ ^ j) = (∑ j ∈ Finset.range p, σ ^ j) * ν := by
    calc ν * (∑ j ∈ Finset.range p, σ ^ j)
        = ∑ j ∈ Finset.range p, ν * σ ^ j := by rw [Finset.mul_sum]
      _ = ∑ j ∈ Finset.range p, σ ^ ((p - 1) * j) * ν := by
          refine Finset.sum_congr rfl fun j _ => hνσpow j
      _ = (∑ j ∈ Finset.range p, σ ^ ((p - 1) * j)) * ν := by rw [Finset.sum_mul]
      _ = (∑ j ∈ Finset.range p, σ ^ j) * ν := by
          rw [sum_range_pow_mul_eq hσ (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
            (Nat.sub_one_lt (Fact.out : p.Prime).ne_zero)]
  have hΨΨ : (ν - 1) * (ν - 1) = 0 := by
    have h2ν : ν + ν = 0 := by rw [← two_mul, h2E, zero_mul]
    have h11 : (1 : Module.End (ZMod 2) M) + 1 = 0 := by rw [← two_mul, mul_one]; exact h2E
    have hexp : (ν - 1) * (ν - 1) = ν * ν - (ν + ν) + 1 := by noncomm_ring
    rw [hexp, hν, h2ν, sub_zero, h11]
  have hU_le_K : LinearMap.range (ν - 1) ≤ LinearMap.ker (ν - 1) := by
    rintro y ⟨a, rfl⟩
    rw [LinearMap.mem_ker, ← Module.End.mul_apply, hΨΨ, LinearMap.zero_apply]
  have hC_le_K : LinearMap.ker (σ - 1) ≤ LinearMap.ker (ν - 1) := by
    intro a ha
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.End.one_apply] at ha
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.End.one_apply]
    exact hfix a ha
  have hNΨ : (∑ j ∈ Finset.range p, σ ^ j) * (ν - 1) =
      (ν - 1) * (∑ j ∈ Finset.range p, σ ^ j) := by
    rw [mul_sub, sub_mul, mul_one, one_mul, hνN]
  have hC_inf_U : LinearMap.ker (σ - 1) ⊓ LinearMap.range (ν - 1) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro c ⟨hcC, hcU⟩
    obtain ⟨a, rfl⟩ := hcU
    have hcC' : σ ((ν - 1) a) = (ν - 1) a := by
      have h := LinearMap.mem_ker.mp hcC
      rwa [LinearMap.sub_apply, sub_eq_zero, Module.End.one_apply] at h
    have h1 : (ν - 1) a = (∑ j ∈ Finset.range p, σ ^ j) ((ν - 1) a) :=
      (hNa ((ν - 1) a) hcC').symm
    rw [h1, ← Module.End.mul_apply, hNΨ, Module.End.mul_apply]
    exact LinearMap.mem_ker.mp (hC_le_K (hNaC a))
  have hK_le : LinearMap.ker (ν - 1) ≤ LinearMap.ker (σ - 1) ⊔ LinearMap.range (ν - 1) := by
    intro a ha
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.End.one_apply] at ha
    obtain ⟨m, hm⟩ := hpodd
    set c : M := (∑ j ∈ Finset.range p, σ ^ j) a with hcdef
    have hcCmem : c ∈ LinearMap.ker (σ - 1) := hcdef.symm ▸ hNaC a
    have hcC : σ c = c := by
      have h := LinearMap.mem_ker.mp hcCmem
      rwa [LinearMap.sub_apply, sub_eq_zero, Module.End.one_apply] at h
    have hNc : (∑ j ∈ Finset.range p, σ ^ j) c = c := hNa c hcC
    have hcc0 : c + c = 0 := hxx c
    set w : M := a + c with hwdef
    have hνw : ν w = w := by rw [hwdef, map_add, ha, hfix c hcC]
    have hNw : (∑ j ∈ Finset.range p, σ ^ j) w = 0 := by
      rw [hwdef, map_add, hNc, ← hcdef, hcc0]
    let u : M := ∑ j ∈ Finset.range m, (σ ^ (j + 1)) w
    have hmp : m < p := by
      rw [hm, two_mul]
      exact Nat.lt_succ_of_le (Nat.le_add_right m m)
    have hstep : ∀ j ∈ Finset.range m,
        (ν - 1) ((σ ^ (j + 1)) w) = (σ ^ (p - 1 - j)) w + (σ ^ (j + 1)) w := by
      intro j hj
      have hjlt : j < m := Finset.mem_range.mp hj
      have hjp : j + 1 ≤ p := Nat.succ_le_of_lt (Nat.lt_trans hjlt hmp)
      rw [LinearMap.sub_apply, Module.End.one_apply, ← Module.End.mul_apply, hνσpow (j + 1),
        Module.End.mul_apply, hνw, pow_pred_mul_eq hp0 hσ hjp]
      rw [add_comm j 1, Nat.sub_sub, sub_eq_add_neg, hneg]
    have hB : ∑ j ∈ Finset.range m, (σ ^ (p - 1 - j)) w =
        ∑ j ∈ Finset.range m, (σ ^ (m + 1 + j)) w := by
      rw [show p - 1 = 2 * m from by rw [hm, Nat.add_sub_cancel]]
      rw [← Finset.sum_range_reflect (fun i => (σ ^ (2 * m - i)) w) m]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjlt : j < m := Finset.mem_range.mp hj
      rw [show 2 * m - (m - 1 - j) = m + 1 + j from by omega]
    have hAB : (∑ j ∈ Finset.range m, (σ ^ (m + 1 + j)) w) +
        (∑ j ∈ Finset.range m, (σ ^ (j + 1)) w) =
        ∑ i ∈ Finset.range (p - 1), (σ ^ (i + 1)) w := by
      have hS : ∑ i ∈ Finset.range (p - 1), (σ ^ (i + 1)) w =
          (∑ j ∈ Finset.range m, (σ ^ (j + 1)) w) +
          (∑ j ∈ Finset.range m, (σ ^ (m + 1 + j)) w) := by
        rw [show p - 1 = m + m from by rw [hm]; omega]
        rw [Finset.sum_range_add]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show (m + j) + 1 = m + 1 + j from by omega]
      rw [hS, add_comm]
    have hSw : ∑ i ∈ Finset.range (p - 1), (σ ^ (i + 1)) w = w := by
      have hNwS : (∑ j ∈ Finset.range p, σ ^ j) w =
          (∑ i ∈ Finset.range (p - 1), (σ ^ (i + 1)) w) + w := by
        have h := Finset.sum_range_succ' (fun i => (σ ^ i) w) (p - 1)
        rw [show p - 1 + 1 = p from Nat.succ_pred_eq_of_pos hp0, pow_zero,
          Module.End.one_apply] at h
        rw [← h, LinearMap.sum_apply]
      have hzero : (∑ i ∈ Finset.range (p - 1), (σ ^ (i + 1)) w) + w = 0 := by
        rw [← hNwS]
        exact hNw
      calc ∑ i ∈ Finset.range (p - 1), (σ ^ (i + 1)) w
          = (∑ i ∈ Finset.range (p - 1), (σ ^ (i + 1)) w) + 0 := (add_zero _).symm
        _ = (∑ i ∈ Finset.range (p - 1), (σ ^ (i + 1)) w) + (w + w) := by rw [hxx w]
        _ = ((∑ i ∈ Finset.range (p - 1), (σ ^ (i + 1)) w) + w) + w :=
            (add_assoc _ _ _).symm
        _ = 0 + w := by rw [hzero]
        _ = w := zero_add w
    have hΨu : (ν - 1) u = w := by
      have hsum : (ν - 1) u = ∑ j ∈ Finset.range m,
          ((σ ^ (p - 1 - j)) w + (σ ^ (j + 1)) w) := by
        change (ν - 1) (∑ j ∈ Finset.range m, (σ ^ (j + 1)) w) = _
        rw [map_sum]
        exact Finset.sum_congr rfl fun j hj => hstep j hj
      rw [hsum, Finset.sum_add_distrib, hB, hAB]
      exact hSw
    have hwU : w ∈ LinearMap.range (ν - 1) := ⟨u, hΨu⟩
    have haw : a = c + w := by
      rw [hwdef, add_comm c (a + c), add_assoc, hcc0, add_zero]
    rw [haw]
    exact Submodule.mem_sup.mpr ⟨c, hcCmem, w, hwU, rfl⟩
  have hKU : LinearMap.ker (ν - 1) = LinearMap.ker (σ - 1) ⊔ LinearMap.range (ν - 1) :=
    le_antisymm hK_le (sup_le hC_le_K hU_le_K)
  have hfinK : Module.finrank (ZMod 2) (LinearMap.ker (ν - 1)) =
      Module.finrank (ZMod 2) (LinearMap.ker (σ - 1)) +
      Module.finrank (ZMod 2) (LinearMap.range (ν - 1)) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.ker (σ - 1)) (LinearMap.range (ν - 1))
    rw [hC_inf_U, finrank_bot, add_zero] at h
    rw [hKU]
    exact h
  have hrn := LinearMap.finrank_range_add_finrank_ker (ν - 1)
  rw [← hrn, hfinK]
  ring

theorem exists_finrank_eq_of_inverting_involution [Finite M] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {σ τ γ ν : Module.End (ZMod 2) M} (hστ : Commute σ τ) (hσ : σ ^ p = 1) (hτ : τ ^ p = 1)
    (hτfix : ∀ a : M, τ a = a → a = 0) (hγ : Function.Injective γ)
    (hγσ : γ * σ = σ * τ * γ) (hγτ : γ * τ = τ * γ) (hν : ν * ν = 1)
    (hνσ : ν * σ = σ ^ (p - 1) * ν) (hfix : ∀ a : M, σ a = a → ν a = a) :
    ∃ k : ℕ, Module.finrank (ZMod 2) M = p * k ∧
      Module.finrank (ZMod 2) (LinearMap.ker (ν - 1)) = (p + 1) * k / 2 ∧
      Module.finrank (ZMod 2) (LinearMap.range (ν - 1)) = (p - 1) * k / 2 := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  obtain ⟨m, hm⟩ := hpodd
  let k : ℕ := Module.finrank (ZMod 2) (LinearMap.ker (σ - 1))
  let u : ℕ := Module.finrank (ZMod 2) (LinearMap.range (ν - 1))
  let Kν : ℕ := Module.finrank (ZMod 2) (LinearMap.ker (ν - 1))
  have h4 : Module.finrank (ZMod 2) M = p * k :=
    finrank_eq_mul_finrank_ker hp hστ hσ hτ hτfix hγ hγσ hγτ
  have h5 : Module.finrank (ZMod 2) M = k + 2 * u :=
    finrank_eq_add_two_mul_finrank_range hp hσ hν hνσ hfix
  have hEq : p * k = k + 2 * u := by rw [← h4, h5]
  have hu : u = m * k := by
    have h2 : 2 * (m * k) = 2 * u := by
      have h := hEq
      rw [hm, add_mul, one_mul, mul_assoc] at h
      rw [add_comm k (2 * u), Nat.add_right_cancel_iff] at h
      exact h
    exact (Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) h2).symm
  have hrn : u + Kν = Module.finrank (ZMod 2) M :=
    LinearMap.finrank_range_add_finrank_ker (ν - 1)
  have hKm : Kν = m * k + k := by
    have h := hrn
    rw [h4, hu, hm] at h
    rw [add_mul, one_mul, mul_assoc] at h
    rw [show 2 * (m * k) = m * k + m * k from by ring, add_assoc] at h
    rw [Nat.add_left_cancel_iff] at h
    exact h
  have hKν : Kν = (m + 1) * k := by rw [hKm, add_mul, one_mul]
  refine ⟨k, h4, ?_, ?_⟩
  · show Kν = (p + 1) * k / 2
    rw [hKν, hm]
    rw [show (2 * m + 1 + 1) * k / 2 = (m + 1) * k from by
      rw [show 2 * m + 1 + 1 = 2 * (m + 1) from by omega, mul_assoc,
        Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]]
  · show u = (p - 1) * k / 2
    rw [hu, hm]
    rw [show (2 * m + 1 - 1) * k / 2 = m * k from by
      rw [show 2 * m + 1 - 1 = 2 * m from by omega, mul_assoc,
        Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]]

end FTwo

end CFSG.LocalAnalysis.WeakClosure81
