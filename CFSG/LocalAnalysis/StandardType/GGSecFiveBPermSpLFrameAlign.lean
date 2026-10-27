module

public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.ZMod.Basic
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestPerm
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.StandardType

namespace LFrameAlign

private def lfa_approx {p n : ℕ} (x y : Fin n → ZMod p) : Prop := ∃ s, ∀ k, x k = y k + s

private theorem lfa_approx_refl {p n : ℕ} (x : Fin n → ZMod p) : lfa_approx x x :=
  ⟨0, fun k => by simp⟩

private theorem lfa_approx_symm {p n : ℕ} {x y : Fin n → ZMod p}
    (h : lfa_approx x y) : lfa_approx y x := by
  obtain ⟨s, hs⟩ := h
  refine ⟨-s, fun k => ?_⟩
  rw [hs k]
  ring

private theorem lfa_approx_trans {p n : ℕ} {x y z : Fin n → ZMod p}
    (h1 : lfa_approx x y) (h2 : lfa_approx y z) : lfa_approx x z := by
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  refine ⟨s + t, fun k => ?_⟩
  rw [hs k, ht k]
  ring

private theorem lfa_approx_add {p n : ℕ} {x y x' y' : Fin n → ZMod p}
    (h1 : lfa_approx x y) (h2 : lfa_approx x' y') :
    lfa_approx (x + x') (y + y') := by
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  refine ⟨s + t, fun k => ?_⟩
  simp only [Pi.add_apply, hs k, ht k]
  ring

private theorem lfa_approx_sub {p n : ℕ} {x y x' y' : Fin n → ZMod p}
    (h1 : lfa_approx x y) (h2 : lfa_approx x' y') :
    lfa_approx (x - x') (y - y') := by
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  refine ⟨s - t, fun k => ?_⟩
  simp only [Pi.sub_apply, hs k, ht k]
  ring

private theorem lfa_approx_smul {p n : ℕ} (c : ZMod p) {x y : Fin n → ZMod p}
    (h : lfa_approx x y) : lfa_approx (c • x) (c • y) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨c * s, fun k => ?_⟩
  simp only [Pi.smul_apply, hs k]
  ring

private theorem lfa_approx_comp {p n : ℕ} {x y : Fin n → ZMod p}
    (h : lfa_approx x y) (σ : Fin n → Fin n) : lfa_approx (x ∘ σ) (y ∘ σ) := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, fun k => hs (σ k)⟩

private theorem lfa_approx_of_sub {p n : ℕ} {x y : Fin n → ZMod p}
    (h : lfa_approx (x - y) 0) : lfa_approx x y := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s, fun k => ?_⟩
  have hk := hs k
  simp only [Pi.sub_apply, Pi.zero_apply, zero_add] at hk
  rw [← hk]
  ring

private theorem lfa_approx_sum {p n : ℕ} {ι : Type*} (s : Finset ι)
    {x y : ι → Fin n → ZMod p} (h : ∀ i ∈ s, lfa_approx (x i) (y i)) :
    lfa_approx (∑ i ∈ s, x i) (∑ i ∈ s, y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lfa_approx_refl (0 : Fin n → ZMod p)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact lfa_approx_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem lfa_exists_ne_ne {n : ℕ} (hn : 3 ≤ n) (a b : Fin n) :
    ∃ k : Fin n, k ≠ a ∧ k ≠ b := by
  have hcard : ({a, b} : Finset (Fin n)).card ≤ 2 := by
    simpa using Finset.card_insert_le a ({b} : Finset (Fin n))
  have hpos : 0 < ({a, b} : Finset (Fin n))ᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_compl] at hk
  exact ⟨k, fun h => hk (by simp [h]), fun h => hk (by simp [h])⟩

private def lfa_e {p n : ℕ} (i : Fin n) : Fin n → ZMod p := Pi.single i 1

private theorem lfa_e_self {p n : ℕ} (i : Fin n) : lfa_e (p := p) i i = 1 := by
  simp [lfa_e]

private theorem lfa_e_ne {p n : ℕ} {i j : Fin n} (h : j ≠ i) :
    lfa_e (p := p) i j = 0 := by
  have h' := Pi.single_eq_of_ne (M := fun _ : Fin n => ZMod p) h (1 : ZMod p)
  simpa [lfa_e] using h'

private theorem lfa_e_comp_symm {p n : ℕ} (a : Fin n) (τ : Equiv.Perm (Fin n)) :
    lfa_e (p := p) a ∘ τ.symm = lfa_e (p := p) (τ a) := by
  ext k
  simp [lfa_e, Pi.single_apply, Equiv.symm_apply_eq]

private theorem lfa_e_approx_e {p n : ℕ} [Fact p.Prime] (hn : 3 ≤ n) {a b : Fin n}
    (h : lfa_approx (lfa_e (p := p) a) (lfa_e (p := p) b)) : a = b := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨k, hka, hkb⟩ := lfa_exists_ne_ne hn a b
  have hs0 : s = 0 := by
    have hk := hs k
    rw [lfa_e_ne hka, lfa_e_ne hkb, zero_add] at hk
    exact hk.symm
  have ha := hs a
  rw [hs0, add_zero, lfa_e_self] at ha
  by_cases hab : a = b
  · exact hab
  · exfalso
    rw [lfa_e_ne hab] at ha
    exact one_ne_zero ha

private theorem lfa_not_approx_e_zero {p n : ℕ} [Fact p.Prime] (hn : 3 ≤ n) (a : Fin n) :
    ¬ lfa_approx (lfa_e (p := p) a) 0 := by
  rintro ⟨s, hs⟩
  obtain ⟨k, hka, -⟩ := lfa_exists_ne_ne hn a a
  have h1 : (1 : ZMod p) = s := by
    have ha := hs a
    rw [lfa_e_self, Pi.zero_apply, zero_add] at ha
    exact ha
  have h0 : (0 : ZMod p) = s := by
    have hk := hs k
    rw [lfa_e_ne hka, Pi.zero_apply, zero_add] at hk
    exact hk
  rw [← h0] at h1
  exact one_ne_zero h1

private theorem lfa_not_approx_sub_e_zero {p n : ℕ} [Fact p.Prime] (hn : 3 ≤ n)
    {a b : Fin n} (hab : a ≠ b) :
    ¬ lfa_approx (lfa_e (p := p) b - lfa_e (p := p) a) 0 := by
  rintro ⟨s, hs⟩
  obtain ⟨k, hka, hkb⟩ := lfa_exists_ne_ne hn a b
  have hk0 : s = 0 := by
    have hk := hs k
    rw [Pi.sub_apply, lfa_e_ne hkb, lfa_e_ne hka, sub_zero, Pi.zero_apply,
      zero_add] at hk
    exact hk.symm
  have hb := hs b
  rw [Pi.sub_apply, lfa_e_self, lfa_e_ne (Ne.symm hab), sub_zero, Pi.zero_apply, hk0,
    zero_add] at hb
  exact one_ne_zero hb

private theorem lfa_map_zsmul {p n : ℕ} [Fact p.Prime]
    (M : (Fin n → ZMod p) →+ (Fin n → ZMod p)) (c : ZMod p) (x : Fin n → ZMod p) :
    M (c • x) = c • M x := by
  have hc : (c.val : ZMod p) = c := ZMod.natCast_zmod_val c
  calc M (c • x) = M ((c.val : ZMod p) • x) := by rw [hc]
    _ = M ((c.val : ℕ) • x) := by rw [Nat.cast_smul_eq_nsmul (ZMod p) c.val x]
    _ = (c.val : ℕ) • M x := map_nsmul M c.val x
    _ = (c.val : ZMod p) • M x := by rw [Nat.cast_smul_eq_nsmul (ZMod p) c.val (M x)]
    _ = c • M x := by rw [hc]

private theorem lfa_two_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have hp : p.Prime := Fact.out
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 p).mp h)
  have hge : 2 ≤ p := hp.two_le
  exact hp2 (by omega)

private theorem lfa_smul_e {p n : ℕ} (c : ZMod p) (i : Fin n) :
    c • lfa_e (p := p) i = Pi.single i c := by
  rw [lfa_e, ← Pi.single_smul]
  simp

private theorem lfa_sum_smul_single {p n : ℕ} (u : Fin n → ZMod p) :
    (∑ i, u i • lfa_e (p := p) i) = u := by
  calc ∑ i, u i • lfa_e (p := p) i = ∑ i, Pi.single i (u i) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [lfa_smul_e]
    _ = u := Finset.univ_sum_single u

private theorem lfa_swap_sub {p n : ℕ} (y : Fin n → ZMod p) {i j : Fin n} (hij : i ≠ j) :
    y ∘ Equiv.swap i j - y
      = (y j - y i) • (lfa_e (p := p) i - lfa_e (p := p) j) := by
  ext k
  by_cases hik : k = i
  · rw [hik]
    simp [lfa_e, Function.comp_apply, Equiv.swap_apply_left, Pi.sub_apply, Pi.smul_apply,
      Pi.single_eq_same, Pi.single_eq_of_ne hij, smul_eq_mul]
  · by_cases hjk : k = j
    · rw [hjk]
      simp [lfa_e, Function.comp_apply, Equiv.swap_apply_right, Pi.sub_apply, Pi.smul_apply,
        Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij), smul_eq_mul]
    · simp [lfa_e, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hik hjk, Pi.sub_apply,
        Pi.smul_apply, Pi.single_eq_of_ne hik, Pi.single_eq_of_ne hjk, smul_eq_mul]

private theorem lfa_swap_approx_const {p n : ℕ} [Fact p.Prime]
    (y : Fin n → ZMod p) {j k o : Fin n} (hjk : j ≠ k) (hjo : j ≠ o) (hko : k ≠ o)
    (h : lfa_approx y (y ∘ Equiv.swap j k)) : y j = y k := by
  obtain ⟨s, hs⟩ := h
  have hsub : lfa_approx (y ∘ Equiv.swap j k - y) 0 := by
    refine ⟨-s, fun l => ?_⟩
    have hl := hs l
    simp only [Function.comp_apply, Pi.sub_apply, Pi.zero_apply]
    rw [hl]
    simp only [Function.comp_apply]
    ring
  rw [lfa_swap_sub y hjk] at hsub
  obtain ⟨t, ht⟩ := hsub
  have ht0 : t = 0 := by
    have ho := ht o
    rw [Pi.smul_apply, Pi.sub_apply, lfa_e_ne (Ne.symm hjo), lfa_e_ne (Ne.symm hko),
      sub_zero] at ho
    simpa using ho.symm
  have hj := ht j
  rw [Pi.smul_apply, Pi.sub_apply, lfa_e_self, lfa_e_ne hjk, sub_zero, Pi.zero_apply,
    ht0, zero_add] at hj
  simp only [smul_eq_mul, mul_one] at hj
  exact (sub_eq_zero.mp hj).symm

private theorem lfa_perm_unique {p n : ℕ} [Fact p.Prime] (hn : 3 ≤ n)
    {τ τ' : Equiv.Perm (Fin n)}
    (h : ∀ v : Fin n → ZMod p, lfa_approx (v ∘ τ.symm) (v ∘ τ'.symm)) : τ = τ' := by
  refine Equiv.ext (fun a => ?_)
  have ha := h (lfa_e (p := p) a)
  rw [lfa_e_comp_symm, lfa_e_comp_symm] at ha
  exact lfa_e_approx_e hn ha

private theorem lfa_choose_unique {p n : ℕ} [Fact p.Prime] (hn : 3 ≤ n)
    (M : (Fin n → ZMod p) →+ (Fin n → ZMod p))
    (hinj : ∀ v : Fin n → ZMod p, lfa_approx (M v) 0 → lfa_approx v 0)
    {w : Equiv.Perm (Fin n)} {τ τ' : Equiv.Perm (Fin n)}
    (hτ : ∀ v : Fin n → ZMod p, lfa_approx (M (v ∘ τ.symm)) (M v ∘ w.symm))
    (hτ' : ∀ v : Fin n → ZMod p, lfa_approx (M (v ∘ τ'.symm)) (M v ∘ w.symm)) :
    τ = τ' := by
  refine lfa_perm_unique (p := p) hn (fun v => ?_)
  have h1 : lfa_approx (M (v ∘ τ.symm)) (M (v ∘ τ'.symm)) :=
    lfa_approx_trans (hτ v) (lfa_approx_symm (hτ' v))
  have h2 : lfa_approx (M ((v ∘ τ.symm) - (v ∘ τ'.symm))) 0 := by
    rw [map_sub]
    simpa using lfa_approx_sub h1 (lfa_approx_refl (M (v ∘ τ'.symm)))
  exact lfa_approx_of_sub (hinj _ h2)

private theorem lfa_Φ_eq_one {p n : ℕ} [Fact p.Prime] (hn : 3 ≤ n)
    (M : (Fin n → ZMod p) →+ (Fin n → ZMod p))
    (hsurj : ∀ y : Fin n → ZMod p, ∃ v s, ∀ k, y k = M v k + s)
    (Φ : Equiv.Perm (Fin n) →* Equiv.Perm (Fin n))
    (hΦ : ∀ (w : Equiv.Perm (Fin n)) (v : Fin n → ZMod p),
      lfa_approx (M (v ∘ (Φ w).symm)) (M v ∘ w.symm))
    {w : Equiv.Perm (Fin n)} (hw : Φ w = 1) : w = 1 := by
  have hMv : ∀ v : Fin n → ZMod p, lfa_approx (M v) (M v ∘ w.symm) := by
    intro v
    have hv := hΦ w v
    rw [hw] at hv
    exact hv
  have hy : ∀ y : Fin n → ZMod p, lfa_approx y (y ∘ w.symm) := by
    intro y
    obtain ⟨v, s, hs⟩ := hsurj y
    have h1 : lfa_approx y (M v) := ⟨s, hs⟩
    have h2 : lfa_approx (M v) (M v ∘ w.symm) := hMv v
    have h3 : lfa_approx (y ∘ w.symm) (M v ∘ w.symm) :=
      lfa_approx_symm (lfa_approx_comp (lfa_approx_symm h1) w.symm)
    exact lfa_approx_trans (lfa_approx_trans h1 h2) (lfa_approx_symm h3)
  refine lfa_perm_unique (p := p) hn (τ := w) (τ' := 1) (fun y => ?_)
  exact lfa_approx_symm (hy y)

private theorem lfa_Φ_swap {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (M : (Fin n → ZMod p) →+ (Fin n → ZMod p))
    (hinj : ∀ v : Fin n → ZMod p, lfa_approx (M v) 0 → lfa_approx v 0)
    (Φ : Equiv.Perm (Fin n) →* Equiv.Perm (Fin n))
    (hΦ : ∀ (w : Equiv.Perm (Fin n)) (v : Fin n → ZMod p),
      lfa_approx (M (v ∘ (Φ w).symm)) (M v ∘ w.symm))
    (hΦone : ∀ w : Equiv.Perm (Fin n), Φ w = 1 → w = 1)
    {i j : Fin n} (hij : i ≠ j) :
    (Φ (Equiv.swap i j)).IsSwap := by
  classical
  set t : Equiv.Perm (Fin n) := Equiv.swap i j with ht
  set τ : Equiv.Perm (Fin n) := Φ t with hτ
  have htt : t * t = 1 := by
    rw [ht]
    exact Equiv.swap_mul_self i j
  have hττ : τ * τ = 1 := by
    rw [hτ, ← map_mul, htt, map_one]
  have hτne : τ ≠ 1 := by
    intro h1
    have ht1 : t = 1 := hΦone t (by rw [← hτ]; exact h1)
    have hji : j = i := by
      have := congrArg (fun σ : Equiv.Perm (Fin n) => σ i) ht1
      simpa [ht] using this
    exact hij hji.symm
  obtain ⟨a, ha⟩ : ∃ a : Fin n, τ a ≠ a := by
    by_contra h
    push Not at h
    exact hτne (Equiv.ext h)
  set b : Fin n := τ a with hb
  have hba : b ≠ a := ha
  have hτb : τ b = a := by
    have h2 := congrArg (fun σ : Equiv.Perm (Fin n) => σ a) hττ
    have h3 : (τ * τ) a = τ b := by rw [Equiv.Perm.mul_apply, hb]
    rw [h3] at h2
    simpa using h2
  have hfix : ∀ c : Fin n, c ≠ a → c ≠ b → τ c = c := by
    intro c hca hcb
    by_contra hne
    set d : Fin n := τ c with hd
    have hda : d ≠ a := by
      intro h
      apply hcb
      apply Equiv.injective τ
      rw [← hd, h, hτb]
    have hdb : d ≠ b := by
      intro h
      apply hca
      apply Equiv.injective τ
      rw [← hd, h, hb]
    have hdc : d ≠ c := hne
    have hτd : τ d = c := by
      have h2 := congrArg (fun σ : Equiv.Perm (Fin n) => σ c) hττ
      have h3 : (τ * τ) c = τ d := by rw [Equiv.Perm.mul_apply, hd]
      rw [h3] at h2
      simpa using h2
    have hb_approx : lfa_approx (M (lfa_e (p := p) b))
        (M (lfa_e (p := p) a) ∘ t.symm) := by
      have h := hΦ t (lfa_e (p := p) a)
      rw [← hτ] at h
      have he : lfa_e (p := p) a ∘ τ.symm = lfa_e (p := p) b := by
        rw [lfa_e_comp_symm, hb]
      rwa [he] at h
    have hd_approx : lfa_approx (M (lfa_e (p := p) d))
        (M (lfa_e (p := p) c) ∘ t.symm) := by
      have h := hΦ t (lfa_e (p := p) c)
      rw [← hτ] at h
      have he : lfa_e (p := p) c ∘ τ.symm = lfa_e (p := p) d := by
        rw [lfa_e_comp_symm, hd]
      rwa [he] at h
    set lam : ZMod p := M (lfa_e (p := p) a) j - M (lfa_e (p := p) a) i with hlam
    set lam' : ZMod p := M (lfa_e (p := p) c) j - M (lfa_e (p := p) c) i with hlam'
    have hd1 : lfa_approx (M (lfa_e (p := p) b - lfa_e (p := p) a))
        (lam • (lfa_e (p := p) i - lfa_e (p := p) j)) := by
      have h1 : lfa_approx (M (lfa_e (p := p) b) - M (lfa_e (p := p) a))
          (M (lfa_e (p := p) a) ∘ t.symm - M (lfa_e (p := p) a)) :=
        lfa_approx_sub hb_approx (lfa_approx_refl _)
      have h2 : M (lfa_e (p := p) a) ∘ t.symm - M (lfa_e (p := p) a)
          = lam • (lfa_e (p := p) i - lfa_e (p := p) j) := by
        rw [hlam, ht]
        have hs : (Equiv.swap i j).symm = Equiv.swap i j := by
          simp
        rw [hs]
        exact lfa_swap_sub (M (lfa_e (p := p) a)) hij
      rw [map_sub, ← h2]
      exact h1
    have hd2 : lfa_approx (M (lfa_e (p := p) d - lfa_e (p := p) c))
        (lam' • (lfa_e (p := p) i - lfa_e (p := p) j)) := by
      have h1 : lfa_approx (M (lfa_e (p := p) d) - M (lfa_e (p := p) c))
          (M (lfa_e (p := p) c) ∘ t.symm - M (lfa_e (p := p) c)) :=
        lfa_approx_sub hd_approx (lfa_approx_refl _)
      have h2 : M (lfa_e (p := p) c) ∘ t.symm - M (lfa_e (p := p) c)
          = lam' • (lfa_e (p := p) i - lfa_e (p := p) j) := by
        rw [hlam', ht]
        have hs : (Equiv.swap i j).symm = Equiv.swap i j := by
          simp
        rw [hs]
        exact lfa_swap_sub (M (lfa_e (p := p) c)) hij
      rw [map_sub, ← h2]
      exact h1
    have h3 : lfa_approx
        (M (lam' • (lfa_e (p := p) b - lfa_e (p := p) a)
          - lam • (lfa_e (p := p) d - lfa_e (p := p) c))) 0 := by
      have hX : lfa_approx (lam' • M (lfa_e (p := p) b - lfa_e (p := p) a))
          (lam' • (lam • (lfa_e (p := p) i - lfa_e (p := p) j))) :=
        lfa_approx_smul lam' hd1
      have hY : lfa_approx (lam • M (lfa_e (p := p) d - lfa_e (p := p) c))
          (lam • (lam' • (lfa_e (p := p) i - lfa_e (p := p) j))) :=
        lfa_approx_smul lam hd2
      have hsub := lfa_approx_sub hX hY
      have hR : lam' • (lam • (lfa_e (p := p) i - lfa_e (p := p) j))
          - lam • (lam' • (lfa_e (p := p) i - lfa_e (p := p) j)) = 0 := by
        rw [smul_smul, smul_smul, mul_comm lam' lam]
        exact sub_self _
      rw [hR] at hsub
      simpa only [map_sub, lfa_map_zsmul] using hsub
    have h4 : lfa_approx
        (lam' • (lfa_e (p := p) b - lfa_e (p := p) a)
          - lam • (lfa_e (p := p) d - lfa_e (p := p) c)) 0 :=
      hinj _ h3
    obtain ⟨s, hs⟩ := h4
    have hXa : (lfa_e (p := p) b - lfa_e (p := p) a) a = -1 := by
      simp [lfa_e, Pi.single_eq_of_ne (Ne.symm hba)]
    have hYa : (lfa_e (p := p) d - lfa_e (p := p) c) a = 0 := by
      simp [lfa_e, Pi.single_eq_of_ne (Ne.symm hda), Pi.single_eq_of_ne (Ne.symm hca)]
    have hsa : -lam' = s := by
      have h := hs a
      rw [Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, hXa, hYa, Pi.zero_apply,
        zero_add] at h
      simpa using h
    have hXb : (lfa_e (p := p) b - lfa_e (p := p) a) b = 1 := by
      simp [lfa_e, Pi.single_eq_of_ne hba]
    have hYb : (lfa_e (p := p) d - lfa_e (p := p) c) b = 0 := by
      simp [lfa_e, Pi.single_eq_of_ne (Ne.symm hdb), Pi.single_eq_of_ne (Ne.symm hcb)]
    have hsb : lam' = s := by
      have h := hs b
      rw [Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, hXb, hYb, Pi.zero_apply,
        zero_add] at h
      simpa using h
    have hXc : (lfa_e (p := p) b - lfa_e (p := p) a) c = 0 := by
      simp [lfa_e, Pi.single_eq_of_ne hcb, Pi.single_eq_of_ne hca]
    have hYc : (lfa_e (p := p) d - lfa_e (p := p) c) c = -1 := by
      simp [lfa_e, Pi.single_eq_of_ne (Ne.symm hdc)]
    have hsc : lam = s := by
      have h := hs c
      rw [Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, hXc, hYc, Pi.zero_apply,
        zero_add] at h
      simpa using h
    have hlam'0 : lam' = 0 := by
      have h : -lam' = lam' := by rw [hsa, ← hsb]
      have hsum : (2 : ZMod p) * lam' = 0 := by
        rw [two_mul]
        exact neg_eq_iff_add_eq_zero.mp h
      exact (mul_eq_zero.mp hsum).resolve_left (lfa_two_ne_zero hp2)
    have hs0 : s = 0 := by rw [← hsb, hlam'0]
    have hlam0 : lam = 0 := by rw [hsc, hs0]
    have hMzero : lfa_approx (M (lfa_e (p := p) b - lfa_e (p := p) a)) 0 := by
      rw [hlam0] at hd1
      simpa using hd1
    exact lfa_not_approx_sub_e_zero hn (Ne.symm hba) (hinj _ hMzero)
  refine ⟨a, b, Ne.symm hba, ?_⟩
  refine Equiv.ext (fun c => ?_)
  by_cases hca : c = a
  · rw [hca, Equiv.swap_apply_left]
  · by_cases hcb : c = b
    · rw [hcb, Equiv.swap_apply_right]
      exact hτb
    · rw [hfix c hca hcb]
      exact (Equiv.swap_apply_of_ne_of_ne hca hcb).symm

private theorem lfa_comp_mul_symm {p n : ℕ} (v : Fin n → ZMod p)
    (f g : Equiv.Perm (Fin n)) :
    v ∘ (f * g).symm = (v ∘ g.symm) ∘ f.symm := by
  have hs : (f * g).symm = g.symm * f.symm := by
    rw [show (f * g).symm = (f * g)⁻¹ from rfl,
      show g.symm * f.symm = g⁻¹ * f⁻¹ from rfl]
    group
  rw [hs]
  ext k
  simp [Function.comp_apply]

private theorem lfa_N_comm {p n : ℕ} [Fact p.Prime]
    (M : (Fin n → ZMod p) →+ (Fin n → ZMod p))
    (Φ : Equiv.Perm (Fin n) →* Equiv.Perm (Fin n))
    (hΦ : ∀ (w : Equiv.Perm (Fin n)) (v : Fin n → ZMod p),
      lfa_approx (M (v ∘ (Φ w).symm)) (M v ∘ w.symm))
    (f : Equiv.Perm (Fin n)) (hf : ∀ w : Equiv.Perm (Fin n), Φ w = f * w * f.symm)
    (w : Equiv.Perm (Fin n)) (u : Fin n → ZMod p) :
    lfa_approx (M ((u ∘ w.symm) ∘ f.symm)) (M (u ∘ f.symm) ∘ w.symm) := by
  have hspec := hΦ w (u ∘ f.symm)
  have hsymm : (Φ w).symm = f * w.symm * f.symm := by
    have h1 : (Φ w).symm = Φ (w.symm) := by
      rw [show (Φ w).symm = (Φ w)⁻¹ from rfl, ← map_inv]
      rfl
    rw [h1, hf (w.symm)]
  have hfun : (u ∘ w.symm) ∘ f.symm = (u ∘ f.symm) ∘ (Φ w).symm := by
    rw [hsymm]
    ext k
    simp [Function.comp_apply]
  rw [← hfun] at hspec
  exact hspec

private theorem lfa_smul_eq_sum {p n : ℕ} (c : ZMod p) (u : Fin n → ZMod p) :
    c • u = ∑ i, u i • (c • lfa_e (p := p) i) := by
  calc c • u = c • ∑ i, u i • lfa_e (p := p) i := by
        conv_lhs => rw [← lfa_sum_smul_single u]
    _ = ∑ i, c • (u i • lfa_e (p := p) i) := by rw [Finset.smul_sum]
    _ = ∑ i, u i • (c • lfa_e (p := p) i) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [smul_smul, smul_smul, mul_comm]

private theorem lfa_N_scalar {p n : ℕ} [Fact p.Prime] (hn : 3 ≤ n)
    (N : (Fin n → ZMod p) →+ (Fin n → ZMod p))
    (hN : ∀ (w : Equiv.Perm (Fin n)) (u : Fin n → ZMod p),
      lfa_approx (N (u ∘ w.symm)) (N u ∘ w.symm)) :
    ∃ c : ZMod p, ∀ u : Fin n → ZMod p, lfa_approx (N u) (c • u) := by
  classical
  let o : Fin n := ⟨0, by omega⟩
  let o' : Fin n := ⟨1, by omega⟩
  have hoo' : o ≠ o' := by
    intro h
    have := congrArg Fin.val h
    simp [o, o'] at this
  let y : Fin n → ZMod p := N (lfa_e (p := p) o)
  have hconst : ∀ j : Fin n, j ≠ o → y j = y o' := by
    intro j hjo
    by_cases hjo' : j = o'
    · rw [hjo']
    · have hy : lfa_approx y (y ∘ Equiv.swap j o') := by
        have h := hN (Equiv.swap j o') (lfa_e (p := p) o)
        have he : lfa_e (p := p) o ∘ (Equiv.swap j o').symm = lfa_e (p := p) o := by
          rw [lfa_e_comp_symm]
          rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hjo) hoo']
        rw [he] at h
        have hs : (Equiv.swap j o').symm = Equiv.swap j o' := by
          simp
        simpa [hs] using h
      exact lfa_swap_approx_const y hjo' hjo (Ne.symm hoo') hy
  set c : ZMod p := y o - y o' with hc
  have h_e : ∀ i : Fin n, lfa_approx (N (lfa_e (p := p) i)) (c • lfa_e (p := p) i) := by
    intro i
    by_cases hio : i = o
    · subst hio
      refine ⟨y o', fun k => ?_⟩
      by_cases hko : k = o
      · rw [hko]
        show y o = (c • lfa_e (p := p) o) o + y o'
        rw [hc]
        simp only [Pi.smul_apply, lfa_e, Pi.single_eq_same]
        ring
      · show y k = (c • lfa_e (p := p) o) k + y o'
        rw [hconst k hko, hc]
        simp [Pi.smul_apply, lfa_e, hko]
    · have h := hN (Equiv.swap o i) (lfa_e (p := p) o)
      have he : lfa_e (p := p) o ∘ (Equiv.swap o i).symm = lfa_e (p := p) i := by
        rw [lfa_e_comp_symm, Equiv.swap_apply_left]
      rw [he] at h
      have h2 : lfa_approx (y ∘ Equiv.swap o i) (c • lfa_e (p := p) i) := by
        refine ⟨y o', fun k => ?_⟩
        by_cases hko : k = o
        · rw [hko, Function.comp_apply, Equiv.swap_apply_left]
          show y i = (c • lfa_e (p := p) i) o + y o'
          rw [hconst i hio, hc]
          simp [Pi.smul_apply, lfa_e, Pi.single_eq_of_ne (Ne.symm hio)]
        · by_cases hki : k = i
          · rw [hki, Function.comp_apply, Equiv.swap_apply_right]
            show y o = (c • lfa_e (p := p) i) i + y o'
            rw [hc]
            simp only [Pi.smul_apply, lfa_e, Pi.single_eq_same]
            ring
          · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hko hki]
            show y k = (c • lfa_e (p := p) i) k + y o'
            rw [hconst k hko, hc]
            simp [Pi.smul_apply, lfa_e, hki]
      have h3 : lfa_approx (y ∘ (Equiv.swap o i).symm) (c • lfa_e (p := p) i) := by
        have hs : (Equiv.swap o i).symm = Equiv.swap o i := by
          simp
        simpa [hs] using h2
      exact lfa_approx_trans h h3
  refine ⟨c, fun u => ?_⟩
  have hNu : N u = ∑ i, N (u i • lfa_e (p := p) i) := by
    conv_lhs => rw [← lfa_sum_smul_single u]
    exact map_sum N (fun i => u i • lfa_e (p := p) i) Finset.univ
  have hsum : ∑ i, u i • (c • lfa_e (p := p) i) = c • u :=
    (lfa_smul_eq_sum c u).symm
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      lfa_approx (N (u i • lfa_e (p := p) i))
        (u i • (c • lfa_e (p := p) i)) := by
    intro i _
    rw [lfa_map_zsmul]
    exact lfa_approx_smul (u i) (h_e i)
  have hsumapprox : lfa_approx (∑ i, N (u i • lfa_e (p := p) i))
      (∑ i, u i • (c • lfa_e (p := p) i)) :=
    lfa_approx_sum Finset.univ hterm
  rw [hNu, ← hsum]
  exact hsumapprox

theorem exists_perm_smul_of_modConst {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (M : (Fin n → ZMod p) →+ (Fin n → ZMod p))
    (hinj : ∀ v, (∃ s, ∀ k, M v k = s) → ∃ s, ∀ k, v k = s)
    (hsurj : ∀ y : Fin n → ZMod p, ∃ v s, ∀ k, y k = M v k + s)
    (hΦ : ∀ w : Equiv.Perm (Fin n), ∃ τ : Equiv.Perm (Fin n),
      ∀ v, ∃ s, ∀ k, M (v ∘ τ.symm) k = M v (w.symm k) + s) :
    ∃ (f : Equiv.Perm (Fin n)) (c : ZMod p), c ≠ 0 ∧
      ∀ v, ∃ s, ∀ k, M v k = c * v (f k) + s := by
  classical
  have hinj' : ∀ v : Fin n → ZMod p, lfa_approx (M v) 0 → lfa_approx v 0 := by
    intro v h
    obtain ⟨s, hs⟩ := h
    obtain ⟨s', hs'⟩ := hinj v ⟨s, fun k => by simpa using hs k⟩
    exact ⟨s', fun k => by simpa using hs' k⟩
  let Φ₀ : Equiv.Perm (Fin n) → Equiv.Perm (Fin n) := fun w => (hΦ w).choose
  have hΦ₀ : ∀ (w : Equiv.Perm (Fin n)) (v : Fin n → ZMod p),
      lfa_approx (M (v ∘ (Φ₀ w).symm)) (M v ∘ w.symm) := by
    intro w v
    exact (hΦ w).choose_spec v
  have huniq : ∀ (w : Equiv.Perm (Fin n)) (τ τ' : Equiv.Perm (Fin n)),
      (∀ v : Fin n → ZMod p, lfa_approx (M (v ∘ τ.symm)) (M v ∘ w.symm)) →
      (∀ v : Fin n → ZMod p, lfa_approx (M (v ∘ τ'.symm)) (M v ∘ w.symm)) →
      τ = τ' := by
    intro w τ τ' hτ hτ'
    exact lfa_choose_unique hn M hinj' hτ hτ'
  have hΦmul : ∀ w w' : Equiv.Perm (Fin n), Φ₀ (w * w') = Φ₀ w * Φ₀ w' := by
    intro w w'
    refine huniq (w * w') (Φ₀ (w * w')) (Φ₀ w * Φ₀ w') (hΦ₀ (w * w')) ?_
    intro v
    have h1 : lfa_approx (M ((v ∘ (Φ₀ w').symm) ∘ (Φ₀ w).symm))
        (M (v ∘ (Φ₀ w').symm) ∘ w.symm) := hΦ₀ w (v ∘ (Φ₀ w').symm)
    have h2 : lfa_approx (M (v ∘ (Φ₀ w').symm) ∘ w.symm)
        ((M v ∘ w'.symm) ∘ w.symm) := lfa_approx_comp (hΦ₀ w' v) w.symm
    have h3 := lfa_approx_trans h1 h2
    rw [lfa_comp_mul_symm v (Φ₀ w) (Φ₀ w'), lfa_comp_mul_symm (M v) w w']
    exact h3
  let Φ : Equiv.Perm (Fin n) →* Equiv.Perm (Fin n) := MonoidHom.mk' Φ₀ hΦmul
  have hΦspec : ∀ (w : Equiv.Perm (Fin n)) (v : Fin n → ZMod p),
      lfa_approx (M (v ∘ (Φ w).symm)) (M v ∘ w.symm) := fun w v => hΦ₀ w v
  have hΦone : ∀ w : Equiv.Perm (Fin n), Φ w = 1 → w = 1 := by
    intro w hw
    exact lfa_Φ_eq_one hn M hsurj Φ hΦspec hw
  have hΦinj : Function.Injective Φ := by
    intro a b hab
    have h1 : Φ (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hab, mul_inv_cancel]
    have h2 : a * b⁻¹ = 1 := hΦone _ h1
    calc a = a * b⁻¹ * b := by group
      _ = 1 * b := by rw [h2]
      _ = b := one_mul b
  have hswap : ∀ σ : Equiv.Perm (Fin n), σ.IsSwap → (Φ σ).IsSwap := by
    intro σ hσ
    obtain ⟨i, j, hij, rfl⟩ := hσ
    exact lfa_Φ_swap hp2 hn M hinj' Φ hΦspec hΦone hij
  obtain ⟨f, hf⟩ := exists_eq_conj_of_isSwap hn Φ hΦinj hswap
  have hf' : ∀ w : Equiv.Perm (Fin n), Φ w = f * w * f.symm := by
    intro w
    rw [hf w]
    rfl
  let pre : (Fin n → ZMod p) →+ (Fin n → ZMod p) :=
    { toFun := fun v => v ∘ f.symm
      map_zero' := by ext k; rfl
      map_add' := by intro x y; ext k; rfl }
  let N : (Fin n → ZMod p) →+ (Fin n → ZMod p) := M.comp pre
  have hNdef : ∀ u : Fin n → ZMod p, N u = M (u ∘ f.symm) := fun u => rfl
  have hNcomm : ∀ (w : Equiv.Perm (Fin n)) (u : Fin n → ZMod p),
      lfa_approx (N (u ∘ w.symm)) (N u ∘ w.symm) := by
    intro w u
    exact lfa_N_comm M Φ hΦspec f hf' w u
  obtain ⟨c, hc⟩ := lfa_N_scalar hn N hNcomm
  have hmain : ∀ v : Fin n → ZMod p, lfa_approx (M v) (c • (v ∘ f)) := by
    intro v
    have h := hc (v ∘ f)
    have hv : N (v ∘ f) = M v := by
      rw [hNdef]
      congr 1
      ext k
      simp [Function.comp_apply]
    rwa [hv] at h
  refine ⟨f, c, ?_, ?_⟩
  · intro hc0
    have hMe : ∀ v : Fin n → ZMod p, lfa_approx (M v) 0 := by
      intro v
      have h := hmain v
      rw [hc0] at h
      simpa using h
    let o : Fin n := ⟨0, by omega⟩
    obtain ⟨v, s, hs⟩ := hsurj (lfa_e (p := p) o)
    obtain ⟨t, ht⟩ := hMe v
    have hcon : lfa_approx (lfa_e (p := p) o) 0 := by
      refine ⟨t + s, fun k => ?_⟩
      have h1 := hs k
      have h2 := ht k
      simp only [Pi.zero_apply] at h2
      rw [h1, h2, Pi.zero_apply]
      ring
    exact lfa_not_approx_e_zero hn o hcon
  · intro v
    obtain ⟨s, hs⟩ := hmain v
    exact ⟨s, fun k => by simpa [Pi.smul_apply, Function.comp_apply] using hs k⟩

end LFrameAlign

end CFSG.StandardType

end
