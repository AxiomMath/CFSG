module

public import CFSG.RankThree.PartOne.K133.PerfectUnip
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.RankThree.PartOne.K133

open Module
open scoped commutatorElement

variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]

theorem pow_finrank_eq_zero_of_isNilpotent [FiniteDimensional K V] {n : Module.End K V}
    (hnil : IsNilpotent n) : n ^ finrank K V = 0 := by
  have h1 := IsNilpotent.charpoly_eq_X_pow_finrank hnil
  have h2 := LinearMap.aeval_self_charpoly n
  rw [h1] at h2
  simpa using h2

theorem perfect_unipotent_of_nilpotent_three_sub [FiniteDimensional K V] (R : Submodule K V)
    (hR : finrank K R = 3) (ρ : G →* Module.End K V) (hG : Group.IsPerfect G)
    (hRinv : ∀ g, ∀ w ∈ R, ρ g w ∈ R) {n : Module.End K V} (hnR : ∀ w ∈ R, n w ∈ R)
    (hn0 : ∃ w ∈ R, n w ≠ 0) (hnil : IsNilpotent n) (hcomm : ∀ g, ρ g * n = n * ρ g) :
    ∀ g, ∀ w ∈ R, (((ρ g - 1 : Module.End K V)) ^ 3) w = 0 := by
  classical
  let ρ' : G →* Module.End K R :=
    { toFun := fun g => (ρ g).restrict (hRinv g)
      map_one' := by
        ext w
        simp
      map_mul' := fun g h => by
        ext w
        simp [Module.End.mul_apply] }
  let n' : Module.End K R := n.restrict hnR
  have hpow : ∀ (f : Module.End K V) (hf : ∀ w ∈ R, f w ∈ R) (k : ℕ) (w : R),
      (((f.restrict hf) ^ k) w : V) = (f ^ k) w := by
    intro f hf k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
      rw [ih ((f.restrict hf) w)]
      simp [LinearMap.restrict_apply]
  have hn'0 : n' ≠ 0 := by
    obtain ⟨w, hw, hnw⟩ := hn0
    intro h
    apply hnw
    have := congrArg (fun f : Module.End K R => (f ⟨w, hw⟩ : V)) h
    simpa [n'] using this
  have hnil' : IsNilpotent n' := by
    obtain ⟨k, hk⟩ := hnil
    refine ⟨k, ?_⟩
    ext w
    have := hpow n hnR k w
    rw [hk] at this
    simpa using this
  have hcomm' : ∀ g, ρ' g * n' = n' * ρ' g := by
    intro g
    ext w
    have := congrArg (fun f : Module.End K V => f w) (hcomm g)
    simpa [ρ', n', Module.End.mul_apply] using this
  have key := perfect_unipotent_of_nilpotent_three hR ρ' hG hn'0 hnil' hcomm'
  intro g w hw
  have h1 := congrArg (fun f : Module.End K R => (f ⟨w, hw⟩ : V)) (key g)
  have h2 : ρ' g - 1 = (ρ g - 1).restrict (fun w hw => R.sub_mem (hRinv g w hw) hw) := by
    ext w
    simp [ρ']
  rw [h2] at h1
  have := hpow (ρ g - 1) (fun w hw => R.sub_mem (hRinv g w hw) hw) 3 ⟨w, hw⟩
  simpa [this] using h1

theorem sub_pow_le_ker_of_range {ρ : G →* Module.End K V} {N : Module.End K V}
    (hcomm : ∀ g, ρ g * N = N * ρ g) {a : ℕ} {g : G}
    (h : ∀ w ∈ LinearMap.range N, (((ρ g - 1 : Module.End K V)) ^ a) w = 0) :
    ∀ v : V, (((ρ g - 1 : Module.End K V)) ^ a) v ∈ LinearMap.ker N := by
  intro v
  rw [LinearMap.mem_ker]
  have hc : N * (ρ g - 1) ^ a = (ρ g - 1) ^ a * N := by
    have : Commute N (ρ g - 1) := by
      have h1 : Commute N (ρ g) := (hcomm g).symm
      exact h1.sub_right (Commute.one_right N)
    exact (this.pow_right a).eq
  have := h (N v) ⟨v, rfl⟩
  rw [← Module.End.mul_apply, ← hc, Module.End.mul_apply] at this
  exact this

theorem ker_range_invariant {f N : Module.End K V} (h : f * N = N * f) :
    (∀ w ∈ LinearMap.ker N, f w ∈ LinearMap.ker N) ∧ (∀ w ∈ LinearMap.range N, f w ∈ LinearMap.range N) := by
  constructor
  · intro w hw
    rw [LinearMap.mem_ker] at hw ⊢
    have := congrArg (fun x : Module.End K V => x w) h
    simp only [Module.End.mul_apply] at this
    rw [← this, hw, map_zero]
  · rintro _ ⟨y, rfl⟩
    refine ⟨f y, ?_⟩
    have := congrArg (fun x : Module.End K V => x y) h
    simp only [Module.End.mul_apply] at this
    exact this.symm

theorem unipotent_of_sq_ne_zero [FiniteDimensional K V] (hV : finrank K V = 4)
    (ρ : G →* Module.End K V) (hG : Group.IsPerfect G) {N : Module.End K V} (hnil : IsNilpotent N)
    (hN2 : N ^ 2 ≠ 0) (hcomm : ∀ g, ρ g * N = N * ρ g) :
    ∀ g, ((ρ g - 1 : Module.End K V)) ^ 4 = 0 := by
  classical
  set R : Submodule K V := LinearMap.range N with hRdef
  have hRinv : ∀ g, ∀ w ∈ R, ρ g w ∈ R := fun g => (ker_range_invariant (hcomm g)).2
  have hNR : ∀ w ∈ R, N w ∈ R := fun w _ => ⟨w, rfl⟩
  have hN4 : N ^ 4 = 0 := by
    have := pow_finrank_eq_zero_of_isNilpotent hnil
    rwa [hV] at this
  let N' : Module.End K R := N.restrict hNR
  have hN'ne : N' ≠ 0 := by
    intro h
    apply hN2
    ext y
    have := congrArg (fun f : Module.End K R => (f ⟨N y, ⟨y, rfl⟩⟩ : V)) h
    simpa [N', pow_two, Module.End.mul_apply] using this
  have hpowR : ∀ k : ℕ, ∀ w : R, ((N' ^ k) w : V) = (N ^ k) w := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
      rw [ih (N' w)]
      simp [N', LinearMap.restrict_apply]
  have hN'nil : IsNilpotent N' := by
    obtain ⟨k, hk⟩ := hnil
    refine ⟨k, ?_⟩
    ext w
    have := hpowR k w
    rw [hk] at this
    simpa using this
  have hNpowR := pow_finrank_eq_zero_of_isNilpotent hN'nil
  have hR3 : finrank K R ≤ 3 := by
    have hlt : R ≠ ⊤ := by
      intro htop
      have hsurj : ∀ y, ∃ z, N z = y := fun y => by
        have : y ∈ R := by rw [htop]; exact Submodule.mem_top
        exact this
      have hV0 : ∀ y : V, y = 0 := by
        intro y
        obtain ⟨z₁, rfl⟩ := hsurj y
        obtain ⟨z₂, rfl⟩ := hsurj z₁
        obtain ⟨z₃, rfl⟩ := hsurj z₂
        obtain ⟨z₄, rfl⟩ := hsurj z₃
        have : (N ^ 4) z₄ = N (N (N (N z₄))) := by simp [pow_succ, Module.End.mul_apply]
        rw [← this, hN4]
        rfl
      have hsub : Subsingleton V := ⟨fun a b => by rw [hV0 a, hV0 b]⟩
      have := Module.finrank_zero_of_subsingleton (R := K) (M := V)
      omega
    have := Submodule.finrank_lt hlt
    rw [hV] at this
    omega
  have hR2 : 2 ≤ finrank K R := by
    by_contra hlt
    push Not at hlt
    have hle : finrank K R ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle with h0 | h1
    · apply hN'ne
      have : Subsingleton R := Module.finrank_zero_iff.1 h0
      exact Subsingleton.elim _ _
    · rw [h1, pow_one] at hNpowR
      exact hN'ne hNpowR
  have hrn := LinearMap.finrank_range_add_finrank_ker N
  rw [← hRdef, hV] at hrn
  by_cases hr3 : finrank K R = 3
  ·
    intro g
    have h3 := perfect_unipotent_of_nilpotent_three_sub R hr3 ρ hG hRinv hNR
      (by
        obtain ⟨y, hy⟩ : ∃ y, (N ^ 2) y ≠ 0 := by
          by_contra hno
          push Not at hno
          exact hN2 (LinearMap.ext hno)
        exact ⟨N y, ⟨y, rfl⟩, by simpa [pow_two, Module.End.mul_apply] using hy⟩) hnil hcomm
    have hext := sub_pow_le_ker_of_range (a := 3) hcomm (g := g) (fun w hw => h3 g w hw)
    have hker : finrank K (LinearMap.ker N) = 1 := by omega
    have hker_inv : ∀ g, ∀ w ∈ LinearMap.ker N, ρ g w ∈ LinearMap.ker N :=
      fun g => (ker_range_invariant (hcomm g)).1
    have hC := perfect_trivial_on_section ρ hG (W' := ⊥) (W := LinearMap.ker N) bot_le
      (by simp [hker]) hker_inv (by
        intro g w hw
        rw [Submodule.mem_bot] at hw ⊢
        simp [hw])
    ext v
    have h1 := hext v
    have h2 := hC g _ h1
    rw [Submodule.mem_bot] at h2
    have h4 : (((ρ g - 1 : Module.End K V)) ^ 4) v =
        ρ g ((((ρ g - 1 : Module.End K V)) ^ 3) v) - (((ρ g - 1 : Module.End K V)) ^ 3) v := by
      rw [pow_succ' _ 3, Module.End.mul_apply]
      simp
    rw [h4, h2]
    rfl
  ·
    have hr2 : finrank K R = 2 := by omega
    have hN3 : N ^ 3 = 0 := by
      have h2 : N' ^ 2 = 0 := by rw [← hr2]; exact hNpowR
      ext v
      have := hpowR 2 ⟨N v, ⟨v, rfl⟩⟩
      rw [h2] at this
      have h5 : (N ^ 3) v = (N ^ 2) (N v) := by
        rw [pow_succ, Module.End.mul_apply]
      rw [h5]
      simpa using this.symm
    set L : Submodule K V := LinearMap.range (N ^ 2) with hLdef
    have hLR : L ≤ R := by
      rw [hLdef, hRdef, pow_two]
      exact LinearMap.range_comp_le_range N N
    have hLker : L ≤ LinearMap.ker N := by
      rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker]
      have : (N ^ 3) y = 0 := by rw [hN3]; rfl
      rw [pow_succ'] at this
      simpa [Module.End.mul_apply] using this
    have hLinv : ∀ g, ∀ w ∈ L, ρ g w ∈ L := fun g =>
      (ker_range_invariant (f := ρ g) (N := N ^ 2)
        (by
          have : Commute (ρ g) N := hcomm g
          exact (this.pow_right 2).eq)).2
    have hLpos : 1 ≤ finrank K L := by
      rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
      intro hbot
      apply hN2
      ext y
      have : (N ^ 2) y ∈ L := ⟨y, rfl⟩
      rw [hbot, Submodule.mem_bot] at this
      simpa using this
    have hLlt : finrank K L < finrank K R := by
      refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hLR fun heq => ?_)
      have h2 : N' ^ 2 = 0 := by rw [← hr2]; exact hNpowR
      have hsurj : ∀ w : R, ∃ z : R, N' z = w := by
        intro w
        have : (w : V) ∈ L := by rw [heq]; exact w.2
        obtain ⟨y, hy⟩ := this
        refine ⟨⟨N y, ⟨y, rfl⟩⟩, ?_⟩
        apply Subtype.ext
        simpa [N', pow_two, Module.End.mul_apply] using hy
      have hall : ∀ w : R, w = 0 := by
        intro w
        obtain ⟨z₁, rfl⟩ := hsurj w
        obtain ⟨z₂, rfl⟩ := hsurj z₁
        have : (N' ^ 2) z₂ = N' (N' z₂) := by simp [pow_two, Module.End.mul_apply]
        rw [← this, h2]
        rfl
      have hsub : Subsingleton R := ⟨fun a b => by rw [hall a, hall b]⟩
      have := Module.finrank_zero_of_subsingleton (R := K) (M := R)
      omega
    have hL1 : finrank K L = 1 := by omega
    have hker2 : finrank K (LinearMap.ker N) = 2 := by omega
    have hker_inv : ∀ g, ∀ w ∈ LinearMap.ker N, ρ g w ∈ LinearMap.ker N :=
      fun g => (ker_range_invariant (hcomm g)).1
    have hbotinv : ∀ g, ∀ w ∈ (⊥ : Submodule K V), ρ g w ∈ (⊥ : Submodule K V) := by
      intro g w hw
      rw [Submodule.mem_bot] at hw ⊢
      simp [hw]
    have cL := perfect_trivial_on_section ρ hG (W' := ⊥) (W := L) bot_le (by simp [hL1]) hLinv hbotinv
    have cR := perfect_trivial_on_section ρ hG (W' := L) (W := R) hLR (by omega) hRinv hLinv
    have cK := perfect_trivial_on_section ρ hG (W' := L) (W := LinearMap.ker N) hLker (by omega)
      hker_inv hLinv
    intro g
    have h2R : ∀ w ∈ R, (((ρ g - 1 : Module.End K V)) ^ 2) w = 0 := by
      intro w hw
      have h1 := cR g w hw
      have h2 := cL g _ h1
      rw [Submodule.mem_bot] at h2
      have h4 : (((ρ g - 1 : Module.End K V)) ^ 2) w = ρ g (ρ g w - w) - (ρ g w - w) := by
        rw [pow_two, Module.End.mul_apply]
        simp
      rw [h4, h2]
    have hext := sub_pow_le_ker_of_range (a := 2) hcomm (g := g) h2R
    ext v
    set x : V := (((ρ g - 1 : Module.End K V)) ^ 2) v with hx
    have h1 : x ∈ LinearMap.ker N := hext v
    have hx1 := cK g x h1
    have hx2 := cL g _ hx1
    rw [Submodule.mem_bot] at hx2
    have h4 : (((ρ g - 1 : Module.End K V)) ^ 4) v = ρ g (ρ g x - x) - (ρ g x - x) := by
      have h5 : ((ρ g - 1 : Module.End K V)) ^ 4 =
          ((ρ g - 1 : Module.End K V)) ^ 2 * ((ρ g - 1 : Module.End K V)) ^ 2 := by
        rw [← pow_add]
      rw [h5, Module.End.mul_apply, ← hx, pow_two, Module.End.mul_apply]
      simp
    rw [h4, hx2]
    rfl

theorem perfect_trivial_of_commute_on [FiniteDimensional K V] (ρ : G →* Module.End K V)
    (hG : Group.IsPerfect G) (W : Submodule K V) (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W)
    (hcomm : ∀ a b : G, ∀ w ∈ W, ρ a (ρ b w) = ρ b (ρ a w)) : ∀ g, ∀ w ∈ W, ρ g w = w := by
  let T : Subgroup G :=
    { carrier := {g | ∀ w ∈ W, ρ g w = w}
      one_mem' := by
        intro w hw
        simp
      mul_mem' := by
        intro g h hg hh w hw
        rw [map_mul, Module.End.mul_apply, hh w hw, hg w hw]
      inv_mem' := by
        intro g hg w hw
        have h1 := hg w hw
        calc ρ g⁻¹ w = ρ g⁻¹ (ρ g w) := by rw [h1]
          _ = w := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
  have hcommT : ∀ a b : G, ⁅a, b⁆ ∈ T := by
    intro a b u hu
    set w : V := ρ ((b * a)⁻¹) u with hwdef
    have hwW : w ∈ W := hW _ u hu
    have hwu : ρ (b * a) w = u := by
      rw [hwdef, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    have hcu : ρ ⁅a, b⁆ u = ρ (a * b) w := by
      rw [← hwu, ← Module.End.mul_apply, ← map_mul]
      congr 2
      rw [commutatorElement_def]
      group
    rw [hcu, map_mul, Module.End.mul_apply, hcomm a b w hwW, ← Module.End.mul_apply, ← map_mul]
    exact hwu
  have htop : T = ⊤ := by
    have h1 : (⊤ : Subgroup G) = ⁅(⊤ : Subgroup G), ⊤⁆ := (hG.commutator_eq_top).symm
    refine eq_top_iff.2 ?_
    rw [h1, Subgroup.commutator_le]
    intro a _ b _
    exact hcommT a b
  intro g w hw
  have : g ∈ T := by rw [htop]; exact Subgroup.mem_top g
  exact this w hw

theorem unipotent_of_rank_two [FiniteDimensional K V] (hV : finrank K V = 4)
    (ρ : G →* Module.End K V) (hG : Group.IsPerfect G) {N N' : Module.End K V}
    (hNN : N * N = 0) (hNN' : N * N' = 0) (hN'N : N' * N = 0)
    (hr : finrank K (LinearMap.range N) = 2) (hcN : ∀ g, ρ g * N = N * ρ g)
    (hcN' : ∀ g, ρ g * N' = N' * ρ g) (hind : ∀ c : K, N' ≠ c • N) :
    ∀ g, ((ρ g - 1 : Module.End K V)) ^ 4 = 0 := by
  classical
  set W : Submodule K V := LinearMap.range N with hWdef
  have hmul : ∀ (A B : Module.End K V) (v : V), (A * B) v = A (B v) := fun A B v => rfl
  have hWker_le : W ≤ LinearMap.ker N := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, ← hmul, hNN]
    rfl
  have hrn := LinearMap.finrank_range_add_finrank_ker N
  rw [hV] at hrn
  have hWker : W = LinearMap.ker N :=
    Submodule.eq_of_le_of_finrank_eq hWker_le (by rw [← hWdef] at hrn; omega)
  have hN'W : ∀ w ∈ W, N' w = 0 := by
    rintro _ ⟨y, rfl⟩
    rw [← hmul, hN'N]
    rfl
  have hrN' : ∀ y, N' y ∈ W := by
    intro y
    rw [hWker, LinearMap.mem_ker, ← hmul, hNN']
    rfl
  have hWinv : ∀ g, ∀ w ∈ W, ρ g w ∈ W := fun g => (ker_range_invariant (hcN g)).2
  have hq : ∃ q : V, ∀ a b : K, a • N q + b • N' q = 0 → a = 0 ∧ b = 0 := by
    by_contra hno
    push Not at hno
    have hclaim : ∀ q : V, ∃ c : K, N' q = c • N q := by
      intro q
      by_cases hNq : N q = 0
      · refine ⟨0, ?_⟩
        have : q ∈ W := by rw [hWker]; exact hNq
        rw [hN'W q this]
        simp
      · obtain ⟨a, b, hab, hne⟩ := hno q
        have hb : b ≠ 0 := by
          intro hb0
          rw [hb0, zero_smul, add_zero] at hab
          exact hne ((smul_eq_zero.1 hab).resolve_right hNq) hb0
        refine ⟨-(a / b), ?_⟩
        have : b • N' q = -(a • N q) := by
          rw [eq_neg_iff_add_eq_zero, add_comm]
          exact hab
        calc N' q = b⁻¹ • (b • N' q) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
          _ = b⁻¹ • (-(a • N q)) := by rw [this]
          _ = -(a / b) • N q := by rw [smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
    obtain ⟨q₁, hq₁⟩ : ∃ q₁ : V, N q₁ ≠ 0 := by
      by_contra hno'
      push Not at hno'
      have hrange0 : W = ⊥ := by
        rw [hWdef, LinearMap.range_eq_bot]
        exact LinearMap.ext hno'
      rw [hrange0, finrank_bot] at hr
      omega
    obtain ⟨c, hc⟩ := hclaim q₁
    apply hind c
    ext q
    show N' q = c • N q
    by_cases hdep : ∃ d : K, N q = d • N q₁
    · obtain ⟨d, hd⟩ := hdep
      have hmem : q - d • q₁ ∈ W := by
        rw [hWker, LinearMap.mem_ker, map_sub, map_smul, hd, sub_self]
      have h0 := hN'W _ hmem
      rw [map_sub, map_smul, hc, sub_eq_zero] at h0
      rw [h0, smul_smul, hd, smul_smul, mul_comm]
    · push Not at hdep
      obtain ⟨cq, hcq⟩ := hclaim q
      obtain ⟨c', hc'⟩ := hclaim (q + q₁)
      rw [map_add, map_add, hcq, hc] at hc'
      have hrel : (cq - c') • N q + (c - c') • N q₁ = 0 := by
        calc (cq - c') • N q + (c - c') • N q₁
            = (cq • N q + c • N q₁) - (c' • N q + c' • N q₁) := by module
          _ = 0 := by rw [hc', smul_add]; exact sub_self _
      have hα : cq - c' = 0 := by
        by_contra hne
        apply hdep (-((c - c') / (cq - c')))
        have : (cq - c') • N q = -((c - c') • N q₁) := by
          rw [eq_neg_iff_add_eq_zero]; exact hrel
        calc N q = (cq - c')⁻¹ • ((cq - c') • N q) := by rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
          _ = (cq - c')⁻¹ • (-((c - c') • N q₁)) := by rw [this]
          _ = -((c - c') / (cq - c')) • N q₁ := by
            rw [smul_neg, smul_smul, neg_smul, div_eq_mul_inv, mul_comm]
      have hβ : c - c' = 0 := by
        rw [hα, zero_smul, zero_add] at hrel
        exact (smul_eq_zero.1 hrel).resolve_right hq₁
      rw [hcq, (sub_eq_zero.1 hα).trans (sub_eq_zero.1 hβ).symm]
  obtain ⟨q, hqind⟩ := hq
  set w₁ : V := N q with hw₁
  set w₂ : V := N' q with hw₂
  have hw₁W : w₁ ∈ W := ⟨q, rfl⟩
  have hw₂W : w₂ ∈ W := hrN' q
  have hli : LinearIndependent K ![w₁, w₂] := by
    rw [LinearIndependent.pair_iff]
    exact hqind
  have hspan : Submodule.span K {w₁, w₂} = W := by
    have hle : Submodule.span K {w₁, w₂} ≤ W :=
      (Submodule.span_le).2 (by
        intro x hx
        rcases hx with rfl | rfl
        · exact hw₁W
        · exact hw₂W)
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    have hrange : Set.range ![w₁, w₂] = {w₁, w₂} := by
      ext x
      simp [or_comm]
    have h2 := finrank_span_eq_card hli
    rw [hrange] at h2
    rw [h2]
    simp [hr]
  obtain ⟨q', hq'⟩ : ∃ q' : V, N q' = w₂ := hw₂W
  obtain ⟨γ, δ, hγδ⟩ : ∃ γ δ : K, N' q' = γ • w₁ + δ • w₂ := by
    have hmem : N' q' ∈ Submodule.span K {w₁, w₂} := by rw [hspan]; exact hrN' q'
    obtain ⟨γ, δ, h⟩ := Submodule.mem_span_pair.1 hmem
    exact ⟨γ, δ, h.symm⟩
  have hrep : ∀ g : G, ∃ α β : K, ρ g w₁ = α • w₁ + β • w₂ ∧
      ρ g w₂ = α • w₂ + β • (γ • w₁ + δ • w₂) := by
    intro g
    have hmemN : N (ρ g q) ∈ Submodule.span K {w₁, w₂} := by rw [hspan]; exact ⟨ρ g q, rfl⟩
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.1 hmemN
    have hc1 : ρ g w₁ = N (ρ g q) := by
      have := congrArg (fun f : Module.End K V => f q) (hcN g)
      simpa [hmul] using this
    have hc2 : ρ g w₂ = N' (ρ g q) := by
      have := congrArg (fun f : Module.End K V => f q) (hcN' g)
      simpa [hmul] using this
    have h1 : ρ g q - (α • q + β • q') ∈ W := by
      rw [hWker, LinearMap.mem_ker, map_sub, map_add, map_smul, map_smul, hq', ← hαβ]
      simp [hw₁]
    have h2 := hN'W _ h1
    rw [map_sub, map_add, map_smul, map_smul, hγδ, sub_eq_zero] at h2
    refine ⟨α, β, ?_, ?_⟩
    · rw [hc1, ← hαβ]
    · rw [hc2, h2]
  have hcomm : ∀ a b : G, ∀ w ∈ W, ρ a (ρ b w) = ρ b (ρ a w) := by
    intro a b w hw
    rw [← hspan] at hw
    obtain ⟨αa, βa, ha1, ha2⟩ := hrep a
    obtain ⟨αb, βb, hb1, hb2⟩ := hrep b
    have hEq : Set.EqOn ((ρ a : Module.End K V) ∘ₗ (ρ b : Module.End K V))
        ((ρ b : Module.End K V) ∘ₗ (ρ a : Module.End K V)) {w₁, w₂} := by
      intro x hx
      rcases hx with rfl | rfl
      · simp only [LinearMap.comp_apply, map_add, map_smul, ha1, ha2, hb1, hb2]
        module
      · simp only [LinearMap.comp_apply, map_add, map_smul, ha1, ha2, hb1, hb2]
        module
    exact LinearMap.eqOn_span hEq hw
  have hWtriv := perfect_trivial_of_commute_on ρ hG W hWinv hcomm
  intro g
  ext v
  have hNv : N v ∈ W := ⟨v, rfl⟩
  have h1 : ρ g v - v ∈ W := by
    rw [hWker, LinearMap.mem_ker, map_sub]
    have hc : ρ g (N v) = N (ρ g v) := by
      have := congrArg (fun f : Module.End K V => f v) (hcN g)
      simpa [hmul] using this
    rw [← hc, hWtriv g (N v) hNv, sub_self]
  have h2 : ρ g (ρ g v - v) = ρ g v - v := hWtriv g _ h1
  have h3 : (((ρ g - 1 : Module.End K V)) ^ 2) v = 0 := by
    rw [pow_two, Module.End.mul_apply]
    simp [h2]
  have h5 : ((ρ g - 1 : Module.End K V)) ^ 4 =
      ((ρ g - 1 : Module.End K V)) ^ 2 * ((ρ g - 1 : Module.End K V)) ^ 2 := by
    rw [← pow_add]
  rw [h5, Module.End.mul_apply, h3, map_zero]
  rfl

theorem eq_of_finrank_one_of_mem [FiniteDimensional K V] {A B : Submodule K V} (hA : finrank K A = 1)
    (hB : finrank K B = 1) {x : V} (hx : x ≠ 0) (hxA : x ∈ A) (hxB : x ∈ B) : A = B := by
  have h1 : Submodule.span K {x} ≤ A := (Submodule.span_singleton_le_iff_mem _ _).2 hxA
  have h2 : Submodule.span K {x} ≤ B := (Submodule.span_singleton_le_iff_mem _ _).2 hxB
  have hs : finrank K (Submodule.span K {x}) = 1 := finrank_span_singleton hx
  have hAs : Submodule.span K {x} = A := Submodule.eq_of_le_of_finrank_eq h1 (by rw [hs, hA])
  have hBs : Submodule.span K {x} = B := Submodule.eq_of_le_of_finrank_eq h2 (by rw [hs, hB])
  rw [← hAs, hBs]

theorem exists_decomp_of_not_mem [FiniteDimensional K V] {H : Submodule K V}
    (hH : finrank K H + 1 = finrank K V) {w₀ : V} (hw₀ : w₀ ∉ H) (v : V) :
    ∃ k ∈ H, ∃ a : K, v = k + a • w₀ := by
  have hlt : H < H ⊔ (K ∙ w₀) := by
    refine lt_of_le_of_ne le_sup_left fun h => hw₀ ?_
    rw [h]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self w₀)
  have h3 : finrank K H < finrank K ↥(H ⊔ (K ∙ w₀)) := Submodule.finrank_lt_finrank_of_lt hlt
  have htop : H ⊔ (K ∙ w₀) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    have := Submodule.finrank_le (H ⊔ (K ∙ w₀))
    omega
  have hv : v ∈ H ⊔ (K ∙ w₀) := by rw [htop]; exact Submodule.mem_top
  obtain ⟨k, hk, z, hz, hkz⟩ := Submodule.mem_sup.1 hv
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
  exact ⟨k, hk, a, hkz.symm⟩

theorem eq_smul_of_ker_eq_of_range_eq [FiniteDimensional K V] (hV : finrank K V = 4) {N N' : Module.End K V}
    (hker : LinearMap.ker N = LinearMap.ker N') (hrange : LinearMap.range N = LinearMap.range N')
    (hr : finrank K (LinearMap.range N) = 1) (hk : finrank K (LinearMap.ker N) = 3) :
    ∃ c : K, N' = c • N := by
  have hne : LinearMap.ker N ≠ ⊤ := by
    intro h
    rw [h, finrank_top, hV] at hk
    omega
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : V, w₀ ∉ LinearMap.ker N := by
    by_contra hall
    push Not at hall
    exact hne (eq_top_iff.2 fun v _ => hall v)
  have hNw₀ : N w₀ ≠ 0 := fun h => hw₀ (LinearMap.mem_ker.2 h)
  have hN'w₀ : N' w₀ ∈ LinearMap.range N := by rw [hrange]; exact ⟨w₀, rfl⟩
  have hspan : LinearMap.range N = Submodule.span K {N w₀} :=
    (Submodule.eq_of_le_of_finrank_eq
      ((Submodule.span_singleton_le_iff_mem _ _).2 (LinearMap.mem_range_self N w₀))
      (by rw [finrank_span_singleton hNw₀, hr])).symm
  rw [hspan] at hN'w₀
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hN'w₀
  refine ⟨c, ?_⟩
  ext v
  obtain ⟨k, hk', a, rfl⟩ := exists_decomp_of_not_mem (H := LinearMap.ker N)
    (by rw [hk, hV]) hw₀ v
  have hk2 : k ∈ LinearMap.ker N' := by rw [← hker]; exact hk'
  rw [LinearMap.mem_ker] at hk' hk2
  simp only [map_add, map_smul, hk', hk2, zero_add, LinearMap.smul_apply]
  rw [← hc]
  simp [smul_smul, mul_comm]

theorem pow_four_apply (e : Module.End K V) (v : V) : (e ^ 4) v = e (e (e (e v))) := by
  simp [pow_succ, Module.End.mul_apply]

theorem unipotent_of_common_range [FiniteDimensional K V] (hV : finrank K V = 4)
    (ρ : G →* Module.End K V) (hG : Group.IsPerfect G) {N₁ N₂ : Module.End K V}
    (h11 : N₁ * N₁ = 0) (h21 : N₂ * N₁ = 0)
    (hc₁ : ∀ g, ρ g * N₁ = N₁ * ρ g) (hc₂ : ∀ g, ρ g * N₂ = N₂ * ρ g)
    (hr₁ : finrank K (LinearMap.range N₁) = 1) (hr₂ : finrank K (LinearMap.range N₂) = 1)
    (hrange : LinearMap.range N₁ = LinearMap.range N₂) (hind : ∀ c : K, N₂ ≠ c • N₁) :
    ∀ g, ((ρ g - 1 : Module.End K V)) ^ 4 = 0 := by
  classical
  have hmul : ∀ (A B : Module.End K V) (v : V), (A * B) v = A (B v) := fun A B v => rfl
  set L : Submodule K V := LinearMap.range N₁ with hLdef
  have hLinv : ∀ g, ∀ w ∈ L, ρ g w ∈ L := fun g => (ker_range_invariant (hc₁ g)).2
  have hbotinv : ∀ g, ∀ w ∈ (⊥ : Submodule K V), ρ g w ∈ (⊥ : Submodule K V) := by
    intro g w hw
    rw [Submodule.mem_bot] at hw ⊢
    simp [hw]
  have cL := perfect_trivial_on_section ρ hG (W' := ⊥) (W := L) bot_le (by simp [hr₁]) hLinv hbotinv
  have hk₁ : finrank K (LinearMap.ker N₁) = 3 := by
    have := LinearMap.finrank_range_add_finrank_ker N₁
    rw [hV, ← hLdef] at this
    omega
  have hk₂ : finrank K (LinearMap.ker N₂) = 3 := by
    have := LinearMap.finrank_range_add_finrank_ker N₂
    rw [hV] at this
    omega
  set Ξ : Submodule K V := LinearMap.ker N₁ ⊓ LinearMap.ker N₂ with hΞdef
  have hΞinv : ∀ g, ∀ w ∈ Ξ, ρ g w ∈ Ξ := fun g w hw =>
    ⟨(ker_range_invariant (hc₁ g)).1 w hw.1, (ker_range_invariant (hc₂ g)).1 w hw.2⟩
  have hLΞ : L ≤ Ξ := by
    rintro _ ⟨y, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, LinearMap.mem_ker, ← hmul, h11]; rfl
    · rw [SetLike.mem_coe, LinearMap.mem_ker, ← hmul, h21]; rfl
  have hΞdim : finrank K Ξ ≤ 2 := by
    by_contra hgt
    push Not at hgt
    have h1 : finrank K Ξ ≤ 3 := hk₁ ▸ Submodule.finrank_mono inf_le_left
    have hΞ3 : finrank K Ξ = 3 := by omega
    have e1 : Ξ = LinearMap.ker N₁ :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [hΞ3, hk₁])
    have e2 : Ξ = LinearMap.ker N₂ :=
      Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [hΞ3, hk₂])
    obtain ⟨c, hc⟩ := eq_smul_of_ker_eq_of_range_eq hV (e1.symm.trans e2) hrange hr₁ hk₁
    exact hind c hc
  have cΞ := perfect_trivial_on_section ρ hG (W' := L) (W := Ξ) hLΞ (by omega) hΞinv hLinv
  intro g
  ext v
  have hv1 : ρ g v - v ∈ Ξ := by
    refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub]
      have hc : ρ g (N₁ v) = N₁ (ρ g v) := by
        have := congrArg (fun f : Module.End K V => f v) (hc₁ g)
        simpa [hmul] using this
      have h0 := cL g (N₁ v) (LinearMap.mem_range_self N₁ v)
      rw [Submodule.mem_bot, sub_eq_zero] at h0
      rw [← hc, h0, sub_self]
    · rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub]
      have hc : ρ g (N₂ v) = N₂ (ρ g v) := by
        have := congrArg (fun f : Module.End K V => f v) (hc₂ g)
        simpa [hmul] using this
      have hN₂v : N₂ v ∈ L := by rw [hrange]; exact LinearMap.mem_range_self N₂ v
      have h0 := cL g (N₂ v) hN₂v
      rw [Submodule.mem_bot, sub_eq_zero] at h0
      rw [← hc, h0, sub_self]
  have hv2 := cΞ g _ hv1
  have hv3 := cL g _ hv2
  rw [Submodule.mem_bot] at hv3
  rw [pow_four_apply]
  simp only [LinearMap.sub_apply, Module.End.one_apply] at *
  rw [hv3]
  simp

theorem unipotent_of_common_ker [FiniteDimensional K V] (hV : finrank K V = 4)
    (ρ : G →* Module.End K V) (hG : Group.IsPerfect G) {N₁ N₂ : Module.End K V}
    (h11 : N₁ * N₁ = 0) (h12 : N₁ * N₂ = 0)
    (hc₁ : ∀ g, ρ g * N₁ = N₁ * ρ g) (hc₂ : ∀ g, ρ g * N₂ = N₂ * ρ g)
    (hker : LinearMap.ker N₁ = LinearMap.ker N₂) (hk : finrank K (LinearMap.ker N₁) = 3)
    (hU : 2 ≤ finrank K ↥(LinearMap.range N₁ ⊔ LinearMap.range N₂)) :
    ∀ g, ((ρ g - 1 : Module.End K V)) ^ 4 = 0 := by
  classical
  have hmul : ∀ (A B : Module.End K V) (v : V), (A * B) v = A (B v) := fun A B v => rfl
  set K₀ : Submodule K V := LinearMap.ker N₁ with hK₀def
  have hK₀inv : ∀ g, ∀ w ∈ K₀, ρ g w ∈ K₀ := fun g => (ker_range_invariant (hc₁ g)).1
  have hbotinv : ∀ g, ∀ w ∈ (⊥ : Submodule K V), ρ g w ∈ (⊥ : Submodule K V) := by
    intro g w hw
    rw [Submodule.mem_bot] at hw ⊢
    simp [hw]
  have cV := perfect_trivial_on_section ρ hG (W' := K₀) (W := ⊤) le_top
    (by rw [finrank_top, hV, hk]) (fun g w _ => Submodule.mem_top) hK₀inv
  set U : Submodule K V := LinearMap.range N₁ ⊔ LinearMap.range N₂ with hUdef
  have hUinv : ∀ g, ∀ w ∈ U, ρ g w ∈ U := by
    intro g w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
    rw [map_add]
    exact Submodule.add_mem_sup ((ker_range_invariant (hc₁ g)).2 a ha)
      ((ker_range_invariant (hc₂ g)).2 b hb)
  have hUK : U ≤ K₀ := by
    refine sup_le ?_ ?_
    · rintro _ ⟨y, rfl⟩
      rw [hK₀def, LinearMap.mem_ker, ← hmul, h11]; rfl
    · rintro _ ⟨y, rfl⟩
      rw [hK₀def, LinearMap.mem_ker, ← hmul, h12]; rfl
  have cK := perfect_trivial_on_section ρ hG (W' := U) (W := K₀) hUK (by omega) hK₀inv hUinv
  intro g
  ext v
  have hx1 : ρ g v - v ∈ K₀ := by
    have := cV g v Submodule.mem_top
    exact this
  have hUtriv : ∀ u ∈ U, ρ g u - u = 0 := by
    intro u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hu
    obtain ⟨ya, rfl⟩ := ha
    obtain ⟨yb, rfl⟩ := hb
    have hca : ρ g (N₁ ya) = N₁ (ρ g ya) := by
      have := congrArg (fun f : Module.End K V => f ya) (hc₁ g)
      simpa [hmul] using this
    have hcb : ρ g (N₂ yb) = N₂ (ρ g yb) := by
      have := congrArg (fun f : Module.End K V => f yb) (hc₂ g)
      simpa [hmul] using this
    have hxa : ρ g ya - ya ∈ K₀ := cV g ya Submodule.mem_top
    have hxb : ρ g yb - yb ∈ LinearMap.ker N₂ := by rw [← hker]; exact cV g yb Submodule.mem_top
    rw [LinearMap.mem_ker, map_sub] at hxb
    rw [hK₀def, LinearMap.mem_ker, map_sub] at hxa
    rw [map_add, hca, hcb]
    have e1 : N₁ (ρ g ya) = N₁ ya := sub_eq_zero.1 hxa
    have e2 : N₂ (ρ g yb) = N₂ yb := sub_eq_zero.1 hxb
    rw [e1, e2]
    abel
  have hx2 := cK g _ hx1
  have hx3 := hUtriv _ hx2
  rw [pow_four_apply]
  simp only [LinearMap.sub_apply, Module.End.one_apply] at *
  rw [hx3]
  simp

theorem rank_one_or_two [FiniteDimensional K V] (hV : finrank K V = 4) {N : Module.End K V}
    (hNN : N * N = 0) (hN : N ≠ 0) :
    finrank K (LinearMap.range N) = 1 ∨ finrank K (LinearMap.range N) = 2 := by
  have hle : LinearMap.range N ≤ LinearMap.ker N := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    have := congrArg (fun f : Module.End K V => f y) hNN
    simpa [Module.End.mul_apply] using this
  have hrn := LinearMap.finrank_range_add_finrank_ker N
  have hmono := Submodule.finrank_mono hle
  have hpos : 1 ≤ finrank K (LinearMap.range N) := by
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    intro hbot
    apply hN
    ext y
    have : N y ∈ LinearMap.range N := LinearMap.mem_range_self N y
    rw [hbot, Submodule.mem_bot] at this
    simpa using this
  omega

theorem finrank_sup_eq_two_of_ne [FiniteDimensional K V] {A B : Submodule K V} (hA : finrank K A = 1)
    (hB : finrank K B = 1) (hne : A ≠ B) : finrank K ↥(A ⊔ B) = 2 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq A B
  have hinf : finrank K ↥(A ⊓ B) = 0 := by
    by_contra h0
    have hle : finrank K ↥(A ⊓ B) ≤ 1 := hA ▸ Submodule.finrank_mono inf_le_left
    have h1 : finrank K ↥(A ⊓ B) = 1 := by omega
    have e1 : A ⊓ B = A := Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h1, hA])
    have e2 : A ⊓ B = B := Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [h1, hB])
    exact hne (e1.symm.trans e2)
  omega

theorem rank_add_ne_one [FiniteDimensional K V] (hV : finrank K V = 4) {N₁ N₂ : Module.End K V}
    (hr₁ : finrank K (LinearMap.range N₁) = 1) (hr₂ : finrank K (LinearMap.range N₂) = 1)
    (hrange : LinearMap.range N₁ ≠ LinearMap.range N₂) (hker : LinearMap.ker N₁ ≠ LinearMap.ker N₂) :
    finrank K (LinearMap.range (N₁ + N₂)) ≠ 1 := by
  intro h3
  have hk₁ : finrank K (LinearMap.ker N₁) = 3 := by
    have := LinearMap.finrank_range_add_finrank_ker N₁
    rw [hV] at this
    omega
  have hk₂ : finrank K (LinearMap.ker N₂) = 3 := by
    have := LinearMap.finrank_range_add_finrank_ker N₂
    rw [hV] at this
    omega
  obtain ⟨v, hv₂, hv₁⟩ : ∃ v, v ∈ LinearMap.ker N₂ ∧ v ∉ LinearMap.ker N₁ := by
    by_contra hno
    push Not at hno
    exact hker (Submodule.eq_of_le_of_finrank_eq (fun v hv => hno v hv) (by rw [hk₁, hk₂])).symm
  obtain ⟨v', hv₁', hv₂'⟩ : ∃ v, v ∈ LinearMap.ker N₁ ∧ v ∉ LinearMap.ker N₂ := by
    by_contra hno
    push Not at hno
    exact hker (Submodule.eq_of_le_of_finrank_eq (fun v hv => hno v hv) (by rw [hk₁, hk₂]))
  have hu₁ : N₁ v ≠ 0 := fun h => hv₁ (LinearMap.mem_ker.2 h)
  have hu₂ : N₂ v' ≠ 0 := fun h => hv₂' (LinearMap.mem_ker.2 h)
  rw [LinearMap.mem_ker] at hv₂ hv₁'
  have e1 : LinearMap.range N₁ = LinearMap.range (N₁ + N₂) :=
    eq_of_finrank_one_of_mem hr₁ h3 hu₁ (LinearMap.mem_range_self N₁ v)
      ⟨v, by simp [hv₂]⟩
  have e2 : LinearMap.range N₂ = LinearMap.range (N₁ + N₂) :=
    eq_of_finrank_one_of_mem hr₂ h3 hu₂ (LinearMap.mem_range_self N₂ v')
      ⟨v', by simp [hv₁']⟩
  exact hrange (e1.trans e2.symm)

theorem unipotent_of_two_square_zero [FiniteDimensional K V] (hV : finrank K V = 4)
    (ρ : G →* Module.End K V) (hG : Group.IsPerfect G) {N₁ N₂ : Module.End K V}
    (h11 : N₁ * N₁ = 0) (h12 : N₁ * N₂ = 0) (h21 : N₂ * N₁ = 0) (h22 : N₂ * N₂ = 0)
    (hc₁ : ∀ g, ρ g * N₁ = N₁ * ρ g) (hc₂ : ∀ g, ρ g * N₂ = N₂ * ρ g)
    (hN₁ : N₁ ≠ 0) (hind : ∀ c : K, N₂ ≠ c • N₁) :
    ∀ g, ((ρ g - 1 : Module.End K V)) ^ 4 = 0 := by
  classical
  have hN₂ : N₂ ≠ 0 := fun h => hind 0 (by rw [h, zero_smul])
  have hN₃ : N₁ + N₂ ≠ 0 := fun h => hind (-1) (by
    rw [neg_one_smul]
    exact eq_neg_of_add_eq_zero_right h)
  have h33 : (N₁ + N₂) * (N₁ + N₂) = 0 := by
    rw [mul_add, add_mul, add_mul, h11, h12, h21, h22]; simp
  have hc₃ : ∀ g, ρ g * (N₁ + N₂) = (N₁ + N₂) * ρ g := by
    intro g
    rw [mul_add, add_mul, hc₁, hc₂]
  have h13 : N₁ * (N₁ + N₂) = 0 := by rw [mul_add, h11, h12]; simp
  have h31 : (N₁ + N₂) * N₁ = 0 := by rw [add_mul, h11, h21]; simp
  have hind₂ : ∀ c : K, N₁ ≠ c • N₂ := by
    intro c hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hN₁ (by rw [hc, zero_smul])
    exact hind c⁻¹ (by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul])
  have hind₃ : ∀ c : K, N₁ ≠ c • (N₁ + N₂) := by
    intro c hc
    by_cases hc0 : c = 0
    · exact hN₁ (by rw [hc, hc0, zero_smul])
    · apply hind ((1 - c) / c)
      have : (1 - c) • N₁ = c • N₂ := by
        rw [sub_smul, one_smul, sub_eq_iff_eq_add]
        calc N₁ = c • (N₁ + N₂) := hc
          _ = c • N₂ + c • N₁ := by rw [smul_add, add_comm]
          _ = c • N₂ + c • N₁ := rfl
      have h5 : N₂ = c⁻¹ • ((1 - c) • N₁) := by
        rw [this, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [h5, smul_smul, div_eq_inv_mul]
  by_cases hr₁ : finrank K (LinearMap.range N₁) = 2
  · exact unipotent_of_rank_two hV ρ hG h11 h12 h21 hr₁ hc₁ hc₂ hind
  by_cases hr₂ : finrank K (LinearMap.range N₂) = 2
  · exact unipotent_of_rank_two hV ρ hG h22 h21 h12 hr₂ hc₂ hc₁ hind₂
  by_cases hr₃ : finrank K (LinearMap.range (N₁ + N₂)) = 2
  · exact unipotent_of_rank_two hV ρ hG h33 h31 h13 hr₃ hc₃ hc₁ hind₃
  have hr₁' : finrank K (LinearMap.range N₁) = 1 :=
    (rank_one_or_two hV h11 hN₁).resolve_right hr₁
  have hr₂' : finrank K (LinearMap.range N₂) = 1 :=
    (rank_one_or_two hV h22 hN₂).resolve_right hr₂
  have hr₃' : finrank K (LinearMap.range (N₁ + N₂)) = 1 :=
    (rank_one_or_two hV h33 hN₃).resolve_right hr₃
  by_cases hrange : LinearMap.range N₁ = LinearMap.range N₂
  · exact unipotent_of_common_range hV ρ hG h11 h21 hc₁ hc₂ hr₁' hr₂' hrange hind
  by_cases hker : LinearMap.ker N₁ = LinearMap.ker N₂
  · have hk : finrank K (LinearMap.ker N₁) = 3 := by
      have := LinearMap.finrank_range_add_finrank_ker N₁
      rw [hV] at this
      omega
    exact unipotent_of_common_ker hV ρ hG h11 h12 hc₁ hc₂ hker hk
      (by rw [finrank_sup_eq_two_of_ne hr₁' hr₂' hrange])
  · exact absurd hr₃' (rank_add_ne_one hV hr₁' hr₂' hrange hker)

theorem perfect_unipotent_of_two_nilpotents_four [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    (hV : finrank K V = 4) (ρ : G →* Module.End K V) (hG : Group.IsPerfect G)
    {N₁ N₂ : Module.End K V} (h12 : N₁ * N₂ = N₂ * N₁) (hn₁ : IsNilpotent N₁)
    (hn₂ : IsNilpotent N₂) (hc₁ : ∀ g, ρ g * N₁ = N₁ * ρ g) (hc₂ : ∀ g, ρ g * N₂ = N₂ * ρ g)
    (hN₁ : N₁ ≠ 0) (hind : ¬ (N₁ ^ 2 = 0 ∧ ∃ c : K, N₂ = c • N₁)) :
    ∀ g, ((ρ g - 1 : Module.End K V)) ^ 4 = 0 := by
  classical
  have hn₃ : IsNilpotent (N₁ + N₂) := Commute.isNilpotent_add (show Commute N₁ N₂ from h12) hn₁ hn₂
  have hc₃ : ∀ g, ρ g * (N₁ + N₂) = (N₁ + N₂) * ρ g := by
    intro g
    rw [mul_add, add_mul, hc₁, hc₂]
  by_cases hsq : N₁ ^ 2 = 0 ∧ N₂ ^ 2 = 0 ∧ (N₁ + N₂) ^ 2 = 0
  · obtain ⟨h1, h2', h3⟩ := hsq
    have h11 : N₁ * N₁ = 0 := by rw [← pow_two]; exact h1
    have h22 : N₂ * N₂ = 0 := by rw [← pow_two]; exact h2'
    have hprod : N₁ * N₂ = 0 := by
      have h33 : (N₁ + N₂) * (N₁ + N₂) = 0 := by rw [← pow_two]; exact h3
      rw [mul_add, add_mul, add_mul, h11, h22, ← h12] at h33
      have h4 : (2 : K) • (N₁ * N₂) = 0 := by
        rw [two_smul]
        simpa using h33
      exact (smul_eq_zero.1 h4).resolve_left h2
    have h21 : N₂ * N₁ = 0 := by rw [← h12]; exact hprod
    refine unipotent_of_two_square_zero hV ρ hG h11 hprod h21 h22 hc₁ hc₂ hN₁ fun c hc => ?_
    exact hind ⟨h1, c, hc⟩
  · by_cases hs1 : N₁ ^ 2 = 0
    · by_cases hs2 : N₂ ^ 2 = 0
      · have hs3 : (N₁ + N₂) ^ 2 ≠ 0 := fun h => hsq ⟨hs1, hs2, h⟩
        exact unipotent_of_sq_ne_zero hV ρ hG hn₃ hs3 hc₃
      · exact unipotent_of_sq_ne_zero hV ρ hG hn₂ hs2 hc₂
    · exact unipotent_of_sq_ne_zero hV ρ hG hn₁ hs1 hc₁

end CFSG.RankThree.PartOne.K133
