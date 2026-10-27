module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20zc
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20zf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

section Cong

variable {X : Type} [Group X] {U : Subgroup X}

theorem uc22pwe_trans {x y z : X} (h₁ : x * y⁻¹ ∈ U) (h₂ : y * z⁻¹ ∈ U) : x * z⁻¹ ∈ U := by
  have e : x * z⁻¹ = (x * y⁻¹) * (y * z⁻¹) := by group
  rw [e]
  exact mul_mem h₁ h₂

theorem uc22pwe_symm {x y : X} (hxy : x * y⁻¹ ∈ U) : y * x⁻¹ ∈ U := by
  have e : y * x⁻¹ = (x * y⁻¹)⁻¹ := by group
  rw [e]
  exact inv_mem hxy

theorem uc22pwe_mul {x₁ y₁ x₂ y₂ : X} (h₁ : x₁ * y₁⁻¹ ∈ U) (h₂ : x₂ * y₂⁻¹ ∈ U)
    (hy₁ : y₁ ∈ normalizer (U : Set X)) : x₁ * x₂ * (y₁ * y₂)⁻¹ ∈ U := by
  have e : x₁ * x₂ * (y₁ * y₂)⁻¹ = (x₁ * y₁⁻¹) * (y₁ * (x₂ * y₂⁻¹) * y₁⁻¹) := by group
  rw [e]
  exact mul_mem h₁ ((Subgroup.mem_normalizer_iff.1 hy₁ _).1 h₂)

theorem uc22pwe_inv {x y : X} (hxy : x * y⁻¹ ∈ U) (hy : y ∈ normalizer (U : Set X)) :
    x⁻¹ * y⁻¹⁻¹ ∈ U := by
  have e : x⁻¹ * y⁻¹⁻¹ = y⁻¹ * (x * y⁻¹)⁻¹ * y⁻¹⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.1 (inv_mem hy) _).1 (inv_mem hxy)

theorem uc22pwe_pow {x y : X} (hxy : x * y⁻¹ ∈ U) (hy : y ∈ normalizer (U : Set X)) (k : ℕ) :
    x ^ k * (y ^ k)⁻¹ ∈ U := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact uc22pwe_mul ih hxy (pow_mem hy k)

theorem uc22pwe_zpow {x y : X} (hxy : x * y⁻¹ ∈ U) (hy : y ∈ normalizer (U : Set X)) (k : ℤ) :
    x ^ k * (y ^ k)⁻¹ ∈ U := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [zpow_natCast, zpow_natCast]
    exact uc22pwe_pow hxy hy k
  · rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
    exact uc22pwe_inv (uc22pwe_pow hxy hy k) (pow_mem hy k)

theorem uc22pwe_map (φ : MulAut X) (hφ : ∀ x, x ∈ U ↔ φ x ∈ U) {x y : X} (hxy : x * y⁻¹ ∈ U) :
    φ x * (φ y)⁻¹ ∈ U := by
  rw [← map_inv, ← map_mul]
  exact (hφ _).1 hxy

theorem uc22pwl_pow_pow_zpow (x : X) (k N : ℕ) (s : ℤ) : ((x ^ k) ^ N) ^ s = (x ^ N) ^ ((k : ℤ) * s) := by
  rw [← pow_mul, mul_comm k N, pow_mul, ← zpow_natCast (x ^ N) k, ← zpow_mul]

theorem uc22pwl_mul_zpow {H H' : X} (hc : Commute H H') (s t c : ℤ) :
    (H ^ s * H' ^ t) ^ c = H ^ (s * c) * H' ^ (t * c) := by
  rw [(hc.zpow_zpow s t).mul_zpow, zpow_mul, zpow_mul]

theorem uc22pwl_act (φ : MulAut X) {u u' y y' : X} (hy : y ∈ normalizer (U : Set X))
    (hy' : y' ∈ normalizer (U : Set X)) (h₁ : φ u * y⁻¹ ∈ U) (h₂ : φ u' * y'⁻¹ ∈ U) (N : ℕ) (s t : ℤ) :
    φ ((u ^ N) ^ s * (u' ^ N) ^ t) * ((y ^ N) ^ s * (y' ^ N) ^ t)⁻¹ ∈ U := by
  rw [map_mul, map_zpow, map_zpow, map_pow, map_pow]
  exact uc22pwe_mul (uc22pwe_zpow (uc22pwe_pow h₁ hy N) (pow_mem hy N) s)
    (uc22pwe_zpow (uc22pwe_pow h₂ hy' N) (pow_mem hy' N) t) (zpow_mem (pow_mem hy N) s)

@[expose] def uc22pwlPowFix (U M : Subgroup X) (hM : IsMulCommutative M) (hMU : M ≤ normalizer (U : Set X))
    (φ : MulAut X) (N : ℕ) : Subgroup X where
  carrier := {y | y ∈ M ∧ φ y * (y ^ N)⁻¹ ∈ U}
  mul_mem' := by
    rintro y z ⟨hy, hyU⟩ ⟨hz, hzU⟩
    refine ⟨M.mul_mem hy hz, ?_⟩
    haveI := hM
    have hc : Commute y z := mul_comm_of_mem_isMulCommutative M hy hz
    rw [map_mul, hc.mul_pow]
    exact uc22pwe_mul hyU hzU (pow_mem (hMU hy) N)
  one_mem' := ⟨M.one_mem, by simp⟩
  inv_mem' := by
    rintro y ⟨hy, hyU⟩
    refine ⟨M.inv_mem hy, ?_⟩
    rw [map_inv, inv_pow]
    exact uc22pwe_inv hyU (pow_mem (hMU hy) N)

end Cong

section CongFinite

variable {X : Type} [Group X] [Finite X] {U : Subgroup X}

theorem uc22pwe_mem_sup_iff {Z : Subgroup X} (hZ : Z ≤ normalizer (U : Set X)) {x : X} :
    x ∈ Z ⊔ U ↔ ∃ z ∈ Z, x * z⁻¹ ∈ U := by
  constructor
  · intro hx
    obtain ⟨z, hz, u, hu, rfl⟩ := uc22pws_exists_mul_of_mem_sup hZ hx
    exact ⟨z, hz, (Subgroup.mem_normalizer_iff.1 (hZ hz) u).1 hu⟩
  · rintro ⟨z, hz, hxz⟩
    have e : x = (x * z⁻¹) * z := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_right hxz) (Subgroup.mem_sup_left hz)

theorem uc22pwl_zpowers_inv_iff {x₀ : X} (hx₀ : x₀ ∈ normalizer (U : Set X)) (φ : MulAut X) :
    (∀ x ∈ zpowers x₀, φ x ∈ zpowers x₀ ⊔ U) ↔ ∃ c : ℤ, φ x₀ * (x₀ ^ c)⁻¹ ∈ U := by
  have hZ : zpowers x₀ ≤ normalizer (U : Set X) := Subgroup.zpowers_le.2 hx₀
  constructor
  · intro h
    obtain ⟨z, hz, hzU⟩ := (uc22pwe_mem_sup_iff hZ).1 (h x₀ (mem_zpowers x₀))
    obtain ⟨c, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact ⟨c, hzU⟩
  · rintro ⟨c, hc⟩
    have hle : zpowers x₀ ≤ (zpowers x₀ ⊔ U).comap φ.toMonoidHom := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_comap.2 ((uc22pwe_mem_sup_iff hZ).2 ⟨x₀ ^ c, zpow_mem (mem_zpowers x₀) c, hc⟩)
    exact fun x hx => Subgroup.mem_comap.1 (hle hx)

theorem uc22pwl_inv_range_iff {Γ : Type} [Group Γ] {ρ : Γ →* MulAut X} {W : Subgroup X} :
    uc22pwsInv U (Set.range ρ) W ↔ ∀ g : Γ, ∀ x ∈ W, ρ g x ∈ W ⊔ U := by
  constructor
  · intro hW g x hx
    exact hW _ ⟨g, rfl⟩ x hx
  · rintro hW _ ⟨g, rfl⟩ x hx
    exact hW g x hx

theorem uc22pwl_exists_zpowers_eq {W : Subgroup X} (hW : IsCyclic W) : ∃ y ∈ W, W = zpowers y := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥W)
  refine ⟨g, g.2, le_antisymm (fun x hx => ?_) (Subgroup.zpowers_le.2 g.2)⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hx⟩)
  exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩

end CongFinite

theorem uc22pwl_diag_iff {K : Type*} [Field K] {s t x y : K} (hs : s ≠ 0) (ht : t ≠ 0) :
    (∃ c : K, x * s = c * s ∧ y * t = c * t) ↔ x = y := by
  constructor
  · rintro ⟨c, h1, h2⟩
    rw [mul_right_cancel₀ hs h1, mul_right_cancel₀ ht h2]
  · rintro rfl
    exact ⟨x, rfl, rfl⟩

theorem uc22pwl_anti_imp {K : Type*} [Field K] {s t x y : K} (h : ∃ c : K, y * t = c * s ∧ x * s = c * t) :
    x * s ^ 2 = y * t ^ 2 := by
  obtain ⟨c, h1, h2⟩ := h
  linear_combination s * h2 - t * h1

theorem uc22pwl_anti_of {K : Type*} [Field K] {s t x y : K} (ht : t ≠ 0) (h : x * s ^ 2 = y * t ^ 2) :
    ∃ c : K, y * t = c * s ∧ x * s = c * t := by
  refine ⟨x * s / t, ?_, (div_mul_cancel₀ _ ht).symm⟩
  rw [div_mul_eq_mul_div, eq_div_iff ht]
  linear_combination -h

theorem uc22pwl_two_pow_ne_zero {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (i : ℕ) :
    (((2 ^ i : ℕ) : ℤ) : ZMod q) ≠ 0 := by
  haveI : Fact q.Prime := ⟨hq⟩
  push_cast
  refine pow_ne_zero i fun h2 => ?_
  have h2' : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h2
  rw [ZMod.natCast_eq_zero_iff] at h2'
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h2')

section Pair

variable {X : Type} [Group X] [Finite X]

structure UC22pwlPair (U : Subgroup X) (q : ℕ) (H H' : X) : Prop where
  prime : q.Prime
  comm : Commute H H'
  ord : orderOf H = q
  ord' : orderOf H' = q
  disj : ∀ i j : ℤ, H ^ i = H' ^ j → H ^ i = 1
  norm : H ∈ normalizer (U : Set X)
  norm' : H' ∈ normalizer (U : Set X)
  meet : ∀ i j : ℤ, H ^ i * H' ^ j ∈ U → H ^ i * H' ^ j = 1

@[expose] def uc22pwlActD (U : Subgroup X) (H H' : X) (φ : MulAut X) (x y : ℤ) : Prop :=
  ∀ s t : ℤ, φ (H ^ s * H' ^ t) * (H ^ (x * s) * H' ^ (y * t))⁻¹ ∈ U

@[expose] def uc22pwlActA (U : Subgroup X) (H H' : X) (φ : MulAut X) (x y : ℤ) : Prop :=
  ∀ s t : ℤ, φ (H ^ s * H' ^ t) * (H ^ (y * t) * H' ^ (x * s))⁻¹ ∈ U

namespace UC22pwlPair

variable {U : Subgroup X} {q : ℕ} {H H' : X} (P : UC22pwlPair U q H H')

include P

theorem zpow_eq_one_iff (i : ℤ) : H ^ i = 1 ↔ (i : ZMod q) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← P.ord, orderOf_dvd_iff_zpow_eq_one]

theorem zpow_eq_one_iff' (i : ℤ) : H' ^ i = 1 ↔ (i : ZMod q) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← P.ord', orderOf_dvd_iff_zpow_eq_one]

theorem mem_normalizer (s t : ℤ) : H ^ s * H' ^ t ∈ normalizer (U : Set X) :=
  mul_mem (zpow_mem P.norm s) (zpow_mem P.norm' t)

theorem mul_zpow (s t c : ℤ) : (H ^ s * H' ^ t) ^ c = H ^ (s * c) * H' ^ (t * c) :=
  uc22pwl_mul_zpow P.comm s t c

theorem mul_pow (s t : ℤ) (n : ℕ) : (H ^ s * H' ^ t) ^ n = H ^ (s * n) * H' ^ (t * n) := by
  rw [← zpow_natCast, P.mul_zpow]

theorem inv_eq (s t : ℤ) : (H ^ s * H' ^ t)⁻¹ = H ^ (-s) * H' ^ (-t) := by
  rw [mul_inv_rev, zpow_neg, zpow_neg]
  exact (P.comm.zpow_zpow s t).inv_inv.symm.eq

theorem coord (s t s' t' : ℤ) :
    (H ^ s * H' ^ t) * (H ^ s' * H' ^ t')⁻¹ ∈ U ↔ (s : ZMod q) = s' ∧ (t : ZMod q) = t' := by
  have e : (H ^ s * H' ^ t) * (H ^ s' * H' ^ t')⁻¹ = H ^ (s - s') * H' ^ (t - t') := by
    have hc : H' ^ (t - t') * H ^ (-s') = H ^ (-s') * H' ^ (t - t') :=
      (P.comm.zpow_zpow (-s') (t - t')).symm.eq
    calc (H ^ s * H' ^ t) * (H ^ s' * H' ^ t')⁻¹ = H ^ s * (H' ^ (t - t') * H ^ (-s')) := by group
      _ = H ^ s * (H ^ (-s') * H' ^ (t - t')) := by rw [hc]
      _ = H ^ (s - s') * H' ^ (t - t') := by group
  rw [e]
  constructor
  · intro hmem
    have h1 := P.meet _ _ hmem
    have h2 : H ^ (s - s') = 1 :=
      P.disj _ (-(t - t')) (by rw [zpow_neg]; exact eq_inv_of_mul_eq_one_left h1)
    have h3 : H' ^ (t - t') = 1 := by
      rw [h2, one_mul] at h1
      exact h1
    rw [P.zpow_eq_one_iff] at h2
    rw [P.zpow_eq_one_iff'] at h3
    push_cast at h2 h3
    exact ⟨sub_eq_zero.1 h2, sub_eq_zero.1 h3⟩
  · rintro ⟨hs, ht⟩
    rw [(P.zpow_eq_one_iff _).2 (by push_cast; rw [hs, sub_self]),
      (P.zpow_eq_one_iff' _).2 (by push_cast; rw [ht, sub_self]), one_mul]
    exact one_mem U

theorem eq_iff (s t s' t' : ℤ) :
    H ^ s * H' ^ t = H ^ s' * H' ^ t' ↔ (s : ZMod q) = s' ∧ (t : ZMod q) = t' := by
  constructor
  · intro h
    exact (P.coord s t s' t').1 (by rw [h, mul_inv_cancel]; exact one_mem U)
  · rintro ⟨hs, ht⟩
    have h1 : H ^ (s - s') = 1 := (P.zpow_eq_one_iff _).2 (by push_cast; rw [hs, sub_self])
    have h2 : H' ^ (t - t') = 1 := (P.zpow_eq_one_iff' _).2 (by push_cast; rw [ht, sub_self])
    rw [zpow_sub, mul_inv_eq_one] at h1 h2
    rw [h1, h2]

theorem eq_one_iff (s t : ℤ) : H ^ s * H' ^ t = 1 ↔ (s : ZMod q) = 0 ∧ (t : ZMod q) = 0 := by
  have := P.eq_iff s t 0 0
  rwa [zpow_zero, zpow_zero, one_mul, Int.cast_zero] at this

theorem pow_q (s t : ℤ) : (H ^ s * H' ^ t) ^ q = 1 := by
  rw [P.mul_pow, P.eq_one_iff]
  push_cast
  simp [ZMod.natCast_self]

theorem orderOf_eq {s t : ℤ} (hne : ¬ ((s : ZMod q) = 0 ∧ (t : ZMod q) = 0)) :
    orderOf (H ^ s * H' ^ t) = q := by
  haveI : Fact q.Prime := ⟨P.prime⟩
  exact orderOf_eq_prime (P.pow_q s t) fun h => hne ((P.eq_one_iff s t).1 h)

theorem card_line {s t : ℤ} (hne : ¬ ((s : ZMod q) = 0 ∧ (t : ZMod q) = 0)) :
    Nat.card (zpowers (H ^ s * H' ^ t)) = q := by
  rw [Nat.card_zpowers, P.orderOf_eq hne]

theorem line_min {s t : ℤ} (hne : ¬ ((s : ZMod q) = 0 ∧ (t : ZMod q) = 0)) {W : Subgroup X}
    (hW : W ≤ zpowers (H ^ s * H' ^ t)) : W = ⊥ ∨ W = zpowers (H ^ s * H' ^ t) := by
  have hd : Nat.card W ∣ q := P.card_line hne ▸ Subgroup.card_dvd_of_le hW
  rcases (Nat.dvd_prime P.prime).1 hd with h1 | h1
  · exact Or.inl (Subgroup.eq_bot_of_card_eq W h1)
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hW (le_of_eq ((P.card_line hne).trans h1.symm)))

theorem line_inv_iff (φ : MulAut X) {s t σ θ : ℤ}
    (hact : φ (H ^ s * H' ^ t) * (H ^ σ * H' ^ θ)⁻¹ ∈ U) :
    (∀ z ∈ zpowers (H ^ s * H' ^ t), φ z ∈ zpowers (H ^ s * H' ^ t) ⊔ U) ↔
      ∃ c : ZMod q, (σ : ZMod q) = c * s ∧ (θ : ZMod q) = c * t := by
  rw [uc22pwl_zpowers_inv_iff (P.mem_normalizer s t) φ]
  constructor
  · rintro ⟨c, hc⟩
    have h1 := uc22pwe_trans (uc22pwe_symm hact) hc
    rw [P.mul_zpow, P.coord] at h1
    exact ⟨c, by rw [h1.1, Int.cast_mul, mul_comm], by rw [h1.2, Int.cast_mul, mul_comm]⟩
  · rintro ⟨c, hcs, hct⟩
    obtain ⟨c', rfl⟩ := ZMod.intCast_surjective c
    refine ⟨c', uc22pwe_trans hact ?_⟩
    rw [P.mul_zpow, P.coord]
    exact ⟨by rw [hcs, Int.cast_mul, mul_comm], by rw [hct, Int.cast_mul, mul_comm]⟩

theorem inv_diag_iff {φ : MulAut X} {x y : ℤ} (hD : uc22pwlActD U H H' φ x y) {s t : ℤ}
    (hs : (s : ZMod q) ≠ 0) (ht : (t : ZMod q) ≠ 0) :
    (∀ z ∈ zpowers (H ^ s * H' ^ t), φ z ∈ zpowers (H ^ s * H' ^ t) ⊔ U) ↔ (x : ZMod q) = y := by
  haveI : Fact q.Prime := ⟨P.prime⟩
  rw [P.line_inv_iff φ (hD s t)]
  simp only [Int.cast_mul]
  exact uc22pwl_diag_iff hs ht

theorem inv_diag_of {φ : MulAut X} {x y : ℤ} (hD : uc22pwlActD U H H' φ x y) (hxy : (x : ZMod q) = y)
    (s t : ℤ) : ∀ z ∈ zpowers (H ^ s * H' ^ t), φ z ∈ zpowers (H ^ s * H' ^ t) ⊔ U := by
  rw [P.line_inv_iff φ (hD s t)]
  exact ⟨x, by rw [Int.cast_mul], by rw [Int.cast_mul, hxy]⟩

theorem inv_anti_imp {φ : MulAut X} {x y : ℤ} (hA : uc22pwlActA U H H' φ x y) {s t : ℤ}
    (h : ∀ z ∈ zpowers (H ^ s * H' ^ t), φ z ∈ zpowers (H ^ s * H' ^ t) ⊔ U) :
    (x : ZMod q) * s ^ 2 = y * t ^ 2 := by
  haveI : Fact q.Prime := ⟨P.prime⟩
  have h1 := (P.line_inv_iff φ (hA s t)).1 h
  simp only [Int.cast_mul] at h1
  exact uc22pwl_anti_imp h1

theorem inv_anti_of {φ : MulAut X} {x y : ℤ} (hA : uc22pwlActA U H H' φ x y) {s t : ℤ}
    (ht : (t : ZMod q) ≠ 0) (h : (x : ZMod q) * s ^ 2 = y * t ^ 2) :
    ∀ z ∈ zpowers (H ^ s * H' ^ t), φ z ∈ zpowers (H ^ s * H' ^ t) ⊔ U := by
  haveI : Fact q.Prime := ⟨P.prime⟩
  rw [P.line_inv_iff φ (hA s t)]
  simp only [Int.cast_mul]
  exact uc22pwl_anti_of ht h

theorem tau_line {φ : MulAut X} {y : ℤ} (hy : (y : ZMod q) ≠ 0) (hA : uc22pwlActA U H H' φ 1 y) {s t : ℤ}
    (h : ∀ z ∈ zpowers (H ^ s * H' ^ t), φ z ∈ zpowers (H ^ s * H' ^ t) ⊔ U) :
    (s : ZMod q) = 0 ↔ (t : ZMod q) = 0 := by
  haveI : Fact q.Prime := ⟨P.prime⟩
  have h1 := P.inv_anti_imp hA h
  simp only [Int.cast_one, one_mul] at h1
  constructor
  · intro hs
    rw [hs, zero_pow two_ne_zero] at h1
    exact pow_eq_zero_iff two_ne_zero |>.1 ((mul_eq_zero.1 h1.symm).resolve_left hy)
  · intro ht
    rw [ht, zero_pow two_ne_zero, mul_zero] at h1
    exact pow_eq_zero_iff two_ne_zero |>.1 h1

end UC22pwlPair

end Pair

section PairGamma

variable {X Γ : Type} [Group X] [Finite X] [Group Γ] {U : Subgroup X} {q : ℕ} {H H' : X}

namespace UC22pwlPair

variable (P : UC22pwlPair U q H H')

include P

theorem inv_of_sq {ρ : Γ →* MulAut X} {τ : Γ}
    (hsh : ∀ g : Γ, (∃ x y : ℤ, uc22pwlActD U H H' (ρ g) x y) ∨ ∃ x y : ℤ, uc22pwlActA U H H' (ρ g) x y)
    {y₀ : ℤ} (hy₀ : (y₀ : ZMod q) ≠ 0) (hτ : uc22pwlActA U H H' (ρ τ) 1 y₀) {s t s' t' : ℤ}
    (hinv : uc22pwsInv U (Set.range ρ) (zpowers (H ^ s * H' ^ t))) (ht : (t : ZMod q) ≠ 0)
    (ht' : (t' : ZMod q) ≠ 0) (hsq : (s' : ZMod q) ^ 2 * t ^ 2 = s ^ 2 * t' ^ 2) :
    uc22pwsInv U (Set.range ρ) (zpowers (H ^ s' * H' ^ t')) := by
  haveI : Fact q.Prime := ⟨P.prime⟩
  rw [uc22pwl_inv_range_iff] at hinv ⊢
  have hs : (s : ZMod q) ≠ 0 := fun h0 => ht ((P.tau_line hy₀ hτ (hinv τ)).1 h0)
  intro g
  rcases hsh g with ⟨x, y, hD⟩ | ⟨x, y, hA⟩
  · exact P.inv_diag_of hD ((P.inv_diag_iff hD hs ht).1 (hinv g)) s' t'
  · refine P.inv_anti_of hA ht' ?_
    have h1 := P.inv_anti_imp hA (hinv g)
    refine mul_right_cancel₀ (pow_ne_zero 2 ht) ?_
    linear_combination (x : ZMod q) * hsq + (t' : ZMod q) ^ 2 * h1

end UC22pwlPair

end PairGamma

theorem uc22pwl_alike_of_pow {X : Type} [Group X] [Finite X] {J : Subgroup X} (hJ : IsMulCommutative J)
    {r : ℕ} (hr : ∀ x ∈ J, x ^ r = 1 → x = 1) {φ₁ φ₂ : MulAut X} {K₁ K₂ : ℕ}
    (h₁ : ∀ x ∈ J, φ₁ x = x ^ (r ^ K₁)) (h₂ : ∀ x ∈ J, φ₂ x = x ^ (r ^ K₂))
    (hi₁ : ∀ x ∈ J, φ₁ (φ₁ x) = x) (hn₁ : ∃ x ∈ J, φ₁ x ≠ x)
    (hi₂ : ∀ x ∈ J, φ₂ (φ₂ x) = x) (hn₂ : ∃ x ∈ J, φ₂ x ≠ x) : ∀ x ∈ J, φ₁ x = φ₂ x := by
  have hcomm : ∀ x y : J, x * y = y * x := fun x y =>
    Subtype.ext (Subgroup.mul_comm_of_mem_isMulCommutative J x.2 y.2)
  let pw : J →* J :=
    { toFun := fun x => x ^ r
      map_one' := one_pow r
      map_mul' := fun x y => Commute.mul_pow (hcomm x y) r }
  have hinj : Function.Injective pw := by
    intro x y hxy
    have h1 : (x * y⁻¹) ^ r = 1 := by
      rw [Commute.mul_pow (hcomm x y⁻¹) r]
      change x ^ r = y ^ r at hxy
      rw [hxy, inv_pow, mul_inv_cancel]
    have h2 : ((x * y⁻¹ : J) : X) = 1 := hr _ (x * y⁻¹).2 (by simpa using congrArg Subtype.val h1)
    exact mul_inv_eq_one.1 (Subtype.ext (by simpa using h2))
  let σ : MulAut J := MulEquiv.ofBijective pw ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
  have hσ : ∀ (K : ℕ) (x : J), (σ ^ K) x = x ^ (r ^ K) := by
    intro K
    induction K with
    | zero => intro x; simp
    | succ K ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, ih]
      change (x ^ r) ^ r ^ K = x ^ r ^ (K + 1)
      rw [← pow_mul, pow_succ, mul_comm]
  have hφ : ∀ (φ : MulAut X) (K : ℕ), (∀ x ∈ J, φ x = x ^ (r ^ K)) → ∀ x : J, ((σ ^ K) x : X) = φ x := by
    intro φ K hK x
    rw [hσ, hK x x.2, Subgroup.coe_pow]
  have hinv : ∀ (φ : MulAut X) (K : ℕ), (∀ x ∈ J, φ x = x ^ (r ^ K)) → (∀ x ∈ J, φ (φ x) = x) →
      ∀ x ∈ (⊤ : Subgroup J), (σ ^ K) ((σ ^ K) x) = x := by
    intro φ K hK hi x _
    apply Subtype.ext
    rw [hφ φ K hK, hφ φ K hK x]
    exact hi x x.2
  have hne : ∀ (φ : MulAut X) (K : ℕ), (∀ x ∈ J, φ x = x ^ (r ^ K)) → (∃ x ∈ J, φ x ≠ x) →
      ∃ x ∈ (⊤ : Subgroup J), (σ ^ K) x ≠ x := by
    rintro φ K hK ⟨x, hx, hne⟩
    exact ⟨⟨x, hx⟩, Subgroup.mem_top _, fun h =>
      hne ((hφ φ K hK ⟨x, hx⟩).symm.trans (congrArg Subtype.val h))⟩
  have key := uc22pwc_pow_alike σ ⊤ (k := K₁) (l := K₂)
    (fun _ => iff_of_true (Subgroup.mem_top _) (Subgroup.mem_top _))
    (fun _ => iff_of_true (Subgroup.mem_top _) (Subgroup.mem_top _))
    (hinv φ₁ K₁ h₁ hi₁) (hne φ₁ K₁ h₁ hn₁) (hinv φ₂ K₂ h₂ hi₂) (hne φ₂ K₂ h₂ hn₂)
  intro x hx
  rw [← hφ φ₁ K₁ h₁ ⟨x, hx⟩, ← hφ φ₂ K₂ h₂ ⟨x, hx⟩, key ⟨x, hx⟩ (Subgroup.mem_top _)]

theorem uc22pwl_powFix_of_two {X : Type} [Group X] {U M : Subgroup X} {hM : IsMulCommutative M}
    {hMU : M ≤ normalizer (U : Set X)} {φ : MulAut X} {y : X} (hyM : y ∈ M) {q r K : ℕ} (hyq : y ^ q = 1)
    (hr : r ≡ 2 [MOD q]) (hy : φ y * (y ^ 2 ^ K)⁻¹ ∈ U) : y ∈ uc22pwlPowFix U M hM hMU φ (r ^ K) := by
  refine ⟨hyM, ?_⟩
  have e : y ^ (r ^ K) = y ^ (2 ^ K) := by
    rw [pow_eq_pow_iff_modEq]
    exact (hr.pow K).of_dvd (orderOf_dvd_of_pow_eq_one hyq)
  rw [e]
  exact hy

theorem uc22pwl_powFix_of_one {X : Type} [Group X] {U M : Subgroup X} {hM : IsMulCommutative M}
    {hMU : M ≤ normalizer (U : Set X)} {φ : MulAut X} {y : X} (hyM : y ∈ M) {q r K : ℕ} (hyq : y ^ q = 1)
    (hr : r ≡ 1 [MOD q]) (hy : φ y * y⁻¹ ∈ U) : y ∈ uc22pwlPowFix U M hM hMU φ (r ^ K) := by
  refine ⟨hyM, ?_⟩
  have e : y ^ (r ^ K) = y ^ 1 := by
    rw [pow_eq_pow_iff_modEq]
    have := (hr.pow K).of_dvd (orderOf_dvd_of_pow_eq_one hyq)
    rwa [one_pow] at this
  rw [e, pow_one]
  exact hy

@[expose] def uc22pwlAlike {X Γ : Type} [Group X] [Group Γ] (ρ : Γ →* MulAut X) (J : Subgroup X) : Prop :=
  ∀ g₁ g₂ : Γ, (∀ x ∈ J, ρ g₁ x ∈ J) → (∀ x ∈ J, ρ g₂ x ∈ J) → (∀ x ∈ J, ρ g₁ (ρ g₁ x) = x) →
    (∃ x ∈ J, ρ g₁ x ≠ x) → (∀ x ∈ J, ρ g₂ (ρ g₂ x) = x) → (∃ x ∈ J, ρ g₂ x ≠ x) → ∀ x ∈ J, ρ g₁ x = ρ g₂ x

@[expose] def uc22pwlLam {X Γ : Type} [Group X] [Finite X] [Group Γ] (ρ : Γ →* MulAut X) (U : Subgroup X)
    (h h' : X) (m b q : ℕ) : Prop :=
  q.Prime ∧ q ∣ b ∧ ∃ s t : ℤ, (t : ZMod q) ≠ 0 ∧
    uc22pwsInv U (Set.range ρ) (zpowers ((h ^ (m / q)) ^ s * (h' ^ (m / q)) ^ t))

section ElemLines

variable {X Γ : Type} [Group X] [Group Γ] [Finite X]

namespace UC22pwtElem

variable {ρ : Γ →* MulAut X} {τ : Γ} {U A₁ A₂ : Subgroup X} {C : UC22pwtCtx ρ τ U A₁ A₂}
  {h w₁ : X} {m a b : ℕ} {α : Set ℕ} (El : UC22pwtElem C h w₁ m a b α)

include El

theorem E_le_normalizer : uc22pwtE h (ρ τ h) a b ≤ normalizer (U : Set X) := by
  refine sup_le (sup_le ?_ ?_) ?_
  · exact Subgroup.zpowers_le.2 (Subgroup.pow_mem _ El.h_norm a)
  · exact Subgroup.zpowers_le.2 (Subgroup.pow_mem _ El.h'_norm a)
  · exact Subgroup.zpowers_le.2 (mul_mem (Subgroup.pow_mem _ El.h_norm b) (Subgroup.pow_mem _ El.h'_norm b))

theorem eq_one_of_mem (hU : IsPGroup 2 U) {x : X} (hxE : x ∈ uc22pwtE h (ρ τ h) a b) (hxU : x ∈ U) :
    x = 1 :=
  uc22pws_eq_one_of_mem_inf hU El.pair.odd_card_E hxE hxU

theorem q_ne_two {q : ℕ} (hqb : q ∣ b) : q ≠ 2 := by
  rintro rfl
  have h2 : 2 ∣ m := El.ab ▸ dvd_mul_of_dvd_right hqb a
  exact (Nat.not_even_iff_odd.2 El.odd) (even_iff_two_dvd.2 h2)

theorem mem_primeFactors_iff {q : ℕ} :
    q ∈ (Nat.card (uc22pwtE h (ρ τ h) a b)).primeFactors ↔ q.Prime ∧ q ∣ m := by
  have h1 := Set.ext_iff.1 El.pair.piSet_E q
  simp only [piSet, Set.mem_setOf_eq] at h1
  rw [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hq, hd, -⟩
    exact h1.1 ⟨hq, hd⟩
  · rintro ⟨hq, hd⟩
    exact ⟨hq, (h1.2 ⟨hq, hd⟩).2, Nat.card_pos.ne'⟩

theorem pairAt (hU : IsPGroup 2 U) {q : ℕ} (hq : q.Prime) (hqb : q ∣ b) :
    h ^ (m / q) ∈ uc22pwtE h (ρ τ h) a b ∧ (ρ τ h) ^ (m / q) ∈ uc22pwtE h (ρ τ h) a b ∧
      UC22pwlPair U q (h ^ (m / q)) ((ρ τ h) ^ (m / q)) := by
  have P := El.pair
  obtain ⟨b', hb'⟩ := hqb
  have hm0 : m ≠ 0 := El.odd.pos.ne'
  have hmq : m = q * (a * b') := by rw [← El.ab, hb']; ring
  have hdiv : m / q = a * b' := by rw [hmq, Nat.mul_div_cancel_left _ hq.pos]
  have hqm : q ∣ m := ⟨a * b', hmq⟩
  have hHE : h ^ (m / q) ∈ uc22pwtE h (ρ τ h) a b := by
    rw [hdiv, pow_mul]
    exact pow_mem (uc22pwtE_ha_mem _ _ a b) b'
  have hH'E : (ρ τ h) ^ (m / q) ∈ uc22pwtE h (ρ τ h) a b := by
    rw [hdiv, pow_mul]
    exact pow_mem (uc22pwtE_ha'_mem _ _ a b) b'
  refine ⟨hHE, hH'E, ⟨hq, P.comm.pow_pow _ _, ?_, ?_, ?_, pow_mem El.h_norm _, pow_mem El.h'_norm _, ?_⟩⟩
  · have h1 := orderOf_pow_orderOf_div (x := h) (n := q) (by rw [El.ord]; exact hm0) (by rw [El.ord]; exact hqm)
    rwa [El.ord] at h1
  · have h1 := orderOf_pow_orderOf_div (x := ρ τ h) (n := q) (by rw [El.ord']; exact hm0)
      (by rw [El.ord']; exact hqm)
    rwa [El.ord'] at h1
  · intro i j hij
    rw [← zpow_natCast h, ← zpow_mul, ← zpow_natCast (ρ τ h), ← zpow_mul] at hij
    rw [← zpow_natCast h, ← zpow_mul]
    exact P.disj _ _ hij
  · intro i j hij
    exact El.eq_one_of_mem hU (mul_mem (zpow_mem hHE i) (zpow_mem hH'E j)) hij

theorem shape (hGal : ∀ g ∈ uc22pwtStab2 ρ A₁ A₂, ∃ i : ℕ, ρ g h * (h ^ 2 ^ i)⁻¹ ∈ U) (g : Γ) :
    (∃ i j : ℕ, ρ g h * (h ^ 2 ^ i)⁻¹ ∈ U ∧ ρ g (ρ τ h) * ((ρ τ h) ^ 2 ^ j)⁻¹ ∈ U) ∨
      ∃ i k : ℕ, ρ g h * ((ρ τ h) ^ 2 ^ i)⁻¹ ∈ U ∧ ρ g (ρ τ h) * (h ^ 2 ^ k)⁻¹ ∈ U := by
  have hτU : ∀ x, x ∈ U ↔ ρ τ x ∈ U := C.Uinv τ
  have hstab : ∀ g ∈ uc22pwtStab2 ρ A₁ A₂, ∃ j : ℕ, ρ g (ρ τ h) * ((ρ τ h) ^ 2 ^ j)⁻¹ ∈ U := by
    intro g hg
    obtain ⟨j, hj⟩ := hGal _ (C.stab_conj hg)
    refine ⟨j, ?_⟩
    rw [uc22pwt_apply_conj ρ τ g h, ← map_pow]
    exact uc22pwe_map (ρ τ) hτU hj
  rcases C.perm g with hg | hg
  · obtain ⟨i, hi⟩ := hGal g hg
    obtain ⟨j, hj⟩ := hstab g hg
    exact Or.inl ⟨i, j, hi, hj⟩
  · obtain ⟨i, hi⟩ := hGal _ hg
    obtain ⟨j, hj⟩ := hstab _ hg
    obtain ⟨i₀, hi₀⟩ := hGal _ C.stab_ττ
    have e : g = τ * (τ⁻¹ * g) := by group
    refine Or.inr ⟨i, i₀ + j, ?_, ?_⟩
    · rw [e, uc22pwt_apply_mul, ← map_pow]
      exact uc22pwe_map (ρ τ) hτU hi
    · have h1 : ρ g (ρ τ h) * (ρ τ ((ρ τ h) ^ 2 ^ j))⁻¹ ∈ U := by
        rw [e, uc22pwt_apply_mul]
        exact uc22pwe_map (ρ τ) hτU hj
      rw [map_pow, ← uc22pwt_apply_mul ρ τ τ h] at h1
      have h3 := uc22pwe_trans h1 (uc22pwe_pow hi₀ (pow_mem El.h_norm (2 ^ i₀)) (2 ^ j))
      rwa [← pow_mul, ← pow_add] at h3

theorem actD {g : Γ} {i j : ℕ} (hi : ρ g h * (h ^ 2 ^ i)⁻¹ ∈ U)
    (hj : ρ g (ρ τ h) * ((ρ τ h) ^ 2 ^ j)⁻¹ ∈ U) (N : ℕ) :
    uc22pwlActD U (h ^ N) ((ρ τ h) ^ N) (ρ g) ((2 ^ i : ℕ) : ℤ) ((2 ^ j : ℕ) : ℤ) := by
  intro s t
  have h1 := uc22pwl_act (ρ g) (pow_mem El.h_norm _) (pow_mem El.h'_norm _) hi hj N s t
  rwa [uc22pwl_pow_pow_zpow h (2 ^ i) N s, uc22pwl_pow_pow_zpow (ρ τ h) (2 ^ j) N t] at h1

theorem actA {g : Γ} {i k : ℕ} (hi : ρ g h * ((ρ τ h) ^ 2 ^ i)⁻¹ ∈ U)
    (hk : ρ g (ρ τ h) * (h ^ 2 ^ k)⁻¹ ∈ U) (N : ℕ) :
    uc22pwlActA U (h ^ N) ((ρ τ h) ^ N) (ρ g) ((2 ^ i : ℕ) : ℤ) ((2 ^ k : ℕ) : ℤ) := by
  intro s t
  have h1 := uc22pwl_act (ρ g) (pow_mem El.h'_norm _) (pow_mem El.h_norm _) hi hk N s t
  rw [uc22pwl_pow_pow_zpow (ρ τ h) (2 ^ i) N s, uc22pwl_pow_pow_zpow h (2 ^ k) N t] at h1
  rwa [((El.pair.comm.pow_pow N N).zpow_zpow (((2 ^ k : ℕ) : ℤ) * t)
    (((2 ^ i : ℕ) : ℤ) * s)).symm.eq] at h1

theorem shapeAt (hGal : ∀ g ∈ uc22pwtStab2 ρ A₁ A₂, ∃ i : ℕ, ρ g h * (h ^ 2 ^ i)⁻¹ ∈ U) (N : ℕ) (g : Γ) :
    (∃ x y : ℤ, uc22pwlActD U (h ^ N) ((ρ τ h) ^ N) (ρ g) x y) ∨
      ∃ x y : ℤ, uc22pwlActA U (h ^ N) ((ρ τ h) ^ N) (ρ g) x y := by
  rcases El.shape hGal g with ⟨i, j, hi, hj⟩ | ⟨i, k, hi, hk⟩
  · exact Or.inl ⟨_, _, El.actD hi hj N⟩
  · exact Or.inr ⟨_, _, El.actA hi hk N⟩

theorem tauAt (hGal : ∀ g ∈ uc22pwtStab2 ρ A₁ A₂, ∃ i : ℕ, ρ g h * (h ^ 2 ^ i)⁻¹ ∈ U) (N : ℕ) :
    ∃ i₀ : ℕ, uc22pwlActA U (h ^ N) ((ρ τ h) ^ N) (ρ τ) 1 ((2 ^ i₀ : ℕ) : ℤ) := by
  obtain ⟨i₀, hi₀⟩ := hGal _ C.stab_ττ
  refine ⟨i₀, ?_⟩
  have h1 : ρ τ h * ((ρ τ h) ^ 2 ^ 0)⁻¹ ∈ U := by
    rw [pow_zero, pow_one, mul_inv_cancel]
    exact one_mem U
  have h2 : ρ τ (ρ τ h) * (h ^ 2 ^ i₀)⁻¹ ∈ U := by
    rw [← uc22pwt_apply_mul ρ τ τ h]
    exact hi₀
  have h3 := El.actA h1 h2 N
  have e : ((2 ^ 0 : ℕ) : ℤ) = 1 := by norm_num
  rwa [e] at h3

theorem decomp {q : ℕ} (hq : q.Prime) (hqb : q ∣ b) {x : X}
    (hx : x ∈ pCoreOf q (uc22pwtE h (ρ τ h) a b)) :
    ∃ s t : ℤ, x = (h ^ (m / q)) ^ s * ((ρ τ h) ^ (m / q)) ^ t := by
  have P := El.pair
  have hxE : x ∈ uc22pwtE h (ρ τ h) a b := ((uc22pws_mem_pCoreOf_iff hq P.isMulCommutative_E).1 hx).1
  have hxq : x ^ q = 1 := (uc22pws_pCoreOf_elem P.isMulCommutative_E P.rank_E hq).1 x hx
  obtain ⟨u, v, rfl⟩ := P.exists_zpow_of_mem_M (uc22pwtE_le_M _ _ a b hxE)
  have h1 : h ^ (u * q) * (ρ τ h) ^ (v * q) = 1 := by
    rw [← uc22pwl_mul_zpow P.comm, zpow_natCast]
    exact hxq
  have h2 : h ^ (u * q) = 1 :=
    P.disj _ (-(v * q)) (by rw [zpow_neg]; exact eq_inv_of_mul_eq_one_left h1)
  have h3 : (ρ τ h) ^ (v * q) = 1 := by
    rw [h2, one_mul] at h1
    exact h1
  rw [← orderOf_dvd_iff_zpow_eq_one, P.ord] at h2
  rw [← orderOf_dvd_iff_zpow_eq_one, P.ord'] at h3
  have hqm : q ∣ m := El.ab ▸ dvd_mul_of_dvd_right hqb a
  have hmq : ((m / q : ℕ) : ℤ) * q = m := by exact_mod_cast Nat.div_mul_cancel hqm
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  obtain ⟨s, hs⟩ : ((m / q : ℕ) : ℤ) ∣ u :=
    (mul_dvd_mul_iff_right hq0).1 (by rw [hmq]; exact h2)
  obtain ⟨t, ht⟩ : ((m / q : ℕ) : ℤ) ∣ v :=
    (mul_dvd_mul_iff_right hq0).1 (by rw [hmq]; exact h3)
  refine ⟨s, t, ?_⟩
  rw [hs, ht, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]

theorem line_le_pCore (hU : IsPGroup 2 U) {q : ℕ} (hq : q.Prime) (hqb : q ∣ b) (s t : ℤ) :
    zpowers ((h ^ (m / q)) ^ s * ((ρ τ h) ^ (m / q)) ^ t) ≤ pCoreOf q (uc22pwtE h (ρ τ h) a b) := by
  obtain ⟨hHE, hH'E, Pq⟩ := El.pairAt hU hq hqb
  rw [Subgroup.zpowers_le, uc22pws_mem_pCoreOf_iff hq El.pair.isMulCommutative_E]
  exact ⟨mul_mem (zpow_mem hHE s) (zpow_mem hH'E t), 1, by rw [pow_one]; exact Pq.pow_q s t⟩

theorem fix_pCore {q : ℕ} (hq : q.Prime) (hqa : q ∣ a) {x : X}
    (hx : x ∈ pCoreOf q (uc22pwtE h (ρ τ h) a b)) (g : Γ) : ρ g x * x⁻¹ ∈ U := by
  have P := El.pair
  have hxE := ((uc22pws_mem_pCoreOf_iff hq P.isMulCommutative_E).1 hx).1
  have hxq : x ^ q = 1 := (uc22pws_pCoreOf_elem P.isMulCommutative_E P.rank_E hq).1 x hx
  have hqm : q ∣ m := El.ab ▸ dvd_mul_of_dvd_left hqa b
  have hqα : q ∈ α := (El.pr q hq hqm).2 hqa
  refine El.alpha_clause g x (uc22pwtb_mem_oPi P.isMulCommutative_E hxE fun p hp hpd => ?_)
  rw [(Nat.prime_dvd_prime_iff_eq hp hq).1 (hpd.trans (orderOf_dvd_of_pow_eq_one hxq))]
  exact hqα

theorem classify (hU : IsPGroup 2 U) (hGal : ∀ g ∈ uc22pwtStab2 ρ A₁ A₂, ∃ i : ℕ, ρ g h * (h ^ 2 ^ i)⁻¹ ∈ U)
    {q : ℕ} (hq : q.Prime) (hqb : q ∣ b) {W : Subgroup X} (hWle : W ≤ pCoreOf q (uc22pwtE h (ρ τ h) a b))
    (hWinv : uc22pwsInv U (Set.range ρ) W) (hW0 : W ≠ ⊥) :
    W = pCoreOf q (uc22pwtE h (ρ τ h) a b) ∨ ∃ s t : ℤ, (s : ZMod q) ≠ 0 ∧ (t : ZMod q) ≠ 0 ∧
      W = zpowers ((h ^ (m / q)) ^ s * ((ρ τ h) ^ (m / q)) ^ t) := by
  have P := El.pair
  obtain ⟨-, -, Pq⟩ := El.pairAt hU hq hqb
  have hcard := (uc22pws_pCoreOf_elem P.isMulCommutative_E P.rank_E hq).2
  rcases uc22pws_card_cases hq P.isMulCommutative_E hWle hW0 hcard with h1 | h2
  · right
    obtain ⟨y, hyW, hy1⟩ := (Subgroup.bot_or_exists_ne_one W).resolve_left hW0
    obtain ⟨s, t, rfl⟩ := El.decomp hq hqb (hWle hyW)
    have hne : ¬ ((s : ZMod q) = 0 ∧ (t : ZMod q) = 0) := fun h0 => hy1 ((Pq.eq_one_iff s t).2 h0)
    have hW : W = zpowers ((h ^ (m / q)) ^ s * ((ρ τ h) ^ (m / q)) ^ t) :=
      (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hyW)
        (le_of_eq (h1.trans (Pq.card_line hne).symm))).symm
    rw [hW] at hWinv
    obtain ⟨i₀, hτ⟩ := El.tauAt hGal (m / q)
    have key := Pq.tau_line (uc22pwl_two_pow_ne_zero hq (El.q_ne_two hqb) i₀) hτ
      ((uc22pwl_inv_range_iff.1 hWinv) τ)
    exact ⟨s, t, fun hs => hne ⟨hs, key.1 hs⟩, fun ht => hne ⟨key.2 ht, ht⟩, hW⟩
  · left
    exact Subgroup.eq_of_le_of_card_ge hWle (by rw [h2]; exact hcard)

theorem lam_of_cyclic (hU : IsPGroup 2 U)
    (hGal : ∀ g ∈ uc22pwtStab2 ρ A₁ A₂, ∃ i : ℕ, ρ g h * (h ^ 2 ^ i)⁻¹ ∈ U) {q : ℕ} (hq : q.Prime)
    (hqb : q ∣ b) {W : Subgroup X} (hWle : W ≤ pCoreOf q (uc22pwtE h (ρ τ h) a b))
    (hWinv : uc22pwsInv U (Set.range ρ) W) (hW0 : W ≠ ⊥) (hcyc : IsCyclic W) :
    uc22pwlLam ρ U h (ρ τ h) m b q := by
  obtain ⟨-, -, Pq⟩ := El.pairAt hU hq hqb
  obtain ⟨y, hyW, rfl⟩ := uc22pwl_exists_zpowers_eq hcyc
  obtain ⟨s, t, rfl⟩ := El.decomp hq hqb (hWle hyW)
  obtain ⟨i₀, hτ⟩ := El.tauAt hGal (m / q)
  have key := Pq.tau_line (uc22pwl_two_pow_ne_zero hq (El.q_ne_two hqb) i₀) hτ
    ((uc22pwl_inv_range_iff.1 hWinv) τ)
  refine ⟨hq, hqb, s, t, fun ht => hW0 ?_, hWinv⟩
  rw [(Pq.eq_one_iff s t).2 ⟨key.2 ht, ht⟩, zpowers_one_eq_bot]

theorem coef_of_inv (hU : IsPGroup 2 U) {q : ℕ} (hq : q.Prime) (hqb : q ∣ b) {s t : ℤ}
    (ht : (t : ZMod q) ≠ 0)
    (hinv : uc22pwsInv U (Set.range ρ) (zpowers ((h ^ (m / q)) ^ s * ((ρ τ h) ^ (m / q)) ^ t)))
    {J : Subgroup X} (hxJ : (h ^ (m / q)) ^ s * ((ρ τ h) ^ (m / q)) ^ t ∈ J)
    (hJE : J ≤ uc22pwtE h (ρ τ h) a b) {g : Γ} (hFg : ∀ x ∈ J, ρ g x ∈ J)
    (hig : ∀ x ∈ J, ρ g (ρ g x) = x) :
    ∃ c : ℤ, (c : ZMod q) ^ 2 = 1 ∧ ρ g ((h ^ (m / q)) ^ s * ((ρ τ h) ^ (m / q)) ^ t) *
      (((h ^ (m / q)) ^ s * ((ρ τ h) ^ (m / q)) ^ t) ^ c)⁻¹ ∈ U := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨-, -, Pq⟩ := El.pairAt hU hq hqb
  obtain ⟨c, hc⟩ := (uc22pwl_zpowers_inv_iff (Pq.mem_normalizer s t) (ρ g)).1
    ((uc22pwl_inv_range_iff.1 hinv) g)
  refine ⟨c, ?_, hc⟩
  have hex : ρ g ((h ^ (m / q)) ^ s * ((ρ τ h) ^ (m / q)) ^ t) =
      ((h ^ (m / q)) ^ s * ((ρ τ h) ^ (m / q)) ^ t) ^ c :=
    mul_inv_eq_one.1 (El.eq_one_of_mem hU (mul_mem (hJE (hFg _ hxJ)) (inv_mem (zpow_mem (hJE hxJ) c))) hc)
  have h2 : ((h ^ (m / q)) ^ s * ((ρ τ h) ^ (m / q)) ^ t) ^ (c * c) =
      ((h ^ (m / q)) ^ s * ((ρ τ h) ^ (m / q)) ^ t) ^ (1 : ℤ) := by
    rw [zpow_one, zpow_mul, ← hex, ← map_zpow, ← hex, hig _ hxJ]
  rw [Pq.mul_zpow, Pq.mul_zpow, Pq.eq_iff] at h2
  have h3 := h2.2
  simp only [Int.cast_mul, Int.cast_one, mul_one] at h3
  rw [sq]
  exact mul_left_cancel₀ ht (h3.trans (mul_one _).symm)

theorem dvd_of_inv_diag (hU : IsPGroup 2 U)
    (hGal : ∀ g ∈ uc22pwtStab2 ρ A₁ A₂, ∃ i : ℕ, ρ g h * (h ^ 2 ^ i)⁻¹ ∈ U) {q : ℕ} (hq : q.Prime)
    (hqb : q ∣ b) {W : Subgroup X} (hWle : W ≤ pCoreOf q (uc22pwtE h (ρ τ h) a b))
    (hWinv : uc22pwsInv U (Set.range ρ) W) (hW0 : W ≠ ⊥) {g : Γ} {i j : ℕ}
    (hi : ρ g h * (h ^ 2 ^ i)⁻¹ ∈ U) (hj : ρ g (ρ τ h) * ((ρ τ h) ^ 2 ^ j)⁻¹ ∈ U)
    (hgW : ∀ x ∈ W, ρ g x = x⁻¹) : q ∣ 2 ^ i + 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨-, -, Pq⟩ := El.pairAt hU hq hqb
  obtain ⟨s, t, hs, hyW⟩ : ∃ s t : ℤ, (s : ZMod q) ≠ 0 ∧
      (h ^ (m / q)) ^ s * ((ρ τ h) ^ (m / q)) ^ t ∈ W := by
    rcases El.classify hU hGal hq hqb hWle hWinv hW0 with hW | ⟨s, t, hs, -, hW⟩
    · refine ⟨1, 0, by simp, ?_⟩
      rw [hW]
      exact El.line_le_pCore hU hq hqb 1 0 (mem_zpowers _)
    · exact ⟨s, t, hs, by rw [hW]; exact mem_zpowers _⟩
  have hD := El.actD hi hj (m / q) s t
  rw [hgW _ hyW, Pq.inv_eq s t, Pq.coord] at hD
  have h1 := hD.1
  push_cast at h1
  have h2 : ((2 : ZMod q) ^ i + 1) * s = 0 := by linear_combination -h1
  have h3 := (mul_eq_zero.1 h2).resolve_right hs
  have h4 : ((2 ^ i + 1 : ℕ) : ZMod q) = 0 := by push_cast; exact h3
  exact (ZMod.natCast_eq_zero_iff _ _).1 h4

theorem lam_of_inv_anti (hU : IsPGroup 2 U)
    (hGal : ∀ g ∈ uc22pwtStab2 ρ A₁ A₂, ∃ i : ℕ, ρ g h * (h ^ 2 ^ i)⁻¹ ∈ U) {q : ℕ} (hq : q.Prime)
    (hqb : q ∣ b) {W : Subgroup X} (hWle : W ≤ pCoreOf q (uc22pwtE h (ρ τ h) a b))
    (hWinv : uc22pwsInv U (Set.range ρ) W) (hW0 : W ≠ ⊥) {g : Γ} {i k : ℕ}
    (hi : ρ g h * ((ρ τ h) ^ 2 ^ i)⁻¹ ∈ U) (hk : ρ g (ρ τ h) * (h ^ 2 ^ k)⁻¹ ∈ U)
    (hgW : ∀ x ∈ W, ρ g x = x⁻¹) : uc22pwlLam ρ U h (ρ τ h) m b q := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨-, -, Pq⟩ := El.pairAt hU hq hqb
  rcases El.classify hU hGal hq hqb hWle hWinv hW0 with hW | ⟨s, t, -, ht, hW⟩
  · exfalso
    have hHW : (h ^ (m / q)) ^ (1 : ℤ) * ((ρ τ h) ^ (m / q)) ^ (0 : ℤ) ∈ W := by
      rw [hW]
      exact El.line_le_pCore hU hq hqb 1 0 (mem_zpowers _)
    have hA := El.actA hi hk (m / q) 1 0
    rw [hgW _ hHW, Pq.inv_eq 1 0, Pq.coord] at hA
    have h1 := hA.1
    simp at h1
  · exact ⟨hq, hqb, s, t, ht, by rw [← hW]; exact hWinv⟩

theorem sel_diag (hU : IsPGroup 2 U)
    (hGal : ∀ g ∈ uc22pwtStab2 ρ A₁ A₂, ∃ i : ℕ, ρ g h * (h ^ 2 ^ i)⁻¹ ∈ U) {S T : ℕ → ℤ}
    (hST : ∀ q, uc22pwlLam ρ U h (ρ τ h) m b q → (T q : ZMod q) ≠ 0 ∧
      uc22pwsInv U (Set.range ρ) (zpowers ((h ^ (m / q)) ^ S q * ((ρ τ h) ^ (m / q)) ^ T q)))
    {g : Γ} {i j : ℕ} (hi : ρ g h * (h ^ 2 ^ i)⁻¹ ∈ U) (hj : ρ g (ρ τ h) * ((ρ τ h) ^ 2 ^ j)⁻¹ ∈ U)
    {q : ℕ} (hΛ : uc22pwlLam ρ U h (ρ τ h) m b q) :
    ρ g ((h ^ (m / q)) ^ S q * ((ρ τ h) ^ (m / q)) ^ T q) *
      (((h ^ (m / q)) ^ S q * ((ρ τ h) ^ (m / q)) ^ T q) ^ 2 ^ i)⁻¹ ∈ U := by
  obtain ⟨hT, hinv⟩ := hST q hΛ
  obtain ⟨hq, hqb, -⟩ := hΛ
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨-, -, Pq⟩ := El.pairAt hU hq hqb
  have hD := El.actD hi hj (m / q)
  obtain ⟨i₀, hτ⟩ := El.tauAt hGal (m / q)
  have hinv' := uc22pwl_inv_range_iff.1 hinv
  have hS : (S q : ZMod q) ≠ 0 := fun h0 =>
    hT ((Pq.tau_line (uc22pwl_two_pow_ne_zero hq (El.q_ne_two hqb) i₀) hτ (hinv' τ)).1 h0)
  have hxy := (Pq.inv_diag_iff hD hS hT).1 (hinv' g)
  refine uc22pwe_trans (hD (S q) (T q)) ?_
  rw [Pq.mul_pow, Pq.coord]
  push_cast at hxy ⊢
  exact ⟨by ring, by rw [hxy]; ring⟩

theorem sel_anti_one (hU : IsPGroup 2 U) {k₀ : ℕ}
    (hk₀ : ∀ q, uc22pwlLam ρ U h (ρ τ h) m b q → uc22pwsInv U (Set.range ρ)
      (zpowers ((h ^ (m / q)) ^ ((2 ^ k₀ : ℕ) : ℤ) * ((ρ τ h) ^ (m / q)) ^ (1 : ℤ))))
    {g : Γ} {i k : ℕ} (hi : ρ g h * ((ρ τ h) ^ 2 ^ i)⁻¹ ∈ U) (hk : ρ g (ρ τ h) * (h ^ 2 ^ k)⁻¹ ∈ U)
    {q : ℕ} (hΛ : uc22pwlLam ρ U h (ρ τ h) m b q) :
    ρ g ((h ^ (m / q)) ^ ((2 ^ k₀ : ℕ) : ℤ) * ((ρ τ h) ^ (m / q)) ^ (1 : ℤ)) *
      (((h ^ (m / q)) ^ ((2 ^ k₀ : ℕ) : ℤ) * ((ρ τ h) ^ (m / q)) ^ (1 : ℤ)) ^ 2 ^ (i + k₀))⁻¹ ∈ U := by
  have hinv := hk₀ q hΛ
  obtain ⟨hq, hqb, -⟩ := hΛ
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨-, -, Pq⟩ := El.pairAt hU hq hqb
  have hA := El.actA hi hk (m / q)
  have hcrit := Pq.inv_anti_imp hA ((uc22pwl_inv_range_iff.1 hinv) g)
  refine uc22pwe_trans (hA _ _) ?_
  rw [Pq.mul_pow, Pq.coord]
  push_cast at hcrit ⊢
  refine ⟨?_, by ring⟩
  linear_combination -hcrit

theorem case_one_of_anti (hU : IsPGroup 2 U)
    (hGal : ∀ g ∈ uc22pwtStab2 ρ A₁ A₂, ∃ i : ℕ, ρ g h * (h ^ 2 ^ i)⁻¹ ∈ U) {S T : ℕ → ℤ}
    (hST : ∀ q, uc22pwlLam ρ U h (ρ τ h) m b q → (T q : ZMod q) ≠ 0 ∧
      uc22pwsInv U (Set.range ρ) (zpowers ((h ^ (m / q)) ^ S q * ((ρ τ h) ^ (m / q)) ^ T q)))
    {g : Γ} {i k : ℕ} (hi : ρ g h * ((ρ τ h) ^ 2 ^ i)⁻¹ ∈ U) (hk : ρ g (ρ τ h) * (h ^ 2 ^ k)⁻¹ ∈ U)
    (hc : ∀ q, uc22pwlLam ρ U h (ρ τ h) m b q → ∃ c : ℤ, (c : ZMod q) ^ 2 = 1 ∧
      ρ g ((h ^ (m / q)) ^ S q * ((ρ τ h) ^ (m / q)) ^ T q) *
        (((h ^ (m / q)) ^ S q * ((ρ τ h) ^ (m / q)) ^ T q) ^ c)⁻¹ ∈ U) :
    ∀ q, uc22pwlLam ρ U h (ρ τ h) m b q → uc22pwsInv U (Set.range ρ)
      (zpowers ((h ^ (m / q)) ^ ((2 ^ (i * (Nat.totient b - 1)) : ℕ) : ℤ) * ((ρ τ h) ^ (m / q)) ^ (1 : ℤ))) := by
  intro q hΛ
  obtain ⟨hT, hinv⟩ := hST q hΛ
  obtain ⟨c, hc2, hcU⟩ := hc q hΛ
  obtain ⟨hq, hqb, -⟩ := hΛ
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨-, -, Pq⟩ := El.pairAt hU hq hqb
  have hA := El.actA hi hk (m / q)
  have h1 := uc22pwe_trans (uc22pwe_symm (hA (S q) (T q))) hcU
  rw [Pq.mul_zpow, Pq.coord] at h1
  obtain ⟨i₀, hτ⟩ := El.tauAt hGal (m / q)
  refine Pq.inv_of_sq (El.shapeAt hGal (m / q)) (uc22pwl_two_pow_ne_zero hq (El.q_ne_two hqb) i₀) hτ hinv hT
    (by simp) ?_
  have hbodd : Odd b := (Nat.odd_mul.1 (El.ab ▸ El.odd)).2
  have hb1 : 1 ≤ Nat.totient b := Nat.totient_pos.2 hbodd.pos
  have htot : (2 : ZMod q) ^ Nat.totient b = 1 := by
    have h2 := (Nat.ModEq.pow_totient (Nat.coprime_two_left.2 hbodd)).of_dvd hqb
    have h3 := (ZMod.natCast_eq_natCast_iff _ _ _).2 h2
    push_cast at h3
    exact h3
  have hwu : (2 : ZMod q) ^ (i * (Nat.totient b - 1)) * 2 ^ i = 1 := by
    rw [← pow_add, ← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hb1, pow_mul', htot, one_pow]
  push_cast at h1 ⊢
  have hT2 : (T q : ZMod q) ^ 2 = ((2 : ZMod q) ^ i) ^ 2 * (S q : ZMod q) ^ 2 := by
    calc (T q : ZMod q) ^ 2 = (T q : ZMod q) ^ 2 * (c : ZMod q) ^ 2 := by rw [hc2, mul_one]
      _ = ((T q : ZMod q) * c) ^ 2 := by ring
      _ = ((2 : ZMod q) ^ i * S q) ^ 2 := by rw [← h1.2]
      _ = ((2 : ZMod q) ^ i) ^ 2 * (S q : ZMod q) ^ 2 := by ring
  rw [hT2]
  linear_combination (S q : ZMod q) ^ 2 * ((2 : ZMod q) ^ (i * (Nat.totient b - 1)) * 2 ^ i + 1) * hwu

end UC22pwtElem

end ElemLines

section Sel

variable {X Γ : Type} [Group X] [Group Γ] [Finite X]
  {ρ : Γ →* MulAut X} {τ : Γ} {U A₁ A₂ : Subgroup X} {C : UC22pwtCtx ρ τ U A₁ A₂}
  {h w₁ : X} {m a b : ℕ} {α : Set ℕ}

theorem uc22pwt_sel_two (El : UC22pwtElem C h w₁ m a b α) (hU : IsPGroup 2 U)
    (hGal : ∀ g ∈ uc22pwtStab2 ρ A₁ A₂, ∃ i : ℕ, ρ g h * (h ^ 2 ^ i)⁻¹ ∈ U) :
    ∃ F : ℕ → Subgroup X,
      (∀ p : ℕ, p.Prime → F p ≤ pCoreOf p (uc22pwtE h (ρ τ h) a b) ∧ uc22pwsInv U (Set.range ρ) (F p) ∧
        (p ∣ Nat.card (uc22pwtE h (ρ τ h) a b) → F p ≠ ⊥) ∧
        ∀ W : Subgroup X, W ≤ F p → uc22pwsInv U (Set.range ρ) W → W = ⊥ ∨ W = F p) ∧
      ∀ J : Subgroup X, J = ⨆ q ∈ (Nat.card (uc22pwtE h (ρ τ h) a b)).primeFactors, F q →
        (IsCyclic J → uc22pwlAlike ρ J) ∧ (3 ∣ b → 5 ∣ b → ∀ g : Γ, ¬ ∀ x ∈ J, ρ g x = x⁻¹) := by
  classical
  have P := El.pair
  have hEab := P.isMulCommutative_E
  have hEU := El.E_le_normalizer
  have hΦE : ∀ φ ∈ Set.range ρ, ∀ x ∈ uc22pwtE h (ρ τ h) a b, φ x ∈ uc22pwtE h (ρ τ h) a b ⊔ U := by
    rintro _ ⟨g, rfl⟩ x hx
    exact El.invariant g x hx
  obtain ⟨F₀, hF₀⟩ := uc22pws_exists_sel hEU hU hEab P.odd_card_E hΦE
  obtain ⟨S, T, hST, hSel⟩ : ∃ S T : ℕ → ℤ,
      (∀ q, uc22pwlLam ρ U h (ρ τ h) m b q → (T q : ZMod q) ≠ 0 ∧
        uc22pwsInv U (Set.range ρ) (zpowers ((h ^ (m / q)) ^ S q * ((ρ τ h) ^ (m / q)) ^ T q))) ∧
      ∀ g : Γ, (∀ q, uc22pwlLam ρ U h (ρ τ h) m b q → ∃ c : ℤ, (c : ZMod q) ^ 2 = 1 ∧
          ρ g ((h ^ (m / q)) ^ S q * ((ρ τ h) ^ (m / q)) ^ T q) *
            (((h ^ (m / q)) ^ S q * ((ρ τ h) ^ (m / q)) ^ T q) ^ c)⁻¹ ∈ U) →
        ∃ K : ℕ, ∀ q, uc22pwlLam ρ U h (ρ τ h) m b q →
          ρ g ((h ^ (m / q)) ^ S q * ((ρ τ h) ^ (m / q)) ^ T q) *
            (((h ^ (m / q)) ^ S q * ((ρ τ h) ^ (m / q)) ^ T q) ^ 2 ^ K)⁻¹ ∈ U := by
    by_cases hcase : ∃ k₀ : ℕ, ∀ q, uc22pwlLam ρ U h (ρ τ h) m b q → uc22pwsInv U (Set.range ρ)
        (zpowers ((h ^ (m / q)) ^ ((2 ^ k₀ : ℕ) : ℤ) * ((ρ τ h) ^ (m / q)) ^ (1 : ℤ)))
    · obtain ⟨k₀, hk₀⟩ := hcase
      have hST : ∀ q, uc22pwlLam ρ U h (ρ τ h) m b q → ((1 : ℤ) : ZMod q) ≠ 0 ∧ uc22pwsInv U (Set.range ρ)
          (zpowers ((h ^ (m / q)) ^ ((2 ^ k₀ : ℕ) : ℤ) * ((ρ τ h) ^ (m / q)) ^ (1 : ℤ))) := fun q hΛ => by
        haveI : Fact q.Prime := ⟨hΛ.1⟩
        exact ⟨by simp, hk₀ q hΛ⟩
      refine ⟨fun _ => ((2 ^ k₀ : ℕ) : ℤ), fun _ => 1, hST, fun g _ => ?_⟩
      rcases El.shape hGal g with ⟨i, j, hi, hj⟩ | ⟨i, k, hi, hk⟩
      · exact ⟨i, fun q hΛ => El.sel_diag hU hGal hST hi hj hΛ⟩
      · exact ⟨i + k₀, fun q hΛ => El.sel_anti_one hU hk₀ hi hk hΛ⟩
    · have hch : ∀ q, ∃ st : ℤ × ℤ, uc22pwlLam ρ U h (ρ τ h) m b q → (st.2 : ZMod q) ≠ 0 ∧
          uc22pwsInv U (Set.range ρ) (zpowers ((h ^ (m / q)) ^ st.1 * ((ρ τ h) ^ (m / q)) ^ st.2)) := by
        intro q
        by_cases hΛ : uc22pwlLam ρ U h (ρ τ h) m b q
        · obtain ⟨-, -, s, t, ht, hinv⟩ := hΛ
          exact ⟨(s, t), fun _ => ⟨ht, hinv⟩⟩
        · exact ⟨(0, 0), fun h' => absurd h' hΛ⟩
      choose st hst using hch
      refine ⟨fun q => (st q).1, fun q => (st q).2, hst, fun g hc => ?_⟩
      rcases El.shape hGal g with ⟨i, j, hi, hj⟩ | ⟨i, k, hi, hk⟩
      · exact ⟨i, fun q hΛ => El.sel_diag hU hGal hst hi hj hΛ⟩
      · exact absurd ⟨i * (Nat.totient b - 1), El.case_one_of_anti hU hGal hst hi hk hc⟩ hcase
  obtain ⟨F, hFΛ, hFn⟩ : ∃ F : ℕ → Subgroup X,
      (∀ q, uc22pwlLam ρ U h (ρ τ h) m b q → F q = zpowers ((h ^ (m / q)) ^ S q * ((ρ τ h) ^ (m / q)) ^ T q)) ∧
      ∀ q, ¬ uc22pwlLam ρ U h (ρ τ h) m b q → F q = F₀ q :=
    ⟨fun q => if uc22pwlLam ρ U h (ρ τ h) m b q then
      zpowers ((h ^ (m / q)) ^ S q * ((ρ τ h) ^ (m / q)) ^ T q) else F₀ q,
      fun q hq => if_pos hq, fun q hq => if_neg hq⟩
  have hFp : ∀ p : ℕ, p.Prime → F p ≤ pCoreOf p (uc22pwtE h (ρ τ h) a b) ∧ uc22pwsInv U (Set.range ρ) (F p) ∧
      (p ∣ Nat.card (uc22pwtE h (ρ τ h) a b) → F p ≠ ⊥) ∧
      ∀ W : Subgroup X, W ≤ F p → uc22pwsInv U (Set.range ρ) W → W = ⊥ ∨ W = F p := by
    intro p hp
    by_cases hΛ : uc22pwlLam ρ U h (ρ τ h) m b p
    · rw [hFΛ p hΛ]
      obtain ⟨hT, hinv⟩ := hST p hΛ
      obtain ⟨-, -, Pq⟩ := El.pairAt hU hp hΛ.2.1
      have hne : ¬ ((S p : ZMod p) = 0 ∧ (T p : ZMod p) = 0) := fun h0 => hT h0.2
      refine ⟨El.line_le_pCore hU hp hΛ.2.1 _ _, hinv, fun _ h0 => ?_, fun W hW _ => Pq.line_min hne hW⟩
      have h1 := Pq.card_line hne
      rw [h0, Subgroup.card_bot] at h1
      exact hp.one_lt.ne h1
    · rw [hFn p hΛ]
      exact hF₀ p hp
  refine ⟨F, hFp, fun J hJ => ?_⟩
  have hJE : J ≤ uc22pwtE h (ρ τ h) a b := by
    rw [hJ]
    exact iSup₂_le fun q hq => (hFp q (Nat.prime_of_mem_primeFactors hq)).1.trans (Subgroup.map_subtype_le _)
  have hFJ : ∀ q, q.Prime → q ∣ m → F q ≤ J := fun q hq hqm => by
    rw [hJ]
    exact le_iSup₂ (f := fun q _ => F q) q (El.mem_primeFactors_iff.2 ⟨hq, hqm⟩)
  have hdvdm : ∀ q, q ∣ b → q ∣ m := fun q hqb => El.ab ▸ dvd_mul_of_dvd_right hqb a
  have hcardE : ∀ q, q.Prime → q ∣ m → q ∣ Nat.card (uc22pwtE h (ρ τ h) a b) := fun q hq hqm =>
    ((Nat.mem_primeFactors.1 (El.mem_primeFactors_iff.2 ⟨hq, hqm⟩)).2.1)
  have hxJ : ∀ q, uc22pwlLam ρ U h (ρ τ h) m b q →
      (h ^ (m / q)) ^ S q * ((ρ τ h) ^ (m / q)) ^ T q ∈ J := fun q hΛ =>
    hFJ q hΛ.1 (hdvdm q hΛ.2.1) (by rw [hFΛ q hΛ]; exact mem_zpowers _)
  refine ⟨fun hcyc => ?_, fun h3 h5 g hgJ => ?_⟩
  ·
    intro g₁ g₂ hF₁ hF₂ hi₁ hn₁ hi₂ hn₂
    have hΛall : ∀ q, q.Prime → q ∣ b → uc22pwlLam ρ U h (ρ τ h) m b q := by
      intro q hq hqb
      by_contra hΛ
      have hle := hFJ q hq (hdvdm q hqb)
      haveI : IsCyclic J := hcyc
      have hcycq : IsCyclic ↥(F q) := Subgroup.isCyclic_of_le hle
      obtain ⟨h1, h2, h3, -⟩ := hFp q hq
      exact hΛ (El.lam_of_cyclic hU hGal hq hqb h1 h2 (h3 (hcardE q hq (hdvdm q hqb))) hcycq)
    obtain ⟨r, hr1, hr2⟩ : ∃ r : ℕ, r ≡ 1 [MOD a] ∧ r ≡ 2 [MOD b] := ⟨_, (Nat.chineseRemainder El.cop 1 2).2⟩
    have hbodd : Odd b := (Nat.odd_mul.1 (El.ab ▸ El.odd)).2
    have hrm : Nat.Coprime r m := by
      rw [← El.ab]
      refine Nat.Coprime.mul_right ?_ ?_
      · rw [Nat.Coprime, hr1.gcd_eq, Nat.gcd_one_left]
      · rw [Nat.Coprime, hr2.gcd_eq]
        exact Nat.coprime_two_left.2 hbodd
    have hK : ∀ g : Γ, (∀ x ∈ J, ρ g x ∈ J) → (∀ x ∈ J, ρ g (ρ g x) = x) →
        ∃ K : ℕ, ∀ x ∈ J, ρ g x = x ^ (r ^ K) := by
      intro g hFg hig
      obtain ⟨K, hKq⟩ := hSel g fun q hΛ =>
        El.coef_of_inv hU hΛ.1 hΛ.2.1 (hST q hΛ).1 (hST q hΛ).2 (hxJ q hΛ) hJE hFg hig
      refine ⟨K, fun x hx => ?_⟩
      have hle : J ≤ uc22pwlPowFix U (uc22pwtE h (ρ τ h) a b) hEab hEU (ρ g) (r ^ K) := by
        rw [hJ]
        refine iSup₂_le fun q hqPF => ?_
        obtain ⟨hq, hqm⟩ := El.mem_primeFactors_iff.1 hqPF
        rcases (Nat.Prime.dvd_mul hq).1 (El.ab ▸ hqm) with hqa | hqb
        · have hΛ : ¬ uc22pwlLam ρ U h (ρ τ h) m b q := fun hΛ =>
            hq.one_lt.ne' (Nat.eq_one_of_dvd_coprimes El.cop hqa hΛ.2.1)
          rw [hFn q hΛ]
          intro y hy
          have hyc := (hF₀ q hq).1 hy
          exact uc22pwl_powFix_of_one ((Subgroup.map_subtype_le _) hyc)
            ((uc22pws_pCoreOf_elem hEab P.rank_E hq).1 y hyc) (hr1.of_dvd hqa) (El.fix_pCore hq hqa hyc g)
        · have hΛ := hΛall q hq hqb
          obtain ⟨hHE, hH'E, Pq⟩ := El.pairAt hU hq hqb
          rw [hFΛ q hΛ, Subgroup.zpowers_le]
          exact uc22pwl_powFix_of_two (mul_mem (zpow_mem hHE _) (zpow_mem hH'E _)) (Pq.pow_q _ _)
            (hr2.of_dvd hqb) (hKq q hΛ)
      have h1 := (hle hx).2
      exact mul_inv_eq_one.1 (El.eq_one_of_mem hU
        (mul_mem (hJE (hFg x hx)) (inv_mem (pow_mem (hJE hx) _))) h1)
    have hrJ : ∀ x ∈ J, x ^ r = 1 → x = 1 := by
      intro x hx hxr
      have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hxr)
        (orderOf_dvd_of_pow_eq_one (P.pow_m_of_mem_E (hJE hx)))
      rw [hrm.gcd_eq_one] at h1
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)
    obtain ⟨K₁, hK₁⟩ := hK g₁ hF₁ hi₁
    obtain ⟨K₂, hK₂⟩ := hK g₂ hF₂ hi₂
    exact uc22pwl_alike_of_pow (uc22pws_isMulCommutative_of_le hEab hJE) hrJ hK₁ hK₂ hi₁ hn₁ hi₂ hn₂
  ·
    have hW : ∀ q, q.Prime → q ∣ b → F q ≤ pCoreOf q (uc22pwtE h (ρ τ h) a b) ∧
        uc22pwsInv U (Set.range ρ) (F q) ∧ F q ≠ ⊥ ∧ ∀ x ∈ F q, ρ g x = x⁻¹ := by
      intro q hq hqb
      obtain ⟨h1, h2, h3, -⟩ := hFp q hq
      exact ⟨h1, h2, h3 (hcardE q hq (hdvdm q hqb)), fun x hx => hgJ x (hFJ q hq (hdvdm q hqb) hx)⟩
    obtain ⟨w3, w3', w3'', w3i⟩ := hW 3 Nat.prime_three h3
    obtain ⟨w5, w5', w5'', w5i⟩ := hW 5 Nat.prime_five h5
    rcases El.shape hGal g with ⟨i, j, hi, hj⟩ | ⟨i, k, hi, hk⟩
    · exact uc22pwc_not_three_five i (El.dvd_of_inv_diag hU hGal Nat.prime_three h3 w3 w3' w3'' hi hj w3i)
        (El.dvd_of_inv_diag hU hGal Nat.prime_five h5 w5 w5' w5'' hi hj w5i)
    · have hΛ3 := El.lam_of_inv_anti hU hGal Nat.prime_three h3 w3 w3' w3'' hi hk w3i
      have hΛ5 := El.lam_of_inv_anti hU hGal Nat.prime_five h5 w5 w5' w5'' hi hk w5i
      obtain ⟨K, hK⟩ := hSel g fun q hΛ => ⟨-1, by simp, by
        rw [hgJ _ (hxJ q hΛ), zpow_neg_one, mul_inv_cancel]
        exact one_mem U⟩
      have hdvd : ∀ q, uc22pwlLam ρ U h (ρ τ h) m b q → q ∣ 2 ^ K + 1 := by
        intro q hΛ
        obtain ⟨hT, -⟩ := hST q hΛ
        obtain ⟨-, -, Pq⟩ := El.pairAt hU hΛ.1 hΛ.2.1
        have hne : ¬ ((S q : ZMod q) = 0 ∧ (T q : ZMod q) = 0) := fun h0 => hT h0.2
        have h1 := hK q hΛ
        rw [hgJ _ (hxJ q hΛ)] at h1
        have h2 := El.eq_one_of_mem hU (mul_mem (inv_mem (hJE (hxJ q hΛ)))
          (inv_mem (pow_mem (hJE (hxJ q hΛ)) _))) h1
        have h3 := congrArg (·⁻¹) h2
        simp only [mul_inv_rev, inv_inv, inv_one] at h3
        rw [← Pq.orderOf_eq hne]
        exact orderOf_dvd_of_pow_eq_one (by rw [pow_succ]; exact h3)
      exact uc22pwc_not_three_five K (hdvd 3 hΛ3) (hdvd 5 hΛ5)

end Sel

end CFSG.LocalAnalysis.UniquenessCase.UC22
