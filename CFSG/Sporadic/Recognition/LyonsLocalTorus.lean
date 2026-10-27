module

public import CFSG.Sporadic.Recognition.LyonsLocalPerfect

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup

theorem disjoint_x1p_x3p : Disjoint x1p x3p := by
  show ∀ x : Fin 11, x1p x = x ∨ x3p x = x
  decide

theorem disjoint_x2p_x3p : Disjoint x2p x3p := by
  show ∀ x : Fin 11, x2p x = x ∨ x3p x = x
  decide

theorem torus_two_cases (a b : ℤ) (h : (x1p ^ a * x2p ^ b).support.card = 3) :
    x1p ^ a * x2p ^ b = x1p ∨ x1p ^ a * x2p ^ b = x1p⁻¹ ∨ x1p ^ a * x2p ^ b = x2p ∨
      x1p ^ a * x2p ^ b = x2p⁻¹ := by
  rcases zpow_cases x1p_pow_three a with ha | ha | ha <;>
    rcases zpow_cases x2p_pow_three b with hb | hb | hb <;>
    rw [ha, hb] at h ⊢ <;> revert h <;> decide

theorem torus_three_cases (a b c : ℤ) (h : (x1p ^ a * x2p ^ b * x3p ^ c).support.card = 3) :
    x1p ^ a * x2p ^ b * x3p ^ c = x1p ∨ x1p ^ a * x2p ^ b * x3p ^ c = x1p⁻¹ ∨
      x1p ^ a * x2p ^ b * x3p ^ c = x2p ∨ x1p ^ a * x2p ^ b * x3p ^ c = x2p⁻¹ ∨
      x1p ^ a * x2p ^ b * x3p ^ c = x3p ∨ x1p ^ a * x2p ^ b * x3p ^ c = x3p⁻¹ := by
  rcases zpow_cases x1p_pow_three a with ha | ha | ha <;>
    rcases zpow_cases x2p_pow_three b with hb | hb | hb <;>
    rcases zpow_cases x3p_pow_three c with hc | hc | hc <;>
    rw [ha, hb, hc] at h ⊢ <;> revert h <;> decide

theorem torus_two_injective (i j i' j' : Fin 3)
    (h : x1p ^ (i : ℕ) * x2p ^ (j : ℕ) = x1p ^ (i' : ℕ) * x2p ^ (j' : ℕ)) : i = i' ∧ j = j' := by
  revert i j i' j'
  decide

theorem torus_three_injective (i j k i' j' k' : Fin 3)
    (h : x1p ^ (i : ℕ) * x2p ^ (j : ℕ) * x3p ^ (k : ℕ) =
      x1p ^ (i' : ℕ) * x2p ^ (j' : ℕ) * x3p ^ (k' : ℕ)) : i = i' ∧ j = j' ∧ k = k' := by
  revert i j k i' j' k'
  decide

section Generic

variable {K : Type*} [Group K]

theorem zpow_triple_mul {x y z : K} (hxy : Commute x y) (hxz : Commute x z) (hyz : Commute y z)
    (a b c a' b' c' : ℤ) :
    x ^ a * y ^ b * z ^ c * (x ^ a' * y ^ b' * z ^ c') =
      x ^ (a + a') * y ^ (b + b') * z ^ (c + c') := by
  have hzx : z ^ c * x ^ a' = x ^ a' * z ^ c := (hxz.zpow_zpow a' c).symm.eq
  have hyx : y ^ b * x ^ a' = x ^ a' * y ^ b := (hxy.zpow_zpow a' b).symm.eq
  have hzy : z ^ c * y ^ b' = y ^ b' * z ^ c := (hyz.zpow_zpow b' c).symm.eq
  calc x ^ a * y ^ b * z ^ c * (x ^ a' * y ^ b' * z ^ c')
      = x ^ a * y ^ b * (z ^ c * x ^ a') * y ^ b' * z ^ c' := by simp only [mul_assoc]
    _ = x ^ a * y ^ b * (x ^ a' * z ^ c) * y ^ b' * z ^ c' := by rw [hzx]
    _ = x ^ a * (y ^ b * x ^ a') * z ^ c * y ^ b' * z ^ c' := by simp only [mul_assoc]
    _ = x ^ a * (x ^ a' * y ^ b) * z ^ c * y ^ b' * z ^ c' := by rw [hyx]
    _ = x ^ a * x ^ a' * y ^ b * (z ^ c * y ^ b') * z ^ c' := by simp only [mul_assoc]
    _ = x ^ a * x ^ a' * y ^ b * (y ^ b' * z ^ c) * z ^ c' := by rw [hzy]
    _ = x ^ (a + a') * y ^ (b + b') * z ^ (c + c') := by
      rw [zpow_add, zpow_add, zpow_add]; simp only [mul_assoc]

theorem zpow_triple_inv {x y z : K} (hxy : Commute x y) (hxz : Commute x z) (hyz : Commute y z)
    (a b c : ℤ) : (x ^ a * y ^ b * z ^ c)⁻¹ = x ^ (-a) * y ^ (-b) * z ^ (-c) := by
  apply inv_eq_of_mul_eq_one_right
  rw [zpow_triple_mul hxy hxz hyz]
  simp

theorem exists_zpow_mul_of_mem_closure_triple {x y z : K} (hxy : Commute x y) (hxz : Commute x z)
    (hyz : Commute y z) {u : K} (hu : u ∈ closure ({x, y, z} : Set K)) :
    ∃ a b c : ℤ, u = x ^ a * y ^ b * z ^ c := by
  induction hu using Subgroup.closure_induction with
  | mem u hu =>
    rcases hu with rfl | rfl | rfl
    · exact ⟨1, 0, 0, by simp⟩
    · exact ⟨0, 1, 0, by simp⟩
    · exact ⟨0, 0, 1, by simp⟩
  | one => exact ⟨0, 0, 0, by simp⟩
  | mul u v _ _ hu hv =>
    obtain ⟨a, b, c, rfl⟩ := hu
    obtain ⟨a', b', c', rfl⟩ := hv
    exact ⟨a + a', b + b', c + c', zpow_triple_mul hxy hxz hyz a b c a' b' c'⟩
  | inv u _ hu =>
    obtain ⟨a, b, c, rfl⟩ := hu
    exact ⟨-a, -b, -c, zpow_triple_inv hxy hxz hyz a b c⟩

theorem exists_zpow_mul_of_mem_closure_pair {x y : K} (hxy : Commute x y) {u : K}
    (hu : u ∈ closure ({x, y} : Set K)) : ∃ a b : ℤ, u = x ^ a * y ^ b := by
  have hu' : u ∈ closure ({x, y, 1} : Set K) :=
    closure_mono (fun v hv => by rcases hv with rfl | rfl <;> simp) hu
  obtain ⟨a, b, c, rfl⟩ := exists_zpow_mul_of_mem_closure_triple hxy (Commute.one_right x)
    (Commute.one_right y) hu'
  exact ⟨a, b, by simp⟩

theorem exists_fin_pow_of_pow_three {x : K} (hx : x ^ 3 = 1) (a : ℤ) :
    ∃ i : Fin 3, x ^ a = x ^ (i : ℕ) := by
  rcases zpow_cases hx a with h | h | h
  · exact ⟨0, by simpa using h⟩
  · exact ⟨1, by simpa using h⟩
  · exact ⟨2, by simpa using h⟩

end Generic

section Torus

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

namespace LyData

omit [Finite G] in
theorem commute_x₁_x₂ (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) : Commute x₁ x₂ :=
  (D.cover.commute_of_rho_commute_pow_three S.pow₁ (g := x₂)
    (by rw [S.rho₁, S.rho₂]; exact disjoint_x1p_x2p.commute.symm.eq)).symm

omit [Finite G] in
theorem commute_x₁_x₃ (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) : Commute x₁ x₃ :=
  (D.cover.commute_of_rho_commute_pow_three S.pow₁ (g := x₃)
    (by rw [S.rho₁, S.rho₃]; exact disjoint_x1p_x3p.commute.symm.eq)).symm

omit [Finite G] in
theorem commute_x₂_x₃ (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) : Commute x₂ x₃ :=
  (D.cover.commute_of_rho_commute_pow_three S.pow₂ (g := x₃)
    (by rw [S.rho₂, S.rho₃]; exact disjoint_x2p_x3p.commute.symm.eq)).symm

omit [Finite G] in
theorem comm₃₁ (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    (x₃ : G) * (x₁ : G) = (x₁ : G) * (x₃ : G) := by
  have := congrArg Subtype.val (D.commute_x₁_x₃ S).symm.eq
  simpa using this

omit [Finite G] in
theorem comm₃₂ (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    (x₃ : G) * (x₂ : G) = (x₂ : G) * (x₃ : G) := by
  have := congrArg Subtype.val (D.commute_x₂_x₃ S).symm.eq
  simpa using this

omit [Finite G] in
theorem exists_zpow_of_mem_closure_two (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) {u : G}
    (hu : u ∈ Subgroup.closure ({(x₁ : G), (x₂ : G)} : Set G)) :
    ∃ a b : ℤ, u = (x₁ : G) ^ a * (x₂ : G) ^ b :=
  exists_zpow_mul_of_mem_closure_pair (show Commute (x₁ : G) (x₂ : G) from (D.comm₂₁ S).symm) hu

omit [Finite G] in
theorem exists_zpow_of_mem_closure_three (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) {u : G}
    (hu : u ∈ Subgroup.closure ({(x₁ : G), (x₂ : G), (x₃ : G)} : Set G)) :
    ∃ a b c : ℤ, u = (x₁ : G) ^ a * (x₂ : G) ^ b * (x₃ : G) ^ c :=
  exists_zpow_mul_of_mem_closure_triple (show Commute (x₁ : G) (x₂ : G) from (D.comm₂₁ S).symm)
    (show Commute (x₁ : G) (x₃ : G) from (D.comm₃₁ S).symm)
    (show Commute (x₂ : G) (x₃ : G) from (D.comm₃₂ S).symm) hu

omit [Finite G] in
theorem orderOf_x₂ (S : LyStd ρ x₁ x₂ x₃) : orderOf (x₂ : G) = 3 := by
  have h3 : (x₂ : G) ^ 3 = 1 := by
    have := congrArg Subtype.val S.pow₂
    simpa using this
  have h1 : (x₂ : G) ≠ 1 := by
    intro h
    have : x₂ = 1 := Subtype.ext h
    have h2 := S.rho₂
    rw [this, map_one] at h2
    exact absurd h2 (by decide)
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime h3 h1

omit [Finite G] in
theorem orderOf_x₃ (S : LyStd ρ x₁ x₂ x₃) : orderOf (x₃ : G) = 3 := by
  have h3 : (x₃ : G) ^ 3 = 1 := by
    have := congrArg Subtype.val S.pow₃
    simpa using this
  have h1 : (x₃ : G) ≠ 1 := by
    intro h
    have : x₃ = 1 := Subtype.ext h
    have h2 := S.rho₃
    rw [this, map_one] at h2
    exact absurd h2 (by decide)
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime h3 h1

omit [Finite G] in
theorem pow_three_torus (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) (a b c : ℤ) :
    (x₁ ^ a * x₂ ^ b * x₃ ^ c) ^ 3 = 1 := by
  have h12 := D.commute_x₁_x₂ S
  have h13 := D.commute_x₁_x₃ S
  have h23 := D.commute_x₂_x₃ S
  have hp : ∀ (y : ↥(centralizer ({t} : Set G))) (n : ℤ), y ^ 3 = 1 → (y ^ n) ^ 3 = 1 :=
    fun y n hy => by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  rw [Commute.mul_pow ((h13.zpow_zpow a c).mul_left (h23.zpow_zpow b c)),
    Commute.mul_pow (h12.zpow_zpow a b), hp x₁ a S.pow₁, hp x₂ b S.pow₂, hp x₃ c S.pow₃,
    one_mul, one_mul]

omit [Finite G] in
theorem rho_torus (S : LyStd ρ x₁ x₂ x₃) (a b c : ℤ) :
    ρ (x₁ ^ a * x₂ ^ b * x₃ ^ c) = x1p ^ a * x2p ^ b * x3p ^ c := by
  rw [map_mul, map_mul, map_zpow, map_zpow, map_zpow, S.rho₁, S.rho₂, S.rho₃]

theorem not_isConj_cycle3_cycle333 (D : LyData G t ρ) {u w : ↥(centralizer ({t} : Set G))}
    (hu3 : u ^ 3 = 1) (hw3 : w ^ 3 = 1) (hu : (ρ u).cycleType = {3})
    (hw : (ρ w).cycleType = {3, 3, 3}) : ¬ IsConj (u : G) (w : G) := by
  obtain ⟨x, hx3, hx⟩ := D.exists_lift_x1p
  obtain ⟨y, hy3, hy⟩ := D.exists_lift_u123p
  have h1 : IsConj u x := D.cover.isConj_of_cycleType_eq hu3 hx3 (by rw [hu, hx, cycleType_x1p])
  have h2 : IsConj w y := D.cover.isConj_of_cycleType_eq hw3 hy3 (by rw [hw, hy, cycleType_u123p])
  have h1' : IsConj (u : G) (x : G) := (centralizer ({t} : Set G)).subtype.map_isConj h1
  have h2' : IsConj (w : G) (y : G) := (centralizer ({t} : Set G)).subtype.map_isConj h2
  intro hc
  exact D.not_isConj_x1p_u123p hx3 hy3 hx hy (h1'.symm.trans (hc.trans h2'))

theorem card_support_rho_eq_three (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    {w : ↥(centralizer ({t} : Set G))} (hw3 : w ^ 3 = 1) (hc : IsConj (x₁ : G) (w : G)) :
    (ρ w).support.card = 3 := by
  have hρ3 : ρ w ^ 3 = 1 := by rw [← map_pow, hw3, map_one]
  have hu : (ρ x₁).cycleType = {3} := by rw [S.rho₁, cycleType_x1p]
  by_cases h1 : ρ w = 1
  · exfalso
    have hw1 : w = 1 := D.eq_of_rho_eq hw3 (one_pow 3) (by rw [h1, map_one])
    rw [hw1, Subgroup.coe_one] at hc
    have hx1 : (x₁ : G) = 1 := isConj_one_left.1 hc
    have := orderOf_x₁ S
    rw [hx1, orderOf_one] at this
    exact absurd this (by norm_num)
  · rcases cycleType_of_pow_three hρ3 h1 with h | h | h
    · rw [← sum_cycleType, h]; rfl
    · exact absurd hc (D.not_isConj_cycle3_cycle33 S.pow₁ hw3 hu h)
    · exact absurd hc (D.not_isConj_cycle3_cycle333 S.pow₁ hw3 hu h)

theorem eq_of_isConj_mem_closure_two (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) {u : G}
    (hu : u ∈ Subgroup.closure ({(x₁ : G), (x₂ : G)} : Set G)) (hc : IsConj (x₁ : G) u) :
    u = (x₁ : G) ∨ u = (x₁ : G)⁻¹ ∨ u = (x₂ : G) ∨ u = (x₂ : G)⁻¹ := by
  obtain ⟨a, b, rfl⟩ := D.exists_zpow_of_mem_closure_two S hu
  have hw3 : (x₁ ^ a * x₂ ^ b) ^ 3 = 1 := by simpa using D.pow_three_torus S a b 0
  have hρ : ρ (x₁ ^ a * x₂ ^ b) = x1p ^ a * x2p ^ b := by simpa using rho_torus S a b 0
  have hwG : ((x₁ ^ a * x₂ ^ b : ↥(centralizer ({t} : Set G))) : G) =
      (x₁ : G) ^ a * (x₂ : G) ^ b := by simp
  rw [← hwG] at hc ⊢
  have hs := D.card_support_rho_eq_three S hw3 hc
  rw [hρ] at hs
  rcases torus_two_cases a b hs with h | h | h | h
  · rw [D.eq_of_rho_eq hw3 S.pow₁ (hρ.trans (h.trans S.rho₁.symm))]
    exact Or.inl rfl
  · rw [D.eq_of_rho_eq hw3 (by rw [inv_pow, S.pow₁, inv_one])
      (by rw [hρ, h, map_inv, S.rho₁])]
    exact Or.inr (Or.inl (by simp))
  · rw [D.eq_of_rho_eq hw3 S.pow₂ (hρ.trans (h.trans S.rho₂.symm))]
    exact Or.inr (Or.inr (Or.inl rfl))
  · rw [D.eq_of_rho_eq hw3 (by rw [inv_pow, S.pow₂, inv_one])
      (by rw [hρ, h, map_inv, S.rho₂])]
    exact Or.inr (Or.inr (Or.inr (by simp)))

theorem eq_of_isConj_mem_closure_three (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) {u : G}
    (hu : u ∈ Subgroup.closure ({(x₁ : G), (x₂ : G), (x₃ : G)} : Set G))
    (hc : IsConj (x₁ : G) u) :
    u = (x₁ : G) ∨ u = (x₁ : G)⁻¹ ∨ u = (x₂ : G) ∨ u = (x₂ : G)⁻¹ ∨ u = (x₃ : G) ∨
      u = (x₃ : G)⁻¹ := by
  obtain ⟨a, b, c, rfl⟩ := D.exists_zpow_of_mem_closure_three S hu
  have hw3 := D.pow_three_torus S a b c
  have hρ := rho_torus S a b c
  have hwG : ((x₁ ^ a * x₂ ^ b * x₃ ^ c : ↥(centralizer ({t} : Set G))) : G) =
      (x₁ : G) ^ a * (x₂ : G) ^ b * (x₃ : G) ^ c := by simp
  rw [← hwG] at hc ⊢
  have hs := D.card_support_rho_eq_three S hw3 hc
  rw [hρ] at hs
  rcases torus_three_cases a b c hs with h | h | h | h | h | h
  · rw [D.eq_of_rho_eq hw3 S.pow₁ (hρ.trans (h.trans S.rho₁.symm))]
    exact Or.inl rfl
  · rw [D.eq_of_rho_eq hw3 (by rw [inv_pow, S.pow₁, inv_one])
      (by rw [hρ, h, map_inv, S.rho₁])]
    exact Or.inr (Or.inl (by simp))
  · rw [D.eq_of_rho_eq hw3 S.pow₂ (hρ.trans (h.trans S.rho₂.symm))]
    exact Or.inr (Or.inr (Or.inl rfl))
  · rw [D.eq_of_rho_eq hw3 (by rw [inv_pow, S.pow₂, inv_one])
      (by rw [hρ, h, map_inv, S.rho₂])]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by simp))))
  · rw [D.eq_of_rho_eq hw3 S.pow₃ (hρ.trans (h.trans S.rho₃.symm))]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · rw [D.eq_of_rho_eq hw3 (by rw [inv_pow, S.pow₃, inv_one])
      (by rw [hρ, h, map_inv, S.rho₃])]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simp)))))

omit [Finite G] in
theorem injective_six (_D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    Function.Injective
      (![(x₁ : G), (x₁ : G)⁻¹, (x₂ : G), (x₂ : G)⁻¹, (x₃ : G), (x₃ : G)⁻¹] : Fin 6 → G) := by
  let g : Fin 6 → ↥(centralizer ({t} : Set G)) := ![x₁, x₁⁻¹, x₂, x₂⁻¹, x₃, x₃⁻¹]
  have hg : (![(x₁ : G), (x₁ : G)⁻¹, (x₂ : G), (x₂ : G)⁻¹, (x₃ : G), (x₃ : G)⁻¹] :
      Fin 6 → G) = fun i => (g i : G) := by
    funext i
    fin_cases i <;> simp [g]
  have hρg : (fun i => ρ (g i)) = ![x1p, x1p⁻¹, x2p, x2p⁻¹, x3p, x3p⁻¹] := by
    funext i
    fin_cases i <;> simp [g, S.rho₁, S.rho₂, S.rho₃]
  have hinj : Function.Injective (fun i => ρ (g i)) := by
    rw [hρg]
    decide
  rw [hg]
  exact Subtype.val_injective.comp (Function.Injective.of_comp hinj : Function.Injective g)

omit [Finite G] in
theorem card_closure_two (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    Nat.card ↥(Subgroup.closure ({(x₁ : G), (x₂ : G)} : Set G)) = 9 := by
  have hX₁ : (x₁ : G) ^ 3 = 1 := by simpa using congrArg Subtype.val S.pow₁
  have hX₂ : (x₂ : G) ^ 3 = 1 := by simpa using congrArg Subtype.val S.pow₂
  let f : Fin 3 × Fin 3 → ↥(Subgroup.closure ({(x₁ : G), (x₂ : G)} : Set G)) := fun p =>
    ⟨(x₁ : G) ^ (p.1 : ℕ) * (x₂ : G) ^ (p.2 : ℕ),
      mul_mem (pow_mem (subset_closure (by simp)) _) (pow_mem (subset_closure (by simp)) _)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, j⟩ ⟨i', j'⟩ h
      have h1 : (x₁ : G) ^ (i : ℕ) * (x₂ : G) ^ (j : ℕ) =
          (x₁ : G) ^ (i' : ℕ) * (x₂ : G) ^ (j' : ℕ) := congrArg Subtype.val h
      have h2 : x₁ ^ (i : ℕ) * x₂ ^ (j : ℕ) = x₁ ^ (i' : ℕ) * x₂ ^ (j' : ℕ) :=
        Subtype.ext (by simpa using h1)
      have h3 := congrArg ρ h2
      simp only [map_mul, map_pow, S.rho₁, S.rho₂] at h3
      obtain ⟨rfl, rfl⟩ := torus_two_injective i j i' j' h3
      rfl
    · rintro ⟨u, hu⟩
      obtain ⟨a, b, rfl⟩ := D.exists_zpow_of_mem_closure_two S hu
      obtain ⟨i, hi⟩ := exists_fin_pow_of_pow_three hX₁ a
      obtain ⟨j, hj⟩ := exists_fin_pow_of_pow_three hX₂ b
      exact ⟨(i, j), Subtype.ext (by simp [f, hi, hj])⟩
  rw [← Nat.card_eq_of_bijective f hf]
  simp

omit [Finite G] in
theorem card_closure_three (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    Nat.card ↥(Subgroup.closure ({(x₁ : G), (x₂ : G), (x₃ : G)} : Set G)) = 27 := by
  have hX₁ : (x₁ : G) ^ 3 = 1 := by simpa using congrArg Subtype.val S.pow₁
  have hX₂ : (x₂ : G) ^ 3 = 1 := by simpa using congrArg Subtype.val S.pow₂
  have hX₃ : (x₃ : G) ^ 3 = 1 := by simpa using congrArg Subtype.val S.pow₃
  let f : Fin 3 × Fin 3 × Fin 3 → ↥(Subgroup.closure ({(x₁ : G), (x₂ : G), (x₃ : G)} : Set G)) :=
    fun p =>
    ⟨(x₁ : G) ^ (p.1 : ℕ) * (x₂ : G) ^ (p.2.1 : ℕ) * (x₃ : G) ^ (p.2.2 : ℕ),
      mul_mem (mul_mem (pow_mem (subset_closure (by simp)) _)
        (pow_mem (subset_closure (by simp)) _)) (pow_mem (subset_closure (by simp)) _)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
      have h1 : (x₁ : G) ^ (i : ℕ) * (x₂ : G) ^ (j : ℕ) * (x₃ : G) ^ (k : ℕ) =
          (x₁ : G) ^ (i' : ℕ) * (x₂ : G) ^ (j' : ℕ) * (x₃ : G) ^ (k' : ℕ) :=
        congrArg Subtype.val h
      have h2 : x₁ ^ (i : ℕ) * x₂ ^ (j : ℕ) * x₃ ^ (k : ℕ) =
          x₁ ^ (i' : ℕ) * x₂ ^ (j' : ℕ) * x₃ ^ (k' : ℕ) :=
        Subtype.ext (by simpa using h1)
      have h3 := congrArg ρ h2
      simp only [map_mul, map_pow, S.rho₁, S.rho₂, S.rho₃] at h3
      obtain ⟨rfl, rfl, rfl⟩ := torus_three_injective i j k i' j' k' h3
      rfl
    · rintro ⟨u, hu⟩
      obtain ⟨a, b, c, rfl⟩ := D.exists_zpow_of_mem_closure_three S hu
      obtain ⟨i, hi⟩ := exists_fin_pow_of_pow_three hX₁ a
      obtain ⟨j, hj⟩ := exists_fin_pow_of_pow_three hX₂ b
      obtain ⟨k, hk⟩ := exists_fin_pow_of_pow_three hX₃ c
      exact ⟨(i, j, k), Subtype.ext (by simp [f, hi, hj, hk])⟩
  rw [← Nat.card_eq_of_bijective f hf]
  simp

end LyData

end Torus

end CFSG.Sporadic.Recognition.LyonsSims
