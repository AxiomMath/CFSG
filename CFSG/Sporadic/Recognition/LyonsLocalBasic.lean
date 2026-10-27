module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Recognition.LyonsAS4Centr
public import CFSG.Sporadic.Recognition.LyonsAS4Two

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup

@[expose] def swapP : Perm (Fin 11) := swap 0 3 * swap 1 4 * swap 2 5 * swap 9 10

@[expose] def swapP23 : Perm (Fin 11) := swap 3 6 * swap 4 7 * swap 5 8 * swap 9 10

theorem sign_swapP : sign swapP = 1 := by decide
theorem sign_swapP23 : sign swapP23 = 1 := by decide
theorem swapP_conj_x1p : swapP * x1p * swapP⁻¹ = x2p := by decide
theorem swapP_conj_x2p : swapP * x2p * swapP⁻¹ = x1p := by decide
theorem swapP_conj_x3p : swapP * x3p * swapP⁻¹ = x3p := by decide
theorem swapP23_conj_x2p : swapP23 * x2p * swapP23⁻¹ = x3p := by decide
theorem swapP23_conj_x3p : swapP23 * x3p * swapP23⁻¹ = x2p := by decide
theorem swapP23_conj_x1p : swapP23 * x1p * swapP23⁻¹ = x1p := by decide
theorem swapP23_fix : swapP23 0 = 0 ∧ swapP23 1 = 1 ∧ swapP23 2 = 2 := by decide

section Setup

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}

structure LyStd (ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11))
    (x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))) : Prop where
  pow₁ : x₁ ^ 3 = 1
  pow₂ : x₂ ^ 3 = 1
  pow₃ : x₃ ^ 3 = 1
  rho₁ : ρ x₁ = x1p
  rho₂ : ρ x₂ = x2p
  rho₃ : ρ x₃ = x3p

namespace LyData

omit [Finite G] in
theorem exists_lift_x2p (D : LyData G t ρ) :
    ∃ x : ↥(centralizer ({t} : Set G)), x ^ 3 = 1 ∧ ρ x = x2p := by
  obtain ⟨c, hc, hc3⟩ := D.cover.exists_lift_cube_one (p := x2p)
    (by rw [sign_of_cycleType, cycleType_x2p]; decide) x2p_pow_three
  exact ⟨c, hc3, hc⟩

omit [Finite G] in
theorem exists_lift_x3p (D : LyData G t ρ) :
    ∃ x : ↥(centralizer ({t} : Set G)), x ^ 3 = 1 ∧ ρ x = x3p := by
  obtain ⟨c, hc, hc3⟩ := D.cover.exists_lift_cube_one (p := x3p)
    (by rw [sign_of_cycleType, cycleType_x3p]; decide) x3p_pow_three
  exact ⟨c, hc3, hc⟩

omit [Finite G] in
theorem exists_lyStd (D : LyData G t ρ) :
    ∃ x₁ x₂ x₃ : ↥(centralizer ({t} : Set G)), LyStd ρ x₁ x₂ x₃ := by
  obtain ⟨x₁, h₁, r₁⟩ := D.exists_lift_x1p
  obtain ⟨x₂, h₂, r₂⟩ := D.exists_lift_x2p
  obtain ⟨x₃, h₃, r₃⟩ := D.exists_lift_x3p
  exact ⟨x₁, x₂, x₃, ⟨h₁, h₂, h₃, r₁, r₂, r₃⟩⟩

omit [Finite G] in
theorem eq_of_rho_eq (D : LyData G t ρ) {a b : ↥(centralizer ({t} : Set G))} (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1)
    (h : ρ a = ρ b) : a = b :=
  D.cover.eq_of_rho_eq_of_pow_three ha hb h

omit [Finite G] in
theorem conj_eq_of_rho (D : LyData G t ρ) {a b g : ↥(centralizer ({t} : Set G))}
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (h : ρ g * ρ a * (ρ g)⁻¹ = ρ b) : g * a * g⁻¹ = b := by
  refine D.eq_of_rho_eq ?_ hb ?_
  · rw [conj_pow, ha]; group
  · rw [map_mul, map_mul, map_inv, h]

omit [Finite G] in
theorem exists_swap (D : LyData G t ρ) {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}
    (S : LyStd ρ x₁ x₂ x₃) :
    ∃ s : ↥(centralizer ({t} : Set G)), s * x₁ * s⁻¹ = x₂ ∧ s * x₂ * s⁻¹ = x₁ ∧
      s * x₃ * s⁻¹ = x₃ ∧ ρ s = swapP := by
  obtain ⟨s, hs⟩ := D.cover.exists_lift sign_swapP
  refine ⟨s, D.conj_eq_of_rho S.pow₁ S.pow₂ ?_, D.conj_eq_of_rho S.pow₂ S.pow₁ ?_,
    D.conj_eq_of_rho S.pow₃ S.pow₃ ?_, hs⟩
  · rw [hs, S.rho₁, S.rho₂]; exact swapP_conj_x1p
  · rw [hs, S.rho₂, S.rho₁]; exact swapP_conj_x2p
  · rw [hs, S.rho₃]; exact swapP_conj_x3p

omit [Finite G] in
theorem exists_swap23 (D : LyData G t ρ) {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}
    (S : LyStd ρ x₁ x₂ x₃) :
    ∃ u : ↥(centralizer ({t} : Set G)), u * x₂ * u⁻¹ = x₃ ∧ u * x₃ * u⁻¹ = x₂ ∧
      u * x₁ * u⁻¹ = x₁ ∧ ρ u ∈ fix012 := by
  obtain ⟨u, hu⟩ := D.cover.exists_lift sign_swapP23
  refine ⟨u, D.conj_eq_of_rho S.pow₂ S.pow₃ ?_, D.conj_eq_of_rho S.pow₃ S.pow₂ ?_,
    D.conj_eq_of_rho S.pow₁ S.pow₁ ?_, ?_⟩
  · rw [hu, S.rho₂, S.rho₃]; exact swapP23_conj_x2p
  · rw [hu, S.rho₃, S.rho₂]; exact swapP23_conj_x3p
  · rw [hu, S.rho₁]; exact swapP23_conj_x1p
  · rw [hu]; exact swapP23_fix

theorem not_isConj_cycle3_cycle33 (D : LyData G t ρ) {u w : ↥(centralizer ({t} : Set G))}
    (hu3 : u ^ 3 = 1) (hw3 : w ^ 3 = 1) (hu : (ρ u).cycleType = {3})
    (hw : (ρ w).cycleType = {3, 3}) : ¬ IsConj (u : G) (w : G) := by
  obtain ⟨x, hx3, hx⟩ := D.exists_lift_x1p
  obtain ⟨y, hy3, hy⟩ := D.exists_lift_y12p
  have h1 : IsConj u x := D.cover.isConj_of_cycleType_eq hu3 hx3 (by rw [hu, hx, cycleType_x1p])
  have h2 : IsConj w y := D.cover.isConj_of_cycleType_eq hw3 hy3 (by rw [hw, hy, cycleType_y12p])
  have h1' : IsConj (u : G) (x : G) := (centralizer ({t} : Set G)).subtype.map_isConj h1
  have h2' : IsConj (w : G) (y : G) := (centralizer ({t} : Set G)).subtype.map_isConj h2
  intro hc
  exact D.not_isConj_x1p_y12p hx3 hy3 hx hy (h1'.symm.trans (hc.trans h2'))

theorem cycleType_x2p_mul_x1p : (x2p * x1p).cycleType = {3, 3} := by
  rw [show x2p * x1p = y12p from disjoint_x1p_x2p.commute.symm.eq, cycleType_y12p]

theorem cycleType_x2p_mul_x1p_sq : (x2p * x1p ^ 2).cycleType = {3, 3} := by
  have hd : Disjoint x2p (x1p ^ 2) := by
    show ∀ x : Fin 11, x2p x = x ∨ (x1p ^ 2) x = x
    decide
  have hinv : x1p ^ 2 = x1p⁻¹ := by decide
  rw [hd.cycleType_mul, hinv, cycleType_inv, cycleType_x1p, cycleType_x2p]
  rfl

theorem zpow_eq_one_of_conj_mul (D : LyData G t ρ) {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}
    (S : LyStd ρ x₁ x₂ x₃) {m : G} {k : ℤ}
    (hm : m * (x₂ : G) * m⁻¹ = (x₂ : G) * (x₁ : G) ^ k) : (x₁ : G) ^ k = 1 := by
  have hX3 : (x₁ : G) ^ 3 = 1 := by
    have := congrArg Subtype.val S.pow₁
    simpa using this
  have hc : x₂ * x₁ = x₁ * x₂ :=
    D.cover.commute_of_rho_commute_pow_three S.pow₁
      (by rw [S.rho₁, S.rho₂]; exact disjoint_x1p_x2p.commute.symm.eq)
  have hu : (ρ x₂).cycleType = {3} := by rw [S.rho₂, cycleType_x2p]
  rcases zpow_cases hX3 k with h1 | h1 | h1
  · exact h1
  · exfalso
    rw [h1] at hm
    have hw3 : (x₂ * x₁) ^ 3 = 1 := by
      rw [Commute.mul_pow (show Commute x₂ x₁ from hc), S.pow₂, S.pow₁, one_mul]
    have hw : (ρ (x₂ * x₁)).cycleType = {3, 3} := by
      rw [map_mul, S.rho₁, S.rho₂]; exact cycleType_x2p_mul_x1p
    exact D.not_isConj_cycle3_cycle33 S.pow₂ hw3 hu hw (isConj_iff.2 ⟨m, hm⟩)
  · exfalso
    rw [h1] at hm
    have hw3 : (x₂ * x₁ ^ 2) ^ 3 = 1 := by
      rw [Commute.mul_pow
        (show Commute x₂ (x₁ ^ 2) from Commute.pow_right (show Commute x₂ x₁ from hc) 2),
        S.pow₂, ← pow_mul, mul_comm 2 3, pow_mul, S.pow₁, one_pow, one_mul]
    have hw : (ρ (x₂ * x₁ ^ 2)).cycleType = {3, 3} := by
      rw [map_mul, map_pow, S.rho₁, S.rho₂]; exact cycleType_x2p_mul_x1p_sq
    refine D.not_isConj_cycle3_cycle33 S.pow₂ hw3 hu hw (isConj_iff.2 ⟨m, ?_⟩)
    rw [hm]
    simp

theorem commute_of_comm_mem_zpowers (D : LyData G t ρ) {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}
    (S : LyStd ρ x₁ x₂ x₃) {m : G}
    (hcomm : m * (x₂ : G) * m⁻¹ * (x₂ : G)⁻¹ ∈ zpowers (x₁ : G)) :
    m * (x₂ : G) = (x₂ : G) * m := by
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hcomm
  have hc : (x₂ : G) * (x₁ : G) = (x₁ : G) * (x₂ : G) := by
    have := congrArg Subtype.val
      (D.cover.commute_of_rho_commute_pow_three S.pow₁
        (g := x₂) (by rw [S.rho₁, S.rho₂]; exact disjoint_x1p_x2p.commute.symm.eq))
    simpa using this
  have hzc : (x₁ : G) ^ k * (x₂ : G) = (x₂ : G) * (x₁ : G) ^ k :=
    ((Commute.zpow_left (show Commute (x₁ : G) (x₂ : G) from hc.symm) k)).eq
  have hm : m * (x₂ : G) * m⁻¹ = (x₂ : G) * (x₁ : G) ^ k := by
    rw [← hzc, hk]; group
  have h1 := D.zpow_eq_one_of_conj_mul S hm
  rw [h1] at hm
  calc m * (x₂ : G) = m * (x₂ : G) * m⁻¹ * m := by group
    _ = (x₂ : G) * 1 * m := by rw [hm]
    _ = (x₂ : G) * m := by rw [mul_one]

end LyData

end Setup

end CFSG.Sporadic.Recognition.LyonsSims
