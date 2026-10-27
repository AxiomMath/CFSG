module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KCover
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier

namespace KM22

def ev (w : List ℕ) : ↥NativeSporadic.M22 :=
  (w.map fun i => if i = 0 then m22a else if i = 1 then m22b else m22b⁻¹).prod

def wb : List ℕ := [0, 1, 0, 1, 0, 2, 0, 2]

def wa : List ℕ := [0, 1, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1]

def wu1 : List ℕ := [2, 0, 1, 1, 0, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1]

def wu2 : List ℕ := [0, 2, 0, 1, 1, 0, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0]

set_option maxRecDepth 100000 in
theorem rel_orders : ev wa ^ 3 = 1 ∧ ev wb ^ 3 = 1 ∧ ev wa * ev wb = ev wb * ev wa := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rel_dist :
    ∀ i j k l : Fin 3, ev wa ^ (i : ℕ) * ev wb ^ (j : ℕ) = ev wa ^ (k : ℕ) * ev wb ^ (l : ℕ) →
      i = k ∧ j = l := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rel_four :
    ev wu1 * ev wu1 = 1 ∧ ev wu2 * ev wu2 = 1 ∧ ev wu1 * ev wu2 = ev wu2 * ev wu1 ∧
    ev wu1 ≠ 1 ∧ ev wu2 ≠ 1 ∧ ev wu1 ≠ ev wu2 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rel_four4 :
    Four4 (ev wu1) (ev wu2) (ev wa * ev wu1 * (ev wa)⁻¹) ∧
    Four4 (ev wu1) (ev wu2) (ev wa * ev wu2 * (ev wa)⁻¹) ∧
    Four4 (ev wu1) (ev wu2) (ev wb * ev wu1 * (ev wb)⁻¹) ∧
    Four4 (ev wu1) (ev wu2) (ev wb * ev wu2 * (ev wb)⁻¹) := by
  unfold Four4
  decide +kernel

set_option maxRecDepth 100000 in
theorem rel_move : ev wa * ev wu1 ≠ ev wu1 * ev wa := by decide +kernel

end KM22

theorem eInvNine_m22 : EInvNine NativeSporadic.M22 := by
  obtain ⟨ha3, hb3, hab⟩ := KM22.rel_orders
  obtain ⟨hu₁, hu₂, hu, hu₁1, hu₂1, hu₁₂⟩ := KM22.rel_four
  obtain ⟨hva₁, hva₂, hvb₁, hvb₂⟩ := KM22.rel_four4
  have hconj : ∀ g t : ↥NativeSporadic.M22, g * t = (g * t * g⁻¹) * g := fun g t => by group
  refine eInvNine_of_card_bound (N := 443520) (m22_center_eq_bot') m22_mulAut_card
    (m22_card) (by decide +kernel) ha3 hb3 hab KM22.rel_dist hu₁ hu₂ hu hu₁1 hu₂1 hu₁₂ hva₁ hva₂
    hvb₁ hvb₂ (hconj _ _) (hconj _ _) (hconj _ _) (hconj _ _) KM22.rel_move

theorem eInvNine_of_mulEquiv_m22 {X : Type} [Group X] (e : X ≃* NativeSporadic.M22) :
    EInvNine X :=
  EInvNine.of_mulEquiv e eInvNine_m22

theorem isPerfect_m22 : Group.IsPerfect NativeSporadic.M22 :=
  isPerfect_of_simple_noncomm fam_m22_simplicity.2.2 ⟨m22a, m22b, m22_gens_not_comm⟩

theorem eInvNine_of_isTripleCover_m22 {X : Type} [Group X] [Finite X]
    (h : Sec4.IsTripleCover X NativeSporadic.M22) : EInvNine X := by
  obtain ⟨hZ3, ⟨e⟩⟩ := h
  have hperf : Group.IsPerfect (X ⧸ Subgroup.center X) := isPerfect_of_mulEquiv e.symm isPerfect_m22
  exact eInvNine_of_central_quotient hZ3 hperf e eInvNine_m22

end CFSG.RankThree.PartTwo.Sec21.Hering214
