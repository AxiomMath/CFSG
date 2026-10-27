module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KNine
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Blueprint CFSG.Sporadic.Schreier

namespace KM23

def ev (w : List ℕ) : ↥NativeSporadic.M23 :=
  (w.map fun i => if i = 0 then m23GenA else if i = 1 then m23GenB else m23GenB⁻¹).prod

def wb : List ℕ := [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1]

def wa : List ℕ := [0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1, 0, 2, 0, 1]

def wu1 : List ℕ := [0, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 2]

def wu2 : List ℕ := [1, 1]

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

end KM23

theorem eInvNine_m23 : EInvNine NativeSporadic.M23 := by
  obtain ⟨ha3, hb3, hab⟩ := KM23.rel_orders
  obtain ⟨hu₁, hu₂, hu, hu₁1, hu₂1, hu₁₂⟩ := KM23.rel_four
  obtain ⟨hva₁, hva₂, hvb₁, hvb₂⟩ := KM23.rel_four4
  have hconj : ∀ g t : ↥NativeSporadic.M23, g * t = (g * t * g⁻¹) * g := fun g t => by group
  have hcard : Nat.card (MulAut NativeSporadic.M23) ≤ 2 * Nat.card NativeSporadic.M23 :=
    m23_mulAut_card.trans (Nat.le_mul_of_pos_left _ (by norm_num))
  refine eInvNine_of_card_bound (N := 10200960) (m23_center_eq_bot') hcard
    (m23_card) (by decide +kernel) ha3 hb3 hab KM23.rel_dist hu₁ hu₂ hu hu₁1 hu₂1 hu₁₂ hva₁ hva₂
    hvb₁ hvb₂ (hconj _ _) (hconj _ _) (hconj _ _) (hconj _ _) KM23.rel_move

theorem eInvNine_of_mulEquiv_m23 {X : Type} [Group X] (e : X ≃* NativeSporadic.M23) :
    EInvNine X :=
  EInvNine.of_mulEquiv e eInvNine_m23

end CFSG.RankThree.PartTwo.Sec21.Hering214
