module

public import CFSG.Quasithin.H13.GoldschmidtQ8SqE9Odd

public section

namespace CFSG.Quasithin.H13.Q8SqE9

open QuaternionGroup Subgroup

variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}

namespace Cfg

theorem mem_normalizer_J (h : Cfg A B) {w y : G}
    (hw : ∀ q ∈ A ⊔ B, w * q * w⁻¹ ∈ A ⊔ B) (hy3 : orderOf y = 3)
    (hyB : ∀ b ∈ B, y * b = b * y) (hyA : ∃ a ∈ A, y * a ≠ a * y)
    (hwy : w * y * w⁻¹ * y ∈ A ⊔ B) :
    w ∈ normalizer ((A ⊔ zpowers y : Subgroup G) : Set G) := by
  have huB : ∀ b' ∈ B, w * y * w⁻¹ * (w * b' * w⁻¹) = (w * b' * w⁻¹) * (w * y * w⁻¹) := by
    intro b' hb'
    calc w * y * w⁻¹ * (w * b' * w⁻¹) = w * (y * b') * w⁻¹ := by group
      _ = w * (b' * y) * w⁻¹ := by rw [hyB b' hb']
      _ = w * b' * w⁻¹ * (w * y * w⁻¹) := by group
  rcases h.map_conj_cases hw with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · have hqA : w * y * w⁻¹ * y ∈ A := by
      refine h.mem_of_comm hwy fun b hb => ?_
      have hb' : b ∈ B.map (MulAut.conj w).toMonoidHom := by rw [hB]; exact hb
      obtain ⟨b', hb'B, rfl⟩ := hb'
      have h1 := huB b' hb'B
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc w * y * w⁻¹ * y * (w * b' * w⁻¹) = w * y * w⁻¹ * (y * (w * b' * w⁻¹)) := by group
        _ = w * y * w⁻¹ * ((w * b' * w⁻¹) * y) := by
          rw [hyB (w * b' * w⁻¹) (by rw [← hB]; exact ⟨b', hb'B, rfl⟩)]
        _ = (w * y * w⁻¹ * (w * b' * w⁻¹)) * y := by group
        _ = ((w * b' * w⁻¹) * (w * y * w⁻¹)) * y := by rw [h1]
        _ = w * b' * w⁻¹ * (w * y * w⁻¹ * y) := by group
    have huJ : w * y * w⁻¹ ∈ A ⊔ zpowers y := by
      have : w * y * w⁻¹ = (w * y * w⁻¹ * y) * y⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hqA)
        (Subgroup.inv_mem _ (Subgroup.mem_sup_right (mem_zpowers y)))
    have hle : (A ⊔ zpowers y).map (MulAut.conj w).toMonoidHom ≤ A ⊔ zpowers y := by
      rw [Subgroup.map_sup, hA, MonoidHom.map_zpowers]
      exact sup_le le_sup_left (zpowers_le.mpr (by simpa using huJ))
    have heq : (A ⊔ zpowers y).map (MulAut.conj w).toMonoidHom = A ⊔ zpowers y :=
      Subgroup.eq_of_le_of_card_ge hle
        (by rw [Subgroup.card_map_of_injective (MulAut.conj w).injective])
    exact mem_normalizer_of_map_eq heq
  · exfalso
    obtain ⟨a, ha, hya⟩ := hyA
    have huA : ∀ m ∈ A, w * y * w⁻¹ * m = m * (w * y * w⁻¹) := by
      intro m hm
      have hm' : m ∈ B.map (MulAut.conj w).toMonoidHom := by rw [hB]; exact hm
      obtain ⟨b', hb', rfl⟩ := hm'
      simpa using huB b' hb'
    have hax : ∀ m ∈ A, y⁻¹ * m * y⁻¹⁻¹ = m ∨ y⁻¹ * m * y⁻¹⁻¹ = m⁻¹ := by
      intro m hm
      have h1 : y⁻¹ * m * y = (w * y * w⁻¹ * y)⁻¹ * m * (w * y * w⁻¹ * y) := by
        calc y⁻¹ * m * y = (w * y * w⁻¹ * y)⁻¹ * (w * y * w⁻¹ * m) * y := by group
          _ = (w * y * w⁻¹ * y)⁻¹ * (m * (w * y * w⁻¹)) * y := by rw [huA m hm]
          _ = (w * y * w⁻¹ * y)⁻¹ * m * (w * y * w⁻¹ * y) := by group
      rw [inv_inv, h1]
      simpa using h.conj_axis_Q (Subgroup.inv_mem _ hwy) hm
    have hodd : Odd (orderOf y⁻¹) := by rw [orderOf_inv, hy3]; decide
    apply hya
    have h2 := commute_of_inv_or hodd hax a ha
    calc y * a = y * (a * y⁻¹) * y := by group
      _ = y * (y⁻¹ * a) * y := by rw [h2]
      _ = a * y := by group

end Cfg

end CFSG.Quasithin.H13.Q8SqE9
