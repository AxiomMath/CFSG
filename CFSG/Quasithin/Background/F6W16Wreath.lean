module

public import CFSG.Quasithin.Background.F6CatRecogTools2
public import CFSG.CharacterTheory.Semidihedral.ElementOrders

public section

namespace CFSG.Quasithin

namespace F6

namespace WreathRes

@[expose] noncomputable def involutionCount (G : Type*) [Group G] : ℕ :=
  Nat.card {x : G // orderOf x = 2}

theorem involutionCount_congr {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') :
    involutionCount G = involutionCount G' :=
  Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
    change orderOf x = 2 ↔ orderOf (e x) = 2
    rw [MulEquiv.orderOf_eq])

theorem involutionCount_eq_card (G : Type*) [Group G] :
    involutionCount G = Nat.card {x : G // x ^ 2 = 1 ∧ x ≠ 1} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => orderOf_eq_prime_iff)

abbrev Z4WrZ2 : Type := Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2)

abbrev wreathSwap : Z4WrZ2 := ⟨1, Multiplicative.ofAdd 1⟩

theorem card_z4WrZ2 : Nat.card Z4WrZ2 = 32 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_of_index_two {H : Subgroup Z4WrZ2} (hH : H.index = 2) : Nat.card H = 16 := by
  have h := H.card_mul_index
  rw [hH, card_z4WrZ2] at h
  omega

theorem exists_eq_sq_of_right_eq_one :
    ∀ x : Z4WrZ2, x ^ 2 = 1 → x.right = 1 → ∃ y : Z4WrZ2, x = y ^ 2 := by
  decide

theorem exists_eq_sq_mul_sq_mul_swap_of_right_ne_one :
    ∀ x : Z4WrZ2, x ^ 2 = 1 → x.right ≠ 1 → ∃ y z : Z4WrZ2, x = y ^ 2 * z ^ 2 * wreathSwap := by
  decide

theorem card_involutions : Nat.card {x : Z4WrZ2 // x ^ 2 = 1 ∧ x ≠ 1} = 7 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_base_involutions :
    Nat.card {x : Z4WrZ2 // (x ^ 2 = 1 ∧ x ≠ 1) ∧ x.right = 1} = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem mem_iff_of_index_two {H : Subgroup Z4WrZ2} (hH : H.index = 2) {x : Z4WrZ2}
    (hx : x ^ 2 = 1) : x ∈ H ↔ x.right = 1 ∨ wreathSwap ∈ H := by
  by_cases hr : x.right = 1
  · obtain ⟨y, hy⟩ := exists_eq_sq_of_right_eq_one x hx hr
    exact iff_of_true (hy ▸ Subgroup.sq_mem_of_index_two hH y) (Or.inl hr)
  · obtain ⟨y, z, hyz⟩ := exists_eq_sq_mul_sq_mul_swap_of_right_ne_one x hx hr
    have h : x ∈ H ↔ wreathSwap ∈ H := by
      rw [hyz]
      exact mul_mem_cancel_left
        (H.mul_mem (Subgroup.sq_mem_of_index_two hH y) (Subgroup.sq_mem_of_index_two hH z))
    rw [h, or_iff_right hr]

theorem involutionCount_of_index_two {H : Subgroup Z4WrZ2} (hH : H.index = 2) :
    involutionCount H = 3 ∨ involutionCount H = 7 := by
  have e : {x : H // orderOf x = 2} ≃ {x : Z4WrZ2 // x ∈ H ∧ orderOf x = 2} :=
    (Equiv.subtypeEquivRight (q := fun x : H => orderOf (x : Z4WrZ2) = 2) fun x => by
      rw [Subgroup.orderOf_coe]).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ H) fun x => orderOf x = 2)
  have hiff : ∀ x : Z4WrZ2, (x ∈ H ∧ orderOf x = 2) ↔
      (x ^ 2 = 1 ∧ x ≠ 1) ∧ (x.right = 1 ∨ wreathSwap ∈ H) := fun x => by
    rw [orderOf_eq_prime_iff]
    exact ⟨fun ⟨hxH, hx⟩ => ⟨hx, (mem_iff_of_index_two hH hx.1).1 hxH⟩,
      fun ⟨hx, h⟩ => ⟨(mem_iff_of_index_two hH hx.1).2 h, hx⟩⟩
  have hc := Nat.card_congr (e.trans (Equiv.subtypeEquivRight hiff))
  by_cases ht : wreathSwap ∈ H
  · right
    rw [involutionCount, hc, ← card_involutions]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [ht])
  · left
    rw [involutionCount, hc, ← card_base_involutions]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [ht])

theorem involutionCount_dihedral_eight : involutionCount (DihedralGroup 8) = 9 := by
  rw [involutionCount_eq_card, Nat.card_eq_fintype_card]
  decide

theorem involutionCount_semidihedral_four :
    involutionCount (CFSG.Open.SemidihedralGroup 4) = 5 := by
  have hn : 3 ≤ 4 := by norm_num
  have e : {g : CFSG.Open.SemidihedralGroup 4 // orderOf g = 2} ≃
      {c : ZMod (CFSG.Semidihedral.modulus 4) × ZMod 2 //
        (c.2 = 0 ∧ c.1 = (CFSG.Semidihedral.half 4 : ZMod (CFSG.Semidihedral.modulus 4))) ∨
          (c.2 = 1 ∧ c.1.val % 2 = 0)} :=
    (CFSG.Semidihedral.coordinateEquiv 4 hn).subtypeEquiv fun g => by
      obtain ⟨⟨i, e⟩, rfl⟩ := (CFSG.Semidihedral.coordinateEquiv 4 hn).symm.surjective g
      rw [Equiv.apply_symm_apply]
      change orderOf (CFSG.Semidihedral.element 4 hn i e) = 2 ↔ _
      rcases CFSG.Semidihedral.exponent_cases e with rfl | rfl
      · rw [CFSG.Semidihedral.rotation_involution_iff]
        simp
      · rw [CFSG.Semidihedral.outside_involution_iff]
        simp
  rw [involutionCount, Nat.card_congr e, Nat.card_eq_fintype_card]
  decide

end WreathRes

end F6

end CFSG.Quasithin
