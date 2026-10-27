module

public import CFSG.Quasithin.H13.A6Statements
public import CFSG.Quasithin.H13.A5OrthAct

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Quasithin CFSG.Quasithin.H13.A5.Orth

theorem q8_center : ∀ x : QuaternionGroup 2, (∀ g : QuaternionGroup 2, x * g = g * x) →
    x = 1 ∨ x = QuaternionGroup.a 2 := by
  decide +kernel

theorem q8_a_two_ne_one : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by
  decide

theorem card_q8_prod : Nat.card (QuaternionGroup 2 × QuaternionGroup 2) = 64 := by
  rw [Nat.card_prod, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem q8_central_of {P : Type} [Group P] {C : Subgroup P} (e : ↥C ≃* QuaternionGroup 2)
    (x : QuaternionGroup 2) (h : ∀ c ∈ C, ((e.symm x : ↥C) : P) * c = c * (e.symm x : ↥C)) :
    x = 1 ∨ x = QuaternionGroup.a 2 := by
  refine q8_center x fun g => ?_
  have h1 : e.symm x * e.symm g = e.symm g * e.symm x := Subtype.ext (h _ (e.symm g).2)
  have h2 := congrArg e h1
  simpa using h2

theorem nonempty_mulEquiv_q8Q8 {P : Type} [Group P] [Finite P] (hP : IsQ8Sq P) :
    Nonempty (P ≃* Q8Q8) := by
  obtain ⟨hcard, A, B, ⟨hAB, hsup⟩, ⟨eA⟩, ⟨eB⟩⟩ := hP
  let f : QuaternionGroup 2 × QuaternionGroup 2 →* P :=
    (mulPair hAB).comp (MonoidHom.prodMap eA.symm.toMonoidHom eB.symm.toMonoidHom)
  have hf : ∀ x y, f (x, y) = ((eA.symm x : ↥A) : P) * ((eB.symm y : ↥B) : P) := fun _ _ => rfl
  have hfs : Function.Surjective f := by
    intro p
    obtain ⟨⟨a, b⟩, hab⟩ := mulPair_surjective hAB hsup p
    refine ⟨(eA a, eB b), ?_⟩
    rw [hf, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    exact hab
  have hker2 : Nat.card f.ker = 2 := by
    have h1 := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker, card_q8_prod, MonoidHom.range_eq_top.2 hfs, Subgroup.card_top,
      hcard] at h1
    omega
  have hker : ∀ x y, f (x, y) = 1 →
      (x = 1 ∧ y = 1) ∨ (x = QuaternionGroup.a 2 ∧ y = QuaternionGroup.a 2) := by
    intro x y h
    rw [hf] at h
    have hab : ((eA.symm x : ↥A) : P) = ((eB.symm y : ↥B) : P)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hba : ((eB.symm y : ↥B) : P) = ((eA.symm x : ↥A) : P)⁻¹ :=
      eq_inv_of_mul_eq_one_right h
    have hx : x = 1 ∨ x = QuaternionGroup.a 2 := q8_central_of eA x fun c hc => by
      rw [hab]
      exact (show Commute ((eB.symm y : ↥B) : P) c from
        Subgroup.mem_centralizer_iff.mp (hAB hc) _ (eB.symm y).2).inv_left.eq
    have hy : y = 1 ∨ y = QuaternionGroup.a 2 := q8_central_of eB y fun c hc => by
      rw [hba]
      exact (show Commute c ((eA.symm x : ↥A) : P) from
        Subgroup.mem_centralizer_iff.mp (hAB (eA.symm x).2) c hc).inv_right.eq.symm
    have hne : ∀ (C : Subgroup P) (e : ↥C ≃* QuaternionGroup 2),
        ((e.symm (QuaternionGroup.a 2) : ↥C) : P) ≠ 1 := fun C e h1 => by
      apply q8_a_two_ne_one
      have h2 : e.symm (QuaternionGroup.a 2) = 1 := Subtype.ext h1
      simpa using congrArg e h2
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · rw [map_one, OneMemClass.coe_one, one_mul] at h
      exact absurd h (hne B eB)
    · rw [map_one, OneMemClass.coe_one, mul_one] at h
      exact absurd h (hne A eA)
    · exact Or.inr ⟨rfl, rfl⟩
  have hzz : f (QuaternionGroup.a 2, QuaternionGroup.a 2) = 1 := by
    by_contra hzz
    have hbot : f.ker = ⊥ := by
      rw [eq_bot_iff]
      rintro ⟨x, y⟩ hxy
      rcases hker x y (MonoidHom.mem_ker.1 hxy) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Subgroup.one_mem _
      · exact absurd (MonoidHom.mem_ker.1 hxy) hzz
    rw [hbot, Subgroup.card_bot] at hker2
    omega
  have hN : f.ker = Subgroup.normalClosure
      {((QuaternionGroup.a 2 : QuaternionGroup 2), (QuaternionGroup.a 2 : QuaternionGroup 2))} := by
    apply le_antisymm
    · rintro ⟨x, y⟩ hxy
      rcases hker x y (MonoidHom.mem_ker.1 hxy) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_normalClosure (Set.mem_singleton _)
    · exact Subgroup.normalClosure_le_normal
        (Set.singleton_subset_iff.2 (MonoidHom.mem_ker.2 hzz))
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hN).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective f hfs)).symm⟩

end CFSG.Quasithin.H13.A6
