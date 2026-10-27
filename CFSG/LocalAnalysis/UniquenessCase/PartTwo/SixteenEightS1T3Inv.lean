module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3InvA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

theorem ThreeNat.eight_le_card (h : ThreeNat A L T) : 8 ≤ Nat.card W := by
  obtain ⟨I, hZI, _hIU, hnat⟩ := SumOfNatShape.exists_summand h.sum (0 : Fin 3)
  have h8 := SumOfNatShape.eight_mul_card_le h.quasi hnat
  haveI : Nonempty ↥(fixV L) := ⟨1⟩
  have hZ1 : 1 ≤ Nat.card ↥(fixV L) := Nat.card_pos
  have hIleW : Nat.card ↥I ≤ Nat.card W := Subgroup.card_le_card_group I
  calc 8 = 8 * 1 := (mul_one 8).symm
    _ ≤ 8 * Nat.card ↥(fixV L) := Nat.mul_le_mul_left 8 hZ1
    _ ≤ Nat.card ↥I := h8
    _ ≤ Nat.card W := hIleW

theorem ThreeNat.eight_mul_card_fixV_le (h : ThreeNat A L T) {t : MulAut W} (ht : t ∈ A)
    (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    8 * Nat.card ↥(fixV (Subgroup.zpowers t)) ≤ Nat.card W := by
  have hker : (commHom t).ker = fixV (Subgroup.zpowers t) := ker_commHom t
  have hcard := Subgroup.card_ker_mul_card_range (commHom t)
  have hrange8 : 8 ≤ Nat.card (commHom t).range := by
    have htN : t ∈ Subgroup.normalizer (L : Set (MulAut W)) := h.normal ht
    have htZ : (fixV L).map t.toMonoidHom = fixV L := s16t3_inv_map_fixV_normalizer htN
    obtain ⟨I, hZI, hind, hsup, hnat⟩ := s16t3_inv_exists_family h.sum
    by_cases hcaseA : ∃ i : Fin 3, ¬ I i ≤ (I i).map t.toMonoidHom
    · obtain ⟨i, hi⟩ := hcaseA
      exact s16t3_inv_eight_le_range_of_move h.quasi (hnat i) htN htZ hi
    · simp only [not_exists, not_not] at hcaseA
      have hstab : ∀ i, I i = (I i).map t.toMonoidHom := by
        intro i
        refine Subgroup.eq_of_le_of_card_ge (hcaseA i) ?_
        exact le_of_eq (Subgroup.card_map_of_injective t.injective)
      have hex : ∀ i, ∃ u ∈ I i, t u * u⁻¹ ∉ fixV L := by
        intro i
        by_contra hcontra
        rw [not_exists] at hcontra
        have htriv : ∀ u ∈ I i, t u * u⁻¹ ∈ fixV L := by
          intro u hu
          by_contra hz
          exact hcontra u ⟨hu, hz⟩
        exact ht1 (s16t3_inv_eq_one_of_trivial_on_summand h ht ht2 hsup hnat hstab htriv)
      let u : Fin 3 → W := fun i => Classical.choose (hex i)
      have huI : ∀ i, u i ∈ I i := fun i => (Classical.choose_spec (hex i)).1
      have huZ : ∀ i, t (u i) * (u i)⁻¹ ∉ fixV L :=
        fun i => (Classical.choose_spec (hex i)).2
      let c : Fin 3 → W := fun i => t (u i) * (u i)⁻¹
      have hcI : ∀ i, c i ∈ I i := by
        intro i
        have htui : t (u i) ∈ I i := by
          have hmem : t (u i) ∈ (I i).map t.toMonoidHom :=
            Subgroup.mem_map.2 ⟨u i, huI i, rfl⟩
          rwa [← hstab i] at hmem
        exact mul_mem htui (Subgroup.inv_mem _ (huI i))
      have hcZ : ∀ i, c i ∉ fixV L := huZ
      have hclos := s16t3_inv_card_closure_eq_eight (fun w => h.elem w) hind hcI hcZ
      have hcle : Subgroup.closure (Set.range c) ≤ (commHom t).range := by
        rw [Subgroup.closure_le]
        rintro x ⟨i, rfl⟩
        exact ⟨u i, rfl⟩
      calc 8 = Nat.card (Subgroup.closure (Set.range c)) := hclos.symm
        _ ≤ Nat.card (commHom t).range := Subgroup.card_le_of_le hcle
  calc 8 * Nat.card ↥(fixV (Subgroup.zpowers t))
      = 8 * Nat.card (commHom t).ker := by rw [hker]
    _ ≤ Nat.card (commHom t).ker * Nat.card (commHom t).range := by
        rw [mul_comm 8 (Nat.card (commHom t).ker)]
        exact Nat.mul_le_mul_left _ hrange8
    _ = Nat.card W := hcard

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
