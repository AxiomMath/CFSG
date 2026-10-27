module

public import CFSG.Permutation.FiveTransitive.Degree28ThreeFreeReduction
public import CFSG.Permutation.FiveTransitive.Degree28FiveSevenFree
public import CFSG.Permutation.FiveTransitive.Degree28LargePrimeFree
public import CFSG.Permutation.FiveTransitive.HighDegreeHallReduction

public section

namespace CFSG

namespace FiveTransitive.Degree28TwoGroupReduction

open MulAction

theorem is_two_group
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : IsPGroup 2 (fixingSubgroup P s) := by
  classical
  apply IsPGroup.of_card
  apply Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
  intro p hp hd
  have hthree := Degree28ThreeFreeReduction.three_not_dvd_five_fixer_card P hcard h5 hnotAlt s hs
  obtain ⟨hfive,hseven⟩ := Degree28FiveSevenFree.five_and_seven_not_dvd_five_fixer_card
    P hcard h5 hnotAlt s hs
  by_cases hlarge : 11 ≤ p
  · let sf := s.toFinite.toFinset
    have he : (sf : Set X) = s := s.toFinite.coe_toFinset
    have hsf : sf.card = 5 := by rw [← Set.ncard_coe_finset,he]; exact hs
    have hn := Degree28LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt sf hsf p hp hlarge
    rw [he] at hn
    exact (hn hd).elim
  · have hle : p ≤ 10 := by omega
    have hcases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
      interval_cases p <;> norm_num at hp <;> norm_num
    rcases hcases with rfl | rfl | rfl | rfl
    · rfl
    · exact (hthree hd).elim
    · exact (hfive hd).elim
    · exact (hseven hd).elim

private theorem card_le_five_hundred_twelve
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 2 Q)
    (hfixed : 6 ≤ Nat.card (fixedPoints Q X)) : Nat.card Q ≤ 512 := by
  classical
  let b : Fin 6 ↪ fixedPoints Q X :=
    (Fin.castLEEmb hfixed).trans (Finite.equivFin (fixedPoints Q X)).symm.toEmbedding
  let bX : Fin 6 ↪ X := b.trans (Function.Embedding.subtype _)
  let t : Set X := Set.range bX
  have ht : t.ncard = 6 := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective bX.injective
  have htfix : t ⊆ fixedPoints Q X := by
    rintro x ⟨i,rfl⟩
    exact (b i).property
  let C : SubMulAction Q X :=
    { carrier := tᶜ
      smul_mem' := by
        intro q x hx
        change x ∉ t at hx
        change q • x ∉ t
        intro hqx
        have he : q • x = x := by
          simpa only [inv_smul_smul] using (htfix hqx q⁻¹).symm
        exact hx (he ▸ hqx) }
  have hfree : ∀ q : Q, ∀ a : Fin 9 ↪ C, q • a = a → q = 1 := by
    intro q a hqa
    by_contra hq
    have hne : q.val.val ≠ 1 := fun he => hq (Subtype.ext (Subtype.ext he))
    have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5
      hnotAlt q.val.property hne
    rw [hcard] at hb
    let f : Fin 9 → X := fun i => (a i).val
    have hf : Function.Injective f := fun i j he => a.injective (Subtype.ext he)
    have hdis : Disjoint t (Set.range f) := by
      apply Set.disjoint_left.mpr
      rintro x hx ⟨i,rfl⟩
      exact (a i).property hx
    have hsub : t ∪ Set.range f ⊆ Function.fixedPoints q.val.val := by
      intro x hx
      rcases hx with hx | ⟨i,rfl⟩
      · exact htfix hx q
      · exact congrArg Subtype.val (DFunLike.congr_fun hqa i)
    have hle := Set.ncard_le_ncard hsub
    rw [Set.ncard_union_eq hdis,ht,Set.ncard_range_of_injective hf,
      ← Nat.card_coe_set_eq,
      Nat.card_eq_fintype_card (α := Function.fixedPoints q.val.val), Equiv.Perm.card_fixedPoints,
      q.val.val.sum_cycleType,hcard] at hle
    simp only [Nat.card_fin] at hle
    omega
  have hd := FreeComplementCard.card_dvd_of_free Q (Fin 9 ↪ C) hfree
  let _ : Fintype C := Fintype.ofFinite C
  have hC : Fintype.card C = 22 := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (tᶜ : Set X) = _
    rw [Nat.card_coe_set_eq,Set.ncard_compl,ht,Nat.card_eq_fintype_card,hcard]
  rw [Nat.card_eq_fintype_card (α := Fin 9 ↪ C),Fintype.card_embedding_eq,
    Fintype.card_fin,hC] at hd
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have he9 : e ≤ 9 := by
    by_contra hn
    have hd1024 : 1024 ∣ Nat.card Q := by
      rw [he]
      exact pow_dvd_pow 2 (by omega : 10 ≤ e)
    have hc := hd1024.trans hd
    norm_num [Nat.descFactorial] at hc
  rw [he]
  exact (Nat.pow_le_pow_right (by norm_num : 0 < 2) he9).trans (by norm_num)

theorem card_bounds
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    2 ≤ Nat.card (fixingSubgroup P s) ∧ Nat.card (fixingSubgroup P s) ≤ 512 := by
  have hQ := is_two_group P hcard h5 hnotAlt s hs
  have hsub : s ⊆ fixedPoints (fixingSubgroup P s) X := by
    intro x hx q
    exact (mem_fixingSubgroup_iff P).mp q.property x hx
  have hfixed : 5 ≤ Nat.card (fixedPoints (fixingSubgroup P s) X) := by
    rw [Nat.card_coe_set_eq,← hs]
    exact Set.ncard_le_ncard hsub
  have hmod := hQ.card_modEq_card_fixedPoints X
  change Nat.card X % 2 = Nat.card (fixedPoints (fixingSubgroup P s) X) % 2 at hmod
  rw [Nat.card_eq_fintype_card,hcard] at hmod
  have hsix : 6 ≤ Nat.card (fixedPoints (fixingSubgroup P s) X) := by omega
  have hd : 2 ∣ Nat.card (fixingSubgroup P s) := even_iff_two_dvd.mp
    (Research.HighDegreeHallReduction.even_card_fixingSubgroup_of_five_transitive
      X P (by omega) h5 s hs)
  exact ⟨Nat.le_of_dvd Nat.card_pos hd,
    card_le_five_hundred_twelve P hcard h5 hnotAlt (fixingSubgroup P s) hQ hsix⟩

end FiveTransitive.Degree28TwoGroupReduction

end CFSG
