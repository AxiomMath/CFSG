module

public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport
public import CFSG.Permutation.FiveTransitive.FreeComplementCard

public section

namespace CFSG

namespace FiveTransitive.Degree31PairFixerBound

open MulAction

theorem card_le_two_thousand_forty_eight
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 2 Q)
    (hfixed : 6 ≤ Nat.card (fixedPoints Q X)) : Nat.card Q ≤ 2048 := by
  classical
  have hpar := hQ.card_modEq_card_fixedPoints X
  change Nat.card X % 2 = Nat.card (fixedPoints Q X) % 2 at hpar
  rw [Nat.card_eq_fintype_card,hcard] at hpar
  have hseven : 7 ≤ Nat.card (fixedPoints Q X) := by omega
  let b : Fin 7 ↪ fixedPoints Q X :=
    (Fin.castLEEmb hseven).trans (Finite.equivFin (fixedPoints Q X)).symm.toEmbedding
  let bX : Fin 7 ↪ X := b.trans (Function.Embedding.subtype _)
  let t : Set X := Set.range bX
  have ht : t.ncard = 7 := by
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
  have hC : Fintype.card C = 24 := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (tᶜ : Set X) = _
    rw [Nat.card_coe_set_eq,Set.ncard_compl,ht,Nat.card_eq_fintype_card,hcard]
  rw [Nat.card_eq_fintype_card (α := Fin 9 ↪ C),Fintype.card_embedding_eq,
    Fintype.card_fin,hC] at hd
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have he11 : e ≤ 11 := by
    by_contra hn
    have hd4096 : 4096 ∣ Nat.card Q := by
      rw [he]
      exact pow_dvd_pow 2 (by omega : 12 ≤ e)
    have hc := hd4096.trans hd
    norm_num [Nat.descFactorial] at hc
  rw [he]
  exact (Nat.pow_le_pow_right (by norm_num : 0 < 2) he11).trans (by norm_num)

end FiveTransitive.Degree31PairFixerBound

end CFSG
