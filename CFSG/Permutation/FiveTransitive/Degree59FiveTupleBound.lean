module

public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport
public import CFSG.Permutation.FiveTransitive.FreeComplementCard

public section

namespace CFSG

namespace FiveTransitive.Degree59FiveTupleBound

open MulAction

private theorem card_dvd_exterior_tuples
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 59)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P)
    (f k : ℕ) (hfk : 30 ≤ f + k)
    (hfixed : f ≤ Nat.card (fixedPoints Q X)) :
    Nat.card Q ∣ (59 - f).descFactorial k := by
  classical
  let b : Fin f ↪ fixedPoints Q X :=
    (Fin.castLEEmb hfixed).trans (Finite.equivFin (fixedPoints Q X)).symm.toEmbedding
  let bX : Fin f ↪ X := b.trans (Function.Embedding.subtype _)
  let t : Set X := Set.range bX
  have ht : t.ncard = f := by
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
  have hfree : ∀ q : Q, ∀ a : Fin k ↪ C, q • a = a → q = 1 := by
    intro q a hqa
    by_contra hq
    have hne : q.val.val ≠ 1 := fun he => hq (Subtype.ext (Subtype.ext he))
    have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5
      hnotAlt q.val.property hne
    rw [hcard] at hb
    let aX : Fin k → X := fun i => (a i).val
    have hf : Function.Injective aX := fun i j he => a.injective (Subtype.ext he)
    have hdis : Disjoint t (Set.range aX) := by
      apply Set.disjoint_left.mpr
      rintro x hx ⟨i,rfl⟩
      exact (a i).property hx
    have hsub : t ∪ Set.range aX ⊆ Function.fixedPoints q.val.val := by
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
  have hd := FreeComplementCard.card_dvd_of_free Q (Fin k ↪ C) hfree
  let _ : Fintype C := Fintype.ofFinite C
  have hC : Fintype.card C = 59 - f := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (tᶜ : Set X) = _
    rw [Nat.card_coe_set_eq,Set.ncard_compl,ht,Nat.card_eq_fintype_card,hcard]
  rw [Nat.card_eq_fintype_card (α := Fin k ↪ C),Fintype.card_embedding_eq,
    Fintype.card_fin,hC] at hd
  exact hd

theorem card_le_twentyFive
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 59)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 5 Q)
    (hfixed : 24 ≤ Nat.card (fixedPoints Q X)) : Nat.card Q ≤ 25 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hd := card_dvd_exterior_tuples P hcard h5 hnotAlt Q 24 6 (by norm_num) hfixed
  obtain ⟨a,ha⟩ := IsPGroup.iff_card.mp hQ
  have habound : a ≤ 2 := by
    by_contra hn
    have hpow : 5^3 ∣ Nat.card Q := by
      rw [ha]
      exact pow_dvd_pow 5 (by omega)
    have hc := hpow.trans hd
    norm_num [Nat.descFactorial] at hc
  rw [ha]
  exact (Nat.pow_le_pow_right (by norm_num : 0 < 5) habound).trans (by norm_num)

end FiveTransitive.Degree59FiveTupleBound

end CFSG
