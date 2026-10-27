module

public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport
public import CFSG.Permutation.FiveTransitive.FreeComplementCard

public section

namespace CFSG

namespace FiveTransitive.Degree60TupleBounds

open MulAction

private theorem card_dvd_exterior_tuples
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 60)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P)
    (f k : ℕ) (hfk : 31 ≤ f + k)
    (hfixed : f ≤ Nat.card (fixedPoints Q X)) :
    Nat.card Q ∣ (60 - f).descFactorial k := by
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
  have hC : Fintype.card C = 60 - f := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (tᶜ : Set X) = _
    rw [Nat.card_coe_set_eq,Set.ncard_compl,ht,Nat.card_eq_fintype_card,hcard]
  rw [Nat.card_eq_fintype_card (α := Fin k ↪ C),Fintype.card_embedding_eq,
    Fintype.card_fin,hC] at hd
  exact hd

theorem two_pow_dvd_bound
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 60)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (a : ℕ)
    (ha : 2 ^ a ∣ Nat.card (fixingSubgroup P s)) : a ≤ 25 := by
  have hfix : 5 ≤ Nat.card (fixedPoints (fixingSubgroup P s) X) := by
    rw [Nat.card_coe_set_eq,← hs]
    exact Set.ncard_le_ncard (by
      intro x hx q
      exact (mem_fixingSubgroup_iff P).mp q.property x hx)
  have hd := card_dvd_exterior_tuples
    P hcard h5 hnotAlt (fixingSubgroup P s) 5 26 (by norm_num) hfix
  by_contra hn
  have hb : 2 ^ 26 ∣ Nat.card (fixingSubgroup P s) :=
    (pow_dvd_pow 2 (by omega : 26 ≤ a)).trans ha
  have hc := hb.trans hd
  norm_num [Nat.descFactorial] at hc

end FiveTransitive.Degree60TupleBounds

end CFSG
