module

public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport
public import CFSG.Permutation.FiveTransitive.FreeComplementCard

public section

namespace CFSG

namespace FiveTransitive.Degree39PrimeTupleDivisibility

open MulAction

theorem card_dvd_desc
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 39)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (k : ℕ) (height : 20 ≤ Nat.card (fixedPoints Q X) + k) :
    Nat.card Q ∣ (39 - Nat.card (fixedPoints Q X)).descFactorial k := by
  classical
  let C : SubMulAction Q X :=
    { carrier := (fixedPoints Q X)ᶜ
      smul_mem' := by
        intro q x hx
        change x ∉ fixedPoints Q X at hx
        change q • x ∉ fixedPoints Q X
        intro hqx
        have he : q • x = x := by
          simpa only [inv_smul_smul] using (hqx q⁻¹).symm
        exact hx (he ▸ hqx) }
  have hfree : ∀ q : Q, ∀ a : Fin k ↪ C, q • a = a → q = 1 := by
    intro q a hqa
    by_contra hq
    have hne : q.val.val ≠ 1 := fun he => hq (Subtype.ext (Subtype.ext he))
    have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5
      hnotAlt q.val.property hne
    rw [hcard] at hb
    let f : Fin k → X := fun i => (a i).val
    have hf : Function.Injective f := fun i j he => a.injective (Subtype.ext he)
    have hdis : Disjoint (fixedPoints Q X) (Set.range f) := by
      apply Set.disjoint_left.mpr
      rintro x hx ⟨i,rfl⟩
      exact (a i).property hx
    have hsub : fixedPoints Q X ∪ Set.range f ⊆ Function.fixedPoints q.val.val := by
      intro x hx
      rcases hx with hx | ⟨i,rfl⟩
      · exact hx q
      · exact congrArg Subtype.val (DFunLike.congr_fun hqa i)
    have hle := Set.ncard_le_ncard hsub
    rw [Set.ncard_union_eq hdis,Set.ncard_range_of_injective hf,
      ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
      Nat.card_eq_fintype_card (α := Function.fixedPoints q.val.val), Equiv.Perm.card_fixedPoints,
      q.val.val.sum_cycleType,hcard] at hle
    simp only [Nat.card_fin] at hle
    omega
  have hd := FreeComplementCard.card_dvd_of_free Q (Fin k ↪ C) hfree
  let _ : Fintype C := Fintype.ofFinite C
  have hC : Fintype.card C = 39 - Nat.card (fixedPoints Q X) := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card ((fixedPoints Q X)ᶜ : Set X) = _
    rw [Nat.card_coe_set_eq,Set.ncard_compl,← Nat.card_coe_set_eq,
      Nat.card_eq_fintype_card,hcard]
  rwa [Nat.card_eq_fintype_card (α := Fin k ↪ C),Fintype.card_embedding_eq,Fintype.card_fin,hC] at hd

end FiveTransitive.Degree39PrimeTupleDivisibility

end CFSG
