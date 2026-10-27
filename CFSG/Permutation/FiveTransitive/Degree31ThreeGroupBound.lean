module

public import CFSG.Permutation.FiveTransitive.MinimalOrbitFixedBounds
public import CFSG.Permutation.FiveTransitive.FreeComplementCard

public section

namespace CFSG

namespace FiveTransitive.Degree31ThreeGroupBound

open MulAction

theorem card_le_eighty_one
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 3 Q)
    (hfixed : 5 ≤ Nat.card (fixedPoints Q X)) : Nat.card Q ≤ 81 := by
  classical
  by_cases hbot : Q = ⊥
  · subst Q
    simp
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hupper := MinimalOrbitFixedBounds.fixed_card_le_half X P (by omega) h5 hnotAlt Q hbot
  rw [hcard] at hupper
  have hmod := hQ.card_modEq_card_fixedPoints X
  change Nat.card X % 3 = Nat.card (fixedPoints Q X) % 3 at hmod
  rw [Nat.card_eq_fintype_card,hcard] at hmod
  have hcases : Nat.card (fixedPoints Q X) = 7 ∨
      Nat.card (fixedPoints Q X) = 10 ∨ Nat.card (fixedPoints Q X) = 13 := by omega
  have hseven : 7 ≤ Nat.card (fixedPoints Q X) := by omega
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
  have hfree : ∀ q : Q, ∀ a : Fin 9 ↪ C, q • a = a → q = 1 := by
    intro q a hqa
    by_contra hq
    have hne : q.val.val ≠ 1 := fun he => hq (Subtype.ext (Subtype.ext he))
    have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5
      hnotAlt q.val.property hne
    rw [hcard] at hb
    let f : Fin 9 → X := fun i => (a i).val
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
  have hd := FreeComplementCard.card_dvd_of_free Q (Fin 9 ↪ C) hfree
  let _ : Fintype C := Fintype.ofFinite C
  have hC : Fintype.card C = 31 - Nat.card (fixedPoints Q X) := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card ((fixedPoints Q X)ᶜ : Set X) = _
    rw [Nat.card_coe_set_eq,Set.ncard_compl,← Nat.card_coe_set_eq,
      Nat.card_eq_fintype_card,hcard]
  rw [Nat.card_eq_fintype_card (α := Fin 9 ↪ C),Fintype.card_embedding_eq,Fintype.card_fin,hC] at hd
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have he4 : e ≤ 4 := by
    by_contra hn
    have hd243 : 243 ∣ Nat.card Q := by
      rw [he]
      exact pow_dvd_pow 3 (by omega : 5 ≤ e)
    have hc := hd243.trans hd
    rcases hcases with h | h | h <;> rw [h] at hc <;> norm_num at hc
  rw [he]
  exact (Nat.pow_le_pow_right (by norm_num : 0 < 3) he4).trans (by norm_num)

end FiveTransitive.Degree31ThreeGroupBound

end CFSG
