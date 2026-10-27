module

public import CFSG.Permutation.FiveTransitive.MinimalOrbitFixedBounds
public import CFSG.Permutation.FiveTransitive.FreeComplementCard

public section

namespace CFSG

namespace FiveTransitive.Degree28LargePrimeElevenBound

open MulAction

theorem fixed_card_eq_six
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 11 Q) (hne : Q ≠ ⊥)
    (hfixed : 5 ≤ Nat.card (fixedPoints Q X)) : Nat.card (fixedPoints Q X) = 6 := by
  let _ : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hupper := MinimalOrbitFixedBounds.fixed_card_le_half X P (by omega) h5 hnotAlt Q hne
  rw [hcard] at hupper
  have hmod := hQ.card_modEq_card_fixedPoints X
  change Nat.card X % 11 = Nat.card (fixedPoints Q X) % 11 at hmod
  rw [Nat.card_eq_fintype_card,hcard] at hmod
  omega

theorem card_eq_eleven
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 11 Q) (hne : Q ≠ ⊥)
    (hfixed : 5 ≤ Nat.card (fixedPoints Q X)) : Nat.card Q = 11 := by
  let _ : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  classical
  have hsix := fixed_card_eq_six P hcard h5 hnotAlt Q hQ hne hfixed
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
  have hC : Fintype.card C = 28 - Nat.card (fixedPoints Q X) := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card ((fixedPoints Q X)ᶜ : Set X) = _
    rw [Nat.card_coe_set_eq,Set.ncard_compl,← Nat.card_coe_set_eq,
      Nat.card_eq_fintype_card,hcard]
  rw [Nat.card_eq_fintype_card (α := Fin 9 ↪ C),Fintype.card_embedding_eq,Fintype.card_fin,hC] at hd
  rw [hsix] at hd
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have he1 : e ≤ 1 := by
    by_contra hn
    have hd121 : 121 ∣ Nat.card Q := by
      rw [he]
      exact pow_dvd_pow 11 (by omega : 2 ≤ e)
    have hc := hd121.trans hd
    norm_num [Nat.descFactorial] at hc
  have he0 : e ≠ 0 := by
    intro hz
    rw [hz,pow_zero] at he
    exact hne (Subgroup.card_eq_one.mp he)
  have heq : e = 1 := by omega
  simpa only [heq,pow_one] using he

end FiveTransitive.Degree28LargePrimeElevenBound

end CFSG
