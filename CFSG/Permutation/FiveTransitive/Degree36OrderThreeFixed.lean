module

public import CFSG.Permutation.FiveTransitive.Degree36SmallPrimeEntrance
public import CFSG.Permutation.FiveTransitive.FourFixerClosure

public section

namespace CFSG

namespace FiveTransitive.Degree36OrderThreeFixed

open MulAction Subgroup SylowFixedActionCore

private theorem fixed_card_of_sylow_orders
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hall : ∀ (s : Set X), s.ncard = 5 → ∀ S : Sylow 3 (fixingSubgroup P s),
      Nat.card S = 1 ∨ Nat.card S = 3)
    (g : P) (hg : orderOf g = 3) (hfixed : 5 ≤ Nat.card (Function.fixedPoints g.val)) :
    Nat.card (Function.fixedPoints g.val) = 6 := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let b : Fin 5 ↪ Function.fixedPoints g.val :=
    (Fin.castLEEmb hfixed).trans (Finite.equivFin (Function.fixedPoints g.val)).symm.toEmbedding
  let bX : Fin 5 ↪ X := b.trans (Function.Embedding.subtype _)
  let s : Set X := Set.range bX
  have hs : s.ncard = 5 := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective bX.injective
  let H := fixingSubgroup P s
  have hgmem : g ∈ H := by
    apply (mem_fixingSubgroup_iff P).mpr
    rintro x ⟨i,rfl⟩
    exact (b i).property
  let u : H := ⟨g,hgmem⟩
  have hu : orderOf u = 3 := (Subgroup.orderOf_coe u).symm.trans hg
  have hZ : IsPGroup 3 (zpowers u) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers,hu,pow_one]
  obtain ⟨S,hZS⟩ := hZ.exists_le_sylow
  have hSge : 3 ≤ Nat.card S := by
    have h := Subgroup.card_le_of_le hZS
    rwa [Nat.card_zpowers,hu] at h
  have hSne : Nat.card S ≠ 1 := by omega
  have hSfive : Nat.card S = 3 := (hall s hs S).resolve_left hSne
  let Q := sylowImage X P s S
  have hQcard : Nat.card Q = 3 := by
    have hmap : Nat.card Q = Nat.card S := Subgroup.card_map_of_injective H.subtype_injective
    exact hmap.trans hSfive
  have hRQ : zpowers g = Q := by
    apply Subgroup.eq_of_le_of_card_ge
    · apply zpowers_le.mpr
      exact ⟨u,hZS (mem_zpowers u),rfl⟩
    · rw [Nat.card_zpowers,hg,hQcard]
  have hF := (Degree36SmallPrimeEntrance.three_entrance P hcard h5 hnotAlt s hs S hSne).1
  have hfixeq : (sylowFixedPoints X P s S : Set X) = fixedPoints Q X :=
    FixedNormalizerAction.fixed_eq Q
  rw [hfixeq] at hF
  have hcyclic : Function.fixedPoints g.val = fixedPoints (zpowers g) X := by
    ext x
    constructor
    · intro hx z
      have hz : zpowers g ≤ stabilizer P x := zpowers_le.mpr hx
      exact hz z.property
    · intro hx
      exact hx ⟨g,mem_zpowers g⟩
  rw [hcyclic,hRQ]
  exact hF

private theorem sylow_card_cases
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (h5 : IsMultiplyPretransitive P X 5)
    (s : Set X) (hs : s.ncard = 5) (h9 : ¬ 9 ∣ Nat.card (fixingSubgroup P s))
    (t : Set X) (ht : t.ncard = 5) (S : Sylow 3 (fixingSubgroup P t)) :
    Nat.card S = 1 ∨ Nat.card S = 3 := by
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have hele : e ≤ 1 := by
    by_contra hn
    apply h9
    rw [(FourFixerClosure.card_data h5 s t hs ht).1]
    exact (show 3^2 ∣ 3^e from pow_dvd_pow 3 (by omega)).trans
      (he ▸ Subgroup.card_subgroup_dvd_card (S : Subgroup (fixingSubgroup P t)))
  interval_cases e <;> simp_all

theorem fixed_card_eq_six
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (h9 : ¬ 9 ∣ Nat.card (fixingSubgroup P s))
    (g : P) (hg : orderOf g = 3) (hfixed : 5 ≤ Nat.card (Function.fixedPoints g.val)) :
    Nat.card (Function.fixedPoints g.val) = 6 :=
  fixed_card_of_sylow_orders P hcard h5 hnotAlt
    (sylow_card_cases P h5 s hs h9) g hg hfixed

end FiveTransitive.Degree36OrderThreeFixed

end CFSG
