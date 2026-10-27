module

public import CFSG.Permutation.FiveTransitive.Degree52SevenFixedElements
public import CFSG.Permutation.FiveTransitive.Degree52SevenCyclicExclusion

public section

namespace CFSG

namespace FiveTransitive.Degree52SevenFree

open MulAction Subgroup SylowFixedActionCore

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ 7 ∣ Nat.card (fixingSubgroup P s) := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  intro hd
  let H := fixingSubgroup P s
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := H) 7 hd
  have hZ : IsPGroup 7 (zpowers u) := by
    apply IsPGroup.of_card
    rw [Nat.card_zpowers,hu,pow_one]
  obtain ⟨S,hZS⟩ := hZ.exists_le_sylow
  have hSge : 7 ≤ Nat.card S := by
    have h := Subgroup.card_le_of_le hZS
    rwa [Nat.card_zpowers,hu] at h
  have hS : Nat.card S ≠ 1 := by omega
  let Q := sylowImage X P s S
  let F := sylowFixedPoints X P s S
  let N := sylowNormalizer X P s S
  let instF : Fintype F := Fintype.ofFinite _
  let rho : N →* Equiv.Perm F := toPermHom N F
  have hQcard : Nat.card Q = Nat.card S := Subgroup.card_map_of_injective H.subtype_injective
  have hQprime : Nat.card Q = 7 := hQcard.trans
    (Degree52SevenOrder.card_eq_seven P hcard h5 hnotAlt s hs S hS)
  obtain ⟨hF,hAlt⟩ := Degree52SevenFixed.fixed_card_and_image P hcard h5 hnotAlt s hs S hS
  change Nat.card F = 10 at hF
  change alternatingGroup F ≤ rho.range at hAlt
  let r : P := u
  have hr : orderOf r = 7 := (Subgroup.orderOf_coe u).trans hu
  have hRQ : zpowers r = Q := by
    apply Subgroup.eq_of_le_of_card_ge
    · apply zpowers_le.mpr
      exact ⟨u,hZS (mem_zpowers u),rfl⟩
    · rw [Nat.card_zpowers,hr,hQprime]
  let instR : Fintype (PrimeCyclicFixedAction.cyclicFixedPoints X P r) := Fintype.ofFinite _
  have htransport (A : Subgroup P) [iA : Fintype (FixedNormalizerAction.Fixed (X := X) A)]
      (hA : A = Q) :
      Nat.card (FixedNormalizerAction.Fixed (X := X) A) = 10 ∧
      alternatingGroup (FixedNormalizerAction.Fixed (X := X) A) ≤
        FixedNormalizerAction.Image (X := X) A := by
    subst A
    cases Subsingleton.elim iA instF
    exact ⟨hF,hAlt⟩
  obtain ⟨hFr,hJ⟩ := @htransport (zpowers r) instR hRQ
  exact @Degree52SevenCyclicExclusion.excluded X _ _ P hcard h5 hnotAlt r instR hr hFr hJ

theorem fixed_card_eq_three
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hg : orderOf g = 7) : Nat.card (Function.fixedPoints g.val) = 3 := by
  classical
  rcases Degree52SevenFixedElements.fixed_card_three_or_ten P hcard h5 hnotAlt g hg with h | h
  · exact h
  · have hn : 5 ≤ (Function.fixedPoints g.val).ncard := by rw [← Nat.card_coe_set_eq,h]; omega
    obtain ⟨s,hsub,hs⟩ := Set.exists_subset_card_eq hn
    let u : fixingSubgroup P s := ⟨g,(mem_fixingSubgroup_iff P).mpr (fun x hx => hsub hx)⟩
    have hu : orderOf u = 7 := (Subgroup.orderOf_coe u).symm.trans hg
    exact False.elim (not_dvd_five_fixer P hcard h5 hnotAlt s hs (hu ▸ orderOf_dvd_natCard u))

end FiveTransitive.Degree52SevenFree

end CFSG
