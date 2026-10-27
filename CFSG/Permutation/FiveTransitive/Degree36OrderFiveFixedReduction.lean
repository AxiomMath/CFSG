module

public import CFSG.Permutation.FiveTransitive.Degree36SmallPrimeEntrance

public section

namespace CFSG

namespace FiveTransitive.Degree36OrderFiveFixedReduction

open MulAction Subgroup SylowFixedActionCore

theorem fixed_card_of_sylow_orders
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hall : ∀ (s : Set X), s.ncard = 5 → ∀ S : Sylow 5 (fixingSubgroup P s),
      Nat.card S = 1 ∨ Nat.card S = 5)
    (g : P) (hg : orderOf g = 5) (hfixed : 5 ≤ Nat.card (Function.fixedPoints g.val)) :
    Nat.card (Function.fixedPoints g.val) = 6 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
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
  have hu : orderOf u = 5 := (Subgroup.orderOf_coe u).symm.trans hg
  have hZ : IsPGroup 5 (zpowers u) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers,hu,pow_one]
  obtain ⟨S,hZS⟩ := hZ.exists_le_sylow
  have hSge : 5 ≤ Nat.card S := by
    have h := Subgroup.card_le_of_le hZS
    rwa [Nat.card_zpowers,hu] at h
  have hSne : Nat.card S ≠ 1 := by omega
  have hSfive : Nat.card S = 5 := (hall s hs S).resolve_left hSne
  let Q := sylowImage X P s S
  have hQcard : Nat.card Q = 5 := by
    have hmap : Nat.card Q = Nat.card S := Subgroup.card_map_of_injective H.subtype_injective
    exact hmap.trans hSfive
  have hRQ : zpowers g = Q := by
    apply Subgroup.eq_of_le_of_card_ge
    · apply zpowers_le.mpr
      exact ⟨u,hZS (mem_zpowers u),rfl⟩
    · rw [Nat.card_zpowers,hg,hQcard]
  have hF := (Degree36SmallPrimeEntrance.five_entrance P hcard h5 hnotAlt s hs S hSne).1
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

theorem twenty_five_not_dvd_of_sylow_orders
    {X : Type} [Fintype X]
    (P : Subgroup (Equiv.Perm X))
    (hall : ∀ (s : Set X), s.ncard = 5 → ∀ S : Sylow 5 (fixingSubgroup P s),
      Nat.card S = 1 ∨ Nat.card S = 5)
    (s : Set X) (hs : s.ncard = 5) : ¬ 25 ∣ Nat.card (fixingSubgroup P s) := by
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro hd
  let S : Sylow 5 (fixingSubgroup P s) := Sylow.nonempty.some
  have h25 : 25 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 2) hd
  rcases hall s hs S with h | h <;> rw [h] at h25 <;> norm_num at h25

end FiveTransitive.Degree36OrderFiveFixedReduction

end CFSG
