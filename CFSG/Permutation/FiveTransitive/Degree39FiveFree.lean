module

public import CFSG.Permutation.FiveTransitive.Degree39FiveSylowData
public import CFSG.Permutation.FiveTransitive.Degree39FiveGroupBound
public import CFSG.Permutation.FiveTransitive.Degree39FiveCentralizer
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

namespace FiveTransitive.Degree39FiveFree

open MulAction SylowFixedActionCore

theorem five_not_dvd_five_fixer_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 39)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ 5 ∣ Nat.card (fixingSubgroup P s) := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  intro hdiv
  let S : Sylow 5 (fixingSubgroup P s) := default
  have hS : Nat.card S ≠ 1 := by
    have hd := S.dvd_card_of_dvd_card hdiv
    intro hh
    rw [hh] at hd
    norm_num at hd
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite _
  obtain ⟨hF,hAlt⟩ := Degree39FiveSylowData.five_fixed_card_and_image P hcard h5 hnotAlt s hs S hS
  change Nat.card F = 9 at hF
  have hQ : IsPGroup 5 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hfixeq : (F : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  have hfixed : Nat.card (fixedPoints Q X) = 9 := by rwa [← hfixeq]
  have hQcard := Degree39FiveGroupBound.card_le_six_hundred_twenty_five P hcard h5 hnotAlt Q hQ hfixed.ge
  let rho : N →* Equiv.Perm F := toPermHom N F
  have hd : 7 ∣ Nat.card rho.range :=
    (odd_prime_dvd_alternating_card F (by decide : Nat.Prime 7) (by decide)
      (by rw [← Nat.card_eq_fintype_card,hF]; decide)).trans (Subgroup.card_dvd_of_le hAlt)
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := N) 7
    (hd.trans (Subgroup.card_range_dvd rho))
  exact Degree39FiveCentralizer.excluded P hcard h5 hnotAlt Q hQ hQcard hfixed g hg

theorem fixed_card_eq_four
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 39)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hg : orderOf g = 5) : Nat.card (Function.fixedPoints g.val) = 4 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hlt : Nat.card (Function.fixedPoints g.val) < 5 := by
    by_contra hn
    have hfixed : 5 ≤ Nat.card (Function.fixedPoints g.val) := by omega
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
    have hd : 5 ∣ Nat.card H := by rw [← hu]; exact orderOf_dvd_natCard u
    exact five_not_dvd_five_fixer_card P hcard h5 hnotAlt s hs hd
  let f : Function.End X := g.val.toFun
  have hf : f ^ 5 = 1 := by
    funext x
    change (g ^ 5).val x = x
    rw [← hg,pow_orderOf_eq_one]
    rfl
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 5) (n := 1)
    (by simpa only [pow_one] using hf)
  change Fintype.card X % 5 = Fintype.card (Function.fixedPoints g.val) % 5 at hm
  rw [hcard,← Nat.card_eq_fintype_card] at hm
  omega

end FiveTransitive.Degree39FiveFree

end CFSG
