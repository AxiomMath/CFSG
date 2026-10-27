module

public import CFSG.Permutation.FiveTransitive.Degree36FourCases

public section

namespace CFSG

namespace FiveTransitive.Degree36FiveFreeFixed

open MulAction

private theorem five_not_dvd_five_fixer_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ¬ 5 ∣ Nat.card (fixingSubgroup P s) := by
  rcases Degree36FourCases.card_cases P hcard h5 hnotAlt s hs with h | h | h | h <;>
    rw [h] <;> norm_num

theorem fixed_card_eq_one
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hg : orderOf g = 5) :
    Nat.card (Function.fixedPoints g.val) = 1 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
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
    have hd : 5 ∣ Nat.card H := by
      rw [← hu]
      exact orderOf_dvd_natCard u
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

end FiveTransitive.Degree36FiveFreeFixed

end CFSG
