module

public import CFSG.Permutation.FiveTransitive.Degree60FiveMaximal
public import CFSG.Permutation.FiveTransitive.Degree60FiveSevenObstruction
public import CFSG.Permutation.FiveTransitive.MaximalOrderFixedLowerBound

public section

namespace CFSG

namespace FiveTransitive.Degree60FiveOrderCore

open MulAction Subgroup FixedNormalizerAction

private theorem eq_bot_of_six_fixed
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 60)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hseven : ∀ g : P, orderOf g = 7 → Nat.card (Function.fixedPoints g.val) = 4)
    (Q : Subgroup P) (hQ : IsPGroup 5 Q)
    (hfix : 6 ≤ Nat.card (fixedPoints Q X)) : Q = ⊥ := by
  classical
  by_contra hne
  obtain ⟨U,hU,hUfix,hQU,hmax⟩ := MaximalOrderFixedLowerBound.exists_maximal 5 6 Q hQ hfix
  have hUcard : 1 < Nat.card U :=
    (Finite.one_lt_card_iff_nontrivial.mpr (Q.nontrivial_iff_ne_bot.mpr hne)).trans_le hQU
  have hUne : U ≠ ⊥ := by intro he; rw [he] at hUcard; simp at hUcard
  let _ : Fintype (Fixed (X := X) U) := Fintype.ofFinite _
  obtain ⟨hF,hAlt⟩ := Degree60FiveMaximal.fixed_ten_and_alternating P hcard h5 hnotAlt U hU hUne hUfix hmax
  exact Degree60FiveSevenObstruction.excluded P hcard hseven U hU hF hAlt

theorem fixed_card_cases
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 60)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hseven : ∀ g : P, orderOf g = 7 → Nat.card (Function.fixedPoints g.val) = 4)
    (g : P) (hg : orderOf g = 5) :
    Nat.card (Function.fixedPoints g.val) = 0 ∨ Nat.card (Function.fixedPoints g.val) = 5 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hle : Nat.card (Function.fixedPoints g.val) ≤ 5 := by
    by_contra hn
    have hQ : IsPGroup 5 (zpowers g) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers,hg,pow_one]
    have heq : Function.fixedPoints g.val = fixedPoints (zpowers g) X := by
      ext x
      constructor
      · intro hx z
        have hh : zpowers g ≤ stabilizer P x := zpowers_le.mpr hx
        exact hh z.property
      · intro hx
        exact hx ⟨g,mem_zpowers g⟩
    have hbot := eq_bot_of_six_fixed P hcard h5 hnotAlt hseven (zpowers g) hQ
      (by rw [← heq]; omega)
    have hg1 : g = 1 := by
      have hh := mem_zpowers g
      rw [hbot,mem_bot] at hh
      exact hh
    rw [hg1,orderOf_one] at hg
    omega
  let a : Function.End X := g.val.toFun
  have ha : a ^ 5 = 1 := by
    funext x
    change (g ^ 5).val x = x
    rw [← hg,pow_orderOf_eq_one]
    rfl
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := 5) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card X % 5 = Fintype.card (Function.fixedPoints g.val) % 5 at hm
  rw [hcard,← Nat.card_eq_fintype_card] at hm
  omega

theorem card_le_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 60)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hseven : ∀ g : P, orderOf g = 7 → Nat.card (Function.fixedPoints g.val) = 4)
    (Q : Subgroup P) (hQ : IsPGroup 5 Q)
    (hF : Nat.card (fixedPoints Q X) = 5) : Nat.card Q ≤ 5 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hfree : ∀ q : Q, ∀ x : X, x ∉ fixedPoints Q X → q • x = x → q = 1 := by
    intro q x hx hqx
    let H := stabilizer Q x
    let R : Subgroup P := H.map Q.subtype
    have hR : IsPGroup 5 R := (hQ.to_subgroup H).map Q.subtype
    have hsub : insert x (fixedPoints Q X) ⊆ fixedPoints R X := by
      intro y hy r
      obtain ⟨u,hu,he⟩ := r.property
      change r.val • y = y
      rw [← he]
      rcases hy with rfl | hy
      · exact hu
      · exact hy u
    have hsize : 6 ≤ Nat.card (fixedPoints R X) := by
      have hh := Set.ncard_le_ncard hsub
      rw [Set.ncard_insert_of_notMem hx,← Nat.card_coe_set_eq,hF,← Nat.card_coe_set_eq] at hh
      exact hh
    have hbot := eq_bot_of_six_fixed P hcard h5 hnotAlt hseven R hR hsize
    have hmem : q.val ∈ R := ⟨q,hqx,rfl⟩
    rw [hbot,mem_bot] at hmem
    exact Subtype.ext hmem
  have hd := FreeComplementCard.card_dvd_complement Q X (fixedPoints Q X)
    (by intro q x hx; simpa only [mem_fixedPoints.mp hx q] using hx) hfree
  rw [← Nat.card_coe_set_eq,hF,Nat.card_eq_fintype_card (α := X),hcard] at hd
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have he1 : e ≤ 1 := by
    by_contra hn
    have hh : 25 ∣ Nat.card Q := by rw [he]; exact pow_dvd_pow 5 (by omega : 2 ≤ e)
    have hh := hh.trans hd
    norm_num at hh
  rw [he]
  exact (Nat.pow_le_pow_right (by decide : 0 < 5) he1).trans (by norm_num)

end FiveTransitive.Degree60FiveOrderCore

end CFSG
