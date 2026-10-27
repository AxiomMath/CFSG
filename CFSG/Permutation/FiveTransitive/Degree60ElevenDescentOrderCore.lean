module

public import CFSG.Permutation.FiveTransitive.Degree60ElevenDescentMaximal
public import CFSG.Permutation.FiveTransitive.Degree60ElevenDescentCentralizer
public import CFSG.Permutation.FiveTransitive.MaximalOrderFixedLowerBound

public section

namespace CFSG

namespace FiveTransitive.Degree60ElevenDescentOrderCore

open MulAction Subgroup FixedNormalizerAction

private theorem eq_bot_of_six_fixed
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 60)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 11 Q)
    (hfix : 6 ≤ Nat.card (fixedPoints Q X)) : Q = ⊥ := by
  classical
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  by_contra hne
  obtain ⟨U,hU,hUfix,hQU,hmax⟩ := MaximalOrderFixedLowerBound.exists_maximal 11 6 Q hQ hfix
  have hUcard : 1 < Nat.card U :=
    (Finite.one_lt_card_iff_nontrivial.mpr (Q.nontrivial_iff_ne_bot.mpr hne)).trans_le hQU
  have hUne : U ≠ ⊥ := by intro he; rw [he] at hUcard; simp at hUcard
  let _ : Fintype (Fixed (X := X) U) := Fintype.ofFinite _
  obtain ⟨hF,hAlt⟩ := Degree60ElevenDescentMaximal.fixed_sixteen_and_alternating P hcard h5 hnotAlt U hU hUne hUfix hmax
  exact Degree60ElevenDescentCentralizer.excluded_of_fixed_sixteen P hcard h5 hnotAlt U hU hF hAlt

theorem card_le_eleven
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 60)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 11 Q)
    (hF : Nat.card (fixedPoints Q X) = 5) : Nat.card Q ≤ 11 := by
  classical
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hfree : ∀ q : Q, ∀ x : X, x ∉ fixedPoints Q X → q • x = x → q = 1 := by
    intro q x hx hqx
    let H := stabilizer Q x
    let R : Subgroup P := H.map Q.subtype
    have hR : IsPGroup 11 R := (hQ.to_subgroup H).map Q.subtype
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
    have hbot := eq_bot_of_six_fixed P hcard h5 hnotAlt R hR hsize
    have hmem : q.val ∈ R := ⟨q,hqx,rfl⟩
    rw [hbot,mem_bot] at hmem
    exact Subtype.ext hmem
  have hd := FreeComplementCard.card_dvd_complement Q X (fixedPoints Q X)
    (by intro q x hx; simpa only [mem_fixedPoints.mp hx q] using hx) hfree
  rw [← Nat.card_coe_set_eq,hF,Nat.card_eq_fintype_card (α := X),hcard] at hd
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have he1 : e ≤ 1 := by
    by_contra hn
    have hh : 121 ∣ Nat.card Q := by rw [he]; exact pow_dvd_pow 11 (by omega : 2 ≤ e)
    have hh := hh.trans hd
    norm_num at hh
  rw [he]
  exact (Nat.pow_le_pow_right (by decide : 0 < 11) he1).trans (by norm_num)

end FiveTransitive.Degree60ElevenDescentOrderCore

end CFSG
