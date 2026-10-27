module

public import CFSG.Permutation.FiveTransitive.OddFourDegreeModFour
public import CFSG.Permutation.FiveTransitive.NormalSylowFixedDegreeSharpened

public section

namespace CFSG

namespace FiveTransitive.NormalSylowFixedDegreeSeven

open MulAction GenericSylowFixedAction

private theorem internal_fixed_degree_not_four_dvd
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (s : Set X) (hs : s.ncard = 4) (S : Sylow 2 (fixingSubgroup G s))
    (hn : 8 ≤ Nat.card (sylowFixedPoints G X s S)) :
    ¬ 4 ∣ Nat.card (sylowFixedPoints G X s S) := by
  classical
  let K := sylowNormalizer G X s S
  let F := sylowFixedPoints G X s S
  let _ : Fintype F := Fintype.ofFinite F
  let J := (MulAction.toPermHom K F).range
  let sF : Set F := {x | (x : X) ∈ s}
  have hsF : s ⊆ (F : Set X) := base_subset_fixedPoints G X s S
  let e : s ≃ sF :=
    { toFun := fun x => ⟨⟨x.1, hsF x.2⟩, x.2⟩
      invFun := fun x => ⟨x.1.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hsFcard : sF.ncard = 4 := by
    rw [← Nat.card_coe_set_eq, Nat.card_congr e.symm, Nat.card_coe_set_eq, hs]
  have hJ4 : MulAction.IsMultiplyPretransitive J F 4 :=
    FiveTransitive.isMultiplyPretransitive_range_toPermHom K F 4
      (NormalSylowFixedDegree.internal_normalizer_four_transitive G X h4 s hs S)
  have hfree := prime_not_dvd_fixedAction_stabilizer_card G X s S
  change ¬ 2 ∣ Nat.card (fixingSubgroup J sF) at hfree
  let _ : Fintype sF := Fintype.ofFinite sF
  have hscard : Fintype.card sF = 4 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hsFcard]
  let es : Fin 4 ≃ sF := (Fintype.equivFinOfCardEq hscard).symm
  let eF : Fin 4 ↪ F := es.toEmbedding.trans (Function.Embedding.subtype _)
  have hrange : Set.range eF = sF := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (es i).property
    · intro hx
      obtain ⟨i, hi⟩ := es.surjective ⟨x, hx⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  have hstab : fixingSubgroup J sF = MulAction.stabilizer J eF := by
    ext g
    rw [mem_fixingSubgroup_iff, MulAction.mem_stabilizer_iff]
    constructor
    · intro hg
      apply DFunLike.ext
      intro i
      exact hg (eF i) (by rw [← hrange]; exact ⟨i, rfl⟩)
    · intro hg x hx
      rw [← hrange] at hx
      obtain ⟨i, rfl⟩ := hx
      exact DFunLike.congr_fun hg i
  have hodd : Odd (Nat.card (MulAction.stabilizer J eF)) := by
    rw [← hstab]
    exact Nat.not_even_iff_odd.mp (fun he => hfree (even_iff_two_dvd.mp he))
  have hnot := OddFourDegreeModFour.not_four_dvd_degree J F hJ4
    (by simpa only [Nat.card_eq_fintype_card] using hn) eF hodd
  simpa only [Nat.card_eq_fintype_card] using hnot

theorem fixed_degree_le_seven
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h5 : MulAction.IsMultiplyPretransitive G X 5)
    (N : Subgroup G) [N.Normal] (hN4 : MulAction.IsMultiplyPretransitive N X 4)
    (s : Set X) (hs : s.ncard = 4) (S : Sylow 2 (fixingSubgroup N s)) :
    Nat.card (NormalSylowFixedFive.normalSylowFixedPoints G X N s S) ≤ 7 := by
  have hcases := NormalSylowFixedDegreeSharpened.fixed_degree_cases G X h5 N hN4 s hs S
  rw [NormalSylowFixedDegree.normal_fixedPoints_eq_internal] at hcases ⊢
  rcases hcases with hsmall | htwelve | htwentyfour
  · exact hsmall
  · have hnot := internal_fixed_degree_not_four_dvd N X hN4 s hs S (by omega)
    rw [htwelve] at hnot
    exact (hnot (by norm_num)).elim
  · have hnot := internal_fixed_degree_not_four_dvd N X hN4 s hs S (by omega)
    rw [htwentyfour] at hnot
    exact (hnot (by norm_num)).elim

end FiveTransitive.NormalSylowFixedDegreeSeven

end CFSG
