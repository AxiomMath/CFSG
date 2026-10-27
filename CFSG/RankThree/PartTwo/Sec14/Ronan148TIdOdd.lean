module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TOddGlue
public import CFSG.RankThree.PartTwo.Sec14.Ronan148TOddL3
import CFSG.RankThree.PartTwo.Sec14.Ronan148TEvenL3
import CFSG.RankThree.PartTwo.Sec14.Ronan148AL3Unique
import CFSG.RankThree.SubgroupLists.RationalFiveExclusions

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedM11)


theorem odd_ident {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (he : 1 ≤ e) (he2 : e ≤ 2) (hiso : Sec4.IsoLThreePi X p e) {K₀ : Subgroup X}
    (hKs : IsSimpleGroup ↥K₀) (hnab : ∃ a b : ↥K₀, a * b ≠ b * a) (hK : K₀ ≠ ⊤) :
    (∃ r k : ℕ, r.Prime ∧ r ≠ 2 ∧ 1 ≤ k ∧ StatedClassicalModel ↥K₀ .PSL 2 r k) ∨
      (∃ f₁ : ℕ, 1 ≤ f₁ ∧ f₁ ≤ 2 ∧ IsLThreeEpsAt ↥K₀ p f₁) ∨
      Nonempty (↥K₀ ≃* alternatingGroup (Fin 7)) := by
  have hp : p.Prime := Fact.out
  haveI := hKs
  have hKp : Group.IsPerfect K₀ := isPerfect_of_simple hKs hnab
  have hrank : CFSG.Assembly.twoRank K₀ = 2 := by
    refine le_antisymm (oddTwoRank X p e hp2 he hiso K₀) ?_
    refine CFSG.Assembly.LowTwoRank.two_le_twoRank K₀ hnab ?_
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    haveI := hKp
    exact Group.IsPerfect.not_isSolvable K₀ hsolv
  rcases CFSG.Milestones.lr_rank_two_isomorphism_types K₀ hnab hrank with
    ⟨r, f, hr, hr2, hf, hM⟩ | ⟨r, f, hr, hr2, hf, hM⟩ | ⟨r, f, hr, hr2, hf, hM⟩ | hM | hφ | hφ
  · exact Or.inl ⟨r, f, hr, hr2, hf, hM⟩
  ·
    rcases oddL3U3 X p e hp2 he he2 hiso K₀ hKs r f hr hr2 hf (Or.inl hM) with
        h | ⟨-, hφ⟩ | ⟨p', f', e', _, hf', he', hiso', hε⟩
    · exact absurd h hK
    · exact Or.inr (Or.inr hφ)
    · obtain ⟨hpp, hee⟩ := Ronan148A.isoLThreePi_unique he (Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by omega) (by omega))) hiso hiso'
      subst hpp
      refine Or.inr (Or.inl ⟨f', hf', ?_, hε⟩)
      have : f' ≤ f' * e' := Nat.le_mul_of_pos_right _ (by omega)
      omega
  ·
    rcases oddL3U3 X p e hp2 he he2 hiso K₀ hKs r f hr hr2 hf (Or.inr hM) with
        h | ⟨-, hφ⟩ | ⟨p', f', e', _, hf', he', hiso', hε⟩
    · exact absurd h hK
    · exact Or.inr (Or.inr hφ)
    · obtain ⟨hpp, hee⟩ := Ronan148A.isoLThreePi_unique he (Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by omega) (by omega))) hiso hiso'
      subst hpp
      refine Or.inr (Or.inl ⟨f', hf', ?_, hε⟩)
      have : f' ≤ f' * e' := Nat.le_mul_of_pos_right _ (by omega)
      omega
  · exact (oddU34Excl X p e hp2 he hiso K₀ hM).elim
  · exact Or.inr (Or.inr hφ)
  ·
    exfalso
    obtain ⟨φ⟩ := hφ
    have hp5 : p = 5 := by
      refine oddFive X p e he hiso (K₀.subtype (φ.symm SubgroupLists.m11Five))
        (K₀.subtype (φ.symm SubgroupLists.m11B)) ?_ ?_ ?_
      · rw [← map_pow, ← map_pow, SubgroupLists.m11Five_pow_five, map_one, map_one]
      · intro h
        apply SubgroupLists.m11Five_ne_one
        apply φ.symm.injective
        rw [map_one]
        exact K₀.subtype_injective (h.trans (map_one K₀.subtype).symm)
      · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul,
          SubgroupLists.m11B_conj, map_pow, map_pow]
    subst hp5
    apply not_eleven_dvd_of_five he he2 hiso
    have h11 : 11 ∣ Nat.card K₀ := by
      rw [Nat.card_congr φ.toEquiv, CFSG.Semidihedral.GL2Recognition.card_lowTwoRankStatedM11]
      norm_num
    exact h11.trans (Subgroup.card_subgroup_dvd_card K₀)

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
