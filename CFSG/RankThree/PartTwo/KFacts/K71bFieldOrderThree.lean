module

public import CFSG.RankThree.PartTwo.Sec11.Omega

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.GorensteinWalter
open CFSG.LocalAnalysis.ComponentInitial

theorem inducesStdKind_field_of_isList1016 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : Sec9.IsList1016 (L ⧸ aschbacherSolvableCore 3 L)) {x : G} (hx3 : x ^ 3 = 1)
    (hout : Sec4.InducesOuterTheta x L) : InducesStdKind L x .field := by
  by_cases hL3 : ∃ n : ℕ, 1 ≤ n ∧ Sec8.IsoLThreeMinusPi (L ⧸ aschbacherSolvableCore 3 L) 2 (3 * n)
  · obtain ⟨n, hn, hX⟩ := hL3
    have hq2 : 2 < 2 ^ (3 * n) :=
      lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * n))
    rcases hX with ⟨hq, ⟨e⟩⟩ | ⟨hq, ⟨e⟩⟩
    · have h : UnitaryFieldData 2 (3 * n) (GaloisField 2 (2 * (3 * n))) :=
        ⟨Nat.prime_two, by omega, GaloisField.card 2 _ (by omega)⟩
      obtain ⟨φ⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
      rcases inducesKindPSU3_diagonal_or_field (h := h) L hq2 hx3 hout (e.trans φ.symm) with
        hd | hf
      · obtain ⟨hx, hdk⟩ := hd
        have hdk' : (stdPinnedPSU3 h).IsDiagonal _ := hdk
        exact absurd (isInnerAut_of_mem_psuConj_range h hq hdk'.1) hdk'.2
      · exact InducesStdKind.psu3 h hq2 ⟨_, hf⟩
    · obtain ⟨φ⟩ := nonempty_projSL_mulEquiv 3 (GaloisField 2 (3 * n))
      rcases inducesKindPSL_diagonal_or_field L le_rfl hx3 hout (e.trans φ) with hd | hf
      · obtain ⟨hx, hdk⟩ := hd
        have hdk' : (stdPinnedPSL 3 (GaloisField 2 (3 * n))).IsDiagonal _ := hdk
        exact absurd (isInnerAut_of_mem_linearAutGroup
          (by rwa [GaloisField.card 2 (3 * n) (by omega)]) hdk'.1) hdk'.2
      · exact InducesStdKind.psl 3 _ le_rfl ⟨_, hf⟩
  · obtain ⟨K, _, _, -, -, ⟨e⟩⟩ := Sec11.exists_mulEquiv_psl2_of_isList1016 hL hL3
    exact InducesStdKind.psl2 K ⟨e, inducesKind_field_of_pow_three L hx3 hout e⟩

end CFSG.RankThree.PartTwo.KFacts
