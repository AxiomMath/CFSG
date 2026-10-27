module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryCfg
public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofLieP
public import CFSG.RankThree.PartTwo.Sec21.Item223RankResProof

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

namespace HeringUnitary

section Rest


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {a : G}
  {haN : a ∈ Subgroup.normalizer (L : Set G)} {m : ℕ}

theorem chevTwo_projSp_two (ha3 : a ^ 3 = 1) (c : UCfg L a haN m) {n : ℕ} (hn : 1 ≤ n)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* projSp 2 (GaloisField 2 n)) :
    InducesStdKind L a .field ∨ InducesStdKind L a .graphField := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · exfalso
    obtain rfl : n = 1 := by omega
    refine c.false_of_two_pow_nine (M := 720) ?_ (by norm_num)
    rw [Nat.card_congr φ.toEquiv, Sec21.Item223CensusProof.card_projSp_two_two]
  · set F := GaloisField 2 n with hF
    have hF4 : Nat.card F = 2 ^ n := GaloisField.card 2 n (by omega)
    have hs : IsSimpleGroup (projSp 2 F) := by
      have := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num)
        (Or.inl (Or.inr (by
          rw [hF4]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2)))
      exact (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage
        (CFSG.Assembly.LowTwoRank.StatedSp 2 F)).symm.isSimpleGroup
    let e : L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSp 2 F) :=
      φ.trans (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage
        (CFSG.Assembly.LowTwoRank.StatedSp 2 F)).symm
    by_cases hout : InducesOuterTheta a L
    · rcases KFacts.inducesKindPSp4Even_diagonal_or_field (L := L) ha3 hout e with
        ⟨hx, hD, hnot⟩ | hf
      · exfalso
        obtain ⟨A, hA⟩ := hD
        exact hnot (hA ▸ KFacts.conjAut_mem_inner_of_charTwo A)
      · exact Or.inl (InducesStdKind.psp4even F ⟨e, hf⟩)
    · exfalso
      have hin : thetaQuotMulAut L (compAction L ⟨a, haN⟩) ∈
          (MulAut.conj : _ →* MulAut (L ⧸ aschbacherSolvableCore 3 L)).range := by
        by_contra h
        exact hout ⟨haN, h⟩
      exact c.false_of_inner hin (Sec4.quotientCenterCongr φ)
        (Res417Three.pRank_projSp_two_le (by norm_num) (by omega) hs)

theorem chevTwo_G2
    (ha3 : a ^ 3 = 1) (c : UCfg L a haN m) {f : ℕ}
    (hX : Blueprint.ChevalleyExceptionalModel (L ⧸ aschbacherSolvableCore 3 L) .G2 2 f) :
    InducesStdKind L a .field ∨ InducesStdKind L a .graphField := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hX.2
  have hf3 : 3 ≤ 2 ^ f := hX.1.2.2.2
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    by_contra h
    have hf1 : f ≤ 1 := by
      by_contra hf
      exact h (calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega))
    interval_cases f <;> omega
  have : Fintype K := Fintype.ofFinite K
  have hcharP : CharP K 2 := charP_of_card_eq_prime_pow (f := f)
    (by rw [← Nat.card_eq_fintype_card, hK])
  have hK3 : ringChar K ≠ 3 := by
    rw [ringChar.eq K 2]
    norm_num
  by_cases hout : InducesOuterTheta a L
  · exact Or.inl (InducesStdKind.g2 K hK3 hK4
      (KFacts.inducesKindG2_field (L := L) hK3 hK4 ha3 hout e))
  · exfalso
    have hin : thetaQuotMulAut L (compAction L ⟨a, haN⟩) ∈
        (MulAut.conj : _ →* MulAut (L ⧸ aschbacherSolvableCore 3 L)).range := by
      by_contra h
      exact hout ⟨haN, h⟩
    exact c.false_of_inner hin (MulEquiv.refl _) (Sec21.g2EvenThreeRankTwo _ f hX)

theorem chevTwo_suzuki (c : UCfg L a haN m) {f : ℕ}
    (h : Blueprint.SuzukiModel (L ⧸ aschbacherSolvableCore 3 L) 2 f) :
    InducesStdKind L a .field ∨ InducesStdKind L a .graphField :=
  (c.false_of_not_three_dvd (KFacts.KP7.three_not_dvd_card h)).elim

theorem chevTwo_tits
    (c : UCfg L a haN m) {p f : ℕ}
    (h : Blueprint.ReeTitsModel (L ⧸ aschbacherSolvableCore 3 L) .Tits p f) :
    InducesStdKind L a .field ∨ InducesStdKind L a .graphField := by
  exfalso
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv _ p f h
  have hX : Nat.card (L ⧸ aschbacherSolvableCore 3 L) = 17971200 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD]
  exact c.false_of_two_pow_fifteen (M := 17971200) (by rw [hX]) (by norm_num) (by norm_num)

end Rest

end HeringUnitary

end CFSG.RankThree.PartTwo.Sec4
