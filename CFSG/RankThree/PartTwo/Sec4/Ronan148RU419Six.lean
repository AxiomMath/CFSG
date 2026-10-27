module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RU419Odd
public import CFSG.RankThree.PartTwo.Sec4.Ronan148WCensusL3
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LRowD4
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LRowG2
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LRowSp4
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LRowF4
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LRowU4
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LRowSzTits
import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofGenTools

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Rows


variable {X : Type} [Group X] [Finite X]

theorem rowU419_D4 (hq : IsQuasisimple X) {f : ℕ}
    (hm : ChevalleyExceptionalModel X .trialityD4 2 f) : RowU419 X := by
  intro α Y m hc
  haveI := hc.isPerfect
  obtain ⟨π, hπ, hker⟩ := hc.cover
  obtain ⟨K, _, _, _, σ, hK, hσ, -, hf, hsimp, ⟨e⟩⟩ :=
    Res417Seven.exists_graphFixedRootGroup_of_trialityD4 hm
  have hs : IsSimpleGroup X := by
    haveI := hsimp
    exact e.isSimpleGroup
  obtain ⟨hfm, hout⟩ := Ronan148L.rowU3_D4 hs (Census.exists_ne_of_isQuasisimple hq) hm
    hc.pow_three hc.ne_one hc.le_autFix hc.isSubnormal hc.odd hc.one_lt π hπ hker
  subst hfm
  refine Or.inr ⟨K, inferInstance, inferInstance, hK, σ, hσ, e, ?_⟩
  refine trialityHasKind_graphField_of_pow_three_eq_one hf hK hσ
    (by rw [← map_pow, hc.pow_three, map_one]) ?_
  rwa [isInnerAut_congr]

theorem rowsU419Six : RowsU419Six := by
  intro X _ _ hq hZ hX
  have hna := Census.exists_ne_of_isQuasisimple hq
  rcases hX with (⟨n, hn, ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩ |
      ⟨f, hm | hm | hm | hm | hm⟩) | ⟨n, hn, hX⟩
  ·
    exact (noCfgU419_projSL_two (p := 2) (by norm_num) φ).rowU419
  ·
    intro α Y m hc
    obtain ⟨π, hπ, hker⟩ := hc.cover
    exact Or.inl (Ronan148W.rowU3_L3eps hq hZ hn (Or.inr (Or.inl ⟨φ⟩)) hc.pow_three hc.ne_one
      hc.le_autFix hc.isPerfect hc.isSubnormal hc.odd hc.one_lt π hπ hker)
  ·
    intro α Y m hc
    obtain ⟨π, hπ, hker⟩ := hc.cover
    exact Or.inl (Ronan148W.rowU3_L3eps hq hZ hn (Or.inr (Or.inr ⟨φ⟩)) hc.pow_three hc.ne_one
      hc.le_autFix hc.isPerfect hc.isSubnormal hc.odd hc.one_lt π hπ hker)
  ·
    apply NoCfgU419.rowU419
    rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
    · refine noCfgU419_of_two_pow_nine (M := 720) ?_ (by decide)
      rw [Nat.card_congr φ.toEquiv, Sec8.Item812Res2.card_projSp_two_one]
    · have hs : IsSimpleGroup X := by
        haveI := Sec21.isSimpleGroup_projSp_two hn2
        exact φ.isSimpleGroup
      intro α Y m hc
      haveI := hc.isPerfect
      obtain ⟨π, hπ, hker⟩ := hc.cover
      exact Ronan148L.rowU3_Sp4 hs hna hn φ hc.pow_three hc.ne_one hc.le_autFix hc.isSubnormal
        hc.odd hc.one_lt π hπ hker
  ·
    apply NoCfgU419.rowU419
    have hs : IsSimpleGroup X := by
      haveI := Sec21.isSimpleGroup_projSU (m := 4) le_rfl hn
      exact φ.isSimpleGroup
    intro α Y m hc
    haveI := hc.isPerfect
    obtain ⟨π, hπ, hker⟩ := hc.cover
    exact Ronan148L.rowU3_U4 hs hna hn φ hc.pow_three hc.ne_one hc.le_autFix hc.isSubnormal
      hc.odd hc.one_lt π hπ hker
  ·
    apply NoCfgU419.rowU419
    intro α Y m hc
    haveI := hc.isPerfect
    obtain ⟨π, hπ, hker⟩ := hc.cover
    exact Ronan148L.rowU3_G2 hm hc.pow_three hc.ne_one hc.le_autFix hc.isSubnormal hc.odd
      hc.one_lt π hπ hker
  ·
    exact rowU419_D4 hq hm
  ·
    apply NoCfgU419.rowU419
    intro α Y m hc
    haveI := hc.isPerfect
    obtain ⟨π, hπ, hker⟩ := hc.cover
    exact Ronan148L.rowU3_Sz hm hc.pow_three hc.ne_one hc.le_autFix hc.isSubnormal hc.odd
      hc.one_lt π hπ hker
  ·
    apply NoCfgU419.rowU419
    intro α Y m hc
    haveI := hc.isPerfect
    obtain ⟨π, hπ, hker⟩ := hc.cover
    exact Ronan148L.rowU3_F4 hm hc.pow_three hc.ne_one hc.le_autFix hc.isSubnormal hc.odd
      hc.one_lt π hπ hker
  ·
    apply NoCfgU419.rowU419
    intro α Y m hc
    haveI := hc.isPerfect
    obtain ⟨π, hπ, hker⟩ := hc.cover
    exact Ronan148L.rowU3_Tits hm hc.pow_three hc.ne_one hc.le_autFix hc.isSubnormal hc.odd
      hc.one_lt π hπ hker
  ·
    intro α Y m hc
    obtain ⟨π, hπ, hker⟩ := hc.cover
    exact Or.inl (Ronan148W.rowU3_L3eps hq hZ hn (Or.inl hX) hc.pow_three hc.ne_one
      hc.le_autFix hc.isPerfect hc.isSubnormal hc.odd hc.one_lt π hπ hker)

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148R
