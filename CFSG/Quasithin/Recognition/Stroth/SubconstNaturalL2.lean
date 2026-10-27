module

public import CFSG.Quasithin.Recognition.Stroth.LemmaSDegree
public import CFSG.Quasithin.Vol2.Ch3E215MC
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelPointStructure
public import CFSG.Quasithin.Recognition.Stroth.Weiss80Route
public import CFSG.Assembly.OrderReductions.CharacterInflation
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellThompson
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperCommutingImages
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SmallerRecognitionDischarge
public import CFSG.Quasithin.Background.E2TwoNoNStmt
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.Quasithin.Stroth

open CFSG.GorensteinWalter CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.MatrixGroups

open scoped MatrixGroups

theorem rankOneData_psl2 (m : ℕ) (hm : 2 ≤ m) :
    ∃ U B : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)),
      RankOneData (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)) U B ∧
        Nat.card U = 2 ^ m := by
  let K := GaloisField 2 m
  let q := 2 ^ m
  have hKcard : Nat.card K = q := by
    simpa [K, q] using GaloisField.card 2 m (by omega)
  have hq4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  haveI : IsSimpleGroup (PSL2MatrixGroup K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hq4
  obtain ⟨-, h2tr, hcardΩ, hUB, hTB, hUnorm, hinf, hsup, hTzero, hTcyc, hTcard,
    ⟨S, hS⟩, hUcard, hreg, hSE, htwoRank, htwoRank', hinv, hcomm, hswap, hstd⟩ :=
      LinearModel.linear_rank_one_point_structure m hm hKcard
  set U : Subgroup (PSL2MatrixGroup K) := psl2UpperUnipotentSubgroup K with hUdef
  set B : Subgroup (PSL2MatrixGroup K) := psl2Borel K with hBdef
  set T : Subgroup (PSL2MatrixGroup K) := LinearModel.torus K with hTdef
  have hUB' : U ≤ B := by rw [hUdef, hBdef]; exact hUB
  have hTB' : T ≤ B := by rw [hTdef, hBdef]; exact hTB
  have hUnorm' : (U.subgroupOf B).Normal := by rwa [hUdef, hBdef]
  have hsup' : U ⊔ T = B := by rw [hUdef, hTdef, hBdef]; exact hsup
  have hTcard' : Nat.card T = q - 1 := by rw [hTdef, hTcard, hKcard]
  have hUcard' : Nat.card U = q := by rw [hUdef, hUcard, hKcard]
  have hTnorm : T ≤ Subgroup.normalizer (U : Set (PSL2MatrixGroup K)) :=
    hTB'.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hUB').mp hUnorm')
  have hnsq : LinearModel.standardSwap K * LinearModel.standardSwap K = 1 := by
    simpa [pow_two, hstd.1] using pow_orderOf_eq_one (LinearModel.standardSwap K)
  have hnT : ∀ t ∈ T, (LinearModel.standardSwap K)⁻¹ * t * LinearModel.standardSwap K ∈ T := by
    intro t ht
    rw [(hswap (LinearModel.standardSwap K) hstd.2.1 hstd.2.2).2.1 t (by rwa [hTdef] at ht)]
    exact T.inv_mem ht
  have hwB : LinearModel.standardSwap K ∉ B := by
    intro h
    have hfix : LinearModel.standardSwap K • psl2ProjectiveInfinity K =
        psl2ProjectiveInfinity K := h
    rw [hstd.2.1] at hfix
    exact (LinearModel.infinity_ne_zero (K := K)).symm hfix
  have hbruhat : ∀ g : PSL2MatrixGroup K, g ∈ B ∨
      ∃ b₁ ∈ B, ∃ b₂ ∈ B, g = b₁ * LinearModel.standardSwap K * b₂ :=
    fun g => CFSG.Quasithin.Ch3E215M.bruhat_psl2Borel hKcard hwB g
  have hUbot : U ≠ ⊥ := by
    intro h
    have h1 : Nat.card U = 1 := by rw [h, Subgroup.card_bot]
    rw [hUcard'] at h1
    have : 2 ≤ q := by
      dsimp [q]
      exact Nat.one_lt_two_pow (by omega)
    omega
  have hdata : RankOneData (PSL2MatrixGroup K) U B := by
    refine ⟨?_, hUbot, ⟨S, ?_⟩, hUB', ?_, ?_, ?_⟩
    · rw [← hS]
      exact S.isPGroup'
    · rw [hS, hUdef]
    · intro M hUM hM
      rcases le_B_or_eq_top_of_bruhat hsup'.symm hTnorm hnT hnsq hUbot hbruhat M hUM with h | h
      · exact h
      · exact absurd h hM.ne
    · rw [hBdef, CFSG.Quasithin.Ch3E215M.index_psl2Borel hKcard, hUcard']
      omega
    · have hle : U.relIndex B ≤ Nat.card T :=
        relIndex_le_card_right_of_sup_eq hsup'.symm hTnorm
      calc
        U.relIndex B ≤ Nat.card T := hle
        _ = q - 1 := hTcard'
        _ < q := by
          have : 2 ≤ q := by
            dsimp [q]
            exact Nat.one_lt_two_pow (by omega)
          omega
        _ = Nat.card U := hUcard'.symm
  refine ⟨U, B, hdata, ?_⟩
  rw [hUcard']

theorem card_eq_of_hasNormalCopy_psl2 :
    ∀ (Y : Type) [Group Y] [Finite Y] (Ω : Type) [Fintype Ω] [MulAction Y Ω]
      [FaithfulSMul Y Ω] (m : ℕ), 2 ≤ m →
      MulAction.IsMultiplyPretransitive Y Ω 2 →
      (∃ e : ℕ, 1 ≤ e ∧ Fintype.card Ω = 1 + 2 ^ e) →
      HasNormalCopy Y (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)) →
      Fintype.card Ω = 2 ^ m + 1 := by
  intro Y _ _ Ω _ _ _ m hm h2 hdeg hcopy
  obtain ⟨M, hMnormal, hMequiv⟩ := hcopy
  let φ : ↥M ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m) :=
    Classical.choice hMequiv
  letI : M.Normal := hMnormal
  obtain ⟨U, B, hdata, hUcard⟩ := rankOneData_psl2 m hm
  let U' : Subgroup M := U.map φ.symm.toMonoidHom
  let B' : Subgroup M := B.map φ.symm.toMonoidHom
  have hdata' : RankOneData M U' B' := hdata.map φ.symm
  have hU'card : Nat.card U' = 2 ^ m := by
    rw [Subgroup.card_map_of_injective φ.symm.injective, hUcard]
  have hMbot : M ≠ ⊥ := by
    intro hbot
    apply hdata'.ne_bot
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subgroup.mem_bot.mp (by simpa [hbot] using x.2))
  have hdeg' := card_eq_one_add_of_rankOneData M hMbot h2 hdeg
    ⟨U', B', hdata', hU'card⟩
  omega

end CFSG.Quasithin.Stroth
