module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Simple
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKJPrimeLie
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSimpleComponentRank
public import CFSG.LieType.Steinberg.CentralExt.PSLCoverCenter
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycSL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallNoTwoGen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s15_eq_one_of_sl_six_seven_component_at_three
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hSL : IsSLn ↥(lBar V₀ V hV L) n 1) :
    s15 D.M V₀ V hV L = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm3 : 3 ≤ m + 1 := by omega
  have hm5 : 5 ≤ m + 1 := by omega
  have hLm : IsLn ↥(lBar V₀ V hV L) (m + 1) 1 := s16k_isLn_of_isSLn hm3 hSL
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) := s16c167_cfg2_simple_ln hLm
  obtain ⟨K, hKf, hKfin, hKcard, ⟨eSL⟩⟩ := hSL
  let _ : Field K := hKf
  let _ : Finite K := hKfin
  let _ : Fintype K := Fintype.ofFinite K
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  have _ : CharP K 2 := charP_of_card_eq_prime_pow (R := K) (p := 2) (f := 1) (by
    simpa [Nat.card_eq_fintype_card] using hKcard)
  obtain ⟨fproj⟩ := s15k_jp_projEquiv hK2 (StatedSL (m + 1) K)
  let eSLPSL : ↥(lBar V₀ V hV L) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) K :=
    eSL.trans (((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj
      (m + 1) K).trans fproj).symm)
  have hcover : ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥(lBar V₀ V hV L)) →
      IsPGroup 2 ↥(Subgroup.center Q) := by
    intro Q _ _ hQ ⟨eQH⟩
    let ePSL : (Q ⧸ Subgroup.center Q) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) K :=
      eQH.trans eSLPSL
    have hperf : Group.IsPerfect Q := ⟨hQ.1⟩
    have hdvd := CFSG.LieType.Steinberg.CentralExt.SLClosed.card_center_dvd_gcd_of_psl_of_five_le
      hperf hm5 ePSL
    have hgcd : Nat.gcd (m + 1) (Nat.card K - 1) = 1 := by
      rw [hK2]
      simp
    have hdiv1 : Nat.card ↥(Subgroup.center Q) ∣ 1 := by
      simpa only [hgcd] using hdvd
    have hZ : Nat.card ↥(Subgroup.center Q) = 1 := Nat.dvd_one.mp hdiv1
    exact IsPGroup.of_card (n := 0) (by simp [hZ])
  have hE9 := CFSG.AGLEmbedding.BlockCyc.hasE9_psl_of_three_le (m := m) (by omega) (F := K)
    eSLPSL.symm
  obtain ⟨E, hEab, hEcard⟩ := hE9
  have hdvdE : 3 ^ 2 ∣ Nat.card ↥E := by rw [hEcard]
  have hrankE : 2 ≤ CFSG.Open.pRank 3 E :=
    CFSG.AGLEmbedding.KFactProofs.SmallIdent.two_le_pRank_of_exponent
      Nat.prime_three E hdvdE (fun s hs => hEab.2 s hs)
  have hrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(lBar V₀ V hV L)) :=
    hrankE.trans (CFSG.SectionRank.pRank_mono (by norm_num) (le_top : E ≤ ⊤))
  exact s15_eq_one_of_simple_component_of_three_rank c hcomp hsimple (by norm_num) hrank hcover

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
