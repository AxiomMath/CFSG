module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC15TFrame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NatRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenSmall
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightV1CardO
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGAlt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGLn
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGOmega
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.GH74.GLS.Stage2.Final.ModelOrd
public import CFSG.HardMathSupport.Foote.E27.TableMat
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCaseTwoCMSection
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatAlt
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesEmbed
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactPiece
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclCard
public import Certificates.Data.E27Q2O

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s1614_row2_summand (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Case168_2Small D ⊥ V hV L) :
    ∃ J₀ J₁ : Subgroup (Vtil ⊥ V hV), J₀ ∈ irrSet (lBar ⊥ V hV L) ∧
      J₁ ∈ irrSet (lBar ⊥ V hV L) ∧ J₀ ⊓ J₁ = ⊥ ∧ J₀ ⊔ J₁ = ⊤ ∧ 4 ≤ rk ↥J₀ ∧
      S1614Hyp2iiiMod (lBar ⊥ V hV L) J₀ := by
  classical
  obtain ⟨-, ⟨L₀, -, hfam⟩, -⟩ := hS
  have hW : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  have hrkJ : ∀ J : Subgroup (Vtil ⊥ V hV), Nat.card J = 2 ^ rk ↥J := fun J =>
    card_eq_two_pow hW J
  rcases hfam with ⟨-, -, hsum⟩ | ⟨-, -, hsum⟩ | ⟨-, -, hsum⟩ | ⟨-, -, hsum⟩
  · obtain ⟨J₀, J₁, hN₀, hN₁, hinf, hsup⟩ := s16c167_sumOfNat_two hsum
    refine ⟨J₀, J₁, s16c167_mem_irrSet_alt (n := 6) (by norm_num) hN₀,
      s16c167_mem_irrSet_alt (n := 6) (by norm_num) hN₁, hinf, hsup, ?_, ?_⟩
    · have h := s16c1610_two_pow_le_card_alternatingNatural (by norm_num : 2 ≤ 6) hN₀
      rw [hrkJ J₀] at h
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h
    · haveI : Finite (FFModel.altDn 6).Amb := by
        change Finite (Multiplicative (Fin 6 → ZMod 2))
        infer_instance
      exact s1614_transport (s1614_hyp2iii_alt (by norm_num)) hN₀
  · obtain ⟨J₀, J₁, hN₀, hN₁, hinf, hsup⟩ := s16c167_sumOfNat_two hsum
    refine ⟨J₀, J₁, s16c167_mem_irrSet_alt (n := 7) (by norm_num) hN₀,
      s16c167_mem_irrSet_alt (n := 7) (by norm_num) hN₁, hinf, hsup, ?_, ?_⟩
    · have h := s16c1610_two_pow_le_card_alternatingNatural (by norm_num : 2 ≤ 7) hN₀
      rw [hrkJ J₀] at h
      exact le_trans (by norm_num) ((Nat.pow_le_pow_iff_right (by norm_num)).1 h)
    · haveI : Finite (FFModel.altDn 7).Amb := by
        change Finite (Multiplicative (Fin 7 → ZMod 2))
        infer_instance
      exact s1614_transport (s1614_hyp2iii_alt (by norm_num)) hN₀
  · obtain ⟨J₀, J₁, hN₀, hN₁, hinf, hsup⟩ := s16c167_sumOfNat_two hsum
    refine ⟨J₀, J₁, s16c167_mem_irrSet_ln (m := 4) (by norm_num) hN₀,
      s16c167_mem_irrSet_ln (m := 4) (by norm_num) hN₁, hinf, hsup, ?_, ?_⟩
    · have h := s16c1610_rk_binaryNaturalSL hN₀
      omega
    · obtain ⟨K, hKf, hKfin, hK, hR⟩ := hN₀
      haveI : Finite (FFModel.nat (StatedSL 4 K)).Amb := by
        change Finite (Multiplicative (Fin 4 → K))
        infer_instance
      exact s1614_transport (s1614_hyp2iii_ln K (by simpa using hK)) hR
  · obtain ⟨J₀, J₁, hN₀, hN₁, hinf, hsup⟩ := s16c167_sumOfNat_two hsum
    refine ⟨J₀, J₁, s16c167_mem_irrSet_omegaMinus (Or.inl rfl) hN₀,
      s16c167_mem_irrSet_omegaMinus (Or.inl rfl) hN₁, hinf, hsup, ?_, ?_⟩
    · have h := s16c1610_rk_natOmegaMinus (by norm_num : 2 ≤ 6) hN₀
      omega
    · obtain ⟨-, K, hKf, hKfin, b, c, hK, hbc, hR⟩ := hN₀
      haveI : Finite (FFModel.nat (StatedOmega (StatedQuadMinus 3 K b c))).Amb := by
        unfold FFModel.nat
        dsimp only
        infer_instance
      exact s1614_transport (s1614_hyp2iii_omega K (by simpa using hK) b c hbc) hR

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
