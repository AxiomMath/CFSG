module

public import CFSG.LocalAnalysis.StandardType.GGF4N2NbrReflection
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestGen
import CFSG.RankThree.PartOne.AUTSL.Interface
import CFSG.RankThree.PartTwo.KFacts.K71L28TwoFree
import all CFSG.LocalAnalysis.StandardType.GGF4N2JModelExclusions

public section

namespace CFSG.StandardType.N2TorusTrace

open Matrix CFSG.SeitzReduction.E6Pilot CFSG.SeitzReduction.LinearPilot
open CFSG.StandardType.N2KCoordinate
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBGraphForm

abbrev S4 := Matrix.SpecialLinearGroup (Fin 4) F4

theorem trace_blockFour (g : S4) :
    Matrix.trace ((blockFour g : SL6F4) : Matrix (Fin 6) (Fin 6) F4) =
      Matrix.trace (g : Matrix (Fin 4) (Fin 4) F4) := by
  rw [coe_blockFour, blockFourMat]
  change Matrix.trace (Matrix.reindex e46 e46 (Matrix.fromBlocks
    (g : Matrix (Fin 4) (Fin 4) F4) 0 0 (1 : Matrix (Fin 2) (Fin 2) F4))) = _
  rw [N2KCoordinate.trace_reindex, N2KCoordinate.trace_fromBlocks_one, Fintype.card_fin]
  simp [CharTwo.two_eq_zero]

theorem trace_coordBlock01 (A : SL2F4) :
    Matrix.trace ((coordBlock01 A : SL6F4) : Matrix (Fin 6) (Fin 6) F4) =
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) F4) := by
  rw [Matrix.trace, Matrix.trace_fin_two]
  simp only [Matrix.diag_apply, coordBlock01, pairEmbed_apply]
  simp [Fin.sum_univ_succ, CharTwo.two_eq_zero]
  ring_nf
  change ((4 : ℕ) : F4) = 0
  rw [CharP.cast_eq_zero_iff F4 2]
  norm_num

theorem coordA2_trace :
    Matrix.trace (coordA2 : Matrix (Fin 2) (Fin 2) F4) ≠ 0 ∧
    Matrix.trace (coordA2 : Matrix (Fin 2) (Fin 2) F4) ≠ 1 ∧
    Matrix.trace ((coordA2⁻¹ : SL2F4) : Matrix (Fin 2) (Fin 2) F4) =
      Matrix.trace (coordA2 : Matrix (Fin 2) (Fin 2) F4) := by
  have hn : ∀ c : F4, (c = 0 ∨ c = 1) →
      Matrix.trace (coordA2 : Matrix (Fin 2) (Fin 2) F4) ≠ c := by
    intro c hc htr
    have h6m := CFSG.RankThree.PartTwo.KFacts.mat2_pow_six_eq_one_of_trace coordA2.2
      (htr ▸ hc)
    have h6 : coordA2 ^ 6 = 1 := Subtype.ext (by simpa using h6m)
    have hd := orderOf_dvd_iff_pow_eq_one.mpr h6
    rw [coordA2_order] at hd
    norm_num at hd
  exact ⟨hn 0 (Or.inl rfl), hn 1 (Or.inr rfl), N2KCoordinate.trace_sl2_inv coordA2⟩

theorem exists_literal_block_witness :
    ∃ g : S4, blockFour g = coordBlock01 coordA2 ∧
      Matrix.trace (g : Matrix (Fin 4) (Fin 4) F4) ≠ 0 ∧
      Matrix.trace (g : Matrix (Fin 4) (Fin 4) F4) ≠ 1 ∧
      Matrix.trace ((g⁻¹ : S4) : Matrix (Fin 4) (Fin 4) F4) =
        Matrix.trace (g : Matrix (Fin 4) (Fin 4) F4) := by
  have h01 : coordBlock01 coordA2 ∈ coordT01 := Subgroup.mem_zpowers _
  have hM : coordBlock01 coordA2 ∈ N2KComplementary.blockM :=
    blockSpecialLinear_mono (by decide : coordJ01 ⊆ N2KComplementary.letterI)
      (coordT01_le_block h01)
  obtain ⟨g, hg⟩ := N2KComplementary.blockM_le_blockFour_range hM
  have htr : Matrix.trace (g : Matrix (Fin 4) (Fin 4) F4) =
      Matrix.trace (coordA2 : Matrix (Fin 2) (Fin 2) F4) := by
    rw [← trace_blockFour, hg, trace_coordBlock01]
  obtain ⟨h0, h1, hi⟩ := coordA2_trace
  refine ⟨g, hg, htr ▸ h0, htr ▸ h1, ?_⟩
  rw [← trace_blockFour (g⁻¹), map_inv, hg, ← map_inv coordBlock01,
    trace_coordBlock01, hi, htr]

theorem exists_of_literal_packet {G : Type} [Group G] {Bs J K : Subgroup G}
    (ψ : SL6F4 →* K) (rho : Bs →* SL6F4) (eJ : ↥J ≃* S4)
    (hRange : (K.subtype.comp (ψ.comp rho)).range = Bs ⊓ K)
    (hTorus : rho.range = coordinateTorus)
    (hChart : ∀ g : S4, (ψ (blockFour g) : G) = (eJ.symm g : G)) :
    ∃ g : S4, blockFour g = coordBlock01 coordA2 ∧ (eJ.symm g : G) ∈ Bs ⊓ J ∧
      Matrix.trace (g : Matrix (Fin 4) (Fin 4) F4) ≠ 0 ∧
      Matrix.trace (g : Matrix (Fin 4) (Fin 4) F4) ≠ 1 ∧
      Matrix.trace ((g⁻¹ : S4) : Matrix (Fin 4) (Fin 4) F4) =
        Matrix.trace (g : Matrix (Fin 4) (Fin 4) F4) := by
  obtain ⟨g, hg, h0, h1, hi⟩ := exists_literal_block_witness
  have htor : coordBlock01 coordA2 ∈ rho.range := by
    rw [hTorus]
    exact (le_sup_left : coordT01 ≤ coordinateTorus) (Subgroup.mem_zpowers _)
  obtain ⟨b, hb⟩ := htor
  have hmem : (ψ (rho b) : G) ∈ Bs ⊓ K := by
    apply hRange ▸ (show (K.subtype.comp (ψ.comp rho)) b ∈
      (K.subtype.comp (ψ.comp rho)).range from ⟨b, rfl⟩)
  have he : (eJ.symm g : G) = (ψ (rho b) : G) := by
    rw [← hChart, hg, ← hb]
  exact ⟨g, hg, ⟨he ▸ hmem.1, (eJ.symm g).2⟩, h0, h1, hi⟩

theorem traces_of_aut (β : MulAut S4) {g : S4}
    (h0 : Matrix.trace (g : Matrix (Fin 4) (Fin 4) F4) ≠ 0)
    (h1 : Matrix.trace (g : Matrix (Fin 4) (Fin 4) F4) ≠ 1)
    (hi : Matrix.trace ((g⁻¹ : S4) : Matrix (Fin 4) (Fin 4) F4) =
      Matrix.trace (g : Matrix (Fin 4) (Fin 4) F4)) :
    Matrix.trace ((β g : S4) : Matrix (Fin 4) (Fin 4) F4) ≠ 0 ∧
    Matrix.trace ((β g : S4) : Matrix (Fin 4) (Fin 4) F4) ≠ 1 ∧
    Matrix.trace (((β g)⁻¹ : S4) : Matrix (Fin 4) (Fin 4) F4) =
      Matrix.trace ((β g : S4) : Matrix (Fin 4) (Fin 4) F4) := by
  obtain ⟨A, σ, ε, hε, hβ⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl (n := 4) (K := F4) (by norm_num) β
  have htr : ∀ a : S4,
      Matrix.trace ((a⁻¹ : S4) : Matrix (Fin 4) (Fin 4) F4) =
        Matrix.trace (a : Matrix (Fin 4) (Fin 4) F4) →
      Matrix.trace ((β a : S4) : Matrix (Fin 4) (Fin 4) F4) =
        σ (Matrix.trace (a : Matrix (Fin 4) (Fin 4) F4)) := by
    intro a ha
    rw [hβ, MulAut.mul_apply, MulAut.mul_apply, trace_slConjugation, trace_slFieldAut]
    interval_cases ε
    · rw [pow_zero, MulAut.one_apply]
    · rw [pow_one, trace_slGraphAut, ha]
  have hg := htr g hi
  have hgi := htr g⁻¹ (by simpa only [inv_inv] using hi.symm)
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    apply h0
    apply σ.injective
    simpa only [map_zero] using hg.symm.trans hz
  · intro ho
    apply h1
    apply σ.injective
    simpa only [map_one] using hg.symm.trans ho
  · rw [← map_inv β g, hgi, hi, hg]

end CFSG.StandardType.N2TorusTrace

namespace CFSG.StandardType

open CFSG.StandardType.N2KCoordinate CFSG.StandardType.N2TorusTrace
open CFSG.SeitzReduction.E6Pilot


theorem ggF4N2_exists_torus_trace_witness
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K) (eJ : ↥J ≃* S4) :
    ∃ g : S4, (eJ.symm g : G) ∈ Bs ⊓ J ∧
      Matrix.trace (g : Matrix (Fin 4) (Fin 4) F4) ≠ 0 ∧
      Matrix.trace (g : Matrix (Fin 4) (Fin 4) F4) ≠ 1 ∧
      Matrix.trace ((g⁻¹ : S4) : Matrix (Fin 4) (Fin 4) F4) =
        Matrix.trace (g : Matrix (Fin 4) (Fin 4) F4) := by
  obtain ⟨ψ, rho, -, -, -, -, -, -, -, hRange, -, hTorus, -, -, ⟨e0, hChart, -⟩⟩ :=
    ggF4N2K_originalLiteralChart_of_original_data hR hNbr hL hK
  obtain ⟨g0, -, hmem, h0, h1, hi⟩ := exists_of_literal_packet ψ rho e0 hRange hTorus hChart
  let β : MulAut S4 := e0.symm.trans eJ
  obtain ⟨h0', h1', hi'⟩ := traces_of_aut β h0 h1 hi
  refine ⟨β g0, ?_, h0', h1', hi'⟩
  simpa only [β, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using hmem

end CFSG.StandardType

end
