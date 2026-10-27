module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Pieces
public import CFSG.LocalAnalysis.StandardType.FS81.LocalOrthRows
public import CFSG.LocalAnalysis.StandardType.FS81.OrthRowCanon
public import CFSG.LocalAnalysis.StandardType.FS81.SplitE
public import CFSG.LocalAnalysis.StandardType.MarkingDict
public import CFSG.Open.StatedZModTwo

public section

namespace CFSG.StandardType.FrameRoute.FS81

open QuadraticMap Module CFSG.Open CFSG.Assembly CFSG.GroupTheory.WeirSylow
  CFSG.LieType.Universal.Spin CFSG.ComponentClassification.OuterAutomorphisms

private theorem nondegenerate_quadMinus_five :
    (QuadraticMap.polarBilin (quadMinus 5 (ZMod 2) 1 1)).Nondegenerate :=
  CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 5 (ZMod 2)
    (by decide : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0)

private theorem isPlusType_quadMinus_five_iff :
    IsPlusType (quadMinus 5 (ZMod 2) 1 1) ↔ Even 5 :=
  ⟨fun h => absurd h (not_isPlusType_quadMinus (by norm_num)
      (by decide : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0)),
    fun h => absurd h (by decide : ¬ Even 5)⟩

theorem not_three_dvd_card_outer_of_isTwD5 {G : Type} [Group G] {K : Subgroup G}
    (hmark : IsTwD5 K) (hcenter : Subgroup.center K = ⊥) : ¬ 3 ∣ Nat.card (Outer K) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaMinus_of_marking (r := 5) (by norm_num) hmark hcenter
  have hΩ : StatedClassicalModel ↥(StatedOmega (StatedQuadMinus 5 (ZMod 2) 1 1))
      .POmegaMinus 5 2 1 := by
    have hbot : StatedScalars (Fin 4 ⊕ Fin 4 ⊕ Fin 2) (ZMod 2) = ⊥ :=
      CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two (K := ZMod 2) (by norm_num) _
    refine ⟨⟨Nat.prime_two, by norm_num, by norm_num⟩, ZMod 2, inferInstance, inferInstance,
      by norm_num, 1, 1, (by decide : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0), ?_⟩
    exact ⟨((QuotientGroup.quotientMulEquivOfEq
      (by rw [hbot, Subgroup.bot_subgroupOf])).trans QuotientGroup.quotientBot).symm⟩
  have hcl : StatedClassicalModel K .POmegaMinus 5 2 1 :=
    CFSG.StandardType.statedClassicalModel_of_mulEquiv' e.symm hΩ
  have hle := CFSG.AGLEmbedding.card_outer_le_two_of_omegaMinus_two hcl
  intro h3
  have h3le : 3 ≤ Nat.card (Outer K) := Nat.le_of_dvd hle.1 h3
  omega

theorem t5Canon_holds :
    ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G),
      HypTwD5 b₀ K E → CanonTwD5 b₀ K E := by
  intro G _ _ b₀ K E hHyp
  obtain ⟨hb₀, hKC, hKn, hcenter, hmark, hcyc, -, -, hEmax, hbE, -, -⟩ := hHyp
  obtain ⟨hdisj, hsup, hmax⟩ := fs81_split_E hb₀ hKC hKn hcenter
    (not_three_dvd_card_outer_of_isTwD5 hmark hcenter) hcyc hEmax hbE
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaMinus_of_marking (r := 5) (by norm_num) hmark hcenter
  have hcanon := fs81_canon_of_orthEquiv (Q := quadMinus 5 (ZMod 2) 1 1)
    nondegenerate_quadMinus_five (n := 5)
    (by rw [Module.finrank_fintype_fun_eq_card]; simp) isPlusType_quadMinus_five_iff
    (e.trans (CFSG.RankThree.PartOne.statedOmegaOrthEquiv
      (Q := quadMinus 5 (ZMod 2) 1 1) (Q₀ := StatedQuadMinus 5 (ZMod 2) 1 1)
      (CFSG.LieType.Universal.Spin.coe_quadMinus 5 (ZMod 2) 1 1))) hmax
  exact ⟨hdisj, hsup, hmax, hcanon.1, hcanon.2⟩

theorem t5Local_holds :
    ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G), StdTwD5 b₀ K E →
      ∃ B : Basis3 G (5 + 1), Adapted B b₀ K E ∧ (LocalOrthI B b₀ ∨ LocalOrthII B b₀) := by
  intro G _ _ b₀ K E hstd
  obtain ⟨-, hHyp, hCanon⟩ := hstd
  obtain ⟨hb₀, hKC, hKn, hcenter, hmark, hcyc, -, -, -, -, -, -⟩ := hHyp
  obtain ⟨-, hsup, hmax, hcard, -⟩ := hCanon
  obtain ⟨hKs, ⟨φ⟩⟩ :=
    isSimpleGroup_and_mulEquiv_of_isRow_twD (r := 5) (by norm_num) hmark hcenter
  obtain ⟨B, hB, hloc, -⟩ := exists_basis_localOrth_of_data (n := 5)
    nondegenerate_quadMinus_five
    (exists_totallySingular_three_quadMinus (n := 4) (by norm_num))
    (omegaAutIsometric_quadMinus (n := 4) (by norm_num))
    (by norm_num) φ hKs hb₀ hKC hKn hcenter hcyc hsup hmax hcard
  exact ⟨B, hB, hloc⟩

end CFSG.StandardType.FrameRoute.FS81

end
