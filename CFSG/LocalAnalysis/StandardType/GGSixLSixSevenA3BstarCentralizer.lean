module

public import CFSG.LocalAnalysis.StandardType.AlternatingEightNormalizerAction
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3OmEntry
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3OmEntryMinus
public import CFSG.LocalAnalysis.StandardType.GGFieldNbrTableB
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  Multiplicative

section Core

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ} {ψ : U →* G}

theorem GGSixCtxV2.bstar_le_normalizer_j (ha₀ : GGLNoncyclicInput)
    (hctx : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) : Bs ≤ Subgroup.normalizer (J : Set G) :=
  hctx.bstar.le_centralizer.trans
    (centralizer_le_normalizer_stdSub hctx.sstar (ha₀ G p B x L hctx.1) hctx.stdSub.1)

theorem GGSixCtxV2.pow_four_le_card_b (hctx : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) :
    p ^ 4 ≤ Nat.card B := by
  have hB : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.sstar.1.2.1
  have h4 : 4 ≤ LargeEvenTwoLocalRank p G := hctx.beta.2.2.2
  rw [hB]
  exact Nat.pow_le_pow_right hctx.prime.pos h4

theorem GGSixCtxV2.card_b_inf_centralizer_j (hctx : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) :
    Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set G)) = p ^ 2 := by
  have hD : D = B ⊓ Subgroup.centralizer (J : Set G) := hctx.stdSub.1.2.2.2.2.2.2
  rw [← hD]
  exact hctx.card_d

theorem GGSixCtxV2.isPGroup_b (hctx : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) : IsPGroup p B :=
  fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hctx.sstar.1.1.2 g g.2)⟩

theorem GGSixCtxV2.isPGroup_bstar (hctx : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) : IsPGroup p Bs :=
  fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hctx.bstar.2.1.2 g g.2)⟩

theorem GGSixCtxV2.alternating_eight_quotient (hctx : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
    (hA : GGSixLSevenA3Case J) :
    commutator ↥J = ⊤ ∧ Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 8)) ∧
      IsPGroup 2 (Subgroup.center ↥J) := by
  have hJq : CFSG.Assembly.IsQuasisimple J := hctx.j_isComponentOf_inf.2.2
  refine ⟨hJq.1, ?_, ?_⟩
  · exact (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff
      (↥J ⧸ Subgroup.center ↥J)).1 hA
  · exact IsPGroup.of_card_dvd_pow (n := 1) (by simpa using card_center_dvd_two_of_a3Case hJq hA)

theorem GGSixCtxV2.bstar_inf_centralizer_le_of_a3 (ha₀ : GGLNoncyclicInput)
    (hctx : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) (hA : GGSixLSevenA3Case J) :
    Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D := by
  have hp : p.Prime := hctx.prime
  have hp2 : p ≠ 2 := hctx.ne_two
  have hcfg : GGConfig p B Bs x L D J := ⟨hctx.1, hctx.bstar, hctx.stdSub⟩
  have hBN : B ≤ Subgroup.normalizer (J : Set G) :=
    hctx.bstar.1.trans (hctx.bstar_le_normalizer_j ha₀)
  have hC : Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 2 :=
    hctx.card_b_inf_centralizer_j.le
  obtain ⟨hperf, ⟨e⟩, hZ⟩ := hctx.alternating_eight_quotient hA
  obtain ⟨T, hT0, hT2, hTJ, hBT⟩ :=
    AlternatingEightAction.exists_two_subgroup_normalized_of_alternating_eight_quotient hp hp2
      hperf e hZ hBN hctx.isPGroup_b hctx.pow_four_le_card_b hC
  exact ggStdSubBstarCentralizer_of_twoSubgroup hcfg ⟨T, hT0, hT2, hTJ, hBT⟩

theorem GGSixCtxV2.a3_structure (ha₀ : GGLNoncyclicInput)
    (hctx : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) (hA : GGSixLSevenA3Case J) :
    p = 3 ∧ Nat.card B = 3 ^ 4 ∧ B = Bs := by
  have hp : p.Prime := hctx.prime
  have hp2 : p ≠ 2 := hctx.ne_two
  have hBB := hctx.bstar_inf_centralizer_le_of_a3 ha₀ hA
  obtain ⟨hperf, ⟨e⟩, -⟩ := hctx.alternating_eight_quotient hA
  have hBBs : B ≤ Bs := hctx.bstar.1
  have hBN : B ≤ Subgroup.normalizer (J : Set G) := hBBs.trans (hctx.bstar_le_normalizer_j ha₀)
  have hBsN : Bs ≤ Subgroup.normalizer (J : Set G) := hctx.bstar_le_normalizer_j ha₀
  have hDle : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D := hBB
  have hDcard : Nat.card D = p ^ 2 := hctx.card_d
  have hB9 : Nat.card B ≤ 9 * p ^ 2 := by
    have h := AlternatingEightAction.card_le_nine_mul_card_inf hp hp2 hperf e hBN hctx.isPGroup_b
    rwa [hctx.card_b_inf_centralizer_j] at h
  have hBs9 : Nat.card Bs ≤ 9 * p ^ 2 := by
    have h := AlternatingEightAction.card_le_nine_mul_card_inf hp hp2 hperf e hBsN
      hctx.isPGroup_bstar
    have h2 : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 2 :=
      (Subgroup.card_le_of_le hDle).trans hDcard.le
    exact h.trans (Nat.mul_le_mul_left 9 h2)
  have h4 : p ^ 4 ≤ Nat.card B := hctx.pow_four_le_card_b
  have hp3 : p = 3 := by
    have hpos : 0 < p ^ 2 := pow_pos hp.pos 2
    have hsq : p ^ 2 ≤ 9 := by
      have h44 : p ^ 4 = p ^ 2 * p ^ 2 := by ring
      exact Nat.le_of_mul_le_mul_right (by rw [← h44]; omega) hpos
    have hp3' : p ≤ 3 := by
      by_contra hcon
      have h4p : 4 ≤ p := by omega
      have := Nat.pow_le_pow_left h4p 2
      omega
    have := hp.two_le
    omega
  subst hp3
  have hB81 : Nat.card B = 3 ^ 4 := by
    have : Nat.card B ≤ 81 := by simpa using hB9
    have h4' : 3 ^ 4 ≤ Nat.card B := h4
    norm_num at h4' ⊢
    omega
  refine ⟨rfl, hB81, ?_⟩
  have hBs81 : Nat.card Bs ≤ 3 ^ 4 := by simpa using hBs9
  exact Subgroup.eq_of_le_of_card_ge hBBs (by rw [hB81]; exact hBs81)

end Core

section Wrapper


theorem ggSixLSixSevenA3BstarInput_of_lNoncyclic (ha₀ : GGLNoncyclicInput) (t : StatedLieTag) :
    GGSixLSixSevenA3BstarInput t := by
  intro G _ _ p B Bs x L D J n f ψ hctx _ _ _ hA
  exact hctx.bstar_inf_centralizer_le_of_a3 ha₀ hA

end Wrapper

section Holds


theorem ggSixLSixSevenA3BstarInput_holds (t : StatedLieTag) : GGSixLSixSevenA3BstarInput t :=
  ggSixLSixSevenA3BstarInput_of_lNoncyclic ggLNoncyclicInput_holds t

theorem ggSixLSixSevenConjA3At_POmegaPlus : GGSixLSixSevenConjA3At .POmegaPlus :=
  ggSixLSixSevenConjA3At_POmegaPlus_of_bstar (ggSixLSixSevenA3BstarInput_holds .POmegaPlus)

theorem ggSixLSixSevenConjA3At_POmegaMinus : GGSixLSixSevenConjA3At .POmegaMinus :=
  ggSixLSixSevenConjA3At_POmegaMinus_of_bstar (ggSixLSixSevenA3BstarInput_holds .POmegaMinus)

end Holds

end CFSG.StandardType
