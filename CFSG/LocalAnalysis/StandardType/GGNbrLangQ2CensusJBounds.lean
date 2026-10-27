module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusDefs
import CFSG.LocalAnalysis.StandardType.GGResLeaf
import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag


theorem q2c_Jbounds {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hJ : GGInnerDiagOn Bs J)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) {d m : ℕ} (hd : 3 ≤ d) (hm : 2 ≤ m)
    (hpd : p ∣ d) (hpm : p ∣ 2 ^ m - 1) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ m)
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :
    d ≤ LargeEvenTwoLocalRank p G ∧ LargeEvenTwoLocalRank p G ≤ d + 1 := by
  classical
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hμ4 : 4 ≤ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.1.2.2.2
  haveI : CharP K 2 :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.charP_two_of_card_pow hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpm
  constructor
  · by_cases hd4 : d ≤ 4
    · omega
    · have hd4' : 4 ≤ d := by omega
      have hsec := slHasSections_of_four_le hp hpK hd4'
      have hT : GGTorusLift p (d - 2) (projectiveSL d K) :=
        TypeA.ggTorusLift_sub_two hp hpK (by omega) hsec
      have h2 := hcfg.torusLift_add_two_le_twoLocalRank (θ.trans (TypeA.recipeEquiv d K)) hT
      omega
  · obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    have hΛ : LargeEvenInLambda2 ⟨.A, d', m⟩ :=
      ⟨show 1 ≤ m by omega, show 1 ≤ d' by omega, fun _ => show 2 ≤ m by omega⟩
    have hhas : GGHasLabel ⟨.A, d', m⟩ (↥J ⧸ Subgroup.center ↥J) := by
      unfold GGHasLabel
      dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeLinear]
      exact ⟨K, inferInstance, inferInstance, hK, ⟨θ⟩⟩
    obtain ⟨hJperf, lab', -, hraw⟩ := ggInnerDiagOn_relabel ggLabelRigidInput_holds hJ hΛ hhas
    obtain ⟨_, _, _, _, _, _, _, hlab', _⟩ := largeEvenRawDatum_exists hraw
    subst hlab'
    obtain ⟨F, _, _, hF, -, -, θJ, -, -, hact⟩ := hraw
    have hpF : p ∣ Nat.card F - 1 := by
      rw [show Nat.card F = Nat.card K from hF.trans hK.symm]
      exact hpK
    set E : Subgroup (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin (d' + 1)) F))) :=
      (ggGamma J hN).range.map (ggInducedAut θJ) with hEdef
    have hE : IsElemAbelian p E := by
      rw [hEdef]
      exact (ggBsAut_range_isElemAbelian hcfg.2.1.2.1 hN).map (ggInducedAut θJ)
    have hcardE : Nat.card E = Nat.card (ggGamma J hN).range := by
      rw [hEdef]
      exact Subgroup.card_map_of_injective (ggInducedAut_injective_of_perfect hJperf θJ)
    have hIE : ∀ b : Bs, ggInducedAut θJ (ggGamma J hN b) ∈
        LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (d' + 1)) F))
          Set.univ := by
      intro b
      have h := ggLAut_mem_of_induces (L := J) (θ := θJ) hN hact b.2
      have h2 : ggInducedAut θJ (ggGamma J hN b) = ggLAut J θJ ⟨b, hN b.2⟩ := by
        rw [ggLAut_eq_ggInducedAut, ggGamma]
        congr 1
      rw [h2]
      exact h
    set X : Subgroup (MulAut (projectiveSL (d' + 1) F)) :=
      E.map (MulAut.congr (TypeA.recipeEquiv (d' + 1) F)).toMonoidHom with hXdef
    have hXelem : IsElemAbelian p X := by
      rw [hXdef]
      exact hE.map (MulAut.congr (TypeA.recipeEquiv (d' + 1) F)).toMonoidHom
    have hXsub : (X : Set (MulAut (projectiveSL (d' + 1) F))) ⊆
        Set.range (conjAut (d' + 1) F) := by
      rintro _ ⟨ψ, hψE, rfl⟩
      obtain ⟨y, hy, rfl⟩ := hψE
      obtain ⟨b, rfl⟩ := hy
      exact TypeA.congr_recipeEquiv_mem (hIE b)
    have hcardX : Nat.card X = Nat.card E := by
      rw [hXdef]
      exact Subgroup.card_map_of_injective
        (MulAut.congr (TypeA.recipeEquiv (d' + 1) F)).injective
    have hbound := TypeA.card_le_of_subset_conjAut_gen hp hp2 hpF (show 0 < d' + 1 by omega)
      hXelem hXsub
    have hcardGamma : Nat.card (ggGamma J hN).range ≤ p ^ d' := by
      rw [hcardX, hcardE] at hbound
      simpa using hbound
    have hle : LargeEvenTwoLocalRank p G - 2 ≤ d' :=
      (Nat.pow_le_pow_iff_right hp.one_lt).mp
        ((hcfg.pow_le_card_gamma_J hN).trans hcardGamma)
    omega

end CFSG.StandardType
