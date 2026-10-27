module

public import CFSG.Yardstones.Mf4cdcdf2e013.Definitions
public import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 Theorem614At SigmaOne4)

variable {G : Type} [Group G]

theorem gamma_le_of_gammaQ_of_le [Finite G] {M Q E : Subgroup G}
    (hE : E ≤ Q) (hΓQ : CFSG.Open.rankThreeGamma 1 3 Q ≤ M) :
    CFSG.Open.rankThreeGamma 1 3 E ≤ M := by
  have h := CFSG.HardMathSupport.Solomon.Proving.GLBCore_mono (p := 3) (k := 1) hE
  simpa [CFSG.Open.rankThreeGamma] using h.trans hΓQ

theorem e9_le_center_sylow_of_omega {P Q E : Subgroup G} (hQP : Q ≤ P)
    (hOmega : CFSG.RankThree.PartOne.omegaOne 3 Q ≤
      (Subgroup.center ↥P).map P.subtype)
    (hE : E ≤ CFSG.RankThree.PartOne.omegaOne 3 Q) :
    E ≤ P ⊓ Subgroup.centralizer (P : Set G) := by
  have hωQ : CFSG.RankThree.PartOne.omegaOne 3 Q ≤ Q :=
    (Subgroup.closure_le Q).2 fun _ hx => hx.1
  refine le_inf ?_ ?_
  · exact hE.trans (hωQ.trans hQP)
  · intro e he
    obtain ⟨z, hz, hze⟩ := Subgroup.mem_map.mp (hOmega (hE he))
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hpz : p * (z : G) = (z : G) * p :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨p, hp⟩)
    have hze' : (z : G) = e := by simpa only [Subgroup.coe_subtype] using hze
    rw [hze'] at hpz
    exact hpz

theorem stronglyPEmbedded_of_e9_le_center_sylow [Finite G]
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (h614 : Theorem614At S.M)
    (hsub : CFSG.Open.uniqueFourSigma S.M ⊆ SigmaOne4 G)
    (h3 : 3 ∉ CFSG.Open.uniqueFourSigma S.M)
    {P E : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P S.M)
    (hE : E ≤ P ⊓ Subgroup.centralizer (P : Set G))
    (hEel : CFSG.Open.IsElemAbelian 3 E) (hEcard : Nat.card E = 9)
    (hΓ : CFSG.Open.rankThreeGamma 1 3 E ≤ S.M) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M :=
  h614 hsub 3 Nat.prime_three (by decide) h3 P hP E hE hEel
    (by rw [hEcard]; norm_num) hΓ

theorem omega_center_of_sylow_eq {P Q : Subgroup G} (hPQ : P = Q)
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) :
    CFSG.RankThree.PartOne.omegaOne 3 Q ≤ (Subgroup.center ↥P).map P.subtype := by
  intro x hx
  have hωQ : CFSG.RankThree.PartOne.omegaOne 3 Q ≤ Q :=
    (Subgroup.closure_le Q).2 fun _ hx => hx.1
  have hxQ : x ∈ Q := hωQ hx
  have hxP : x ∈ P := hPQ.symm ▸ hxQ
  refine Subgroup.mem_map.mpr ⟨⟨x, hxP⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact (hQab x hxQ y (hPQ ▸ y.2)).symm

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
