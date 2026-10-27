module

public import CFSG.LocalAnalysis.StandardType.FS81.E7CentModelBasic
public import CFSG.LieType.Steinberg.Collection

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction CFSG.SeitzReduction.EPilot CFSG.SeitzReduction.E7Pilot
open CFSG.QuasithinUnique CFSG.HardMathSupport.C14Idx CFSG.RankThree.Chevalley
open scoped commutatorElement


private abbrev e7CentPAlpha : Fin (Tag.rank .E7) → ℤ := Pi.single 2 1
private abbrev e7CentPBeta : Fin (Tag.rank .E7) → ℤ := Pi.single 3 1

private theorem e7CentP_hsum  :
    IsRoot .E7 (e7CentPAlpha + e7CentPBeta) :=
  RootOps.isRootB_iff.1 (by decide +kernel : RootOps.isRootB .E7
    (e7CentPAlpha + e7CentPBeta) = true)

private noncomputable def e7CentPB1  :
    ↥(adjointGroup .E7 (ZMod 2)) :=
  e7CentBstar (e7CentPAlpha + e7CentPBeta) e7CentP_hsum

private theorem e7CentP_roots_mem_overlap  :
    ∀ i j : Fin 3, i ≠ j →
      a2PairRoot e7CentPAlpha e7CentPBeta i j ∈ overlapRootsD4 .high .seven := by
  have hcheck : ∀ i j : Fin 3, i ≠ j →
      RootOps.isRootB .E7 (a2PairRoot e7CentPAlpha e7CentPBeta i j) = true ∧
      iform E7Neighbour.high.root (a2PairRoot e7CentPAlpha e7CentPBeta i j) = 0 ∧
      iform E7Neighbour.seven.root (a2PairRoot e7CentPAlpha e7CentPBeta i j) = 0 ∧
      iform (E7Neighbour.high.thirdRoot E7Neighbour.seven)
        (a2PairRoot e7CentPAlpha e7CentPBeta i j) = 0 := by
    decide +kernel
  intro i j hij
  obtain ⟨h1, h2, h3, h4⟩ := hcheck i j hij
  exact ⟨⟨⟨RootOps.isRootB_iff.1 h1, h2⟩, ⟨RootOps.isRootB_iff.1 h1, h3⟩⟩,
    ⟨RootOps.isRootB_iff.1 h1, h4⟩⟩

private theorem e7CentP_L3  :
    ∃ P : Subgroup ↥(adjointGroup .E7 (ZMod 2)), P ≤ e7D4 ∧
      Nonempty (↥P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧ e7CentPB1 ∈ P := by
  have hOdd : OddDerivPair .E7 e7CentPAlpha e7CentPBeta :=
    (oddDerivPairB_iff (τ := .E7) (a := e7CentPAlpha) (b := e7CentPBeta)).1
      (by decide +kernel)
  obtain ⟨P, hPle, hPJ, hPiso⟩ := exists_sl3_of_oddDerivPair hOdd
    (overlapRootsD4 .high .seven) e7CentP_roots_mem_overlap
  have hPAG : P ≤ adjointGroup .E7 (ZMod 2) :=
    hPle.trans (iSup₂_le fun γ _ => rootSubgroup_le_adjointGroup γ)
  let P' : Subgroup ↥(adjointGroup .E7 (ZMod 2)) :=
    P.subgroupOf (adjointGroup .E7 (ZMod 2))
  have hP'le : P' ≤ e7D4 := Subgroup.subgroupOf_mono _ hPle
  have hiso : Nonempty (↥P' ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hPAG).trans hPiso.some⟩
  have hb₁ : e7CentPB1 ∈ P' := by
    refine Subgroup.mem_subgroupOf.2 ?_
    have hmemP : (e7CentPB1 : ModGL .E7 (ZMod 2)) ∈ P := by
      rw [show (e7CentPB1 : ModGL .E7 (ZMod 2)) = rootSL2 .E7 (ZMod 2)
          (e7CentPAlpha + e7CentPBeta) (uSL 1 * vSL 1) from rfl]
      have hrange : rootSL2 .E7 (ZMod 2) (e7CentPAlpha + e7CentPBeta) (uSL 1 * vSL 1) ∈
          (rootSL2 .E7 (ZMod 2) (e7CentPAlpha + e7CentPBeta)).range :=
        ⟨uSL 1 * vSL 1, rfl⟩
      rw [range_rootSL2_of_isRoot e7CentP_hsum] at hrange
      exact hPJ hrange
    exact hmemP
  exact ⟨P', hP'le, hiso, hb₁⟩

private theorem e7CentP_conj  :
    ∃ g : ↥(adjointGroup .E7 (ZMod 2)), g * e7CentB * g⁻¹ = e7CentPB1 := by
  have hα : IsRoot .E7 e7Alpha7 :=
    isRoot_single .E7 (⟨6, by decide⟩ : Fin (Tag.rank .E7))
  obtain ⟨n₁, hn₁, hmap₁⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.E7Model.exists_conj_rankOne_to_theta
      (F := ZMod 2) (β := e7Alpha7) hα
  obtain ⟨n₂, hn₂, hmap₂⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.E7Model.exists_conj_rankOne_to_theta
      (F := ZMod 2) (β := e7CentPAlpha + e7CentPBeta) e7CentP_hsum
  have htheta : CFSG.ClassicalInvolution.ModelFacts.Levi.thetaE7 = highRoot .E7 := by
    rw [CFSG.ClassicalInvolution.ModelFacts.E7Model.thetaE7_eq]
    rfl
  have hmap₁' : (rootRankOneGroup .E7 (ZMod 2) e7Alpha7).map
      (MulAut.conj n₁).toMonoidHom = rootRankOneGroup .E7 (ZMod 2) (highRoot .E7) := by
    rw [← htheta, ← hmap₁]
  have hmap₂' : (rootRankOneGroup .E7 (ZMod 2) (e7CentPAlpha + e7CentPBeta)).map
      (MulAut.conj n₂).toMonoidHom = rootRankOneGroup .E7 (ZMod 2) (highRoot .E7) := by
    rw [← htheta, ← hmap₂]
  have hmap : (rootRankOneGroup .E7 (ZMod 2) e7Alpha7).map
      (MulAut.conj (n₂⁻¹ * n₁)).toMonoidHom =
        rootRankOneGroup .E7 (ZMod 2) (e7CentPAlpha + e7CentPBeta) := by
    rw [CFSG.LieType.Steinberg.map_conj_mul, hmap₁',
      CFSG.LieType.Steinberg.map_conj_inv_of_map_conj hmap₂']
  obtain ⟨g, hg, hconj⟩ := e7CentRootSL2_conj (a := e7Alpha7)
    (b := e7CentPAlpha + e7CentPBeta) (n := n₂⁻¹ * n₁) hα e7CentP_hsum
    (mul_mem (inv_mem hn₂) hn₁) hmap
  refine ⟨⟨g, hg⟩, ?_⟩
  rw [e7CentB_eq_bstar hα]
  apply Subtype.ext
  exact hconj

theorem e7CentModelP_holds :
    E7CentModelP := by
  obtain ⟨P, hPle, hiso, hb⟩ := e7CentP_L3
  obtain ⟨g, hg⟩ := e7CentP_conj
  exact ⟨P, hPle, hiso, e7CentPB1, hb, g, hg⟩

end CFSG.StandardType.FrameRoute.FS81
