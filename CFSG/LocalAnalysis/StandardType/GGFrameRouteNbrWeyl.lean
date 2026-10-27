module

public import CFSG.LocalAnalysis.StandardType.GGTBFix
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQSplit
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerCore
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeAFrame
public import CFSG.LocalAnalysis.StandardType.GGNbrLangRestRank
public import CFSG.LocalAnalysis.StandardType.GGNbrLangRest
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly

theorem exists_automizer_moves_x_of_innerWeyl {G : Type} [Group G] [Finite G]
    (hW : GGNbrInnerWeylInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hI : GGInnerDiagAll p B Bs x L D J) {y : G} {K : Subgroup G} (hN : GGNbr p B x D J y K)
    (hx : x ∈ Bs) : ∃ φ ∈ ggAutomizer K Bs, φ ⟨x, hx⟩ ≠ ⟨x, hx⟩ := by
  have hK := hI.2 y K hN
  obtain ⟨-, -, R, _, I, -, θ, -, hBsN, -⟩ := largeEvenMarking_exists' hK
  have hxK : x ∈ Subgroup.normalizer (K : Set G) := hBsN hx
  have hM := ggNbrInnerXNotNormalInput_of_weyl hW G p B Bs x L D J hcfg y K hN hBsN hxK _ hK
  obtain ⟨-, -, R, _, I, -, θ, -, ⟨hBsN', hBs3⟩, hQ⟩ := largeEvenMarking_exists' hM
  obtain ⟨k, hkK, hkN, hkx⟩ := hQ (ggLAut_mem_of_induces K θ hBsN' hBs3 hx)
  refine ⟨Bs.normalizerMonoidHom ⟨k, hkN⟩, Subgroup.subset_closure ⟨k, hkK, hkN, fun _ => rfl⟩,
    fun h => hkx ?_⟩
  have hkx' : k * x * k⁻¹ = x := congrArg Subtype.val h
  have hc : Commute k x := by
    show k * x = x * k
    calc k * x = k * x * k⁻¹ * k := by group
      _ = x * k := by rw [hkx']
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun g hg => ?_)
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  exact ((hc.zpow_right i).eq).symm

theorem ggNbrInnerWeylInput_of_rest (hI3 : GGNbrSubcomponentInput)
    (hweyl : GGNbrInnerWeylOn GGNbrWeylRestLabel) : GGNbrInnerWeylInput := by
  refine ggNbrInnerWeylInput_of_on (ggNbrInnerWeylOn_true_of
    (ggNbrInnerWeylOn_typeASplit_of_subcomponent hI3) ?_)
  refine (hweyl.or ggNbrInnerWeylOn_linearTwo).mono ?_
  intro p lab hS
  by_cases h : GGLinearTwoLabel lab
  · exact Or.inr h
  · exact Or.inl ⟨hS, h⟩

theorem exists_automizer_moves_x_of_rest {G : Type} [Group G] [Finite G]
    (hI3 : GGNbrSubcomponentInput)
    (hweyl : GGNbrInnerWeylOn GGNbrWeylRestLabel) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hR : GGSecFiveRestHyp 3 B Bs x L D J) {y : G} {K : Subgroup G}
    (hN : GGNbr 3 B x D J y K) (hx : x ∈ Bs) :
    ∃ φ ∈ ggAutomizer K Bs, φ ⟨x, hx⟩ ≠ ⟨x, hx⟩ :=
  exists_automizer_moves_x_of_innerWeyl (ggNbrInnerWeylInput_of_rest hI3 hweyl) hR.1 hR.2.2.1 hN hx

theorem ggNbrInnerWeylInput_of_reduction (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hinW : GGNbrInnerWeylOn GGNbrWeylRestLabel) : GGNbrInnerWeylInput :=
  ggNbrInnerWeylInput_of_rest (ggNbrSubcomponentInput_of_lBalance hLB hP) hinW

end CFSG.StandardType.FrameRoute

end
