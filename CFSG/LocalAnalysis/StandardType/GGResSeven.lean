module

public import CFSG.LocalAnalysis.StandardType.GGResLeaves
public import CFSG.LocalAnalysis.StandardType.GGResSevenNbr
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs
public import CFSG.LocalAnalysis.StandardType.GGKG3Assembly
public import CFSG.LocalAnalysis.StandardType.GGForkA8NotReflHolds
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResSevenInput_of (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) : GGResSevenInput := by
  unfold GGResSevenInput GGResLeaf
  intro G _ _ p B Bs x L D J y K hH _ hFork hStd hE6 hP
  exfalso
  rcases hP with hL | hK
  · obtain ⟨labJ, labX, hΛJ, hΛX, hLabJ, hLabX, hrow⟩ := hL
    obtain ⟨hp7, h5⟩ := hrow
    obtain ⟨hcfg, -, -, -, hnb, -, -⟩ := hH
    exact ggSeven_L_absurd hTCJ hRig hcfg hp7 hnb hΛX hLabX h5
  · obtain ⟨labJ, labX, hΛJ, hΛX, hLabJ, hLabX, hrow⟩ := hK
    obtain ⟨hp7, h5⟩ := hrow
    exact ggSeven_K_absurd hTCJ hRig hTPn hA8 hraw hiso hH hp7 hΛX hLabX h5

section ActualSeven

theorem ggSeven_e6Nbr_noReflection
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hC : GGConfig 7 B Bs x L D J)
    (hI : GGInnerDiagAll 7 B Bs x L D J) (hN : GGNbr 7 B x D J y K)
    (hK : GGHasLabel ⟨.E6, 0, 1⟩ (K ⧸ Subgroup.center K)) :
    ∀ φ ∈ ggAutomizer K Bs, ¬ GGIsReflection 7 φ := by
  have hM : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.E6, 0, 1⟩) 7 Bs K :=
    ggInnerDiagOn_relabel ggLabelRigidInput_holds (hI.2 y K hN) largeEvenInLambda2_e6 hK
  obtain ⟨hperf, lab, hΛ, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => lab = ⟨.E6, 0, 1⟩)
    (fun lab _ heq => by rw [heq]; exact GGKG3.kg3)
    (fun _ _ _ _ _ _ h => h.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, hBsI⟩, r, hlift, hT⟩ :=
    largeEvenRawDatum_exists hraw
  have hnoref := ggNoRefl_of_marking (by norm_num : Nat.Prime 7) (by norm_num : 7 ≠ 2)
    hC.2.1.2.1 hC.2.1.2.2.2 hperf θ hBsN
    (fun b hb => ggLAut_mem_of_induces K θ hBsN hBsI hb)
    (pow_le_card_range_ggGamma_bstar_of_torusLift hC hN hperf θ hBsN hlift)
    (pow_three_le_card_range_ggGamma_bstar hC hN hBsN) hT
  intro φ hφ
  exact hnoref φ (mem_ggAutomizer_iff.mp hφ)

theorem ggSeven_K_absurd_of_leviLE3
    {G : Type} [Group G] [Finite G] [Fact (Nat.Prime 7)]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {sel : Prop → Prop → Prop}
    {typ : ∀ {Λ Λ' : Type}, CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop}
    (hH : GGResHyp 7 B Bs x L D J y K)
    (hK : GGHasLabel ⟨.A, 8, 1⟩ (K ⧸ Subgroup.center K) ∨
      GGHasLabel ⟨.E6, 0, 1⟩ (K ⧸ Subgroup.center K))
    (hD : GGResLeviDatumLE3 7 Bs L J K sel typ ∨
      GGResLeviDatumLE3 7 Bs K J L sel typ) : False := by
  rcases hK with hA | hE
  · exact ggForkNbrSevenExcl'_of_notRefl
      (ggForkA8NotReflInput_of_mp ggInnerDiagMpInput_holds)
      G B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K hH.2.2.2.2.1
      hH.2.2.2.2.2.1 hA
  · have hnoref := ggSeven_e6Nbr_noReflection hH.1 hH.2.2.1 hH.2.2.2.2.1 hE
    rcases hD with hD | hD
    · obtain ⟨Λ, _, _, S, Λa, _, _, ML, CL, MK, CK, V, _, _, ι, φ, h, α,
        -, -, ha, -, -, -, -, -, -, -, hφ, -, -, -, -, ⟨fK, hfK⟩, -⟩ := hD
      have hpos : 0 < Fintype.card Λa := by
        simpa only [Nat.card_eq_fintype_card] using (lt_of_lt_of_le Nat.zero_lt_one ha)
      obtain ⟨a⟩ := Fintype.card_pos_iff.mp hpos
      have hmem : φ (Sum.inr a) ∈ ggAutomizer K Bs := by
        have := (fK (MK.simple (Sum.inr a))).property
        simpa [hfK] using this
      exact hnoref _ hmem (hφ (Sum.inr a))
    · obtain ⟨Λ, _, _, S, Λa, _, _, MK, CK, ML, CL, V, _, _, ι, φ, h, α,
        hs, -, -, -, -, -, -, -, -, -, hφ, -, -, -, ⟨fK, hfK⟩, -⟩ := hD
      obtain ⟨b, _⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0 < 2) hs)
      have hmem : φ (Sum.inl b) ∈ ggAutomizer K Bs := by
        have := (fK (MK.simple b)).property
        simpa only [hfK] using this
      exact hnoref _ hmem (hφ (Sum.inl b))

end ActualSeven

end CFSG.StandardType

end
