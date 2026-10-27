module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitSolvableOmega
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf20OmegaA
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecQuot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

theorem sylow_le_twoCore_preimage_of_hypOmegaGen
    {X : Type} [Group X] [Finite X] {Ω : Set (Subgroup X)} (hΩ : HypOmegaGen Ω)
    (H : Subgroup X) (hHsolv : Group.IsSolvable H) (hH3 : ¬ 3 ∣ Nat.card H)
    {J P : Subgroup X} (hJ : J ∈ Ω) (hP : IsSylow2In P J) (hPH : P ≤ H) :
    P ≤ ((CFSG.pCore 2 (H ⧸ classicalInvolutionOddCore H)).comap
      (QuotientGroup.mk' (classicalInvolutionOddCore H))).map H.subtype := by
  let : Group.IsSolvable H := hHsolv
  let π : H →* H ⧸ classicalInvolutionOddCore H :=
    QuotientGroup.mk' (classicalInvolutionOddCore H)
  let L : Subgroup X := tightCore (J ⊓ H)
  have hLH : L ≤ H := (tightCore_le _).trans inf_le_right
  have hPL : P ≤ L := le_tightCore_of_isPGroup (le_inf hP.1 hPH) hP.2.1
  have hLfam : L.subgroupOf H ∈ omegaAFam Ω H :=
    ⟨L, ⟨J, hJ, ⟨P, hP, hPH⟩, rfl⟩, hLH, rfl⟩
  have hquot : HypOmegaGen (quotFamily (omegaAFam Ω H) (classicalInvolutionOddCore H)) :=
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge.hypOmegaGen_quotFamily_odd
      (hypOmegaGen_omegaAFam hΩ H)
      (CFSG.ClassicalInvolution.QuaternionStructure.odd_natCard_oddCore H)
  have himage : (L.subgroupOf H).map π ≤ CFSG.pCore 2 (H ⧸ classicalInvolutionOddCore H) :=
    le_pCore_two_of_hypOmegaGen_solvable_threePrime hquot
      (CFSG.ClassicalInvolution.QuaternionStructure.oddCore_quotient_oddCore_eq_bot H)
      (fun h3 => hH3 (h3.trans (Subgroup.card_quotient_dvd_card
        (classicalInvolutionOddCore H)))) ⟨L.subgroupOf H, hLfam, rfl⟩
  intro x hx
  refine ⟨⟨x, hPH hx⟩, ?_, rfl⟩
  exact himage (Subgroup.mem_map_of_mem π (hPL hx))

end CFSG.LocalAnalysis.UniquenessCase.UC22
