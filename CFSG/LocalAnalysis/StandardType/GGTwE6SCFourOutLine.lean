module

public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourOutTransport
public import CFSG.LocalAnalysis.StandardType.GGTwE6K1LeviDefs
public import Certificates.Certificate13659
public import Certificates.Certificate13660
import CFSG.Assembly.Subnormal
import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourOutAd
import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourOutD4
import CFSG.LocalAnalysis.StandardType.GGMarkingAllInduces
import CFSG.LocalAnalysis.StandardType.GGOutsideInndiagCriteria
import CFSG.LocalAnalysis.StandardType.GGInndiagThreeRankTwoLabels
import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigIso
import CFSG.LocalAnalysis.StandardType.GGAssemblyFiveDefs
import CFSG.LocalAnalysis.StandardType.GGExclNoIso
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag
import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitMarking
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownLemmas
import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeHypSix
import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCover
import CFSG.LocalAnalysis.StandardType.GGTwE6K1LeviMain

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.NoOffTwE6Three


theorem ggTwE6SCFourOutLine_of (hS : E6LeviThreeToralBar) : GGTwE6SCFourOutLine := by
  intro n hn h3 K _ _ σ hK hσ h hh1 hh3 E hE hcard hfE hEI hnt J hJ hEJ hCJ hmark
  have hraw : GGRawInnFieldInput := ggRawInnFieldInput_holds
  have hiso : GGRawInndiagIsoInput :=
    ggRawInndiagIsoInput_of_rest (ggRawInndiagIsoRestInput_of_round5 ggRawInndiagIsoRound5_holds)
  have hJp : ⁅J, J⁆ = J := commutator_eq_self_of_isComponentOf (isComponentOf_iff_open.2 hJ)
  have hnorm : ∀ e ∈ E, ∀ l ∈ J, e l ∈ J := fun e he l hl => by
    rw [← hEJ e he]
    exact Subgroup.mem_map_of_mem _ hl
  rcases largeEvenMarking_label_or hmark with hD | hR
  · obtain ⟨e, he, hni⟩ := exists_not_inner_of_d4 hS hn h3 hK hσ hh1 hh3 hE hcard hfE hEI hnt hJ
      hEJ hCJ hD
    refine ⟨e, he, hnorm e he, ggMarkingAll_not_induces hraw hiso ?_⟩
    refine largeEvenMarking_mono (fun _ _ _ _ _ θ hI => not_induces_of_not_inner hJp (hEJ e he)
      hni hI.2 θ) (largeEvenMarking_and_labelAll_simple (S := fun lab => lab = ⟨.D, 4, n⟩)
        (P' := fun R _ I _ => I ⊆ LargeEvenInnSet R) (fun lab hlab hl => ?_)
        (fun _ _ _ _ _ _ hl => hl) hD)
    subst hl
    exact largeEvenLabelAll_subset_inn hlab
      (Or.inl (Or.inr (Or.inr (Or.inl ⟨rfl, (by decide : (4 : ℕ) ≠ 3)⟩))))
  · by_contra hno
    have hind : ∀ e ∈ (E : Set (MulAut (twistedE6RootGroup K σ))),
        LargeEvenMarking ↥J fun _ _ _ I _ θ => ∃ φ ∈ Subgroup.closure I,
          LargeEvenInduces θ (fun l l' : ↥J => (l' : twistedE6RootGroup K σ) = e l) φ := by
      intro e he
      rcases largeEvenMarking_or (largeEvenMarking_mono (P' := fun _ _ _ I _ θ =>
          (∃ φ ∈ Subgroup.closure I,
            LargeEvenInduces θ (fun l l' : ↥J => (l' : twistedE6RootGroup K σ) = e l) φ) ∨
          ¬ ∃ φ ∈ Subgroup.closure I,
            LargeEvenInduces θ (fun l l' : ↥J => (l' : twistedE6RootGroup K σ) = e l) φ)
          (fun _ _ _ _ _ _ _ => em _) hR) with hi | hni
      · exact hi
      · exact (hno ⟨e, he, hnorm e he, ggMarkingAll_not_induces hraw hiso hni⟩).elim
    have h3' : 3 ∣ 2 ^ (3 * n) + 1 := by
      have h33 := Odd.nat_add_dvd_pow_add_pow (2 ^ n) 1 (⟨1, rfl⟩ : Odd 3)
      rw [one_pow, ← pow_mul, mul_comm n 3] at h33
      exact h3.trans h33
    have hb := largeEvenMarking_and_labelAll_simple (P' := GGInndiagThreeRankTwo)
      (S := fun lab => lab = ⟨.triD4, 0, n⟩ ∨ lab = ⟨.A, 2, 3 * n⟩ ∨ lab = ⟨.twA, 2, 3 * n⟩)
      (fun lab hlab hl => by
        rcases hl with rfl | rfl | rfl
        · exact largeEvenLabelAll_threeRankTwo_triD4 hlab rfl
        · exact largeEvenLabelAll_threeRankTwo_A2 rfl rfl h3'
        · exact largeEvenLabelAll_threeRankTwo_twA2 hlab rfl rfl)
      (fun _ _ _ _ _ _ hl => hl) hR
    obtain ⟨-, lab, -, hr⟩ := ggMarkingAll_induces hraw hiso
      (fun (e : MulAut (twistedE6RootGroup K σ)) (l l' : ↥J) =>
        (l' : twistedE6RootGroup K σ) = e l) _ hind _ hb
    obtain ⟨R, _, I, F, -, -, θ, ⟨-, hB⟩, hall⟩ := largeEvenRawDatum_exists hr
    exact not_forall_induces_of_threeRankTwo hJp hE hcard hfE hEJ hCJ hB θ hall

theorem ggTwE6SCFourOutKnown_of_inputs (hS : E6LeviThreeToralBar) : GGTwE6SCFourOutKnown :=
  ggTwE6SCFourOutKnown_of_ad (ggTwE6SCFourOutAd_of_line (ggTwE6SCFourOutLine_of hS))

theorem ggTwE6SCFourOutKnown_holds : GGTwE6SCFourOutKnown :=
  ggTwE6SCFourOutKnown_of_inputs e6LeviThreeToralBar

end CFSG.StandardType.SCFourCover

end
