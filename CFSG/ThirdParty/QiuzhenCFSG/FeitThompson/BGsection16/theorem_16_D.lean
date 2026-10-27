module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection16.theorem_16_C
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_1
import Mathlib.GroupTheory.Schreier
import Mathlib.Order.Preorder.Finite

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Theorem 16 d from BG Section 16 -/

section MainResults

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
/-- Theorem D of Section 16. -/
public theorem CFSG.theorem_16_D
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U) :
    section16TheoremDConclusions M MF K U := by
  classical
  have hMF15 : section15MFSubgroup M MF :=
    section16_mf_to_section15 (G := G) hMF
  refine ⟨section16_fusion_in_msigma (G := G) hM hMF15, ?_, ?_⟩
  · intro g hg
    exact ⟨section16_msigma_inf_conjBy_eq (G := G) hM g,
      section16_msigma_inf_conjBy_cyclic (G := G) hM g hg⟩
  · intro x hx hxne
    refine ⟨section14R x, section16_theoremDComplement (G := G) hM hx hxne, ?_⟩
    intro hCGnot
    have hMx : M ∈ section14MsigmaElement x := by
      exact ⟨hM, by simpa [section14MsigmaElement, section14MsigmaFamily,
        Set.singleton_subset_iff] using hx⟩
    have hσ : (section14MsigmaElement x).Nonempty := ⟨M, hMx⟩
    have h14 := theorem_14_4 (G := G) (x := x) hxne hσ
    have hcard :
        1 < Nat.card {L : Subgroup G // L ∈ section14MsigmaElement x} :=
      section16_msigmaElement_card_gt_one_of_not_centralizer_le (G := G) hM hx hCGnot
    rcases h14.2.2 hcard with ⟨N, hNcont, hNdata, hNuniq⟩
    have hDataM := hNdata M hMx
    rcases hDataM with
      ⟨hReq, _hRne, _hprod, _hsupp, _htau, _hbeta, hcompN, hNF_or_P2⟩
    refine ⟨N, ?_, hReq, ?_, ?_, hcompN, ?_⟩
    · ext L
      constructor
      · intro hL
        have hLN : L = N := hNuniq L hL
        simp [hLN]
      · intro hL
        have hLN : L = N := by simpa using hL
        simpa [hLN] using hNcont
    · exact section16_theoremD_auxiliary_data (G := G)
        (M := M) (N := N) (x := x) hxne hNcont hReq _hRne _hsupp hNF_or_P2
    · simpa [section16MaximalTypeF, section16MaximalTypeP2] using hNF_or_P2
    · intro hNP2
      have hNP2' : N ∈ section14MFamilyP2 G := by
        simpa [section16MaximalTypeP2] using hNP2
      have hNnotF : N ∉ section14MFamilyF G := by
        intro hNF
        rcases hNP2'.1.2 with ⟨p, hpκ⟩
        simp [hNF.2] at hpκ
      rcases section16_exists_prime_order_zpower (G := G) hxne with
        ⟨r, xr, hr, hxrmem, hxrorder⟩
      rcases corollary_15_9 (G := G) (M := M) (N := N) (x := x)
          (xᵣ := xr) (r := r) hM hx hxne hNcont hCGnot hNnotF
          hr hxrmem hxrorder with
        ⟨E, hE⟩
      rcases hE with
        ⟨hEcomp, hMFam, _hNP2, hEcyc, _hFrob, _hrTau, _hNorm, _hCard⟩
      have hMF15 : section15MFSubgroup M MF :=
        section16_mf_to_section15 (G := G) hMF
      have hKU15 : section15KUData M K U :=
        section16_kudata_to_section15 (G := G) hKU
      have hMF_eq : MF = section10Msigma M :=
        section16_MF_eq_msigma_of_typeF (G := G) hM hMF15 hKU15.1 hMFam
      refine ⟨?_, ?_, ?_⟩
      · simpa [section16MaximalTypeF] using hMFam
      · exact
          section16_frobeniusWithCyclicComplement_of_typeF_cyclic_msigma_complement
            (G := G) hM hMF15 hKU15.1 hMFam hEcomp hEcyc
      · exact
          section16_not_TISubset_MF_of_not_centralizer_le
            (G := G) hM hMF_eq hx hxne hCGnot

end MainResults
