module

public import CFSG.LocalAnalysis.WeakClosure81.W183TwoDefs
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoFac
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoKS
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoGr
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoSv
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoShape
public import CFSG.LocalAnalysis.WeakClosure81.W183Psp
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Dynkin
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5PSp4B
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.UniquenessCase.UC22ListB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

variable {G : Type} [Group G] [Finite G]

section Main


theorem tail1812Two_AS_of_CF
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hComp : OddTranspositionCompFactorInput) (hList : OddTranspListBundle)
    (hIn : OrthReflParabolic) (hCF : Tail1812TwoNoSectionCF) (hGraph : FinGraphOdd)
    (h56 : Tail1812TwoL24U34 G) : Tail1812Two_AS G := by
  intro h162 h172 h5_4 h5_11 h5_12 h5_13 D V₀ V H i c hc g hgT hgK hgi hA
  have cx : Tail1812TwoCtx G D V₀ V H i g :=
    ⟨h162, h172, h5_4, h5_11, h5_12, h5_13, c, hc, hgT, hgK, hgi, hA⟩
  have hB : ListBNonabelian := listBNonabelian
  have hO : LieOrderFormulasInput :=
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  have hM : OddMultiplier186Triv := oddMultiplier186Triv_of_griess hGA
  have hDyn : Asch5_4Dynkin := asch5_4Dynkin_of_asch5_4 h5_4
  obtain ⟨hOK, L, hL, hLT, hShape⟩ := c.exists_component182_ker_AS h172 h5_4 h5_11 h5_13 hc
  have hfac := tail1812Two_hfac hB hComp cx hL
  have key := shape54_to_seven hO hCF hShape
    (fun X _ hφ hs hnc => hfac X (by rwa [hOK] at hφ) hs hnc)
  rw [hOK] at key
  rcases key with h1 | h2 | ⟨h3, t, htT, hDy⟩ | h4 | h5 | h6
  · obtain ⟨X, hXg, φ, hφs, hφk, hX⟩ := h1
    letI := hXg
    obtain ⟨-, hs, hnc⟩ := isSimple_nonab_of_shape hO (X := X) (by tauto)
    have hK1 := tail1812Two_kstar hB cx hM hL hnc (shape186OddTriv_of_shapes (Or.inl hX)) φ hφs hφk
    exact h56 h162 h172 h5_4 h5_11 h5_12 h5_13 c hc hK1
      ⟨L, hL, hLT, ⟨X, hXg, φ, hφs, hφk, hX⟩⟩ hgT hgK hgi hA
  · obtain ⟨X, hXg, φ, hφs, hφk, hX⟩ := h2
    letI := hXg
    obtain ⟨hf, hs, hnc⟩ := isSimple_nonab_of_shape hO (X := X) (by tauto)
    obtain ⟨t, htT, hDy⟩ := c.exists_dynkin_182 hDyn hc (hOK ▸ hL) hLT
      ⟨X, hXg, φ, hφs, by rwa [hOK], Or.inl hX⟩
    exact tail1812Two_false_graph hB hGraph cx hL hnc φ hφs hφk (Or.inl hX) htT
      (by rwa [hOK] at hDy)
  · obtain ⟨X, hXg, φ, hφs, hφk, hX⟩ := h3
    letI := hXg
    obtain ⟨hf, hs, hnc⟩ := isSimple_nonab_of_shape hO (X := X) (by tauto)
    exact tail1812Two_false_graph hB hGraph cx hL hnc φ hφs hφk (Or.inr hX) htT hDy
  · obtain ⟨X, hXg, φ, hφs, hφk, hX⟩ := h4
    letI := hXg
    obtain ⟨hf, hs, hnc⟩ := isSimple_nonab_of_shape hO (X := X)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨5, 2, Nat.prime_five,
        by norm_num, by norm_num, hX⟩)))))))
    have hK1 := tail1812Two_kstar hB cx hM hL hnc
      (shape186OddTriv_of_shapes (Or.inr (Or.inr (Or.inl hX)))) φ hφs hφk
    exact tail1812Two_false_seven hB hO hList hIn cx hK1 hL hnc φ hφs hφk (Or.inl hX)
  · obtain ⟨X, hXg, φ, hφs, hφk, hX⟩ := h5
    letI := hXg
    obtain ⟨hf, hs, hnc⟩ := isSimple_nonab_of_shape hO (X := X)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨5, Nat.prime_five,
        by norm_num, Or.inr (Or.inr hX)⟩)))))))
    have hK1 := tail1812Two_kstar hB cx hM hL hnc
      (shape186OddTriv_of_shapes (Or.inr (Or.inr (Or.inr hX)))) φ hφs hφk
    exact tail1812Two_false_seven hB hO hList hIn cx hK1 hL hnc φ hφs hφk (Or.inr hX)
  · exact c.false_of_psp4_three asch5_PSp4Three_holds h5_11 h5_13 hOK hL hLT h6

end Main

end CFSG.LocalAnalysis.WeakClosure81

end
