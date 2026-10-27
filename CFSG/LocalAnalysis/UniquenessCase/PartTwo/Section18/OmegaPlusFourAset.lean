module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSeventeen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def K_Omega4Plus_aParam_le : Prop :=
  ∀ {W : Type} [CommGroup W] [Finite W] (X : Subgroup (MulAut W)) (n : ℕ),
    2 ≤ n → IsOmegaPlus ↥X 4 n → NatOmegaPlus X ⊤ ⊥ 4 n →
      E3.aParam (Subgroup.normalizer (X : Set (MulAut W))) ≤ n

section Certified


theorem gap_18_19_aBar (hK : K_Omega4Plus_aParam_le)
    {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G} (h : Hyp18 D V₀ V p L)
    (h1742 : S17.R17_42At D V₀ V) :
    Gap_18_19_aBar D V₀ V p L h := by
  intro h3
  obtain ⟨f, hO, hN⟩ := h3
  obtain ⟨-, hnof, h2f, -⟩ := isOmegaPlus_barSub_cong h h1742 hO
  have hXM : UC22.conjClosure D.M L ≤ D.M := TwelveTwentyThree.conjClosure_le h.hL.1.1.le
  have hMN : D.M ≤ Subgroup.normalizer (UC22.conjClosure D.M L : Set G) :=
    TwelveTwentyThree.le_normalizer_conjClosure D.M L
  have hXbarMbar : barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) ≤
      Mbar D.M V₀ V h.hyp125.isElemAbelian :=
    barSub_mono V₀ V h.hyp125.isElemAbelian hXM
  have hnormal : ((barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)).subgroupOf
      (Mbar D.M V₀ V h.hyp125.isElemAbelian)).Normal :=
    barSub_subgroupOf_mbar_normal h.hyp125.isElemAbelian hXM hMN
  have hleN : Mbar D.M V₀ V h.hyp125.isElemAbelian ≤
      Subgroup.normalizer
        (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) :
          Set (MulAut (Vtil V₀ V h.hyp125.isElemAbelian))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXbarMbar).1 hnormal
  have hmono := E3.aParam_mono hleN
  have hKbar := hK (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) f h2f hO hN
  have hle : E3.aParam (Mbar D.M V₀ V h.hyp125.isElemAbelian) ≤ f := hmono.trans hKbar
  simpa [aBar, hnof] using hle

theorem eighteen_nineteen_of_K (hK : K_Omega4Plus_aParam_le)
    (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h66 : UC6.R6_6 D)
    (h127 : R127 D) (h1114 : R1114 D) (h111 : W3Thm111 G) (h183 : W3Thm183 G)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h16 : R18_16_3wAt D V₀ V p L h) (h17 : R18_17_3At D V₀ V p L h)
    (h18 : R18_18bAt D V₀ V p L h)
    (h1742 : S17.R17_42At D V₀ V) (h4 : R18_4At D V₀ V p L) :
    R18_19At D V₀ V p L h :=
  eighteen_nineteen D V₀ V p L h hx h61 h126 h66 h127 h1114 h111 h183 h1669 h16 h17 h18
    (gap_18_19_aBar hK h h1742) h1742 h4

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
