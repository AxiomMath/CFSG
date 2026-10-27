module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFieldExtensionExclusion
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Pred
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16RankF
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4R51
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16CoverR119
public import CFSG.Quasithin.Background.G64ExtSq
public import CFSG.Quasithin.Background.G64NatTop
public import CFSG.Quasithin.Vol2.Ch10SecD33
public import CFSG.Quasithin.Vol2.Ch10SecDClA
public import CFSG.Quasithin.Vol2.Ch11SecA11Main
public import CFSG.Quasithin.Vol2.Ch11SecAKA2
public import CFSG.Quasithin.Vol2.Ch11SecAKA6
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22G
public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartD
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4E
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4F
public import CFSG.Quasithin.Vol2.Ch11SecSMain
public import CFSG.Quasithin.Vol2.Ch11SecSShape2
public import CFSG.Quasithin.Vol2.Ch11SecSSym2
public import CFSG.Quasithin.Vol2.Ch11SecSSym3
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.Quasithin.Vol2.Ch3B513NC1Nat
public import CFSG.Quasithin.Vol2.KGNatSL3NatFixed
public import CFSG.Quasithin.Vol2.KGNatSL3NatPoint

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem fixV_lBar_eq_bot_of_field_four
    (D : Data G) (hx : DataExt D)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (h61 : UC6.R6_1 D) (h126 : R126 D) (h111 : W3Thm111 G)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (h151 : Hyp151 D V₀ V L) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1)
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4)
    (hreal : (FFModel.nat (StatedSL 2 K)).Realizes (lBar V₀ V hV L)
        (commSub ⊤ (lBar V₀ V hV L))
        (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) ∨
      (FFModel.nat (StatedSp 2 K)).Realizes (lBar V₀ V hV L)
        (commSub ⊤ (lBar V₀ V hV L))
        (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)))
    (hLne : lBar V₀ V hV L ≠ ⊥)
    (hcentral : Mbar D.M V₀ V hV ⊓
      Subgroup.centralizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) ≠ ⊥)
    (hp : 3 ∈ D.sig)
    (hm : MBarGT D.M V₀ V 1) :
    fixV (lBar V₀ V hV L) = ⊥ := by
  classical
  by_contra hfix
  have hwt : commSub ⊤ (lBar V₀ V hV L) = ⊤ :=
    wTil_eq_top_of_case163_2 hconc hs
  have hrealTop : (FFModel.nat (StatedSL 2 K)).Realizes (lBar V₀ V hV L) ⊤
        (fixV (lBar V₀ V hV L)) ∨
      (FFModel.nat (StatedSp 2 K)).Realizes (lBar V₀ V hV L) ⊤
        (fixV (lBar V₀ V hV L)) := by
    rcases hreal with hR | hR
    · exact Or.inl (s16g_realizes_top hconc hs (StatedSL 2 K) hR)
    · exact Or.inr (s16g_realizes_top hconc hs (StatedSp 2 K) hR)
  have hHnorm : Mbar D.M V₀ V hV ≤
      Subgroup.normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
    intro g hg
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (lBar_conj_eq_of_s15_eq_one hs hg)
  have hHn : (lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV) |>.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hHnorm
  have hV₀ : V₀ = ⊥ := by
    by_contra hV₀ne
    exact hfix (s15_Kbar_fixV_eq_bot_of_ne_bot h151.hyp125 hV₀ne
      (barSub_mono V₀ V hV h151.le) hHn hLne)
  subst hV₀
  have hHA : lBar (⊥ : Subgroup G) V hV L ≤ Mbar D.M (⊥ : Subgroup G) V hV :=
    barSub_mono (⊥ : Subgroup G) V hV h151.le
  have hHn' : ∀ a ∈ Mbar D.M (⊥ : Subgroup G) V hV,
      ∀ x ∈ lBar (⊥ : Subgroup G) V hV L, a * x * a⁻¹ ∈ lBar (⊥ : Subgroup G) V hV L := by
    intro a ha x hx
    exact (Subgroup.mem_normalizer_iff.mp (hHnorm ha) x).mp hx
  exact false_of_field_four_natural_extension D hx hSg h61 h126 h111 hV
    h151.hyp125 hp hm hK hHA hHn' hwt hrealTop hcentral hfix

theorem fixV_lBar_eq_bot_of_field_eight
    (D : Data G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h126 : R126 D) (h111 : W3Thm111 G)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (h151 : Hyp151 D V₀ V L) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1)
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 8)
    (hreal : (FFModel.nat (StatedSL 2 K)).Realizes (lBar V₀ V hV L)
        (commSub ⊤ (lBar V₀ V hV L))
        (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) ∨
      (FFModel.nat (StatedSp 2 K)).Realizes (lBar V₀ V hV L)
        (commSub ⊤ (lBar V₀ V hV L))
        (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)))
    (hLne : lBar V₀ V hV L ≠ ⊥)
    (hcentral : Mbar D.M V₀ V hV ⊓
      Subgroup.centralizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) ≠ ⊥)
    (hp : 7 ∈ D.sig)
    (hm : MBarGT D.M V₀ V 2) :
    fixV (lBar V₀ V hV L) = ⊥ := by
  classical
  by_contra hfix
  have hwt : commSub ⊤ (lBar V₀ V hV L) = ⊤ :=
    wTil_eq_top_of_case163_2 hconc hs
  have hrealTop : (FFModel.nat (StatedSL 2 K)).Realizes (lBar V₀ V hV L) ⊤
        (fixV (lBar V₀ V hV L)) ∨
      (FFModel.nat (StatedSp 2 K)).Realizes (lBar V₀ V hV L) ⊤
        (fixV (lBar V₀ V hV L)) := by
    rcases hreal with hR | hR
    · exact Or.inl (s16g_realizes_top hconc hs (StatedSL 2 K) hR)
    · exact Or.inr (s16g_realizes_top hconc hs (StatedSp 2 K) hR)
  have hHnorm : Mbar D.M V₀ V hV ≤
      Subgroup.normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
    intro g hg
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (lBar_conj_eq_of_s15_eq_one hs hg)
  have hHn : (lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV) |>.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hHnorm
  have hV₀ : V₀ = ⊥ := by
    by_contra hV₀ne
    exact hfix (s15_Kbar_fixV_eq_bot_of_ne_bot h151.hyp125 hV₀ne
      (barSub_mono V₀ V hV h151.le) hHn hLne)
  subst hV₀
  have hHA : lBar (⊥ : Subgroup G) V hV L ≤ Mbar D.M (⊥ : Subgroup G) V hV :=
    barSub_mono (⊥ : Subgroup G) V hV h151.le
  have hHn' : ∀ a ∈ Mbar D.M (⊥ : Subgroup G) V hV,
      ∀ x ∈ lBar (⊥ : Subgroup G) V hV L, a * x * a⁻¹ ∈ lBar (⊥ : Subgroup G) V hV L := by
    intro a ha x hx
    exact (Subgroup.mem_normalizer_iff.mp (hHnorm ha) x).mp hx
  exact false_of_field_eight_natural_extension D hx h61 h126 h111 hV
    h151.hyp125 hp hm hK hHA hHn' hwt hrealTop hcentral hfix

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
