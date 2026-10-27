module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyOne
public import CFSG.LocalAnalysis.UniquenessCase.UC22Main1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def W4McClurg3D4 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)) (n : ℕ),
      L ≤ Y → (L.subgroupOf Y).Normal → CFSG.LocalAnalysis.UniquenessCase.UC22.Is3D4 ↥L n →
        fixV L = ⊥ → Odd n → 6 * n ≤ E3.mParam Y

theorem centralizer_Z_le_of_ne_bot {D : Data G} {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) (hV₀ : V₀ ≠ ⊥) :
    centralizer (D.Z : Set G) ≤ D.M := by
  have hCU : CentralizersUnique D.M D.T := by
    rcases hV.1 with ⟨-, h0⟩ | ⟨-, hcu, -⟩
    · exact absurd h0 hV₀
    · exact hcu
  obtain ⟨z, hzZ, hz1⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr (uc22main1_Z_ne_bot D))
  have hz1' : z ≠ 1 := by simpa using hz1
  have hzmem := CFSG.LocalAnalysis.RankThreeUC.omegaOneCenterIn_le_inf_centralizer D.T hzZ
  have hzT : z ∈ D.T := hzmem.1
  have hzc : ∀ t ∈ D.T, z * t = t * z := by
    intro t ht
    exact (Subgroup.mem_centralizer_iff.1 hzmem.2 t ht).symm
  have hCz : centralizer ({z} : Set G) ≤ D.M := (hCU z hzT hzc hz1').1
  refine (?_ : centralizer (D.Z : Set G) ≤ centralizer ({z} : Set G)).trans hCz
  intro g hg
  rw [Subgroup.mem_centralizer_iff] at hg ⊢
  intro y hy
  have hyz : y = z := by simpa using hy
  exact hyz ▸ hg z hzZ

theorem v0_eq_bot_of_not_centralizer_le {D : Data G} {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) (h : ¬ centralizer (D.Z : Set G) ≤ D.M) : V₀ = ⊥ := by
  by_contra hV₀
  exact h (centralizer_Z_le_of_ne_bot hV hV₀)

theorem v0_eq_bot_of_uc2_10_9 {D : Data G} (h109 : Inputs1719.UC2_10_9 D)
    {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    {s p : ℕ} {B : Subgroup G} (hs : Odd s) (hp : p.Prime) (hdvd : p ∣ 2 ^ s - 1)
    (hB : B ≤ D.M ⊓ Subgroup.normalizer (D.T : Set G)) (hcard : Nat.card B = p)
    (hU : UC6.InU D.M B) (hcent : B ≤ Subgroup.centralizer (D.Z : Set G)) :
    V₀ = ⊥ :=
  v0_eq_bot_of_not_centralizer_le hV ((h109 s p B hs hp hdvd hB hcard hU).2.2.1 hcent)

section Certified


theorem is3D4_barSub_of_is3D4 {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    {L : Subgroup G} {n : ℕ} (hL : L ∈ calC D.M)
    (hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥)
    (h3D4 : CFSG.LocalAnalysis.UniquenessCase.UC22.Is3D4 (Bar2 L) n) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.Is3D4 ↥(barSub V₀ V hV.isElemAbelian L) n := by
  have hCE : CFSG.Blueprint.ChevalleyExceptionalModel (Bar2 L) .trialityD4 2 n :=
    CFSG.Blueprint.LieModel.chevalleyExceptionalModel h3D4 (by decide)
  have hsimple :=
    (CFSG.LieType.Simplicity.fam_3d4_simplicity (Bar2 L) 2 n hCE).2
  obtain ⟨e⟩ := barSubBar2Equiv_of_isSimpleGroup hV hL hL1 hsimple
  exact CFSG.Blueprint.LieModel.of_mulEquiv e h3D4

theorem seventeen_thirtytwo_normal_v0eq1 (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h126 : R126 D) (h111 : W3Thm111 G) (h869 : F08.R869 D) (h127 : R127 D)
    (h640 : UC6.R6_40_2 D) (hFF : W4Thm12McClurg)
    (hMc3D4 : W4McClurg3D4)
    (h891 : CFSG.LocalAnalysis.UniquenessCase.UC22.F08.R891 D)
    {V : Subgroup G} (hV : Hyp125 D ⊥ V)
    (L : Subgroup G) (hL : L ∈ calC D.M) (hN : (L.subgroupOf D.M).Normal)
    (n : ℕ) (h3D4 : Is3D4 (Bar2 L) n) (hnodd : Odd n)
    (h3D4N : Inputs1719.W4Lem4_17TrialityD4N) : False := by
  have hshape : ((∃ n : ℕ, CFSG.Quasithin.Is2F4 n (Bar2 L)) ∨
      CFSG.Blueprint.LieModel (Bar2 L) .Tits 0 2 1 ∨ (∃ n : ℕ, Is3D4 (Bar2 L) n)) :=
    Or.inr (Or.inr ⟨n, h3D4⟩)
  have hnt := not_thin_of_exceptional k_exceptionalNotThin hshape
  have hL1 := barSub_ne_bot_of_not_thin_bot h869 h127 hV hL hnt
  have hU := uniqueMax_conjClosure_of_not_thin h869 hL hnt
  have hcomp : barSub ⊥ V hV.isElemAbelian L ∈ compBar D.M ⊥ V hV.isElemAbelian :=
    barSub_mem_compBar_of_ne_bot hV hL hL1
  have hshapeBar := is3D4_barSub_of_is3D4 hV hL hL1 h3D4
  have hfix := fixV_barSub_eq_bot_of_normal h640 hFF h869 h127 hV hL hN
    (Or.inr (Or.inr ⟨n, h3D4⟩))
  have hLMbar : barSub ⊥ V hV.isElemAbelian L ≤ Mbar D.M ⊥ V hV.isElemAbelian :=
    barSub_mono ⊥ V hV.isElemAbelian hL.1.le
  have hMN : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).1 hN
  have hNormBar : ((barSub ⊥ V hV.isElemAbelian L).subgroupOf
      (Mbar D.M ⊥ V hV.isElemAbelian)).Normal :=
    barSub_subgroupOf_mbar_normal hV.isElemAbelian hL.1.le hMN
  have hpow : ∀ w : Vtil ⊥ V hV.isElemAbelian, w ^ 2 = 1 :=
    s15_Infra_vtil_sq_eq_one ⊥ V hV.isElemAbelian
  have hm := hMc3D4 (W := Vtil ⊥ V hV.isElemAbelian) hpow
    (Y := Mbar D.M ⊥ V hV.isElemAbelian) (L := barSub ⊥ V hV.isElemAbelian L) (n := n)
    hLMbar hNormBar hshapeBar hfix hnodd
  have hm' : 6 * n ≤ mBar D.M ⊥ V hV.isElemAbelian := hm
  have hsimple : IsSimpleGroup (Bar2 L) := by
    have hCE : CFSG.Blueprint.ChevalleyExceptionalModel (Bar2 L) .trialityD4 2 n :=
      CFSG.Blueprint.LieModel.chevalleyExceptionalModel h3D4 (by decide)
    exact (CFSG.LieType.Simplicity.fam_3d4_simplicity (Bar2 L) 2 n hCE).2
  have hbb := bBar_le_four_mul_of_is3D4 hV h3D4N hL hN hL1 hfix hsimple h3D4
  have hbb' : bBar (UC22.conjClosure D.M L) D.M ⊥ V hV.isElemAbelian ≤ 4 * n := by
    rwa [uc22p2214_conjClosure_eq_of_normal hL.1.le hN]
  have h1 := twelve_twentyThree_one D hx h61 h126 h111 hV rfl hL.1 hL.2.2 hL1 hU
  have hk : D.k = 1 := by
    have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := h891 L hL n h3D4
    unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
    rw [if_pos hsp]
  rw [hk] at h1
  have hn1 : 1 ≤ n := (CFSG.Blueprint.LieModel.admissible h3D4).2.1
  omega

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
