module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U33AutE8
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L33AutE8
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BBarConjShape
public import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)

theorem aCandidate_le_two_of_aParam_le_two (t : StatedLieTag) {r p f : ℕ}
    (h : ∀ {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
      (Y : Subgroup (MulAut W)),
      CFSG.Open.IsQuasisimple ↥(genFittingFStar ↥Y) →
      LieModel (↥(genFittingFStar ↥Y) ⧸ Subgroup.center ↥(genFittingFStar ↥Y)) t r p f →
      E3.aParam Y ≤ 2)
    {H : Type} [Group H] [Finite H] (hH : CFSG.Open.IsQuasisimple H)
    (hU : LieModel (H ⧸ Subgroup.center H) t r p f)
    {n : ℕ} (c : ACandidate H n) : n ≤ 2 := by
  classical
  letI := c.commGroup
  letI := c.finiteW
  haveI : Finite (MulAut c.W) :=
    Finite.of_injective (fun φ : MulAut c.W => (φ : c.W → c.W)) DFunLike.coe_injective
  haveI : Finite ↥c.Y := Subtype.finite
  rw [c.eq_n]
  have hFstar : fstarSubOf c.Y = genFittingFStar ↥c.Y := by
    rw [fstarSubOf, CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar,
      CFSG.subgroupOf_map_subtype_eq]
  have hq : CFSG.Open.IsQuasisimple ↥(genFittingFStar ↥c.Y) := by
    rw [← hFstar]
    exact (CFSG.Quasithin.A3.isQuasisimple_iff_open).1 c.hLgq
  have hHtop : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup H) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv Subgroup.topEquiv hH
  have hft : fstarTop H = ⊤ := fstar_eq_self_of_isQuasisimple hHtop
  let eTop : ↥(fstarTop H) ≃* H :=
    hft ▸ (Subgroup.topEquiv : ↥(⊤ : Subgroup H) ≃* H)
  let eQTop : (H ⧸ Subgroup.center H) ≃*
      (↥(fstarTop H) ⧸ Subgroup.center ↥(fstarTop H)) :=
    QuotientGroup.congr (Subgroup.center H)
      (Subgroup.center ↥(fstarTop H)) eTop.symm
      (Subgroup.map_center_eq eTop.symm)
  have hU' : LieModel (↥(genFittingFStar ↥c.Y) ⧸
      Subgroup.center ↥(genFittingFStar ↥c.Y)) t r p f := by
    rw [← hFstar]
    exact LieModel.of_mulEquiv (eQTop.trans c.φ) hU
  exact h c.expTwo c.Y hq hU'

theorem aCandidate_le_two_of_U33 (hK : K_U33AutE8) {H : Type} [Group H] [Finite H]
    (hH : CFSG.Open.IsQuasisimple H)
    (hU : LieModel (H ⧸ Subgroup.center H) .PSU 3 3 1) {n : ℕ}
    (c : ACandidate H n) : n ≤ 2 :=
  aCandidate_le_two_of_aParam_le_two .PSU (aParam_le_two_of_U33 hK) hH hU c

theorem aCandLe_two_of_U33 (hK : K_U33AutE8) {X : Type} [Group X]
    (h : LieModel X .PSU 3 3 1) : ACandLe X 2 := by
  intro H _ _ hH _ ⟨eH⟩ n hn
  exact aCandidate_le_two_of_U33 hK hH (LieModel.of_mulEquiv eH.symm h) hn.some

theorem aCandidate_le_two_of_L33 (hK : K_L33AutE8) {H : Type} [Group H] [Finite H]
    (hH : CFSG.Open.IsQuasisimple H)
    (hU : LieModel (H ⧸ Subgroup.center H) .PSL 3 3 1) {n : ℕ}
    (c : ACandidate H n) : n ≤ 2 :=
  aCandidate_le_two_of_aParam_le_two .PSL (aParam_le_two_of_L33 hK) hH hU c

theorem aCandLe_two_of_L33 (hK : K_L33AutE8) {X : Type} [Group X]
    (h : LieModel X .PSL 3 3 1) : ACandLe X 2 := by
  intro H _ _ hH _ ⟨eH⟩ n hn
  exact aCandidate_le_two_of_L33 hK hH (LieModel.of_mulEquiv eH.symm h) hn.some

theorem lieModel_barInf_of_classicalTag {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (t : StatedLieTag) (ht : t ∈ CFSG.Blueprint.classicalTags) (hL : L ∈ calC M)
    (h : LieModel (Bar2 L) t 3 3 1) : LieModel (BarInf L) t 3 3 1 := by
  haveI : IsSimpleGroup (Bar2 L) := LieModel.isSimpleGroup_of_mem_classicalTags ht h
  have hc : Subgroup.center (Bar2 L) = ⊥ := uc22p21k_center_eq_bot hL.2.2
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_center_bot hL.2.2 hc
  exact LieModel.of_mulEquiv e.symm h

theorem lieModel_barInf_of_U33 {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hL : L ∈ calC M) (h : LieModel (Bar2 L) .PSU 3 3 1) :
    LieModel (BarInf L) .PSU 3 3 1 :=
  lieModel_barInf_of_classicalTag .PSU (by decide) hL h

theorem lieModel_barInf_of_L33 {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hL : L ∈ calC M) (h : LieModel (Bar2 L) .PSL 3 3 1) :
    LieModel (BarInf L) .PSL 3 3 1 :=
  lieModel_barInf_of_classicalTag .PSL (by decide) hL h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
