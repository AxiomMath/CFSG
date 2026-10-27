module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1Row
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicCoverCenterOddHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEightInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem aCandidate_le_tableA {s : TauCeti.SporadicName} (hrow : W4Thm11_1Row s)
    {H : Type} [Group H] [Finite H] (hH : CFSG.Open.IsQuasisimple H)
    (hodd : Odd (Nat.card (Subgroup.center H)))
    (hs : IsSpor (H ⧸ Subgroup.center H) s)
    {n : ℕ} (c : Inputs1719.ACandidate H n) : n ≤ tableA s := by
  classical
  letI := c.commGroup
  have := c.finiteW
  have hHtop : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup H) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv Subgroup.topEquiv hH
  have hft : fstarTop H = ⊤ := fstar_eq_self_of_isQuasisimple hHtop
  obtain ⟨Z₀, hZ₀, hZ₀le, ⟨e⟩⟩ := c.central_factor
  have : Z₀.Normal := hZ₀
  have hFle : Fstar c.Y ≤ c.Y := Subgroup.map_subtype_le _
  let eY : ↥(fstarSubOf c.Y) ≃* ↥(Fstar c.Y) :=
    Subgroup.subgroupOfEquivOfLe hFle
  let qmap : ↥(fstarTop H) →* (↥(fstarTop H) ⧸ Z₀) := QuotientGroup.mk' Z₀
  let φ : ↥(fstarTop H) →* ↥(Fstar c.Y) :=
    eY.toMonoidHom.comp (e.symm.toMonoidHom.comp qmap)
  have hφs : Function.Surjective φ :=
    eY.surjective.comp (e.symm.surjective.comp (QuotientGroup.mk'_surjective Z₀))
  have hker : φ.ker ≤ Subgroup.center ↥(fstarTop H) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : e.symm (qmap x) = 1 := by
      apply eY.injective
      rw [map_one]
      simpa [φ] using hx
    have h2 : qmap x = 1 := e.symm.injective (by simpa using h1)
    exact hZ₀le ((QuotientGroup.eq_one_iff x).1 h2)
  have hcenter : Subgroup.center ↥(Fstar c.Y) =
      (Subgroup.center ↥(fstarTop H)).map φ :=
    CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple c.hLq hφs hker
  have hoddTop : Odd (Nat.card (Subgroup.center ↥(fstarTop H))) := by
    rw [hft]
    rw [Nat.card_congr (Subgroup.centerCongr
      (Subgroup.topEquiv : ↥(⊤ : Subgroup H) ≃* H)).toEquiv]
    exact hodd
  have hoddF : Odd (Nat.card (Subgroup.center ↥(Fstar c.Y))) := by
    rw [hcenter]
    exact Odd.of_dvd_nat hoddTop
      (Subgroup.card_map_dvd (H := Subgroup.center ↥(fstarTop H)) (f := φ))
  have hLgq : CFSG.Open.IsQuasisimple ↥(fstarSubOf c.Y) :=
    (CFSG.Quasithin.A3.isQuasisimple_iff_open).1 c.hLgq
  have hLq : CFSG.Open.IsQuasisimple ↥(Fstar c.Y) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv eY.symm hLgq
  have hO2 : O2Trivial (Fstar c.Y) := S17.o2Trivial_of_isQuasisimple_of_odd_center hLq hoddF
  have hsY : IsSpor (↥(Fstar c.Y) ⧸ Subgroup.center ↥(Fstar c.Y)) s := by
    let eTop : ↥(fstarTop H) ≃* H :=
      hft ▸ (Subgroup.topEquiv : ↥(⊤ : Subgroup H) ≃* H)
    let eQTop : (H ⧸ Subgroup.center H) ≃*
        (↥(fstarTop H) ⧸ Subgroup.center ↥(fstarTop H)) :=
      QuotientGroup.congr (Subgroup.center H)
        (Subgroup.center ↥(fstarTop H)) eTop.symm
        (Subgroup.map_center_eq eTop.symm)
    let eQY : (↥(fstarSubOf c.Y) ⧸ Subgroup.center ↥(fstarSubOf c.Y)) ≃*
        (↥(Fstar c.Y) ⧸ Subgroup.center ↥(Fstar c.Y)) :=
      QuotientGroup.congr (Subgroup.center ↥(fstarSubOf c.Y))
        (Subgroup.center ↥(Fstar c.Y)) eY (Subgroup.map_center_eq eY)
    obtain ⟨f⟩ := hs
    exact ⟨(eQTop.trans (c.φ.trans eQY)).symm.trans f⟩
  have hLqNat : CFSG.IsQuasisimple ↥(Fstar c.Y) :=
    (CFSG.Quasithin.A3.isQuasisimple_iff_open).2 hLq
  rw [c.eq_n]
  exact (hrow c.W c.expTwo c.Y (Fstar c.Y) hFle c.hLgn rfl hLqNat hO2 hsY).1

theorem aCandLe_tableA {s : TauCeti.SporadicName} (hrow : W4Thm11_1Row s)
    {X : Type} [Group X] (hs : IsSpor X s) : ACandLe X (tableA s) := by
  intro H _ _ hH hodd ⟨eH⟩ n ⟨c⟩
  obtain ⟨f⟩ := hs
  exact aCandidate_le_tableA hrow hH hodd ⟨eH.trans f⟩ c

theorem isSpor_barInf_of_isSpor_bar2 {M L : Subgroup G} (hL : L ∈ calC M)
    {s : TauCeti.SporadicName} (hsimp : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier s))
    (h : IsSpor (Bar2 L) s) : IsSpor (BarInf L) s := by
  obtain ⟨e⟩ := h
  have : IsSimpleGroup (Bar2 L) := e.isSimpleGroup_congr.mpr hsimp
  obtain ⟨f⟩ := uc22p21k_barInf_equiv_of_center_bot hL.2.2 (uc22p21k_center_eq_bot hL.2.2)
  exact ⟨f.trans e⟩

theorem bBar_conjClosure_le_tableA {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h77 : Inputs1719.W4Lem7_7) {s : TauCeti.SporadicName} (hrow : W4Thm11_1Row s)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hs : IsSpor (BarInf L) s) :
    bBar (UC22.conjClosure D.M L) D.M V₀ V hV.isElemAbelian ≤ tableA s :=
  bBar_conjClosure_le_of_aCandLe hV h77 hL (aCandLe_tableA hrow hs)

theorem bBar_le_tableA_of_normal {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h77 : Inputs1719.W4Lem7_7) {s : TauCeti.SporadicName} (hrow : W4Thm11_1Row s)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hN : (L.subgroupOf D.M).Normal)
    (hs : IsSpor (BarInf L) s) :
    bBar L D.M V₀ V hV.isElemAbelian ≤ tableA s := by
  have h := bBar_conjClosure_le_tableA hV h77 hrow hL hs
  rwa [Inputs1719.conjClosure_eq_self_of_normal hL.1.le hN] at h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isSpor_bar2_of_isSpor_barInf {M L : Subgroup G} (hL : L ∈ calC M)
    {s : TauCeti.SporadicName}
    (hcov : ∀ {E : Type} [Group E] [Finite E] [Group.IsPerfect E]
      (π : E →* CFSG.Blueprint.NativeSporadic.Carrier s), Function.Surjective π →
        π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) → π.ker = ⊥)
    (h : IsSpor (BarInf L) s) : IsSpor (Bar2 L) s := by
  obtain ⟨f⟩ := h
  obtain ⟨e1⟩ := uc22p21k_barInf_equiv_of_calC hL
  have : Group.IsPerfect (Bar2 L) := (Group.isPerfect_def).2 hL.2.2.1
  have hZ : Subgroup.center (Bar2 L) = ⊥ :=
    Inputs1719.center_eq_bot_of_perfect_odd_cover (e1.symm.trans f)
      (uc22p20p_odd_center_bar2 ↥L) hcov
  obtain ⟨e2⟩ := uc22p21k_quotCenter_equiv hZ
  exact ⟨e2.symm.trans (e1.symm.trans f)⟩

theorem barSub_ne_bot_of_two_le_pRank_bar2 {D : Data G} {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) (h117 : C117 D V₀ V) {L : Subgroup G} (hL : L ∈ calC D.M)
    (h3 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L))) :
    barSub V₀ V hV.isElemAbelian L ≠ ⊥ :=
  barSub_ne_bot_of_not_thin hV h117 hL
    (not_thin8_of_two_le_pRank Nat.prime_three (by norm_num)
      (two_le_pRank_of_bar2 Nat.prime_three (by norm_num) h3))

theorem fixV_barSub_eq_bot_of_dichotomy {D : Data G} {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hN : (L.subgroupOf D.M).Normal)
    (hd : fixV (barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M L)) = ⊥ ∨
      (V₀ = ⊥ ∧ ClassicalEvenAltG2Der (UC22.Bar2 L)))
    (hnc : ¬ ClassicalEvenAltG2Der (UC22.Bar2 L)) :
    fixV (barSub V₀ V hV.isElemAbelian L) = ⊥ := by
  rcases hd with h | ⟨-, h⟩
  · rwa [Inputs1719.conjClosure_eq_self_of_normal hL.1.le hN] at h
  · exact absurd h hnc

theorem fixV_barSub_eq_bot_of_not_classical (D : Data G) {V₀ V : Subgroup G}
    (h869 : F08.R869 D) (h127 : R127 D) (h640 : UC6.R6_40_2 D) (hFF : W4Thm12McClurg)
    (hV : Hyp125 D V₀ V) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hN : (L.subgroupOf D.M).Normal) (hnt : ¬ F08.Thin8 L)
    (hnc : ¬ ClassicalEvenAltG2Der (UC22.Bar2 L)) :
    fixV (barSub V₀ V hV.isElemAbelian L) = ⊥ :=
  fixV_barSub_eq_bot_of_dichotomy hV hL hN
    (fixV_dichotomy_of_not_thin D h869 h127 h640 hFF hV hL hnt) hnc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
