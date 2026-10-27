module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.B1Restrict
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c8_rk_vStar_eq (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) :
    rk ↥(⊤ : Subgroup (vStar D.M V₀ V hV L)) =
      s15 D.M V₀ V hV L * gamma15 D.M V₀ V hV L := by
  have h1 := mSub_eq_s15_mul_gamma15_add D h1217 h hV hL
  have h2 := s15_Infra_mSub_eq_rk_imgTil_add (v1Sub D.M V₀ V hV L) V V hV le_rfl
  rw [s15_Infra_imgTil_top (v1Sub D.M V₀ V hV L) V hV,
    inf_eq_right.mpr (s15_Infra_v1Sub_le h.hyp125 hV)] at h2
  have h3 : rk ↥(⊤ : Subgroup (vStar D.M V₀ V hV L)) + mSub (v1Sub D.M V₀ V hV L) =
      s15 D.M V₀ V hV L * gamma15 D.M V₀ V hV L + mSub (v1Sub D.M V₀ V hV L) :=
    h2.symm.trans h1
  omega

private lemma c8_imgTil_mono {V₀ V A B : Subgroup G} (hV : IsElemAbelian 2 V) (h : A ≤ B) :
    imgTil V₀ V hV A ≤ imgTil V₀ V hV B := by
  intro q hq
  obtain ⟨x, hx, rfl⟩ := (mem_imgTil V₀ V hV A q).1 hq
  exact (mem_imgTil V₀ V hV B _).2 ⟨x, h hx, rfl⟩

theorem c8_rk_wTil_eq (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hV : IsElemAbelian 2 V) (L : Subgroup G) :
    rk ↥(wTil V₀ V hV L) =
      gamma15 D.M V₀ V hV L + rk ↥(wTil V₀ V hV L ⊓ imgTil V₀ V hV (v1Sub D.M V₀ V hV L)) := by
  have hV₀W : V₀ ≤ wSub V₀ V hV L := s15_Two_le_wSub hV h.pairFacts.le L
  have hV₀V₁ : V₀ ≤ v1Sub D.M V₀ V hV L := s15_Infra_le_v1Sub D.M V₀ V hV L
  have hWV : wSub V₀ V hV L ≤ V := preTil_le V₀ V hV (wTil V₀ V hV L)
  have himgW : imgTil V₀ V hV (wSub V₀ V hV L) = wTil V₀ V hV L := by
    rw [wSub]
    exact imgTil_preTil V₀ V hV (wTil V₀ V hV L)
  have ha : mSub (wSub V₀ V hV L) = rk ↥(wTil V₀ V hV L) + mSub V₀ := by
    have h1 := s15_Infra_mSub_eq_rk_imgTil_add V₀ V (wSub V₀ V hV L) hV hWV
    rw [himgW, inf_eq_right.mpr hV₀W] at h1
    exact h1
  have hb : mSub (wSub V₀ V hV L) =
      gamma15 D.M V₀ V hV L + mSub (wSub V₀ V hV L ⊓ v1Sub D.M V₀ V hV L) := by
    rw [mSub_wSub D h hV]
    unfold delta15
    rw [inf_comm]
  have himgI : imgTil V₀ V hV (wSub V₀ V hV L ⊓ v1Sub D.M V₀ V hV L) =
      wTil V₀ V hV L ⊓ imgTil V₀ V hV (v1Sub D.M V₀ V hV L) := by
    refine le_antisymm ?_ ?_
    · refine le_inf ?_ ?_
      · rw [← himgW]
        exact c8_imgTil_mono hV inf_le_left
      · exact c8_imgTil_mono hV inf_le_right
    · intro q hq
      rw [Subgroup.mem_inf] at hq
      obtain ⟨hqW, hqV₁⟩ := hq
      obtain ⟨x, hxV₁, hxq⟩ := (mem_imgTil V₀ V hV (v1Sub D.M V₀ V hV L) q).1 hqV₁
      have hxW : x.val ∈ wSub V₀ V hV L := by
        rw [wSub]
        exact (mem_preTil V₀ V hV (wTil V₀ V hV L)).2
          ⟨x, rfl, by rw [hxq]; exact hqW⟩
      exact (mem_imgTil V₀ V hV (wSub V₀ V hV L ⊓ v1Sub D.M V₀ V hV L) q).2
        ⟨x, Subgroup.mem_inf.mpr ⟨hxW, hxV₁⟩, hxq⟩
  have hc : mSub (wSub V₀ V hV L ⊓ v1Sub D.M V₀ V hV L) =
      rk ↥(wTil V₀ V hV L ⊓ imgTil V₀ V hV (v1Sub D.M V₀ V hV L)) + mSub V₀ := by
    have h1 := s15_Infra_mSub_eq_rk_imgTil_add V₀ V
      (wSub V₀ V hV L ⊓ v1Sub D.M V₀ V hV L) hV (inf_le_left.trans hWV)
    rw [himgI, show (wSub V₀ V hV L ⊓ v1Sub D.M V₀ V hV L) ⊓ V₀ = V₀ from
      inf_eq_right.mpr (le_inf hV₀W hV₀V₁)] at h1
    exact h1
  omega

theorem c8_gamma15_le_rk_wTil (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hV : IsElemAbelian 2 V) (L : Subgroup G) :
    gamma15 D.M V₀ V hV L ≤ rk ↥(wTil V₀ V hV L) := by
  have := c8_rk_wTil_eq D h hV L
  omega

theorem c8_mQuot_wTil_le_gamma15 (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) :
    E3.mQuot (wTil V₀ V hV L) (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) ≤
      gamma15 D.M V₀ V hV L := by
  have hW : IsPGroup 2 ↥(wTil V₀ V hV L) :=
    isPGroup_two_of_sq_eq_one fun w =>
      Subtype.ext (s15_Infra_vtil_sq_eq_one V₀ V hV (w : Vtil V₀ V hV))
  have hcard := E3.card_eq_two_pow_mul (G := Vtil V₀ V hV) hW
    (inf_le_left : wTil V₀ V hV L ⊓ imgTil V₀ V hV (v1Sub D.M V₀ V hV L) ≤
      wTil V₀ V hV L)
  have hrank : rk ↥(wTil V₀ V hV L) =
      E3.mQuot (wTil V₀ V hV L)
        (wTil V₀ V hV L ⊓ imgTil V₀ V hV (v1Sub D.M V₀ V hV L)) +
      rk ↥(wTil V₀ V hV L ⊓ imgTil V₀ V hV (v1Sub D.M V₀ V hV L)) := by
    unfold rk
    rw [hcard,
      padicValNat.mul (pow_ne_zero _ (by norm_num))
        (Nat.card_pos (α := ↥(wTil V₀ V hV L ⊓
          imgTil V₀ V hV (v1Sub D.M V₀ V hV L)))).ne',
      padicValNat.prime_pow]
  have hA := c8_rk_wTil_eq D h.hyp125 hV L
  have hmq : E3.mQuot (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ imgTil V₀ V hV (v1Sub D.M V₀ V hV L)) =
      gamma15 D.M V₀ V hV L := by omega
  have hfix : imgTil V₀ V hV (v1Sub D.M V₀ V hV L) ≤ fixV (lBar V₀ V hV L) := by
    have h1 := s15_Core_imgTil_v1Sub_le_fixV h (m := (1 : G)) D.M.one_mem
    simpa only [conjSubgroup_one, lBar] using h1
  have hBC : wTil V₀ V hV L ⊓ imgTil V₀ V hV (v1Sub D.M V₀ V hV L) ≤
      wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L) := inf_le_inf_left _ hfix
  exact (E3.mQuot_mono hBC).trans (le_of_eq hmq)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
