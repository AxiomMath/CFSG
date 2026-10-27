module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Base
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Card
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Frat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Star
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Close
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Forty7aCommon

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

structure G47Star (D : Data G) (H L V : Subgroup G) (z : G) : Prop where
  pCore_bot : CFSG.pCore 2 (Bar2 H) = ⊥
  pRank_le : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 H)) ≤ 1
  normal_Y : (starImg H (yGen L z)).Normal
  le_XY : starImg H (xInf L z) ≤ starImg H (yGen L z)
  split : ∀ h : Bar2 H, ∃ y ∈ starImg H (yGen L z), ∃ b ∈ starImg H (H ⊓ D.M), h = y * b
  conj_B : ∀ b ∈ starImg H (H ⊓ D.M), ∀ v ∈ starImg H V, b * v * b⁻¹ ∈ starImg H V
  conj_X : ∀ x ∈ starImg H (xInf L z), ∀ v ∈ starImg H V, x * v * x⁻¹ ∈ starImg H V
  sq : ∀ v ∈ starImg H V, v * v = 1
  pgroup : IsPGroup 2 (starImg H V)

theorem G47Star.of_ctx {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    {x : IntMod V hV} (hsp : IsStronglyPEmbedded 3 D.M) (hL : L ∈ calC D.M)
    (ctx : G47Ctx D V₀ V L hV x)
    (hX : IsSL2Prime ↥(starImg (centralizer ({x.val} : Set G)) (xInf L x.val)) 5) :
    G47Star D (centralizer ({x.val} : Set G)) L V x.val := by
  have hP := ctx.sect.setting.hyp151.hyp125.pairFacts
  have hLM : L ≤ D.M := hL.1.le
  have hXHL := s16c1_G47_xInf_le L x.val
  have hXH : xInf L x.val ≤ centralizer ({x.val} : Set G) := hXHL.trans inf_le_left
  have hXM : xInf L x.val ≤ D.M := (hXHL.trans inf_le_right).trans hLM
  have hXY : xInf L x.val ≤ yGen L x.val := s16c1_xInf_le_yGen L x.val
  have hYH : yGen L x.val ≤ centralizer ({x.val} : Set G) := s16c1_G47_yGen_le L x.val
  have hYn := s16c1_G47_yGen_normal L x.val
  have hr : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 (centralizer ({x.val} : Set G)))) ≤ 1 := by
    rw [s16c1_G47_pRank_bar _ Nat.prime_three (by norm_num)]
    exact ctx.rank3.le
  have hQM : pCoreOf 2 (centralizer ({x.val} : Set G)) ≤ D.M :=
    s16c1_pCoreOf_le_M D ctx.sylow
  have h120 : Nat.card ↥(starImg (centralizer ({x.val} : Set G)) (xInf L x.val)) = 120 :=
    (s16c1_sl2five_facts hX).1
  have h3X : 3 ∣ Nat.card ↥(xInf L x.val) := by
    have h := s16c1_G47_card_starImg_mul hXH
    rw [h120] at h
    rw [← h]
    exact Dvd.dvd.mul_right (by norm_num) _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := ↥(xInf L x.val)) 3 h3X
  have hd3 : orderOf (d : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hd
  refine ⟨s16c1_G47_pCore_bar _, hr, ?_, s16c1_starImg_mono _ hXY, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.Normal.map hYn _ (QuotientGroup.mk'_surjective _)
  · exact s16c1_G47_frat hQM hsp hXY hYH hXM hYn d.2 hd3 hr
  · exact fun b hb v hv => s16c1_G47_starImg_conj inf_le_left
      (inf_le_right.trans hP.le_normalizer) hb hv
  · exact fun b hb v hv => s16c1_G47_starImg_conj hXH
      (hXM.trans hP.le_normalizer) hb hv
  · exact (s16c1_G47_starImg_sq hP.elemAbelian).1
  · exact (s16c1_G47_starImg_sq hP.elemAbelian).2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
