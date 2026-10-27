module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKTri8Cent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKTri8Inner
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKTri8Four

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V} {K₁ K₂ : Type} [Field K₁] [Field K₂] [Finite K₁] [Finite K₂]
  {I₁ I₂ : Subgroup (Vtil V₀ V hV)}
  {π₁ : ↥(StatedOmega (StatedQuadPlus 4 K₁)) →* ↥(lBar V₀ V hV L)}
  {π₂ : ↥(StatedOmega (StatedQuadPlus 4 K₂)) →* ↥(lBar V₀ V hV L)}

theorem s16k_false_of_sum_two_omegaPlus_triality (hOut : S16kOmega8OutInner)
    (h : S16gRowCtx D V₀ V L hV) (hc : S16kTri8Cfg D V₀ V L hV I₁ I₂ π₁ π₂) : False := by
  obtain ⟨t, htM, ht2, ht1, htrk, -⟩ := h.conc
  obtain ⟨hI₁, hI₂⟩ := s16k_tri8_fix_of_rk h hc htM ht2 htrk
  obtain ⟨l, hlL, hl⟩ := s16k_tri8_inner hOut h hc htM hI₁ hI₂
  have hlM : l ∈ Mbar D.M V₀ V hV := barSub_mono V₀ V hV h.setting.hyp151.le hlL
  have hcen := s16k_tri8_cent_eq_one h hc (mul_mem (inv_mem hlM) htM) fun x hx => by
    calc l⁻¹ * t * x = l⁻¹ * (t * x * t⁻¹) * t := by group
      _ = l⁻¹ * (l * x * l⁻¹) * t := by rw [hl x hx]
      _ = x * (l⁻¹ * t) := by group
  have htl : t = l := (inv_mul_eq_one.1 hcen).symm
  have := s16k_tri8_rank_four h hc (htl ▸ hlL) ht1
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
