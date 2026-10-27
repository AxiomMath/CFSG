module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIITwE6Model
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIITwE6Dim
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIITwE6Levi
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIISUCentralizerPlace
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIITwE6Root
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1OddCoverK2

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.StandardType CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.SeitzReduction.TwistedE6Pilot CFSG.StandardType.RCKK1IIISU

private theorem ker_comp_inclusion_le_center {X C Y : Type} [Group X] [Group C] [Group Y]
    {J K : Subgroup X} (hJK : J ≤ K) (ε : ↥K →* C) (hεker : ε.ker ≤ Subgroup.center ↥K)
    (ι : C →* Y) (hι : Function.Injective ι) :
    ((ι.comp ε).comp (Subgroup.inclusion hJK)).ker ≤ Subgroup.center ↥J := by
  intro x hx
  have hx1 : ε (Subgroup.inclusion hJK x) = 1 :=
    hι (by simpa using (MonoidHom.mem_ker).1 hx)
  have hxc := hεker ((MonoidHom.mem_ker).2 hx1)
  rw [Subgroup.mem_center_iff] at hxc ⊢
  intro y
  have h1 := hxc (Subgroup.inclusion hJK y)
  rw [Subtype.ext_iff] at h1 ⊢
  simpa using h1


theorem k2At_of_row_III_of_twistedE6_label
    {X : Type} [Group X] [Finite X] {p : ℕ} {K J B₁ : Subgroup X} {d r : X} {V : Subgroup X}
    (hp : p.Prime) (hp2 : p ≠ 2) (hBab : IsElemAbelian p B₁) (hdB : d ∈ B₁)
    (hB1K : B₁ ≤ Subgroup.normalizer (K : Set X))
    (hrank : p ^ 2 * Nat.card ↥(B₁ ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B₁)
    (hKq : CFSG.Assembly.IsQuasisimple ↥K)
    (hlab : GGHasLabel ⟨.twE6, 0, 1⟩ (↥K ⧸ Subgroup.center ↥K))
    (hJcomp : IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    (hrow : GGSixRCKJRow .III J) (hoddJ : Odd (Nat.card (Subgroup.center ↥J)))
    (hoddK : Odd (Nat.card (Subgroup.center ↥K))) (hJK : J ≤ K)
    (hFour : FourAt J V r) (hCore : CoreCommAt J V r) (hShort : ShortAt J r) :
    K2At K V r := by
  obtain ⟨ε, hεs, hεker, h, hh3, hh1, hJcomp', hrow'⟩ :=
    exists_twistedE6_model_of_row_III hp hp2 hBab hdB hB1K hrank hKq hlab hoddK hJcomp hrow hJK
  have hK4 : Nat.card SUF = 4 := rckSU_suF_card.trans (by norm_num)
  have hdim :=
    twE6MatFixDim_eq_36_or_28_of_row_III hK4 rckSUc_sigma_apply hh3 hh1 hJcomp' hrow'
  obtain ⟨c, hc, hdN, hcomp⟩ :=
    exists_conj_component_su6Levi_of_dim hK4 rckSUc_sigma_apply hh3 hh1 hJcomp' hdim
  obtain ⟨ι, hι⟩ : ∃ ι : ↥(twistedE6RootGroup SUF SUσ) →* ModGL TwistTag.E6.tag SUF,
      ι = (MulAut.conj c).toMonoidHom.comp (twistedE6RootGroup SUF SUσ).subtype := ⟨_, rfl⟩
  have hιinj : Function.Injective ι := by
    rw [hι]
    exact (MulAut.conj c).injective.comp Subtype.val_injective
  have hrange : ((ι.comp ε).comp (Subgroup.inclusion hJK)).range =
      ((J.subgroupOf K).map ε).map ι := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range, Subgroup.map_map]
  have hd3 : (c * (h : ModGL TwistTag.E6.tag SUF) * c⁻¹) ^ 3 = 1 := by
    rw [conj_pow, ← Subgroup.coe_pow, hh3, OneMemClass.coe_one, mul_one c, mul_inv_cancel]
  have hfin : Finite (ModGL TwistTag.E6.tag SUF) := CFSG.LieType.Chevalley.finite_modGL
  obtain ⟨hrJ, g, hPr, hPV⟩ :=
    rckSU_exists_conj_suV_of_centralizer_component (m := 6) (by norm_num) hrow hoddJ
      twE6LeviMap twE6LeviMap_range twE6LeviMap_ker_le_center hdN hd3
      ((ι.comp ε).comp (Subgroup.inclusion hJK))
      (ker_comp_inclusion_le_center hJK ε hεker.le ι hιinj)
      (by rw [hrange, hι]; exact hcomp) hFour hCore hShort
  have hrK : r ∈ K := hJK hrJ
  have hVmap : (V.subgroupOf J).map (Subgroup.inclusion hJK) = V.subgroupOf K := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    refine ⟨?_, fun hx => ⟨⟨x, hFour.2.1 hx⟩, hx, rfl⟩⟩
    rintro ⟨y, hy, rfl⟩
    exact hy
  have hR := pCoreOf_centralizer_le_normalizer_of_twE6LeviMap hc
    (V := (V.subgroupOf K).map ε) (r := ε ⟨r, hrK⟩) g
    (by rw [hι] at hPr; exact hPr)
    (by
      rw [← hι, ← hPV, Subgroup.map_map, ← hVmap, Subgroup.map_map])
  exact k2At_of_map_of_odd_central_ker ε hεs hεker.le (by rw [hεker]; exact hoddK) hrK
    (hFour.2.2.1.2 r hFour.1) (hFour.2.1.trans hJK) hFour.2.2.1.isPGroup hR

end CFSG.StandardType.RCKC1
