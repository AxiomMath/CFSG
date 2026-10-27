module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1FbKit

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_M_le_stabTil {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) : D.M ≤ stabTil V₀ V :=
  le_stabTil hS.setting.hyp151.hyp125.pairFacts.le_normalizer
    hS.setting.hyp151.hyp125.pairFacts.le_normalizer₀

private theorem s16c1_card_ne_zero {X : Type*} [Group X] [Finite X] (H : Subgroup X) :
    Nat.card H ≠ 0 :=
  Nat.card_ne_zero.mpr ⟨Nonempty.intro (1 : ↥H), inferInstance⟩

private theorem s16c1_relIndex_map_dvd {G₁ G₂ : Type*} [Group G₁] [Group G₂] (φ : G₁ →* G₂)
    (H K : Subgroup G₁) : (H.map φ).relIndex (K.map φ) ∣ H.relIndex K := by
  have hK : K.map φ = (φ.comp K.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hK, ← Subgroup.index_comap]
  exact Subgroup.index_dvd_of_le fun k hk =>
    Subgroup.mem_comap.mpr (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩)

theorem s16c1_Mbar_le_normalizer_lBar {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hCT : OmegaCentTriv (lBar V₀ V hV L)) :
    Mbar D.M V₀ V hV ≤ normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
  intro g hg
  by_contra hgn
  obtain ⟨t, htM, -, -, -, hW⟩ := hS.conc
  have hcent : lBar V₀ V hV L ≤
      Subgroup.centralizer
        ((lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom : Set (MulAut (Vtil V₀ V hV))) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).1 (hW.2.1 g hg hgn).1
  have hLg : (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom = ⊥ := by
    refine le_bot_iff.1 fun y hy => ?_
    rw [Subgroup.mem_bot]
    exact hCT y fun h hh => Subgroup.mem_centralizer_iff.1 (hcent hh) y hy
  have hbot : lBar V₀ V hV L = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (lBar V₀ V hV L)
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).1 hLg
  exact hS.ne_bot hbot

theorem s16c1_barSub_sylow {M T V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hM : M ≤ stabTil V₀ V) (hT : IsSylowIn 2 T M) :
    IsSylowIn 2 (barSub V₀ V hV T) (barSub V₀ V hV M) := by
  let S := stabTil V₀ V
  let F : ↥S →* MulAut (Vtil V₀ V hV) := actTil V₀ V hV
  have hT'p : IsPGroup 2 (T.subgroupOf S) := hT.isPGroup.comap_subtype
  refine ⟨barSub_mono V₀ V hV hT.le, ?_, ?_⟩
  · show IsPGroup 2 ((T.subgroupOf S).map F)
    exact hT'p.map F
  · change ¬ 2 ∣ ((T.subgroupOf S).map F).relIndex ((M.subgroupOf S).map F)
    intro hdvd
    have hdvd' : 2 ∣ (T.subgroupOf S).relIndex (M.subgroupOf S) :=
      hdvd.trans (s16c1_relIndex_map_dvd F (T.subgroupOf S) (M.subgroupOf S))
    rw [Subgroup.relIndex_subgroupOf hM] at hdvd'
    exact hT.not_dvd_relIndex hdvd'

theorem s16c1_sylow_lBar {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hCT : OmegaCentTriv (lBar V₀ V hV L)) :
    IsSylowIn 2 (barSub V₀ V hV D.T ⊓ lBar V₀ V hV L) (lBar V₀ V hV L) := by
  have hM : D.M ≤ stabTil V₀ V := s16c1_M_le_stabTil hS
  have hT : IsSylowIn 2 D.T D.M := CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM
  have hTsyl : IsSylowIn 2 (barSub V₀ V hV D.T) (Mbar D.M V₀ V hV) :=
    s16c1_barSub_sylow hM hT
  have hLM : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV hS.setting.hyp151.le
  have hN : ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mpr
      (s16c1_Mbar_le_normalizer_lBar hS hCT)
  exact IsSylowIn.inf_normal hTsyl hLM hN

theorem s16c1_sylow_preBarSub {M T V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hM : M ≤ stabTil V₀ V) (hT : IsSylowIn 2 T M)
    {Q : Subgroup (MulAut (Vtil V₀ V hV))} (hQ : Q ≤ barSub V₀ V hV T) :
    IsSylowIn 2 (T ⊓ preBarSub M V₀ V hV Q) (preBarSub M V₀ V hV Q) := by
  classical
  set C : Subgroup G := preBarSub M V₀ V hV ⊥ with hCdef
  set P₀ : Subgroup G := preBarSub M V₀ V hV Q with hP₀def
  set Y : Subgroup G := T ⊓ P₀ with hYdef
  have hP₀M : P₀ ≤ M := by rw [hP₀def]; exact inf_le_left
  have hP₀S : P₀ ≤ stabTil V₀ V := by
    rw [hP₀def]
    exact le_trans inf_le_right (Subgroup.map_subtype_le _)
  have hCM : C ≤ M := by rw [hCdef]; exact inf_le_left
  have hCP₀ : C ≤ P₀ := by
    intro g hg
    rw [hCdef] at hg
    rw [hP₀def, mem_preBarSub]
    obtain ⟨hgM, h, hh⟩ := (mem_preBarSub M V₀ V hV ⊥).1 hg
    exact ⟨hgM, h, by rw [Subgroup.mem_bot.1 hh]; exact Subgroup.one_mem Q⟩
  have hY_le_T : Y ≤ T := by rw [hYdef]; exact inf_le_left
  have hY_le_P₀ : Y ≤ P₀ := by rw [hYdef]; exact inf_le_right
  have hTC_le_Y : T ⊓ C ≤ Y := by
    rw [hYdef]
    exact le_inf inf_le_left (inf_le_right.trans hCP₀)
  let fP : ↥P₀ →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion hP₀S)
  let fY : ↥Y →* MulAut (Vtil V₀ V hV) :=
    fP.comp (Subgroup.inclusion hY_le_P₀)
  have hQMbar : Q ≤ Mbar M V₀ V hV := hQ.trans (barSub_mono V₀ V hV hT.le)
  have hkerP : fP.ker = C.subgroupOf P₀ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hCdef, mem_preBarSub]
    constructor
    · intro hx
      refine ⟨hP₀M x.2, hP₀S x.2, ?_⟩
      rw [Subgroup.mem_bot]
      rw [show fP x = actTil V₀ V hV ⟨x.val, hP₀S x.2⟩ from rfl] at hx
      exact hx
    · rintro ⟨-, h, hh⟩
      rw [show fP x = actTil V₀ V hV ⟨x.val, hP₀S x.2⟩ from rfl]
      rw [show (⟨x.val, h⟩ : ↥(stabTil V₀ V)) = ⟨x.val, hP₀S x.2⟩ from Subtype.ext rfl]
      exact Subgroup.mem_bot.1 hh
  have hcardkerP : Nat.card fP.ker = Nat.card C := by
    rw [hkerP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCP₀).toEquiv
  have hrangeP : fP.range = Q := by
    have h1 : fP.range = (P₀.subgroupOf (stabTil V₀ V)).map (actTil V₀ V hV) := by
      dsimp only [fP]
      rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rw [h1, hP₀def]
    change barSub V₀ V hV (preBarSub M V₀ V hV Q) = Q
    rw [barSub_preBarSub, inf_eq_left.mpr hQMbar]
  have hkerY : fY.ker = (T ⊓ C).subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    rw [show fY y = fP ⟨y.val, hY_le_P₀ y.2⟩ from rfl, ← MonoidHom.mem_ker, hkerP,
      Subgroup.mem_subgroupOf]
    exact ⟨fun hy => ⟨hY_le_T y.2, hy⟩, fun hy => hy.2⟩
  have hcardkerY : Nat.card fY.ker = Nat.card ↥(T ⊓ C) := by
    rw [hkerY]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC_le_Y).toEquiv
  have hrangeY : fY.range = Q := by
    refine le_antisymm ?_ ?_
    · rintro q ⟨y, rfl⟩
      rw [show fY y = fP ⟨y.val, hY_le_P₀ y.2⟩ from rfl]
      exact hrangeP ▸ (MonoidHom.mem_range).2 ⟨_, rfl⟩
    · intro q hq
      obtain ⟨t, htT, htq⟩ := (mem_barSub V₀ V hV T q).1 (hQ hq)
      have htM : (t : G) ∈ M := hT.le htT
      have htP₀ : (t : G) ∈ P₀ :=
        (mem_preBarSub M V₀ V hV Q).2 ⟨htM, t.2, by rw [htq]; exact hq⟩
      have htY : (t : G) ∈ Y := ⟨htT, htP₀⟩
      refine ⟨⟨(t : G), htY⟩, ?_⟩
      rw [show fY ⟨(t : G), htY⟩ =
          actTil V₀ V hV ⟨(t : G), hP₀S (hY_le_P₀ htY)⟩ from rfl]
      rw [show (⟨(t : G), hP₀S (hY_le_P₀ htY)⟩ : ↥(stabTil V₀ V)) = t from Subtype.ext rfl]
      exact htq
  have hcardP₀ : Nat.card P₀ = Nat.card C * Nat.card Q := by
    have h := Subgroup.card_ker_mul_card_range fP
    rw [hcardkerP, hrangeP] at h
    exact h.symm
  have hcardY : Nat.card Y = Nat.card ↥(T ⊓ C) * Nat.card Q := by
    have h := Subgroup.card_ker_mul_card_range fY
    rw [hcardkerY, hrangeY] at h
    exact h.symm
  let gM : ↥M →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion hM)
  have hCker : C.subgroupOf M = gM.ker := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hCdef, mem_preBarSub]
    constructor
    · rintro ⟨-, h, hh⟩
      rw [show gM x = actTil V₀ V hV ⟨x.val, hM x.2⟩ from rfl]
      rw [show (⟨x.val, h⟩ : ↥(stabTil V₀ V)) = ⟨x.val, hM x.2⟩ from Subtype.ext rfl]
      exact Subgroup.mem_bot.1 hh
    · intro hx
      exact ⟨x.2, hM x.2, by rw [Subgroup.mem_bot]; exact hx⟩
  have hCnorm : (C.subgroupOf M).Normal := by
    rw [hCker]
    exact MonoidHom.normal_ker gM
  have hTC_sylow : IsSylowIn 2 (T ⊓ C) C := IsSylowIn.inf_normal hT hCM hCnorm
  have hcardTC : Nat.card ↥(T ⊓ C) = 2 ^ (Nat.card C).factorization 2 := hTC_sylow.card_eq
  have hQ2 : IsPGroup 2 Q := (s16c1_barSub_sylow hM hT).isPGroup.to_le hQ
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ2
  have hqfact : (Nat.card Q).factorization 2 = n := by
    rw [hn, Nat.factorization_pow_self Nat.prime_two]
  have hcardP₀fact : (Nat.card P₀).factorization 2 = (Nat.card C).factorization 2 + n := by
    rw [hcardP₀, Nat.factorization_mul (s16c1_card_ne_zero C) (s16c1_card_ne_zero Q),
      Finsupp.add_apply, hqfact]
  have hcardY' : Nat.card Y = 2 ^ ((Nat.card C).factorization 2 + n) := by
    rw [hcardY, hcardTC, hn, ← pow_add]
  have hcardYeq : Nat.card Y = 2 ^ (Nat.card P₀).factorization 2 := by
    rw [hcardY', hcardP₀fact]
  exact isSylowIn_of_card_eq inf_le_right hcardYeq

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
