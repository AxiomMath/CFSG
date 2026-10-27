module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Transport
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.CorN1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Lemma2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Lemma2Bridge
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row18HS
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row18Out
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Helpers

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Quasithin.SBd7
  CFSG.Quasithin.S153D
open scoped commutatorElement Pointwise

namespace Stellmacher.L3YC

section Row18

theorem row18_equiv_sl_of_isPSL {X : Type} [Group X] (h : IsPSL 3 2 1 X) :
    Nonempty (X ≃* Row18.SL32) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  exact ⟨e.trans (CFSG.QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two 3 K
    (by simpa using hK))⟩

theorem row18_data {Λ : Type} [Group Λ]
    (h : IsExt Λ (fun V _ => IsZ4Cubed V) (fun Y' _ => IsPSL 3 2 1 Y')) :
    Nat.card Λ = 10752 ∧ ∃ ψ : Λ →* Row18.SL32, Function.Surjective ψ := by
  obtain ⟨V, hVn, hV, hQ⟩ := h
  obtain ⟨e⟩ := hV
  obtain ⟨φ⟩ := row18_equiv_sl_of_isPSL hQ
  refine ⟨?_, φ.toMonoidHom.comp (QuotientGroup.mk' V),
    φ.surjective.comp (QuotientGroup.mk'_surjective V)⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup V
  rw [Nat.card_congr φ.toEquiv, Row18.card_SL32, Nat.card_congr e.toEquiv] at h1
  rw [h1]
  simp [Nat.card_eq_fintype_card]

variable {G : Type} [Group G] [Finite G]

theorem row18_false_of_rank
    (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3) (c12 : Concl15312Two Yp L)
    (hV : ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥) (hYY : Yp = Y153 Mc M)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    {t' : G} (ht'T : t' ∈ T) (ht'S : t' ∉ Sgp153 T V₁)
    (hswap : B6.conjSub t' (YL153 Yp L) = YC153 Yp L)
    (h4 : MS93.IsC134Case4Corr (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L)
    {Vc Vn : Subgroup G} {c₀ u₀ : G} (hlabel : (Vc = V₁ ∧ Vn = V₂) ∨ (Vc = V₂ ∧ Vn = V₁))
    (hc₀ : c₀ ∈ c134CQ (L ⊔ Sgp153 T V₁) L) (hc₀Vc : c₀ ∈ Vc) (hc₀1 : c₀ ≠ 1)
    (hu₀ : u₀ ∈ Vn) (hu₀1 : u₀ ≠ 1) (hu₀S : ∀ s ∈ Sgp153 T V₁, s * u₀ = u₀ * s)
    (hsw : t' * c₀ * t'⁻¹ = u₀)
    {H : Subgroup G} (hH : H = Subgroup.centralizer ({c₀} : Set G))
    (hSyl : IsSylowTwoOf (Sgp153 T V₁) H) {L₁ : Subgroup G} (hLL₁ : L ≤ L₁)
    (hN : (L₁.subgroupOf H).Normal) (hrk : CFSG.Open.pRank 3 H ≤ 2)
    (hrow : IsExt ↥(modO2Image H L) (fun V _ => IsZ4Cubed V) (fun Y' _ => IsPSL 3 2 1 Y') ∧
      IsSporadic .HS ↥(modO2Image H L₁)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, x, s₁, s₂, hyY, hy3, hxL, hx3, hxy, hxu, hxn, hs₁S, hs₂S, h2₁, h2₂, hs₁y, hs₁x, hs₂x,
      hs₂y, heYL, heL, he3, hx₂3, hcomm, hx₂c, hx₂nL, -, -, -, -, -, -⟩ :=
    exists_e_x2 h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4 hlabel hc₀ hc₀Vc hc₀1 hu₀ hu₀1
      hu₀S hsw
  have hperf : ⁅L, L⁆ = L := by
    obtain ⟨h, -⟩ := c.conc
    exact perfect_of_mem_cComp h
  have hLH : L ≤ H := by
    rw [hH]
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc₀).2 l hl
  have hSH : Sgp153 T V₁ ≤ H := hSyl.1
  have heH : t'⁻¹ * y * t' ∈ H := hLH heL
  have hx₂H : t'⁻¹ * x * t' ∈ H := by
    rw [hH, Subgroup.mem_centralizer_singleton_iff]
    have := hx₂c
    calc (t'⁻¹ * x * t') * c₀ = ((t'⁻¹ * x * t') * c₀ * (t'⁻¹ * x * t')⁻¹) * (t'⁻¹ * x * t') := by
          group
      _ = c₀ * (t'⁻¹ * x * t') := by rw [hx₂c]
  let mk : ↥H →* ↥H ⧸ CFSG.pCore 2 ↥H := QuotientGroup.mk' (CFSG.pCore 2 ↥H)
  set N : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) := modO2Image H L₁ with hNdef
  set Lb : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) := modO2Image H L with hLbdef
  have hNn : N.Normal := Subgroup.Normal.map hN _ (QuotientGroup.mk'_surjective _)
  have hLbN : Lb ≤ N := Subgroup.map_mono fun _ hx => hLL₁ hx
  have hN' : Nonempty (↥N ≃* CFSG.Blueprint.NativeSporadic.Carrier .HS) := hrow.2
  have heb : mk ⟨t'⁻¹ * y * t', heH⟩ ∈ Lb := ⟨⟨t'⁻¹ * y * t', heH⟩, heL, rfl⟩
  have he3b := Row18.orderOf_mk_eq_three heH he3
  have hx3b := Row18.orderOf_mk_eq_three hx₂H hx₂3
  have hcommb : mk ⟨t'⁻¹ * y * t', heH⟩ * mk ⟨t'⁻¹ * x * t', hx₂H⟩ =
      mk ⟨t'⁻¹ * x * t', hx₂H⟩ * mk ⟨t'⁻¹ * y * t', heH⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg mk (Subtype.ext hcomm)
  have hxbL : mk ⟨t'⁻¹ * x * t', hx₂H⟩ ∉ Subgroup.normalizer (Lb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    fun h => hx₂nL (mem_normalizer_of_mk_mem hSyl hSL hperf hLH hx₂H h)
  have hxN : mk ⟨t'⁻¹ * x * t', hx₂H⟩ ∈ N :=
    haveI := hNn
    lemma2_trivial_center hLbN (le_nine_modO2_of_pRank_le H hrk) (Row18.center_trivial_HS hN')
      (Row18.three_conj_inner_HS hN') heb he3b hx3b hcommb hxbL
  set Sb : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) := ((Sgp153 T V₁).subgroupOf H).map mk with hSbdef
  have hSb : IsSylowTwoOf Sb ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hSyl) mk
      (QuotientGroup.mk'_surjective _)
  have hSbL : Sb ≤ Subgroup.normalizer (Lb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    Row18.bar_le_normalizer hSL
  have hS₀ : IsSylowTwoOf (Sb ⊓ N) N :=
    B6.isSylowTwoOf_inf_normal hSb le_top (by rw [Subgroup.normalizer_eq_top (H := N)])
  obtain ⟨hLbc, ψ, hψ⟩ := row18_data hrow.1
  have hNc : Nat.card ↥N = 2 ^ 9 * 86625 := Row18.card_of_equiv_HS hN'
  have hS₀c : Nat.card ↥(Sb ⊓ N) = 2 ^ 9 :=
    Row18.card_eq_pow_of_isSylowTwoOf hS₀ hNc (by omega)
  have hS₀L : Sb ⊓ N ≤ Lb :=
    Row18.le_of_normalizes_of_card_dvd hS₀ hLbN (inf_le_left.trans hSbL)
      (by rw [hS₀c]; exact ⟨21, by rw [hLbc]; norm_num⟩)
  have hTS : T ≤ Subgroup.normalizer (Sgp153 T V₁ : Set G) := by
    have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
    exact Hyp153.T_le_normalizer_Sgp153 hh.hyp hh.decomp
  obtain ⟨Y, hY5, hSbY, hxbY⟩ := Row18.exists_bar_overgroup (H := H) (L := L)
    (S := Sgp153 T V₁) (t' := t') (x := x) Nat.prime_five (by norm_num) hSH hSyl.2.1 hSL
    (SBd5.not_five_dvd_of_isLnTwoQuot hq) hxL hx₂H
    (fun s hs => (Subgroup.mem_normalizer_iff.mp (hTS ht'T) s).mp hs)
  have hP : Y ⊓ N ≤ Lb :=
    Row18.hs_overgroup_le_of_psl32 hN' hLbN hS₀ hS₀L hLbc ψ hψ
      (le_inf (inf_le_left.trans hSbY) inf_le_right) inf_le_right
      (fun h => hY5 (h.trans (Subgroup.card_dvd_of_le inf_le_left)))
  exact hxbL (Subgroup.le_normalizer (hP ⟨hxbY, hxN⟩))

theorem row18_false
    (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3) (c12 : Concl15312Two Yp L)
    (hV : ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥) (hYY : Yp = Y153 Mc M)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    {t' : G} (ht'T : t' ∈ T) (ht'S : t' ∉ Sgp153 T V₁)
    (hswap : B6.conjSub t' (YL153 Yp L) = YC153 Yp L)
    (h4 : MS93.IsC134Case4Corr (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L)
    {Vc Vn : Subgroup G} {c₀ u₀ : G} (hlabel : (Vc = V₁ ∧ Vn = V₂) ∨ (Vc = V₂ ∧ Vn = V₁))
    (hc₀ : c₀ ∈ c134CQ (L ⊔ Sgp153 T V₁) L) (hc₀Vc : c₀ ∈ Vc) (hc₀1 : c₀ ≠ 1)
    (hu₀ : u₀ ∈ Vn) (hu₀1 : u₀ ≠ 1) (hu₀S : ∀ s ∈ Sgp153 T V₁, s * u₀ = u₀ * s)
    (hsw : t' * c₀ * t'⁻¹ = u₀) (hc₀2 : c₀ * c₀ = 1)
    {H : Subgroup G} (hH : H = Subgroup.centralizer ({c₀} : Set G))
    (hSyl : IsSylowTwoOf (Sgp153 T V₁) H) {L₁ : Subgroup G} (hLL₁ : L ≤ L₁)
    (hN : (L₁.subgroupOf H).Normal) (hev : evenRank G ≤ 2)
    (hrow : IsExt ↥(modO2Image H L) (fun V _ => IsZ4Cubed V) (fun Y' _ => IsPSL 3 2 1 Y') ∧
      IsSporadic .HS ↥(modO2Image H L₁)) : False := by
  have hloc : IsTwoLocal H := by
    rw [hH]
    exact CFSG.QuasithinUnique.Lin2.isTwoLocal_centralizer_of_sq_eq_one
      (by rw [pow_two]; exact hc₀2) hc₀1
  have hrk := CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
    (by norm_num) _ hloc
  exact row18_false_of_rank h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4 hlabel hc₀ hc₀Vc
    hc₀1 hu₀ hu₀1 hu₀S hsw hH hSyl hLL₁ hN (hrk.trans hev) hrow

end Row18

end Stellmacher.L3YC

end CFSG.Quasithin
