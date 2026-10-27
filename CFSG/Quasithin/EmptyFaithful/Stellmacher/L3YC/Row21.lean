module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Transport
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.CorN1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row18Common
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row21Case3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row21Contra
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.Setting

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Quasithin.SBd7
  CFSG.Quasithin.S153D
open scoped commutatorElement Pointwise

namespace Stellmacher.L3YC

section Row21

variable {G : Type} [Group G] [Finite G]

theorem row21_false_of_a36
    (h36 : A36ForSQTK) (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hQ : quasithinIsQTKECat G) (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
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
    (hSyl : IsSylowTwoOf (Sgp153 T V₁) H) {L₁ : Subgroup G} (hL₁ : L₁ ∈ cComp H) (hLL₁ : L ≤ L₁)
    (hN : (L₁.subgroupOf H).Normal)
    (hrow : ⁅(CFSG.oddCore ↥(modO2Image H L₁)).map (modO2Image H L₁).subtype,
          modO2Image H L₁⁆ ≠ ⊥ ∧
        modO2Image H L₁ = modO2Image H L ⊔
          (CFSG.oddCore ↥(modO2Image H L₁)).map (modO2Image H L₁).subtype ∧
        IsSL2 7 (↥(modO2Image H L₁) ⧸ CFSG.oddCore ↥(modO2Image H L₁)) ∧
        Nat.card ↥(modO2Image H L) = 336) : False := by
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
  have heH : t'⁻¹ * y * t' ∈ H := hLH heL
  have hx₂H : t'⁻¹ * x * t' ∈ H := by
    rw [hH, Subgroup.mem_centralizer_singleton_iff]
    calc (t'⁻¹ * x * t') * c₀ = ((t'⁻¹ * x * t') * c₀ * (t'⁻¹ * x * t')⁻¹) * (t'⁻¹ * x * t') := by
          group
      _ = c₀ * (t'⁻¹ * x * t') := by rw [hx₂c]
  let mk : ↥H →* ↥H ⧸ CFSG.pCore 2 ↥H := QuotientGroup.mk' (CFSG.pCore 2 ↥H)
  have hNn : (modO2Image H L₁).Normal := Subgroup.Normal.map hN _ (QuotientGroup.mk'_surjective _)
  have hLbN : modO2Image H L ≤ modO2Image H L₁ := Subgroup.map_mono fun _ hx => hLL₁ hx
  have heb : mk ⟨t'⁻¹ * y * t', heH⟩ ∈ modO2Image H L := ⟨⟨t'⁻¹ * y * t', heH⟩, heL, rfl⟩
  have he3b := Row18.orderOf_mk_eq_three heH he3
  have hcommb : mk ⟨t'⁻¹ * y * t', heH⟩ * mk ⟨t'⁻¹ * x * t', hx₂H⟩ =
      mk ⟨t'⁻¹ * x * t', hx₂H⟩ * mk ⟨t'⁻¹ * y * t', heH⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg mk (Subtype.ext hcomm)
  have hxbL : mk ⟨t'⁻¹ * x * t', hx₂H⟩ ∉
      Subgroup.normalizer (modO2Image H L : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    fun h => hx₂nL (mem_normalizer_of_mk_mem hSyl hSL hperf hLH hx₂H h)
  have hpc : pCoreOf 2 H ≠ ⊥ := by
    rw [hH]
    exact Stellmacher.CD.L3YC.pCoreOf_centralizer_ne_bot hc₀1 hc₀2
  have hSQ := sqtkHyp_quotient_of_pCoreOf_ne_bot hQ hs hnab hpc
  have hA := h36 _ hSQ (modO2Image H L₁) (modO2Image_mem_cComp hL₁)
  obtain ⟨hnat, hFO⟩ := Row21.natural_of_strong hA hrow.1 hrow.2.2.1
  have := hNn
  exact Row21.contra_of_natural hLbN hrow.2.2.2 hrow.2.1 hnat hFO heb he3b hcommb.symm hxbL

end Row21

end Stellmacher.L3YC

end CFSG.Quasithin
