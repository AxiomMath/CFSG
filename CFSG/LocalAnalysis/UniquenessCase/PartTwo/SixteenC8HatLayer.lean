module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CatalogueThreePrime
import CFSG.Quasithin.H13.NQCatSubnormalCore
import CFSG.Blueprint.LieModelAPI
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Suzuki
import CFSG.Quasithin.Background.C2Eleven
import CFSG.LargeExtraspecial.S5Comp
import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Foundations.KCoreOpen
public import CFSG.LieType.Simplicity.Suzuki

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem c8h_openIsKGroup {X : Type} [Group X] (h : CFSG.IsKGroup X) :
    CFSG.Open.IsKGroup X :=
  fun K L _ _ hsimple _ => h K (L.subgroupOf K) hsimple

private lemma c8h_sz_facts {X : Type} [Group X] {n : ℕ} (hn : UC22.IsSz X n)
    (hq : CFSG.Open.IsQuasisimple X) :
    Subgroup.center X = ⊥ ∧ ∃ x : X, orderOf x = 5 := by
  have hs : CFSG.Blueprint.SuzukiModel X 2 n := (CFSG.Blueprint.LieModel.suzukiModel hn).2
  obtain ⟨a, -, ⟨e⟩⟩ :=
    CFSG.LieType.Simplicity.exists_mulEquiv_suzukiMatrixGroup_of_suzukiModel hs
  refine ⟨?_, ⟨e.symm (CFSG.BenderSuzuki.lemma115_suzukiStandardElement a), ?_⟩⟩
  · haveI : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_2b2_simplicity X 2 n hs).2
    rcases (inferInstance : (Subgroup.center X).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2
      haveI : Subsingleton (X ⧸ (⊤ : Subgroup X)) := QuotientGroup.subsingleton_quotient_top
      haveI : Subsingleton (X ⧸ Subgroup.center X) :=
        (QuotientGroup.quotientMulEquivOfEq h).injective.subsingleton
      exact not_subsingleton (X ⧸ Subgroup.center X) inferInstance
  · rw [MulEquiv.orderOf_eq, CFSG.BenderSuzuki.lemma115_suzuki_standard_order_five]

private lemma c8h_coe_not_mem_centerOf {G : Type} [Group G] {H : Subgroup G}
    (hc : Subgroup.center ↥H = ⊥) {x : ↥H} (hx : orderOf x ≠ 1) :
    (x : G) ∉ centerOf H := by
  intro h
  have hxcent : x ∈ Subgroup.center ↥H := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp h.2 (z : G) z.2
  rw [hc, Subgroup.mem_bot] at hxcent
  exact hx (by rw [hxcent, orderOf_one])

private theorem c8h_component_isSz {Γ : Type} [Group Γ] [Finite Γ] (hK : CFSG.IsKGroup Γ)
    (hSz : Inputs1719.K_CatalogueThreePrimeSz) (h2 : CFSG.pCore 2 Γ = ⊥)
    {J : Subgroup Γ} (hJ : CFSG.Open.IsComponentOf J (CFSG.pPrimeCore 3 Γ)) :
    ∃ n : ℕ, UC22.IsSz ↥J n := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3I : ¬ 3 ∣ Nat.card ↥(CFSG.pPrimeCore 3 Γ) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card
  have hJI : J ≤ CFSG.pPrimeCore 3 Γ := hJ.1
  have hJsn : J.IsSubnormal :=
    CFSG.Open.IsSubnormal.mathlib hJ.2.1 (Subgroup.Normal.isSubnormal inferInstance)
  have h3J : 3 ∉ UC22.piSet (⊤ : Subgroup ↥J) := by
    intro h
    simp only [UC22.piSet, Set.mem_setOf_eq] at h
    obtain ⟨-, hdvd⟩ := h
    rw [Subgroup.card_top] at hdvd
    exact h3I (hdvd.trans (Subgroup.card_dvd_of_le hJI))
  have hK' : CFSG.Open.IsKGroup Γ := c8h_openIsKGroup hK
  have hKJ : CFSG.Open.IsKGroup ↥J := hK'.subgroup J
  obtain ⟨n, hn⟩ := hSz ↥J hKJ hJ.2.2 h3J
  have hbot : CFSG.pCore 2 ↥J = ⊥ := by
    have hle := CFSG.Quasithin.H13.NQCat.map_pCore_le_pCore_of_isSubnormal' (p := 2) hJsn
    rw [h2, le_bot_iff] at hle
    exact (Subgroup.map_eq_bot_iff_of_injective (CFSG.pCore 2 ↥J) J.subtype_injective).1 hle
  exact ⟨n, CFSG.Blueprint.LieModel.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot) hn⟩

theorem c8h_layer_components {Γ : Type} [Group Γ] [Finite Γ] (hK : IsKGroup Γ)
    (hSz : Inputs1719.K_CatalogueThreePrimeSz) (h2 : CFSG.pCore 2 Γ = ⊥)
    (h5 : pRank 5 (⊤ : Subgroup Γ) ≤ 2) :
    (∀ J : Subgroup Γ, IsComponentOf J (CFSG.pPrimeCore 3 Γ) → ∃ n : ℕ, IsSz ↥J n) ∧
      {J : Subgroup Γ | IsComponentOf J (CFSG.pPrimeCore 3 Γ)}.ncard ≤ 2 := by
  constructor
  · intro J hJ
    exact c8h_component_isSz hK hSz h2 hJ
  · by_contra hcon
    haveI : Finite (Subgroup Γ) := Finite.of_injective _ SetLike.coe_injective
    obtain ⟨J₁, J₂, J₃, h₁, h₂, h₃, h12, h13, h23⟩ :=
      (Set.two_lt_ncard_iff (Set.toFinite _)).1 (not_le.1 hcon)
    obtain ⟨n₁, hn₁⟩ := c8h_component_isSz hK hSz h2 h₁
    obtain ⟨n₂, hn₂⟩ := c8h_component_isSz hK hSz h2 h₂
    obtain ⟨n₃, hn₃⟩ := c8h_component_isSz hK hSz h2 h₃
    obtain ⟨hc₁, x₁, hx₁⟩ := c8h_sz_facts hn₁ h₁.2.2
    obtain ⟨hc₂, x₂, hx₂⟩ := c8h_sz_facts hn₂ h₂.2.2
    obtain ⟨hc₃, x₃, hx₃⟩ := c8h_sz_facts hn₃ h₃.2.2
    have ho₁ : orderOf (x₁ : Γ) = 5 := by rw [Subgroup.orderOf_coe, hx₁]
    have ho₂ : orderOf (x₂ : Γ) = 5 := by rw [Subgroup.orderOf_coe, hx₂]
    have ho₃ : orderOf (x₃ : Γ) = 5 := by rw [Subgroup.orderOf_coe, hx₃]
    have hc₁' : (x₁ : Γ) ∉ centerOf J₁ :=
      c8h_coe_not_mem_centerOf hc₁ (by rw [hx₁]; norm_num)
    have hc₂' : (x₂ : Γ) ∉ centerOf J₂ :=
      c8h_coe_not_mem_centerOf hc₂ (by rw [hx₂]; norm_num)
    have hc₃' : (x₃ : Γ) ∉ centerOf J₃ :=
      c8h_coe_not_mem_centerOf hc₃ (by rw [hx₃]; norm_num)
    have hcomm₁₂ := CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne h₁ h₂ h12
    have hcomm₁₃ := CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne h₁ h₃ h13
    have hcomm₂₃ := CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne h₂ h₃ h23
    have h3 := CFSG.Quasithin.C2Eleven.three_le_pRank (p := 5) (H := ⊤) (by norm_num)
      hcomm₁₂ hcomm₁₃ hcomm₂₃ le_top le_top le_top
      x₁.2 x₂.2 x₃.2 ho₁ ho₂ ho₃ hc₁' hc₂' hc₃'
    have h5' : CFSG.Open.pRank 5 (⊤ : Subgroup Γ) ≤ 2 := by
      rwa [← CFSG.SectionRank.pRank_coe_eq_openPRank]
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
