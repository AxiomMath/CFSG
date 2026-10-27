module

public import CFSG.RankThree.PartOne.S11c.HNInvolutionNative
public import CFSG.RankThree.PartOne.S11c.HNSevenFix
public import CFSG.Sporadic.HNOddCore.Five
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.QuotientGraph
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.PrimitiveBase
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.Sporadic.ThSchreier.GlobalIndexBase
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate10090
public import Certificates.Certificate10090Base
public import Certificates.Certificate1021
public import Certificates.Certificate2051
public import Certificates.Certificate2053
public import Certificates.Certificate2056
public import Certificates.Certificate2057
public import Certificates.Certificate2058
public import Certificates.Certificate2130
public import Certificates.Certificate2135
public import Certificates.Certificate2136
public import Certificates.Certificate2139
public import Certificates.Certificate2140
public import Certificates.Certificate2145
public import Certificates.Certificate2309
public import Certificates.Certificate2311
public import Certificates.Certificate2313
public import Certificates.Certificate2314
public import Certificates.Certificate2315
public import Certificates.Certificate2317
public import Certificates.Certificate2323
public import Certificates.Certificate2324
public import Certificates.Certificate2325
public import Certificates.Certificate3085
public import Certificates.Certificate3085Base

public section

namespace CFSG.RankThree.PartOne.HNRed

open Subgroup CFSG CFSG.Assembly.LowTwoRank
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore

section Abstract

@[expose] def SevenCommuteConj (G : Type*) [Group G] : Prop :=
  ∀ f w : G, orderOf f = 5 → orderOf w = 5 → (∃ u : G, orderOf u = 7 ∧ f * u = u * f) →
    (∃ u : G, orderOf u = 7 ∧ w * u = u * w) → ∃ (g : G) (a : ℕ), w = g * f ^ a * g⁻¹

theorem sevenCommuteConj_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : SevenCommuteConj H) : SevenCommuteConj G := by
  intro f w hf hw ⟨u, hu, hfu⟩ ⟨v, hv, hwv⟩
  have key : ∀ z u : G, z * u = u * z → e z * e u = e u * e z := fun z u h => by
    rw [← map_mul, ← map_mul, h]
  obtain ⟨g, a, hga⟩ := h (e f) (e w) (by rw [MulEquiv.orderOf_eq]; exact hf)
    (by rw [MulEquiv.orderOf_eq]; exact hw)
    ⟨e u, by rw [MulEquiv.orderOf_eq]; exact hu, key f u hfu⟩
    ⟨e v, by rw [MulEquiv.orderOf_eq]; exact hv, key w v hwv⟩
  refine ⟨e.symm g, a, e.injective ?_⟩
  rw [map_mul, map_mul, map_pow, MulEquiv.apply_symm_apply, map_inv, MulEquiv.apply_symm_apply]
  exact hga

theorem card_centralizer_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    Nat.card (centralizer ({e x} : Set H)) = Nat.card (centralizer ({x} : Set G)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv e.symm.toEquiv fun y => ?_)
  simp only [mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
  constructor
  · intro h
    have := congrArg e.symm h
    simpa [map_mul] using this
  · intro h
    apply e.symm.injective
    simpa [map_mul] using h

theorem coverage_data_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) {f₀ : H}
    (hf₀ : orderOf f₀ = 5) (hf₀u : ∃ u : H, orderOf u = 7 ∧ f₀ * u = u * f₀)
    (hc₀ : Nat.card (centralizer ({f₀} : Set H)) = 630000) :
    orderOf (e.symm f₀) = 5 ∧ (∃ u : G, orderOf u = 7 ∧ e.symm f₀ * u = u * e.symm f₀) ∧
      Nat.card (centralizer ({e.symm f₀} : Set G)) = 630000 := by
  obtain ⟨u, hu, hfu⟩ := hf₀u
  refine ⟨by rw [MulEquiv.orderOf_eq]; exact hf₀,
    ⟨e.symm u, by rw [MulEquiv.orderOf_eq]; exact hu, ?_⟩, ?_⟩
  · rw [← map_mul, ← map_mul, hfu]
  · rw [← card_centralizer_of_mulEquiv e (e.symm f₀), MulEquiv.apply_symm_apply, hc₀]

theorem exists_order_seven_commute {G : Type} [Group G] [Finite G] {w : G} {M : Subgroup G}
    (hM : M ≤ centralizer ({w} : Set G)) (hmodel : StatedClassicalModel M .PSU 3 5 1) :
    ∃ u : G, orderOf u = 7 ∧ w * u = u * w := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hcard := (CFSG.RankThree.Classical.unitary_three_five_model M hmodel).1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := M) 7 (by rw [hcard]; norm_num)
  refine ⟨(x : G), by rw [Subgroup.orderOf_coe]; exact hx, ?_⟩
  exact (mem_centralizer_singleton_iff.1 (hM x.2)).symm

theorem fiveCoverage_of_data {G : Type} [Group G] [Finite G] (hcov : SevenCommuteConj G)
    (f₀ : G) (hf₀ : orderOf f₀ = 5) (hf₀u : ∃ u : G, orderOf u = 7 ∧ f₀ * u = u * f₀)
    (hc₀ : Nat.card (centralizer ({f₀} : Set G)) = 630000)
    {f t : G} {K Y : Subgroup G} (hw : IsNativeWitness f t K Y) :
    centralizer ({f} : Set G) ≤ zpowers f ⊔ K ∧
    ∀ w : G, orderOf w = 5 →
      (∃ K' : Subgroup G, K' ≤ centralizer ({w} : Set G) ∧
        StatedClassicalModel K' .PSU 3 5 1) →
      ∃ (g : G) (a : ℕ), w = g * f ^ a * g⁻¹ := by
  obtain ⟨hf5, hKf, -, hinf, -, -, hKmod, -⟩ := hw
  have hfu := exists_order_seven_commute hKf hKmod
  refine ⟨?_, fun w hw5 ⟨K', hK'w, hK'mod⟩ =>
    hcov f w hf5 hw5 hfu (exists_order_seven_commute hK'w hK'mod)⟩
  obtain ⟨g, a, hga⟩ := hcov f₀ f hf₀ hf5 hf₀u hfu
  have hcf : Nat.card (centralizer ({f} : Set G)) = 630000 := by
    rw [card_centralizer_eq_of_conj_pow hf₀ hf5 hga, hc₀]
  have hKcard := (CFSG.RankThree.Classical.unitary_three_five_model K hKmod).1
  have hL : zpowers f ⊔ K ≤ centralizer ({f} : Set G) := by
    refine sup_le ?_ hKf
    rw [zpowers_le]
    exact mem_centralizer_singleton_iff.2 rfl
  have h1 : Nat.card K ∣ Nat.card (zpowers f ⊔ K : Subgroup G) :=
    Subgroup.card_dvd_of_le le_sup_right
  have h2 : Nat.card (zpowers f ⊔ K : Subgroup G) ∣ Nat.card (centralizer ({f} : Set G)) :=
    Subgroup.card_dvd_of_le hL
  rw [hKcard] at h1
  rw [hcf] at h2
  obtain ⟨k, hk⟩ := h1
  rw [hk] at h2
  have hk5 : k ∣ 5 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 126000)
    (by simpa using h2)
  rcases (Nat.dvd_prime Nat.prime_five).1 hk5 with rfl | rfl
  · exfalso
    have : Finite ↥K := Finite.of_injective _ K.subtype_injective
    have hLeq : K = zpowers f ⊔ K := by
      refine Subgroup.eq_of_le_of_card_ge le_sup_right ?_
      rw [hk, hKcard]
    have hfK : f ∈ K := hLeq ▸ (le_sup_left : zpowers f ≤ zpowers f ⊔ K) (mem_zpowers f)
    have : f ∈ zpowers f ⊓ K := ⟨mem_zpowers f, hfK⟩
    rw [hinf] at this
    have hf1 : f = 1 := this
    rw [hf1, orderOf_one] at hf5
    omega
  · have : Finite ↥(centralizer ({f} : Set G)) :=
      Finite.of_injective _ (Subgroup.subtype_injective _)
    have hLeq : zpowers f ⊔ K = centralizer ({f} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hL (by rw [hcf, hk])
    exact hLeq.ge

theorem fiveCoverage_of_equiv {G H : Type} [Group G] [Group H] [Finite H] (e : G ≃* H)
    (hcov : SevenCommuteConj H) (f₀ : H) (hf₀ : orderOf f₀ = 5)
    (hf₀u : ∃ u : H, orderOf u = 7 ∧ f₀ * u = u * f₀)
    (hc₀ : Nat.card (centralizer ({f₀} : Set H)) = 630000)
    {f t : G} {K Y : Subgroup G} (hw : IsNativeWitness f t K Y) :
    centralizer ({f} : Set G) ≤ zpowers f ⊔ K ∧
    ∀ w : G, orderOf w = 5 →
      (∃ K' : Subgroup G, K' ≤ centralizer ({w} : Set G) ∧
        StatedClassicalModel K' .PSU 3 5 1) →
      ∃ (g : G) (a : ℕ), w = g * f ^ a * g⁻¹ := by
  have hfin : Finite G := Finite.of_equiv H e.symm.toEquiv
  obtain ⟨hf₁, hf₁u, hc₁⟩ := coverage_data_of_mulEquiv e hf₀ hf₀u hc₀
  exact fiveCoverage_of_data (sevenCommuteConj_of_mulEquiv e hcov) _ hf₁ hf₁u hc₁ hw

end Abstract

section Main

theorem hnFiveCoverage_holds :
    HNFiveCoverage := by
  intro f t K Y hw
  have hcovJ : SevenCommuteConj JH := fun _ _ hf hw hfu hwu =>
    exists_conj_pow_of_commute_seven_JH hf hw hfu hwu
  obtain ⟨hcomm, -, -, hfJ5, hcardC, hcardI, -⟩ := ctuc_hn_five_centralizer_perfect_factor
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := IJ) 7 (by rw [hcardI]; norm_num)
  have hfJu : ∃ u : JH, orderOf u = 7 ∧ fJ * u = u * fJ :=
    ⟨(x : JH), by rw [Subgroup.orderOf_coe]; exact hx, hcomm fJ (mem_zpowers fJ) x x.2⟩
  exact @fiveCoverage_of_equiv (Carrier .HN) (↥JH) (CFSG.Blueprint.NativeSporadic.carrierGroup .HN)
    inferInstance inferInstance hnEquivJ hcovJ fJ hfJ5 hfJu hcardC f t K Y hw

end Main

end CFSG.RankThree.PartOne.HNRed
