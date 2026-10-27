module

public import CFSG.OddTranspositions.PartThree.EightEight.ASNZTypes

import CFSG.OddTranspositions.PartThree.EightEight.StarOrbit
import CFSG.OddTranspositions.PartThree.EightSeven
import CFSG.OddTranspositions.PartThree.HalphaConj

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ
  CFSG.OddTranspositions.PartFour

variable {G : Type} [Group G] [Finite G] {D : Set G}

@[expose] def starO (hC : HypothesisC D) (x w y : G) (n : ℕ) (s : G) : Set G :=
  {o | o ∈ DalphaStar D hC.alpha ∧ Commute o ((x * y * w) ^ n * s)}

theorem commute_of_innerAt_of_not_innerAt (hC : HypothesisC D) {t d e : G} {ρ ρ' : Set G}
    (hρ : ρ ∈ blockClass hC.alpha) (hρ' : ρ' ∈ blockClass hC.alpha) (hd : d ∈ ρ) (he : e ∈ ρ')
    (hdt : Commute d t) (het : Commute e t) (hin : InnerAt D ρ t) (hout : ¬ InnerAt D ρ' t) :
    Commute d e := by
  by_contra hde
  exact hout ((innerAt_iff_of_not_commute hC hρ hρ' hd he hdt het hde).mpr hin)

theorem StandingAS.not_innerAt_of_mem_starGamma (h86 : Lemma8_6) (h87 : Theorem8_7)
    {hC : HypothesisC D} (hSt : StandingAS hC) {x w y : G} {n : ℕ}
    (hT : IsStarTriangle hC x w y) (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) {s c : G}
    (hs : s ∈ starN D hC.alpha (starSigma D x w y n)) (hc : c ∈ starGamma hC x w y n s)
    {ρ : Set G} (hρ : ρ ∈ blockClass hC.alpha) (hcρ : c ∈ ρ) :
    ¬ InnerAt D ρ ((x * y * w) ^ n * s) := by
  obtain ⟨ρs, hρs, hsρs⟩ := hs.2
  have hρs' : ρs ∈ blockClass hC.alpha := hρs.1
  have hout := hSt.not_innerAt_pow_mul_of_mem_block h86 h87 hT hn hord hs.1 hρs' hsρs
  obtain ⟨hk, -, -, -, -⟩ := hSt.orderOf_mul_of_mem_starGamma h86 h87 hT hn hord hs hc
  have hss := hC.setup.oddT.mul_self_eq_one hs.1.1.1
  have hcc := hC.setup.oddT.mul_self_eq_one (DalphaStar_subset hC.isBlock_alpha hc.1)
  have hodd : Odd (orderOf (s * c)) := by
    have e : (c * s)⁻¹ = s * c := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hss, inv_eq_of_mul_eq_one_right hcc]
    rwa [← e, orderOf_inv]
  obtain ⟨ℓ, hℓ, hℓs⟩ := CFSG.Timmesfeld.exists_conj_of_odd_orderOf_mul hss hcc hodd
  have hle : Subgroup.closure ({s, c} : Set G) ≤
      Subgroup.centralizer {(x * y * w) ^ n * s} := by
    rw [Subgroup.closure_le]
    rintro a (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    · exact (hs.1.1.2.mul_right (Commute.refl _)).eq
    · exact hc.2.2.eq
  have hℓτ : Commute ℓ ((x * y * w) ^ n * s) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hle hℓ)
  have hρeq : cimg ℓ ρs = ρ := eq_of_mem_of_mem_blockClass hC.isBlock_alpha
    (cimg_mem_blockClass_iff.mpr hρs') hρ ⟨c, ⟨s, hsρs, hℓs⟩, hcρ⟩
  rw [← hρeq, innerAt_cimg_iff_of_commute hC hρs' hℓτ]
  exact hout

theorem StandingAS.not_commute_of_commute_of_mem_starGamma (h86 : Lemma8_6) (h87 : Theorem8_7)
    {hC : HypothesisC D} (hSt : StandingAS hC) {x w y : G} {n : ℕ}
    (hT : IsStarTriangle hC x w y) (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) {s c p : G}
    (hs : s ∈ starN D hC.alpha (starSigma D x w y n)) (hc : c ∈ starGamma hC x w y n s)
    (hp : p ∈ DalphaStar D hC.alpha) (hps : Commute p s) : ¬ Commute p c := by
  intro hpc
  have hpH := mem_Halpha_of_mem_DalphaStar hp
  have hsH := mem_Halpha_of_mem_DalphaStar hs.2
  have hcH := mem_Halpha_of_mem_DalphaStar hc.1
  have hzH := mul_mul_pow_mem_Halpha hC hT.2.2.1 hT.2.2.2.1 hT.2.2.2.2.1 n
  have h1 := hSt.inv_mul_mem_starSocle_of_commute (starBar_mem_imageClass hC hp)
    (starBar_mem_imageClass hC hs.2) (starBar_commute hpH hsH hps)
  have h2 := hSt.inv_mul_mem_starSocle_of_commute (starBar_mem_imageClass hC hp)
    (starBar_mem_imageClass hC hc.1) (starBar_commute hpH hcH hpc)
  have h3 := hSt.inv_mul_mem_starSocle_of_commute_starBar_pow h86 h87 hT hn hord hs.2
    (starBar_commute hsH hzH hs.1.1.2)
  apply hc.2.1
  have h4 := Subgroup.mul_mem _ (Subgroup.mul_mem _ h3 (Subgroup.inv_mem _ h1)) h2
  have e : (starBar D hC.alpha x)⁻¹ * starBar D hC.alpha s *
      ((starBar D hC.alpha p)⁻¹ * starBar D hC.alpha s)⁻¹ *
        ((starBar D hC.alpha p)⁻¹ * starBar D hC.alpha c) =
      (starBar D hC.alpha x)⁻¹ * starBar D hC.alpha c := by group
  rwa [e] at h4

theorem StandingAS.not_innerAt_of_mem_starO (h86 : Lemma8_6) (h87 : Theorem8_7)
    {hC : HypothesisC D} (hSt : StandingAS hC) {x w y : G} {n : ℕ}
    (hT : IsStarTriangle hC x w y) (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) {s p : G}
    (hs : s ∈ starN D hC.alpha (starSigma D x w y n)) (hp : p ∈ starO hC x w y n s)
    {ρ : Set G} (hρ : ρ ∈ blockClass hC.alpha) (hpρ : p ∈ ρ) :
    ¬ InnerAt D ρ ((x * y * w) ^ n * s) := by
  intro hin
  obtain ⟨c, hc⟩ := hSt.starGamma_nonempty h86 h87 hT hn hord hs
  obtain ⟨ρs, hρs, hsρs⟩ := hs.2
  obtain ⟨ρc, hρc, hcρc⟩ := hc.1
  have hsτ : Commute s ((x * y * w) ^ n * s) := hs.1.1.2.mul_right (Commute.refl s)
  have hps : Commute p s := commute_of_innerAt_of_not_innerAt hC hρ hρs.1 hpρ hsρs hp.2 hsτ hin
    (hSt.not_innerAt_pow_mul_of_mem_block h86 h87 hT hn hord hs.1 hρs.1 hsρs)
  exact hSt.not_commute_of_commute_of_mem_starGamma h86 h87 hT hn hord hs hc hp.1 hps
    (commute_of_innerAt_of_not_innerAt hC hρ hρc.1 hpρ hcρc hp.2 hc.2.2 hin
      (hSt.not_innerAt_of_mem_starGamma h86 h87 hT hn hord hs hc hρc.1 hcρc))

omit [Finite G] in
theorem conj_mem_starO_of_mem_closure (hC : HypothesisC D) {x w y : G} {n : ℕ} {s m p : G}
    (hm : m ∈ Subgroup.closure (starO hC x w y n s)) (hp : p ∈ starO hC x w y n s) :
    m * p * m⁻¹ ∈ starO hC x w y n s := by
  have hle : Subgroup.closure (starO hC x w y n s) ≤
      Halpha D hC.alpha ⊓ Subgroup.centralizer {(x * y * w) ^ n * s} := by
    rw [Subgroup.closure_le]
    intro o ho
    exact ⟨Subgroup.subset_closure ho.1, Subgroup.mem_centralizer_singleton_iff.mpr ho.2.eq⟩
  obtain ⟨hmH, hmτ⟩ := hle hm
  have hmτ' : Commute m ((x * y * w) ^ n * s) := Subgroup.mem_centralizer_singleton_iff.mp hmτ
  refine ⟨(Subgroup.mem_set_normalizer_iff.mp (Halpha_le_normalizer hC.setup.normal hmH) p).mp
    hp.1, ?_⟩
  have h := hp.2.conj m
  rwa [show m * ((x * y * w) ^ n * s) * m⁻¹ = (x * y * w) ^ n * s by
    rw [hmτ'.eq, mul_inv_cancel_right]] at h

theorem StandingAS.conjOrbit_closure_starO_eq (h86 : Lemma8_6) (h87 : Theorem8_7)
    {hC : HypothesisC D} (hSt : StandingAS hC) {x w y : G} {n : ℕ}
    (hT : IsStarTriangle hC x w y) (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) {s : G}
    (hs : s ∈ starN D hC.alpha (starSigma D x w y n)) :
    conjOrbit (Subgroup.closure (starO hC x w y n s)) s = starO hC x w y n s := by
  set O := starO hC x w y n s with hO
  have hsO : s ∈ O := ⟨hs.2, hs.1.1.2.mul_right (Commute.refl s)⟩
  obtain ⟨c, hc⟩ := hSt.starGamma_nonempty h86 h87 hT hn hord hs
  have hcO : c ∈ O := ⟨hc.1, hc.2.2⟩
  have key : ∀ {a b : G}, a ∈ O → b ∈ O → ¬ Commute a b →
      ∃ g ∈ Subgroup.closure O, g * a * g⁻¹ = b := by
    intro a b ha hb hab
    have haD : a ∈ D := DalphaStar_subset hC.isBlock_alpha ha.1
    have hbD : b ∈ D := DalphaStar_subset hC.isBlock_alpha hb.1
    obtain ⟨g, hg, hgab⟩ := CFSG.Timmesfeld.exists_conj_of_odd_orderOf_mul
      (hC.setup.oddT.mul_self_eq_one haD) (hC.setup.oddT.mul_self_eq_one hbD)
      (hC.setup.oddT.odd_of_not_commute haD hbD hab)
    refine ⟨g, Subgroup.closure_mono ?_ hg, hgab⟩
    rintro e (rfl | rfl)
    · exact ha
    · exact hb
  apply Set.Subset.antisymm
  · rintro _ ⟨m, hm, rfl⟩
    exact conj_mem_starO_of_mem_closure hC hm hsO
  · intro p hp
    by_cases hps : Commute p s
    · have hpc := hSt.not_commute_of_commute_of_mem_starGamma h86 h87 hT hn hord hs hc hp.1 hps
      obtain ⟨g, hg, hgc⟩ := key hcO hp fun h => hpc h.symm
      have hsc : ¬ Commute s c := fun h =>
        (hSt.orderOf_and_pow_of_mem_starN h86 h87 hT hn hord hs hc.1 hc.2.1 hc.2.2).1 h.symm
      obtain ⟨g', hg', hg's⟩ := key hsO hcO hsc
      refine ⟨g * g', Subgroup.mul_mem _ hg hg', ?_⟩
      rw [← hgc, ← hg's]
      group
    · obtain ⟨g, hg, hgs⟩ := key hsO hp fun h => hps h.symm
      exact ⟨g, hg, hgs.symm⟩


theorem alpha_subset_starSigma (hC : HypothesisC D)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} {n : ℕ} (hT : IsStarTriangle hC x w y) (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) : hC.alpha ⊆ starSigma D x w y n := by
  intro u hu
  have hzH := mul_mul_pow_mem_Halpha hC hT.2.2.1 hT.2.2.2.1 hT.2.2.2.2.1 n
  refine ⟨⟨subset_of_mem_blockClass hC.setup.normal hC.isBlock_alpha
    (mem_blockClass_self _) hu, ?_⟩, notMem_conjOrbit_of_mem_alpha hC hne hT.1 hT.2.2.1
      hT.2.2.2.1 hT.2.2.2.2.1 hn hord hu⟩
  exact (show Commute ((x * y * w) ^ n) u from
    Subgroup.mem_centralizer_iff.mp (mem_centralizer_Halpha_of_mem hu) _ hzH).symm

theorem alpha_subset_starN (hC : HypothesisC D)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} {n : ℕ} (hT : IsStarTriangle hC x w y) (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {s : G}
    (hs : s ∈ starN D hC.alpha (starSigma D x w y n)) {ρ : Set G}
    (hρ : ρ ∈ blockClass hC.alpha) (hsρ : s ∈ ρ) :
    hC.alpha ⊆ starN D ρ (starSigma D x w y n) := by
  intro u hu
  refine ⟨alpha_subset_starSigma hC hne hT hn hord hu, ?_⟩
  obtain ⟨β, hβ, hsβ⟩ := hs.2
  have hβρ : β = ρ := eq_of_mem_of_mem_blockClass hC.isBlock_alpha hβ.1 hρ ⟨s, hsβ, hsρ⟩
  subst hβρ
  exact ⟨hC.alpha, mem_Dalpha_of_commute_mem hC.setup.normal hC.setup.oddT hC.isBlock_alpha
    hβ.1 (mem_blockClass_self _) hβ.2.2.1 hsβ hu ((mem_Dalpha_iff.mp hβ).2.2.2 u hu s hsβ).symm,
    hu⟩

theorem StandingAS.innerAt_of_mem_starN (h86 : Lemma8_6) (h87 : Theorem8_7)
    {hC : HypothesisC D} (hSt : StandingAS hC) {x w y : G} {n : ℕ}
    (hT : IsStarTriangle hC x w y) (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) {s : G}
    (hs : s ∈ starSigma D x w y n) {ρ : Set G} (hρ : ρ ∈ blockClass hC.alpha) (hsρ : s ∈ ρ)
    {v : G} (hv : v ∈ starN D ρ (starSigma D x w y n)) {ρv : Set G}
    (hρv : ρv ∈ blockClass hC.alpha) (hvρv : v ∈ ρv) :
    InnerAt D ρv ((x * y * w) ^ n * s) := by
  obtain ⟨β, hβ, hvβ⟩ := hv.2
  have hvs : Commute v s := ((mem_Dalpha_iff.mp hβ).2.2.2 s hsρ v hvβ).symm
  have hsρv : s ∉ ρv := by
    intro h
    have hρvρ : ρv = ρ := eq_of_mem_of_mem_blockClass hC.isBlock_alpha hρv hρ ⟨s, h, hsρ⟩
    have hβα : β ∈ blockClass hC.alpha := by
      rw [← blockClass_eq_of_mem_blockClass hρ]
      exact hβ.1
    exact hβ.2.2.1 (eq_of_mem_of_mem_blockClass hC.isBlock_alpha hβα hρ
      ⟨v, hvβ, hρvρ ▸ hvρv⟩)
  exact hSt.innerAt_pow_mul_of_commute_of_notMem h86 h87 hT hn hord hv.1 hs hvs hρv hvρv hsρv

theorem StandingAS.commute_of_mem_starO_of_mem_starN (h86 : Lemma8_6) (h87 : Theorem8_7)
    {hC : HypothesisC D} (hSt : StandingAS hC) {x w y : G} {n : ℕ}
    (hT : IsStarTriangle hC x w y) (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) {s : G}
    (hs : s ∈ starN D hC.alpha (starSigma D x w y n)) {ρ : Set G}
    (hρ : ρ ∈ blockClass hC.alpha) (hsρ : s ∈ ρ) {o v : G} (ho : o ∈ starO hC x w y n s)
    (hv : v ∈ starN D ρ (starSigma D x w y n)) : Commute o v := by
  obtain ⟨ρo, hρo, hoρo⟩ := ho.1
  obtain ⟨ρv, hρv, hvρv⟩ :=
    exists_mem_blockClass_of_mem hC.setup.isClass hC.isBlock_alpha hv.1.1.1
  obtain ⟨β, hβ, hvβ⟩ := hv.2
  have hvs : Commute v s := ((mem_Dalpha_iff.mp hβ).2.2.2 s hsρ v hvβ).symm
  exact (commute_of_innerAt_of_not_innerAt hC hρv hρo.1 hvρv hoρo (hv.1.1.2.mul_right hvs) ho.2
    (hSt.innerAt_of_mem_starN h86 h87 hT hn hord hs.1 hρ hsρ hv hρv hvρv)
    (hSt.not_innerAt_of_mem_starO h86 h87 hT hn hord hs ho hρo.1 hoρo)).symm

end CFSG.OddTranspositions.PartThree.EightEight

end
