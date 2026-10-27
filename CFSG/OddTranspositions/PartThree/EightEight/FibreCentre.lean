module

public import CFSG.Timmesfeld.Bridge.Asc72Basic
public import CFSG.OddTranspositions.HypothesisC
public import CFSG.OddTranspositions.Blocks

import CFSG.GroupTheory.InvolutionClassDerived
import CFSG.OddTranspositions.PartThree.EightEight.Fibres
import CFSG.OddTranspositions.PartThree.Nine.ThreeSplit
import CFSG.OddTranspositions.PartFour.LineTransport
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.Bridge.Asc72Triangle
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.Asc72
open CFSG.GroupTheory

variable {X : Type} [Group X] [Finite X] {E : Set X}

omit [Finite X] in
theorem notMem_derivedSeries_two_of_derivedSeries_ne (hS : Setup X E)
    (hne : derivedSeries X 1 ≠ derivedSeries X 2) {x : X} (hx : x ∈ E) :
    x ∉ derivedSeries X 2 := by
  intro hx2
  have hEsub : E ⊆ derivedSeries X 2 := by
    intro y hy
    obtain ⟨g, rfl⟩ := isConj_iff.mp (hS.isConj hx hy)
    exact (derivedSeries_normal X 2).conj_mem x hx2 g
  have htop : (⊤ : Subgroup X) ≤ derivedSeries X 2 := by
    rw [← hS.gen]
    rw [Subgroup.closure_le]
    exact hEsub
  have h2top : derivedSeries X 2 = ⊤ := le_antisymm le_top htop
  have h21 : derivedSeries X 2 ≤ derivedSeries X 1 := by
    rw [derivedSeries_succ X 1]
    exact Subgroup.commutator_le_self _
  have h1top : derivedSeries X 1 = ⊤ := le_antisymm le_top (htop.trans h21)
  exact hne (by rw [h1top, h2top])

omit [Finite X] in
theorem mem_derivedSeries_two_of_mem_center (hS : Setup X E)
    (hne : derivedSeries X 1 ≠ derivedSeries X 2) {c : X} (hc : c ∈ Subgroup.center X)
    (hc2 : c * c = 1) : c ∈ derivedSeries X 2 := by
  let π : X →* X ⧸ derivedSeries X 2 := QuotientGroup.mk' (derivedSeries X 2)
  let T : Set (X ⧸ derivedSeries X 2) := π '' E
  have hneT : ∃ t ∈ T, ∃ t' ∈ T, t ≠ t' := by
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_mk_ne_of_derivedSeries_ne hS hne
    exact ⟨π x, ⟨x, hx, rfl⟩, π y, ⟨y, hy, rfl⟩, hxy⟩
  have hconj : ∀ t ∈ T, ∀ t' ∈ T, IsConj t t' := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact MonoidHom.map_isConj π (hS.isConj hx hy)
  have hsq : ∀ t ∈ T, t * t = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact mk_mul_self_eq_one_of_mem hS hx
  have hgen : Subgroup.closure T = ⊤ := closure_mk_image_eq_top hS
  have hder : derivedSeries (X ⧸ derivedSeries X 2) 2 = ⊥ :=
    derivedSeries_two_quotient_eq_bot
  have hodd : ∀ t ∈ T, ∀ t' ∈ T, Odd (orderOf (t * t')) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul]
    exact odd_orderOf_mk_mul hS hx hy
  have hcπ : π c ∈ Subgroup.center (X ⧸ derivedSeries X 2) :=
    Subgroup.map_center_le_center (f := π) (QuotientGroup.mk'_surjective _)
      (Subgroup.mem_map.mpr ⟨c, hc, rfl⟩)
  have hcπ2 : π c * π c = 1 := by rw [← map_mul, hc2, map_one]
  have hπc : π c = 1 :=
    eq_one_of_mem_center_of_isConj hneT hconj hsq hgen hder hodd hcπ hcπ2
  exact (QuotientGroup.eq_one_iff c).mp hπc

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem commute_of_mem_of_mem_DalphaStar {β : Set G} {a x : G} (ha : a ∈ β)
    (hx : x ∈ DalphaStar D β) : Commute a x := by
  obtain ⟨γ, hγ, hxγ⟩ := hx
  exact (mem_Dalpha_iff.mp hγ).2.2.2 a ha x hxγ

omit [Finite G] in
theorem derivedSeries_Halpha_ne_of_mem_blockClass (hC : HypothesisC D)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {ρ : Set G} (hρ : ρ ∈ blockClass hC.alpha) :
    derivedSeries (Halpha D ρ) 1 ≠ derivedSeries (Halpha D ρ) 2 := by
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hρ
  have hH : Halpha D ρ = (Halpha D hC.alpha).map (MulAut.conj g).toMonoidHom := by
    rw [hg]
    exact CFSG.OddTranspositions.PartFour.Halpha_cimg hC.setup.normal g hC.alpha
  let e : Halpha D hC.alpha ≃* Halpha D ρ :=
    ((Halpha D hC.alpha).equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hH.symm)
  intro heq
  apply hne
  have h1 : (derivedSeries (Halpha D hC.alpha) 1).map (e : Halpha D hC.alpha →* Halpha D ρ)
      = derivedSeries (Halpha D ρ) 1 := map_derivedSeries_eq e.surjective 1
  have h2 : (derivedSeries (Halpha D hC.alpha) 2).map (e : Halpha D hC.alpha →* Halpha D ρ)
      = derivedSeries (Halpha D ρ) 2 := map_derivedSeries_eq e.surjective 2
  exact Subgroup.map_injective e.injective (by rw [h1, h2, heq])

@[expose] def fibreSubgroup (D ρ : Set G) : Subgroup G :=
  (derivedSeries (Halpha D ρ) 2).map (Halpha D ρ).subtype

omit [Finite G] in
theorem conj_mem_fibreSubgroup (D ρ : Set G) {h m : G} (hh : h ∈ Halpha D ρ)
    (hm : m ∈ fibreSubgroup D ρ) : h * m * h⁻¹ ∈ fibreSubgroup D ρ := by
  rw [fibreSubgroup, Subgroup.mem_map] at hm ⊢
  obtain ⟨k, hk, rfl⟩ := hm
  exact ⟨⟨h, hh⟩ * k * ⟨h, hh⟩⁻¹,
    (derivedSeries_normal (Halpha D ρ) 2).conj_mem k hk ⟨h, hh⟩, rfl⟩

omit [Finite G] in
theorem mem_fibreSubgroup_iff {D ρ : Set G} {h : G} (hh : h ∈ Halpha D ρ) :
    h ∈ fibreSubgroup D ρ ↔ (⟨h, hh⟩ : Halpha D ρ) ∈ derivedSeries (Halpha D ρ) 2 := by
  constructor
  · intro hm
    rw [fibreSubgroup, Subgroup.mem_map] at hm
    obtain ⟨k, hk, hkeq⟩ := hm
    have hk' : k = ⟨h, hh⟩ := Subtype.ext hkeq
    simpa [hk'] using hk
  · intro hk
    exact Subgroup.mem_map.mpr ⟨⟨h, hh⟩, hk, rfl⟩

theorem notMem_fibreSubgroup (hC : HypothesisC D)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {ρ : Set G} (hρ : ρ ∈ blockClass hC.alpha) {d : G} (hd : d ∈ DalphaStar D ρ) :
    d ∉ fibreSubgroup D ρ := by
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hρ
  let hC' : HypothesisC D := hC.conj g
  have hα : hC'.alpha = ρ := by
    rw [show hC'.alpha = CFSG.OddTranspositions.cimg g hC.alpha from
      HypothesisC.conj_alpha hC g, hg]
  rw [← hα]
  intro hdm
  have hρ' : hC'.alpha ∈ blockClass hC.alpha := hα.symm ▸ hρ
  have hne' := derivedSeries_Halpha_ne_of_mem_blockClass hC hne hρ'
  have hd' : d ∈ DalphaStar D hC'.alpha := by rw [hα]; exact hd
  have hdH : d ∈ Halpha D hC'.alpha := Subgroup.subset_closure hd'
  have hdm' : (⟨d, hdH⟩ : Halpha D hC'.alpha) ∈ derivedSeries (Halpha D hC'.alpha) 2 :=
    (mem_fibreSubgroup_iff hdH).mp hdm
  exact notMem_derivedSeries_two_of_derivedSeries_ne
    (CFSG.OddTranspositions.PartThree.Nine.setup_DstarH hC') hne' hd' hdm'

theorem mul_mem_fibreSubgroup_of_commute (hC : HypothesisC D) {ρ : Set G}
    (hρ : ρ ∈ blockClass hC.alpha) {p q : G} (hp : p ∈ DalphaStar D ρ)
    (hq : q ∈ DalphaStar D ρ) (hpq : Commute p q) : p * q ∈ fibreSubgroup D ρ := by
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hρ
  let hC' : HypothesisC D := hC.conj g
  have hα : hC'.alpha = ρ := by
    rw [show hC'.alpha = CFSG.OddTranspositions.cimg g hC.alpha from
      HypothesisC.conj_alpha hC g, hg]
  rw [← hα]
  have hp' : p ∈ DalphaStar D hC'.alpha := by rw [hα]; exact hp
  have hq' : q ∈ DalphaStar D hC'.alpha := by rw [hα]; exact hq
  have hp_H : p ∈ Halpha D hC'.alpha := Subgroup.subset_closure hp'
  have hq_H : q ∈ Halpha D hC'.alpha := Subgroup.subset_closure hq'
  have hcomm : Commute (⟨p, hp_H⟩ : Halpha D hC'.alpha) ⟨q, hq_H⟩ :=
    (commute_iff_eq _ _).2 (Subtype.ext hpq.eq)
  have hmul := mul_mem_derivedSeries_two_of_commute
    (CFSG.OddTranspositions.PartThree.Nine.setup_DstarH hC') hp' hq' hcomm
  rw [mem_fibreSubgroup_iff (Subgroup.mul_mem _ hp_H hq_H)]
  simpa using hmul

theorem mem_fibreSubgroup_of_forall_commute (hC : HypothesisC D)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {ρ : Set G} (hρ : ρ ∈ blockClass hC.alpha) {c : G} (hc : c ∈ Halpha D ρ)
    (hcd : ∀ d ∈ DalphaStar D ρ, Commute c d) (hc2 : c * c = 1) :
    c ∈ fibreSubgroup D ρ := by
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hρ
  let hC' : HypothesisC D := hC.conj g
  have hα : hC'.alpha = ρ := by
    rw [show hC'.alpha = CFSG.OddTranspositions.cimg g hC.alpha from
      HypothesisC.conj_alpha hC g, hg]
  rw [← hα]
  have hc' : c ∈ Halpha D hC'.alpha := by rw [hα]; exact hc
  have hρ' : hC'.alpha ∈ blockClass hC.alpha := hα.symm ▸ hρ
  have hne' := derivedSeries_Halpha_ne_of_mem_blockClass hC hne hρ'
  have hcd' : ∀ t ∈ DalphaStar D hC'.alpha, Commute c t := by
    intro t ht
    exact hcd t (by rw [hα] at ht; exact ht)
  have hcent : c ∈ Subgroup.centralizer (Halpha D hC'.alpha : Set G) := by
    rw [Halpha, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro t ht
    exact (hcd' t ht).symm.eq
  have hcenter : (⟨c, hc'⟩ : Halpha D hC'.alpha) ∈ Subgroup.center (Halpha D hC'.alpha) := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hcent (x : G) x.2
  have hc2' : (⟨c, hc'⟩ : Halpha D hC'.alpha) * ⟨c, hc'⟩ = 1 := Subtype.ext hc2
  have hm := mem_derivedSeries_two_of_mem_center
    (CFSG.OddTranspositions.PartThree.Nine.setup_DstarH hC') hne' hcenter hc2'
  exact (mem_fibreSubgroup_iff hc').mpr hm

end CFSG.OddTranspositions.PartThree.EightEight

end
