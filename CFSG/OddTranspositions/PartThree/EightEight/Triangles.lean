module

public import CFSG.OddTranspositions.HypothesisC
public import CFSG.Timmesfeld.Bridge.Asc72Triangle

import CFSG.OddTranspositions.PartThree.Nine.ThreeBlocks
import CFSG.OddTranspositions.TheoremTwo.AalphaNonempty
import CFSG.OddTranspositions.PartThree.EightEight.Fibres
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.OddTranspositions
open CFSG.OddTranspositions.PartThree.Nine
open CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem isMaxBlock_of_mem_blockClass (hC : HypothesisC D) {β : Set G}
    (hβ : β ∈ blockClass hC.alpha) : IsMaxBlock D β := by
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hβ
  rw [hg]
  have h := (hC.conj g).isMaxBlock_alpha
  rwa [HypothesisC.conj_alpha] at h

theorem mem_perp_iff_exists_commute (hC : HypothesisC D) {β ω : Set G}
    (hβ : β ∈ blockClass hC.alpha) (hω : ω ∈ blockClass hC.alpha) {x : G} (hx : x ∈ β) :
    ω ∈ perp D β ↔ ∃ e ∈ ω, Commute e x := by
  constructor
  · intro hωβ
    rcases mem_perp_iff.mp hωβ with hωD | rfl
    · obtain ⟨e, he⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hω
      exact ⟨e, he, (hωD.2.2.2 x hx e he).symm⟩
    · exact ⟨x, hx, Commute.refl x⟩
  · rintro ⟨e, he, hex⟩
    have heD : e ∈ D := subset_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hω he
    rcases mem_block_or_DalphaStar_of_commute hC hβ hx heD hex.symm with heβ | ⟨γ, hγ, heγ⟩
    · exact mem_perp_iff.mpr (Or.inr (eq_of_mem_of_mem_blockClass hC.isBlock_alpha hω hβ
        ⟨e, he, heβ⟩))
    · refine mem_perp_iff.mpr (Or.inl ?_)
      have hγc : γ ∈ blockClass hC.alpha :=
        mem_blockClass_of_mem_blockClass (mem_blockClass_comm.mp hβ) hγ.1
      rw [eq_of_mem_of_mem_blockClass hC.isBlock_alpha hω hγc ⟨e, he, heγ⟩]
      exact hγ

theorem eq_of_forall_commute_iff (hC : HypothesisC D) {β β' : Set G}
    (hβ : β ∈ blockClass hC.alpha) (hβ' : β' ∈ blockClass hC.alpha) {x x' : G}
    (hx : x ∈ β) (hx' : x' ∈ β') (h : ∀ e ∈ D, Commute e x ↔ Commute e x') : β = β' := by
  have hclass : ∀ {ω : Set G}, ω ∈ perp D β → ω ∈ blockClass hC.alpha := by
    intro ω hω
    rcases mem_perp_iff.mp hω with h | rfl
    · exact mem_blockClass_of_mem_blockClass (mem_blockClass_comm.mp hβ) h.1
    · exact hβ
  have hclass' : ∀ {ω : Set G}, ω ∈ perp D β' → ω ∈ blockClass hC.alpha := by
    intro ω hω
    rcases mem_perp_iff.mp hω with h | rfl
    · exact mem_blockClass_of_mem_blockClass (mem_blockClass_comm.mp hβ') h.1
    · exact hβ'
  have hperp : perp D β = perp D β' := by
    ext ω
    constructor
    · intro hω
      have hωc : ω ∈ blockClass hC.alpha := hclass hω
      rw [mem_perp_iff_exists_commute hC hβ' hωc hx']
      rw [mem_perp_iff_exists_commute hC hβ hωc hx] at hω
      obtain ⟨e, he, hex⟩ := hω
      exact ⟨e, he, (h e (subset_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hωc he)).mp
        hex⟩
    · intro hω
      have hωc : ω ∈ blockClass hC.alpha := hclass' hω
      rw [mem_perp_iff_exists_commute hC hβ hωc hx]
      rw [mem_perp_iff_exists_commute hC hβ' hωc hx'] at hω
      obtain ⟨e, he, hex⟩ := hω
      exact ⟨e, he, (h e (subset_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hωc he)).mpr
        hex⟩
  have hβ'V : β' ∈ Valpha D β :=
    mem_Valpha_iff.mpr ⟨mem_blockClass_of_mem_blockClass hβ hβ', hperp.symm⟩
  have hmax : IsMaxBlock D β := isMaxBlock_of_mem_blockClass hC hβ
  have hproper : Valpha D β ≠ blockClass β := by
    intro hV
    obtain ⟨γ, hγ⟩ := Aalpha_nonempty hC.setup
      (isBlock_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hβ)
    have hγV : γ ∈ Valpha D β := by rw [hV]; exact hγ.1
    have hγp : γ ∈ perp D β := by
      rw [← (mem_Valpha_iff.mp hγV).2]
      exact mem_perp_iff.mpr (Or.inr rfl)
    exact (mem_Aalpha_iff.mp hγ).2 hγp
  have hsingle : Valpha D β = {β} :=
    Valpha_eq_singleton_of_isMaxBlock_of_ne hC.setup.normal hmax hproper
  have hβ'eq : β' = β := by simpa [hsingle] using hβ'V
  exact hβ'eq.symm

theorem not_odd_orderOf_of_derivedSeries_ne (hC : HypothesisC D)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (hx : x ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha)
    (ht : IsTriangle D x w y) :
    ¬ Odd (orderOf (x * y * w)) := by
  intro hodd
  have hxStar : x ∈ DalphaStar D hC.alpha := hx
  obtain ⟨hxyD, hcomm⟩ := ht.commute_iff_of_odd hC.setup hodd
  obtain ⟨β, hβ, hxβ⟩ := hx
  obtain ⟨β', hβ', hxyβ'⟩ :=
    exists_mem_blockClass_of_mem hC.setup.isClass hC.isBlock_alpha hxyD
  have hβeq : β = β' := eq_of_forall_commute_iff hC hβ.1 hβ' hxβ hxyβ' hcomm
  have hxyStar : x * y ∈ DalphaStar D hC.alpha :=
    ⟨β, hβ, by rw [hβeq]; exact hxyβ'⟩
  let H := Halpha D hC.alpha
  let xH : H := ⟨x, Subgroup.subset_closure hxStar⟩
  let yH : H := ⟨y, Subgroup.subset_closure hy⟩
  let zH : H := ⟨x * y, Subgroup.subset_closure hxyStar⟩
  have hcommH : Commute xH yH := Subtype.ext ht.2.2.2.2.1.eq
  have hxH : xH ∈ DstarH hC := (mem_DstarH_iff hC).mpr hxStar
  have hyH : yH ∈ DstarH hC := (mem_DstarH_iff hC).mpr hy
  have hmul : xH * yH ∈ derivedSeries H 2 :=
    mul_mem_derivedSeries_two_of_commute (setup_DstarH hC) hxH hyH hcommH
  have hzH : zH ∈ derivedSeries H 2 := by
    have hz_eq : zH = xH * yH := Subtype.ext rfl
    rwa [hz_eq]
  have hzDstar : zH ∈ DstarH hC := (mem_DstarH_iff hC).mpr hxyStar
  have hDsub : DstarH hC ⊆ derivedSeries H 2 := by
    obtain ⟨d₀, hclass⟩ := DstarH_isClass hC
    intro g hg
    have hg' : IsConj d₀ g := by
      rw [hclass] at hg
      exact hg
    have hzclass : IsConj d₀ zH := by
      have hz' : zH ∈ DstarH hC := hzDstar
      rwa [hclass] at hz'
    obtain ⟨c, hc⟩ := isConj_iff.mp ((IsConj.symm hzclass).trans hg')
    rw [← hc]
    exact (derivedSeries_normal H 2).conj_mem zH hzH c
  have htop2 : derivedSeries H 2 = ⊤ :=
    top_le_iff.mp (DstarH_closure_eq_top hC ▸ (Subgroup.closure_le (derivedSeries H 2)).mpr hDsub)
  have h21 : derivedSeries H 2 ≤ derivedSeries H 1 := by
    rw [derivedSeries_succ H 1]
    exact Subgroup.commutator_le_self _
  have htop1 : derivedSeries H 1 = ⊤ := le_antisymm le_top (htop2 ▸ h21)
  exact hne (by rw [htop1, htop2])

end CFSG.OddTranspositions.PartThree.EightEight
