module

public import CFSG.OddTranspositions.HalphaQuotient

import CFSG.OddTranspositions.PartFour.LineTransport
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Timmesfeld.Bridge.Asc72Lift
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity
open CFSG.OddTranspositions.PartFour

variable {G : Type} [Group G] [Finite G] {D : Set G}

@[expose] def BlocksInCosets (D ρ : Set G) : Prop :=
  ∀ β ∈ Dalpha D ρ, ∀ a b : Halpha D ρ, (a : G) ∈ β → (b : G) ∈ β →
    QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) a =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) b

@[expose] def FibresAnticlique (D ρ : Set G) : Prop :=
  ∀ a b : Halpha D ρ, (a : G) ∈ DalphaStar D ρ → (b : G) ∈ DalphaStar D ρ → a ≠ b →
    QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) a =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) b → ¬ Commute a b

@[expose] def DalphaAdj (D β ρ ρ' : Set G) : Prop :=
  ρ' ∈ Dalpha D β ∧ ρ' ∈ Dalpha D ρ

omit [Finite G] in
private theorem mk_eq_iff_inv_mul_mem_Malpha_w4b {D ρ : Set G} {a b : Halpha D ρ} :
    QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) a =
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) b ↔
      (a : G)⁻¹ * (b : G) ∈ Malpha D ρ := by
  let H := Halpha D ρ
  let R : Subgroup H := CFSG.solvableRadical H
  change QuotientGroup.mk' R a = QuotientGroup.mk' R b ↔
    (a : G)⁻¹ * (b : G) ∈ R.map H.subtype
  constructor
  · intro h
    have hR : a⁻¹ * b ∈ R := (QuotientGroup.eq).mp h
    simpa using Subgroup.mem_map_of_mem H.subtype hR
  · intro h
    obtain ⟨r, hr, hrv⟩ := Subgroup.mem_map.mp h
    have hEq : r = a⁻¹ * b := Subtype.ext (by simpa using hrv)
    rw [hEq] at hr
    exact (QuotientGroup.eq).mpr hr

omit [Finite G] in
private theorem conj_mem_Malpha_cimg_iff_w4b {D ρ : Set G} (hN : IsNormalSet D) (g : G)
    {x : G} : g * x * g⁻¹ ∈ Malpha D (cimg g ρ) ↔ x ∈ Malpha D ρ := by
  rw [Malpha_cimg hN g ρ]
  constructor
  · intro h
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp h
    have hxy' : (MulAut.conj g) y = g * x * g⁻¹ := by
      simpa only [MulEquiv.coe_toMonoidHom] using hxy
    have hyx : y = x := by
      apply (MulAut.conj g).injective
      rw [hxy', MulAut.conj_apply]
    rwa [hyx] at hy
  · intro hx
    refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

omit [Finite G] in
private theorem exists_conj_eq_of_mem_Halpha_cimg_w4b {D ρ : Set G} (hN : IsNormalSet D)
    (g : G) {a : Halpha D (cimg g ρ)} :
    ∃ a₀ : Halpha D ρ, (a : G) = g * (a₀ : G) * g⁻¹ := by
  have ha : (a : G) ∈ (Halpha D ρ).map (MulAut.conj g).toMonoidHom := by
    rw [← Halpha_cimg hN g ρ]
    exact a.2
  obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp ha
  have hxa' : (MulAut.conj g) x = (a : G) := by
    simpa only [MulEquiv.coe_toMonoidHom] using hxa
  exact ⟨⟨x, hx⟩, by simpa only [MulAut.conj_apply] using hxa'.symm⟩

omit [Finite G] in
private theorem conj_mem_DalphaStar_cimg_iff_w4b {D ρ : Set G} (hN : IsNormalSet D) (g : G)
    {x : G} : g * x * g⁻¹ ∈ DalphaStar D (cimg g ρ) ↔ x ∈ DalphaStar D ρ := by
  rw [DalphaStar_cimg hN g ρ, mem_cimg]
  have h : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rw [h]

omit [Finite G] in
private theorem mk_eq_cimg_inv_of_mk_eq_w4b {D ρ : Set G} (hN : IsNormalSet D) {g : G}
    {a₀ b₀ : Halpha D ρ} {a b : Halpha D (cimg g ρ)}
    (ha : (a : G) = g * (a₀ : G) * g⁻¹) (hb : (b : G) = g * (b₀ : G) * g⁻¹)
    (hmk : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D (cimg g ρ))) a =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D (cimg g ρ))) b) :
    QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) a₀ =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) b₀ := by
  have hmem : (a : G)⁻¹ * (b : G) ∈ Malpha D (cimg g ρ) :=
    (mk_eq_iff_inv_mul_mem_Malpha_w4b (D := D) (ρ := cimg g ρ)).mp hmk
  have hconj : g⁻¹ * ((a : G)⁻¹ * (b : G)) * g ∈ Malpha D ρ := by
    have h : g * (g⁻¹ * ((a : G)⁻¹ * (b : G)) * g) * g⁻¹ ∈
        Malpha D (cimg g ρ) := by
      have e : g * (g⁻¹ * ((a : G)⁻¹ * (b : G)) * g) * g⁻¹ =
          (a : G)⁻¹ * (b : G) := by group
      rwa [e]
    exact (conj_mem_Malpha_cimg_iff_w4b hN g).mp h
  have hEq : g⁻¹ * ((a : G)⁻¹ * (b : G)) * g = (a₀ : G)⁻¹ * (b₀ : G) := by
    rw [ha, hb]
    group
  have hmem₀ : (a₀ : G)⁻¹ * (b₀ : G) ∈ Malpha D ρ := by
    rwa [hEq] at hconj
  exact (mk_eq_iff_inv_mul_mem_Malpha_w4b (D := D) (ρ := ρ)).mpr hmem₀

omit [Finite G] in
private theorem commute_cimg_inv_of_commute_w4b {D ρ : Set G} {g : G}
    {a₀ b₀ : Halpha D ρ} {a b : Halpha D (cimg g ρ)}
    (ha : (a : G) = g * (a₀ : G) * g⁻¹) (hb : (b : G) = g * (b₀ : G) * g⁻¹)
    (h : Commute a b) : Commute a₀ b₀ := by
  have hcommG : Commute (a : G) (b : G) := h.map (Halpha D (cimg g ρ)).subtype
  have hconj : Commute (g⁻¹ * (a : G) * g) (g⁻¹ * (b : G) * g) :=
    by simpa using hcommG.conj g⁻¹
  have h1 : g⁻¹ * (a : G) * g = (a₀ : G) := by rw [ha]; group
  have h2 : g⁻¹ * (b : G) * g = (b₀ : G) := by rw [hb]; group
  rw [h1, h2] at hconj
  exact (commute_map_iff (Subgroup.subtype_injective (Halpha D ρ))).mp hconj

omit [Finite G] in
private theorem blocksInCosets_cimg_w4b {D ρ : Set G} (hN : IsNormalSet D)
    (hB : BlocksInCosets D ρ) (g : G) : BlocksInCosets D (cimg g ρ) := by
  intro β hβ a b ha hb
  obtain ⟨a₀, ha₀⟩ := exists_conj_eq_of_mem_Halpha_cimg_w4b hN g (a := a)
  obtain ⟨b₀, hb₀⟩ := exists_conj_eq_of_mem_Halpha_cimg_w4b hN g (a := b)
  have hβ₀ : cimg g⁻¹ β ∈ Dalpha D ρ := by
    have h : cimg g⁻¹ β ∈ Dalpha D (cimg g⁻¹ (cimg g ρ)) :=
      Dalpha.conj hN hβ g⁻¹
    rw [cimg_inv_cimg] at h
    exact h
  have ha₀β : (a₀ : G) ∈ cimg g⁻¹ β := by
    rw [mem_cimg]
    simpa [← ha₀] using ha
  have hb₀β : (b₀ : G) ∈ cimg g⁻¹ β := by
    rw [mem_cimg]
    simpa [← hb₀] using hb
  have hmk₀ := hB (cimg g⁻¹ β) hβ₀ a₀ b₀ ha₀β hb₀β
  have hmem₀ : (a₀ : G)⁻¹ * (b₀ : G) ∈ Malpha D ρ :=
    (mk_eq_iff_inv_mul_mem_Malpha_w4b (D := D) (ρ := ρ)).mp hmk₀
  have hmem : g * ((a₀ : G)⁻¹ * (b₀ : G)) * g⁻¹ ∈ Malpha D (cimg g ρ) :=
    (conj_mem_Malpha_cimg_iff_w4b hN g).mpr hmem₀
  have hEq : (a : G)⁻¹ * (b : G) = g * ((a₀ : G)⁻¹ * (b₀ : G)) * g⁻¹ := by
    rw [ha₀, hb₀]
    group
  have hmem' : (a : G)⁻¹ * (b : G) ∈ Malpha D (cimg g ρ) := by
    rwa [hEq]
  exact (mk_eq_iff_inv_mul_mem_Malpha_w4b (D := D) (ρ := cimg g ρ)).mpr hmem'

omit [Finite G] in
private theorem fibresAnticlique_cimg_w4b {D ρ : Set G} (hN : IsNormalSet D)
    (hA : FibresAnticlique D ρ) (g : G) : FibresAnticlique D (cimg g ρ) := by
  intro a b ha hb hne hmk
  obtain ⟨a₀, ha₀⟩ := exists_conj_eq_of_mem_Halpha_cimg_w4b hN g (a := a)
  obtain ⟨b₀, hb₀⟩ := exists_conj_eq_of_mem_Halpha_cimg_w4b hN g (a := b)
  have ha₀star : (a₀ : G) ∈ DalphaStar D ρ := by
    have h : g * (a₀ : G) * g⁻¹ ∈ DalphaStar D (cimg g ρ) := by rwa [← ha₀]
    exact (conj_mem_DalphaStar_cimg_iff_w4b hN g).mp h
  have hb₀star : (b₀ : G) ∈ DalphaStar D ρ := by
    have h : g * (b₀ : G) * g⁻¹ ∈ DalphaStar D (cimg g ρ) := by rwa [← hb₀]
    exact (conj_mem_DalphaStar_cimg_iff_w4b hN g).mp h
  have ha₀ne : a₀ ≠ b₀ := by
    intro hab
    apply hne
    apply Subtype.ext
    rw [ha₀, hb₀, hab]
  have hmk₀ := mk_eq_cimg_inv_of_mk_eq_w4b hN ha₀ hb₀ hmk
  exact fun hcomm => hA a₀ b₀ ha₀star hb₀star ha₀ne hmk₀
    (commute_cimg_inv_of_commute_w4b ha₀ hb₀ hcomm)

omit [Finite G] in
private theorem mk_ne_commute_of_mem_Dalpha_w4b {D ρ : Set G} (hρ : IsBlock D ρ)
    (hA : FibresAnticlique D ρ) {β β' : Set G} (hβ : β ∈ Dalpha D ρ)
    (hβ' : β' ∈ Dalpha D ρ) {a b : Halpha D ρ} (ha : (a : G) ∈ β) (hb : (b : G) ∈ β')
    (hβ'β : β' ∈ Dalpha D β) :
    QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) a ≠
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) b ∧
      Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) a)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) b) := by
  have hβne : β ≠ β' := (Dalpha.ne_self hβ'β).symm
  have haStar : (a : G) ∈ DalphaStar D ρ := ⟨β, hβ, ha⟩
  have hbStar : (b : G) ∈ DalphaStar D ρ := ⟨β', hβ', hb⟩
  have hcommG : Commute (a : G) (b : G) := hβ'β.2.2.2 (a : G) ha (b : G) hb
  have hcomm : Commute a b :=
    (commute_map_iff (Subgroup.subtype_injective (Halpha D ρ))).mp hcommG
  have hcommq : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) a)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) b) :=
    hcomm.map (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)))
  have hne : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) a ≠
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) b := by
    intro hmk
    have hane : a ≠ b := by
      intro hab
      have hval : (a : G) = (b : G) := congrArg Subtype.val hab
      have hmem : (a : G) ∈ β' := by rw [hval]; exact hb
      exact hβne (eq_of_mem_of_mem_blockClass hρ hβ.1 hβ'.1 ⟨(a : G), ha, hmem⟩)
    exact (hA a b haStar hbStar hane hmk) hcomm
  exact ⟨hne, hcommq⟩

omit [Finite G] in
private theorem mem_Dalpha_of_mk_ne_commute_w4b (hN : IsNormalSet D) (hodd : IsOddTransp D)
    {ρ : Set G} (hρ : IsBlock D ρ)
    (hW : ∀ β ∈ Dalpha D ρ, ∀ a b : Halpha D ρ, (a : G) ∈ β → (b : G) ∈ β → a ≠ b →
      ¬ Commute a b)
    {β β' : Set G} (hβ : β ∈ Dalpha D ρ) (hβ' : β' ∈ Dalpha D ρ) {a b : Halpha D ρ}
    (ha : (a : G) ∈ β) (hb : (b : G) ∈ β')
    (h : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) a ≠
          QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) b ∧
        Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) a)
          (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) b)) :
    β' ∈ Dalpha D β := by
  let H := Halpha D ρ
  let R : Subgroup H := CFSG.solvableRadical H
  have hDpre : IsOddTransp (((↑) : H → G) ⁻¹' D) := IsOddTransp.preimage hodd H
  have haD : (a : G) ∈ D := hβ.2.1 ha
  have hbD : (b : G) ∈ D := hβ'.2.1 hb
  have hcomm : Commute a b :=
    commute_of_commute_of_ne hDpre haD hbD h.1 h.2
  have hcommG : Commute (a : G) (b : G) := hcomm.map H.subtype
  have hβ'ne : β' ≠ β := by
    intro heq
    exact hW β hβ a b ha (heq ▸ hb) (fun hab => h.1 (by rw [hab])) hcomm
  have hclass : β' ∈ blockClass β := by
    rw [blockClass_eq_of_mem hβ.1]
    exact hβ'.1
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hclass
  have hne' : cimg g β ≠ β := fun hh => hβ'ne (hg.trans hh)
  have hβblock : IsBlock D β := isBlock_of_mem_blockClass hN hρ hβ.1
  have hall := commute_block_of_mem_apply hN hodd hβblock hne' ha (hg ▸ hb) hcommG
  refine ⟨hclass, hβ'.2.1, hβ'ne, ?_⟩
  intro x hx y hy
  rw [hg] at hy
  exact hall x hx y hy

omit [Finite G] in
theorem BlocksInCosets.of_mem_blockClass (hN : IsNormalSet D) {ρ ρ' : Set G}
    (hB : BlocksInCosets D ρ) (hρ' : ρ' ∈ blockClass ρ) : BlocksInCosets D ρ' := by
  obtain ⟨g, rfl⟩ := mem_blockClass_iff.mp hρ'
  exact blocksInCosets_cimg_w4b hN hB g

omit [Finite G] in
theorem FibresAnticlique.of_mem_blockClass (hN : IsNormalSet D) {ρ ρ' : Set G}
    (hA : FibresAnticlique D ρ) (hρ' : ρ' ∈ blockClass ρ) : FibresAnticlique D ρ' := by
  obtain ⟨g, rfl⟩ := mem_blockClass_iff.mp hρ'
  exact fibresAnticlique_cimg_w4b hN hA g

theorem exists_mem_Dalpha_mk_eq (hC : HypothesisC D)
    {q : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hq : q ∈ imageClass hC) :
    ∃ ρ ∈ Dalpha D hC.alpha, ∃ a : Halpha D hC.alpha, (a : G) ∈ ρ ∧
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a = q := by
  obtain ⟨a, ha, rfl⟩ := hq
  obtain ⟨ρ, hρ, haρ⟩ := (mem_DstarH_iff hC).mp ha
  exact ⟨ρ, hρ, a, haρ, rfl⟩

omit [Finite G] in
theorem mem_Dalpha_iff_mk (hN : IsNormalSet D) (hodd : IsOddTransp D) {ρ : Set G}
    (hρ : IsBlock D ρ)
    (hW : ∀ β ∈ Dalpha D ρ, ∀ a b : Halpha D ρ, (a : G) ∈ β → (b : G) ∈ β → a ≠ b →
      ¬ Commute a b)
    (hA : FibresAnticlique D ρ) {β β' : Set G}
    (hβ : β ∈ Dalpha D ρ) (hβ' : β' ∈ Dalpha D ρ) {a b : Halpha D ρ} (ha : (a : G) ∈ β)
    (hb : (b : G) ∈ β') :
    β' ∈ Dalpha D β ↔
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) a ≠
          QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) b ∧
        Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) a)
          (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) b) := by
  constructor
  · exact mk_ne_commute_of_mem_Dalpha_w4b hρ hA hβ hβ' ha hb
  · exact mem_Dalpha_of_mk_ne_commute_w4b hN hodd hρ hW hβ hβ' ha hb

omit [Finite G] in
theorem BlocksInCosets.not_commute {ρ : Set G} (hB : BlocksInCosets D ρ)
    (hA : FibresAnticlique D ρ) :
    ∀ β ∈ Dalpha D ρ, ∀ a b : Halpha D ρ, (a : G) ∈ β → (b : G) ∈ β → a ≠ b →
      ¬ Commute a b :=
  fun β hβ a b ha hb hab => hA a b ⟨β, hβ, ha⟩ ⟨β, hβ, hb⟩ hab (hB β hβ a b ha hb)

omit [Finite G] in
theorem BlocksInCosets.mem_Dalpha_iff_mk (hN : IsNormalSet D) (hodd : IsOddTransp D)
    {ρ : Set G} (hρ : IsBlock D ρ) (hB : BlocksInCosets D ρ) (hA : FibresAnticlique D ρ)
    {β β' : Set G} (hβ : β ∈ Dalpha D ρ) (hβ' : β' ∈ Dalpha D ρ) {a b : Halpha D ρ}
    (ha : (a : G) ∈ β) (hb : (b : G) ∈ β') :
    β' ∈ Dalpha D β ↔
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) a ≠
          QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) b ∧
        Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) a)
          (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) b) :=
  EightEight.mem_Dalpha_iff_mk hN hodd hρ (hB.not_commute hA) hA hβ hβ' ha hb

end CFSG.OddTranspositions.PartThree.EightEight
