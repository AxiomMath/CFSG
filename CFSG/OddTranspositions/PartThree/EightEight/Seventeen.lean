module

public import CFSG.OddTranspositions.PartThree.Statements
public import CFSG.OddTranspositions.HypothesisC
public import CFSG.OddTranspositions.FaithfulBlocks
public import CFSG.OddTranspositions.Blocks
public import CFSG.Timmesfeld.Bridge.Asc72Triangle
public import CFSG.Timmesfeld.Bridge.OddTranspDefs

import CFSG.OddTranspositions.PartThree.EightEight.Triangles
import CFSG.OddTranspositions.PartThree.EightSeven
import CFSG.OddTranspositions.PartThree.EightNine.Tools
import CFSG.OddTranspositions.PartThree.Nine.ThreeBlocks
import CFSG.OddTranspositions.SixSevenLocalStep
import CFSG.OddTranspositions.SixNineUnconditional
import CFSG.OddTranspositions.SixTenPetersen
import CFSG.OddTranspositions.PartThree.SixThreeGlobal
import CFSG.Timmesfeld.Bridge.OddTranspSecondKind

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ
open CFSG.OddTranspositions CFSG.OddTranspositions.PartThree
open CFSG.OddTranspositions.PartThree.Nine
open CFSG.Timmesfeld.Bridge

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem isTriangle_of_mem_of_notMem_perp (hC : HypothesisC D) {β γ : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) (hγ : γ ∈ Dalpha D hC.alpha)
    (hγβ : γ ∉ perp D β) {a x c : G} (ha : a ∈ β) (hx : x ∈ β)
    (hax : a ≠ x) (hcomm : Commute a x) (hc : c ∈ γ) :
    IsTriangle D a c x := by
  have hN := hC.setup.normal
  have hodd := hC.setup.oddT
  have hne : β ≠ γ := by
    intro h
    exact hγβ (h ▸ mem_perp_iff.mpr (Or.inr rfl))
  have hcβ : c ∉ β := by
    intro hcβ
    exact hne (eq_of_mem_of_mem_blockClass hC.isBlock_alpha hβ.1 hγ.1 ⟨c, hcβ, hc⟩)
  have hnac : ¬ Commute a c := by
    intro hac
    exact hγβ (mem_perp_iff.mpr (Or.inl
      (mem_Dalpha_of_commute_mem hN hodd hC.isBlock_alpha hβ.1 hγ.1 hne ha hc hac)))
  have hncx : ¬ Commute x c := by
    intro hxc
    exact hγβ (mem_perp_iff.mpr (Or.inl
      (mem_Dalpha_of_commute_mem hN hodd hC.isBlock_alpha hβ.1 hγ.1 hne hx hc hxc)))
  exact ⟨hβ.2.1 ha, hβ.2.1 hx, hγ.2.1 hc, hax, hcomm, hnac, hncx⟩

omit [Finite G] in
theorem conj_image_eq_of_mem_Dalpha {β γ : Set G} {a x : G} (ha : a ∈ β) (hx : x ∈ β)
    (hγ : γ ∈ Dalpha D β) :
    (fun y => (a * x) * y * (a * x)⁻¹) '' γ = γ := by
  have hfix : ∀ y ∈ γ, (a * x) * y * (a * x)⁻¹ = y := by
    intro y hy
    have hay : Commute a y := hγ.2.2.2 a ha y hy
    have hxy : Commute x y := hγ.2.2.2 x hx y hy
    rw [(hay.mul_left hxy).eq, mul_inv_cancel_right]
  calc (fun y => (a * x) * y * (a * x)⁻¹) '' γ = (fun y => y) '' γ := Set.image_congr hfix
    _ = γ := Set.image_id' γ

theorem conj_image_alpha_eq_of_mem (hC : HypothesisC D) {β : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) {a x : G} (ha : a ∈ β) (hx : x ∈ β) :
    (fun y => (a * x) * y * (a * x)⁻¹) '' hC.alpha = hC.alpha :=
  conj_image_eq_of_mem_Dalpha ha hx (Dalpha_symm hβ hC.isBlock_alpha.subset)

theorem conj_image_beta_eq_of_mem (hC : HypothesisC D) {β : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) {a x : G} (ha : a ∈ β) (hx : x ∈ β) :
    (fun y => (a * x) * y * (a * x)⁻¹) '' β = β := by
  have hβblock : IsBlock D β := isBlock_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hβ.1
  have haN : a ∈ Subgroup.normalizer β := mem_normalizer_of_mem_block hβblock ha
  have hxN : x ∈ Subgroup.normalizer β := mem_normalizer_of_mem_block hβblock hx
  exact Subgroup.mem_normalizer_iff_conj_image_eq.mp (Subgroup.mul_mem _ haN hxN)

omit [Finite G] in
theorem commute_mul_of_mem_DalphaStar {β : Set G} {a x : G} (ha : a ∈ β) (hx : x ∈ β)
    {y : G} (hy : y ∈ DalphaStar D β) : Commute (a * x) y := by
  obtain ⟨γ, hγ, hyγ⟩ := hy
  exact (hγ.2.2.2 a ha y hyγ).mul_left (hγ.2.2.2 x hx y hyγ)

theorem exists_conj_image_ne_of_commute_of_mem (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {a x : G} (ha : a ∈ β) (hx : x ∈ β)
    (hax : a ≠ x) :
    ∃ γ ∈ Dalpha D hC.alpha, γ ∉ perp D β ∧
      (fun y => (a * x) * y * (a * x)⁻¹) '' γ ≠ γ := by
  classical
  by_contra h
  push Not at h
  have hcommStar : ∀ y ∈ DalphaStar D β, Commute (a * x) y :=
    fun y hy => commute_mul_of_mem_DalphaStar ha hx hy
  have htβ := conj_image_beta_eq_of_mem hC hβ ha hx
  have hperp : ∀ γ ∈ perp D hC.alpha, (fun y => (a * x) * y * (a * x)⁻¹) '' γ = γ := by
    intro γ hγ
    rcases mem_perp_iff.mp hγ with hγD | rfl
    · by_cases hγβ : γ ∈ perp D β
      · rcases mem_perp_iff.mp hγβ with hγβD | rfl
        · exact conj_image_eq_of_mem_Dalpha ha hx hγβD
        · exact htβ
      · exact h γ hγD hγβ
    · exact conj_image_alpha_eq_of_mem hC hβ ha hx
  have htriv := actsTriviallyOnBlocks_of_perp_of_theorem8_7 h87 hC hrad hO4 hβ
    hcommStar htβ hperp
  exact hax (by
    rw [eq_inv_of_mul_eq_one_right (hF (a * x) htriv), hC.setup.oddT.inv_eq (hβ.2.1 ha)])

theorem solvable_closure_of_secondKind (h86 : Lemma8_6) (hC : HypothesisC D)
    {a c x : G} (htri : IsTriangle D a c x) (h4 : orderOf (a * x * c) = 4) :
    Group.IsSolvable (Subgroup.closure ({a, c, x} : Set G)) :=
  h86 G D hC.setup.normal hC.setup.oddT a c x htri h4

theorem not_isThirdKind_of_mem_closure_of_secondKind (h86 : Lemma8_6) (hC : HypothesisC D)
    {a c x : G} (htri : IsTriangle D a c x) (h4 : orderOf (a * x * c) = 4) :
    ∀ y ∈ D, y ∈ Subgroup.closure {a, c} →
      IsTriangle D a y x → ¬ IsThirdKind a y x := by
  have hsolv := solvable_closure_of_secondKind h86 hC htri h4
  have hsub : ({a, c} : Set G) ⊆ ({a, c, x} : Set G) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    tauto
  intro y _ hyX htriY
  have hyK : y ∈ Subgroup.closure ({a, c, x} : Set G) :=
    Subgroup.closure_mono hsub hyX
  have haK : a ∈ Subgroup.closure ({a, c, x} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hxK : x ∈ Subgroup.closure ({a, c, x} : Set G) :=
    Subgroup.subset_closure (by simp)
  exact not_isThirdKind_of_solvable_subgroup hC.setup.oddT hC.setup.normal hsolv
    haK hyK hxK htriY

theorem exists_conj_mul_of_secondKind (h86 : Lemma8_6) (hC : HypothesisC D)
    {β γ : Set G} (hβ : β ∈ Dalpha D hC.alpha) (hγ : γ ∈ Dalpha D hC.alpha)
    (hγβ : γ ∉ perp D β) {a x c g₁ : G} (ha : a ∈ β) (hx : x ∈ β)
    (hax : a ≠ x) (hcomm : Commute a x) (hc : c ∈ γ)
    (h4 : orderOf (a * x * c) = 4)
    (hg₁X : g₁ ∈ Subgroup.closure ({a, c} : Set G))
    (hg₁ : g₁ * a * g₁⁻¹ = c) :
    ∃ h ∈ conjClosure (Subgroup.closure ({a, c} : Set G)) (a * x),
      h * a * h⁻¹ = g₁⁻¹ * ((a * x) * c * (a * x)⁻¹) * g₁ := by
  classical
  have hN := hC.setup.normal
  have hD := hC.setup.oddT
  have htri : IsTriangle D a c x :=
    isTriangle_of_mem_of_notMem_perp hC hβ hγ hγβ ha hx hax hcomm hc
  have hno := not_isThirdKind_of_mem_closure_of_secondKind h86 hC htri h4
  let X : Subgroup G := Subgroup.closure ({a, c} : Set G)
  let K : Subgroup G := Subgroup.closure ({a, c, x} : Set G)
  let Q : Subgroup G := conjClosure X (a * x)
  have hXK : X ≤ K := by
    dsimp only [X, K]
    exact Subgroup.closure_mono (by intro z hz; rcases hz with rfl | rfl <;> simp)
  have hg₁K : g₁ ∈ K := hXK hg₁X
  have htQ : a * x ∈ Q := by
    dsimp only [Q]
    exact Subgroup.subset_closure ⟨1, X.one_mem, by simp⟩
  have SK : SecondKindStructure a c x :=
    OddTransp.secondKind_structure hD hN htri h4 hno
  let t := a * x
  let h := g₁⁻¹ * t * g₁
  have hhQ : h ∈ Q := by
    dsimp only [h, t]
    simpa only [inv_inv] using
      (SK.normal g₁⁻¹ (Subgroup.inv_mem _ hg₁K) (a * x) htQ)
  refine ⟨h, hhQ, ?_⟩
  change (g₁⁻¹ * t * g₁) * a * (g₁⁻¹ * t * g₁)⁻¹ =
    g₁⁻¹ * (t * c * t⁻¹) * g₁
  calc (g₁⁻¹ * t * g₁) * a * (g₁⁻¹ * t * g₁)⁻¹
      = g₁⁻¹ * t * (g₁ * a * g₁⁻¹) * t⁻¹ * g₁ := by group
    _ = g₁⁻¹ * t * c * t⁻¹ * g₁ := by rw [hg₁]
    _ = g₁⁻¹ * (t * c * t⁻¹) * g₁ := by group

theorem mem_alpha_of_mem_sup_secondKind (h86 : Lemma8_6) (hC : HypothesisC D)
    {β γ : Set G} (hβ : β ∈ Dalpha D hC.alpha) (hγ : γ ∈ Dalpha D hC.alpha)
    (hγβ : γ ∉ perp D β) {a x c d h : G} (ha : a ∈ β) (hx : x ∈ β)
    (hax : a ≠ x) (hcomm : Commute a x) (hc : c ∈ γ)
    (h4 : orderOf (a * x * c) = 4) (hdD : d ∈ D)
    (hhK : h ∈ Subgroup.closure ({a, c, x} : Set G)) (hhd : h * a * h⁻¹ = d)
    (hdS : d ∈ Subgroup.zpowers a ⊔
      conjClosure (Subgroup.closure ({a, c} : Set G)) (a * x)) :
    d ∈ β := by
  classical
  have hD := hC.setup.oddT
  have htri : IsTriangle D a c x :=
    isTriangle_of_mem_of_notMem_perp hC hβ hγ hγβ ha hx hax hcomm hc
  have hno := not_isThirdKind_of_mem_closure_of_secondKind h86 hC htri h4
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hβ.1
  let hC' : HypothesisC D := hC.conj g
  have hα' : hC'.alpha = β := by
    dsimp only [hC']
    rw [HypothesisC.conj_alpha, hg]
  have hγA : γ ∈ Aalpha D hC'.alpha := by
    rw [hα']
    exact mem_Aalpha_iff.mpr ⟨mem_blockClass_of_mem_blockClass hβ.1 hγ.1, hγβ⟩
  have ha' : a ∈ hC'.alpha := by rw [hα']; exact ha
  have hx' : x ∈ hC'.alpha := by rw [hα']; exact hx
  have hdα : d ∈ hC'.alpha :=
    CFSG.OddTranspositions.mem_alpha_of_conj_mem_secondKindS hC' hγA ha' hx' hcomm hax
      hc h4 hno hdD hdS hhK hhd
  have hdβ : d ∈ β := by rwa [hα'] at hdα
  exact hdβ

theorem mem_alpha_of_conj_mul_secondKind (h86 : Lemma8_6) (hC : HypothesisC D)
    {β γ : Set G} (hβ : β ∈ Dalpha D hC.alpha) (hγ : γ ∈ Dalpha D hC.alpha)
    (hγβ : γ ∉ perp D β) {a x c g₁ : G} (ha : a ∈ β) (hx : x ∈ β)
    (hax : a ≠ x) (hcomm : Commute a x) (hc : c ∈ γ)
    (h4 : orderOf (a * x * c) = 4)
    (hg₁X : g₁ ∈ Subgroup.closure ({a, c} : Set G))
    (hg₁ : g₁ * a * g₁⁻¹ = c) :
    g₁⁻¹ * ((a * x) * c * (a * x)⁻¹) * g₁ ∈ β := by
  classical
  have hN := hC.setup.normal
  have hD := hC.setup.oddT
  have htri : IsTriangle D a c x :=
    isTriangle_of_mem_of_notMem_perp hC hβ hγ hγβ ha hx hax hcomm hc
  have hno := not_isThirdKind_of_mem_closure_of_secondKind h86 hC htri h4
  let X : Subgroup G := Subgroup.closure ({a, c} : Set G)
  let K : Subgroup G := Subgroup.closure ({a, c, x} : Set G)
  let Q : Subgroup G := conjClosure X (a * x)
  have SK : SecondKindStructure a c x :=
    OddTransp.secondKind_structure hD hN htri h4 hno
  obtain ⟨h, hhQ, hhd⟩ :=
    exists_conj_mul_of_secondKind h86 hC hβ hγ hγβ ha hx hax hcomm hc h4 hg₁X hg₁
  have hhK : h ∈ K := SK.le hhQ
  have haK : a ∈ K := by
    dsimp only [K]
    exact Subgroup.subset_closure (by simp)
  have haD : a ∈ D := hβ.2.1 ha
  have ha2 : a * a = 1 := hD.mul_self_eq_one haD
  have hcD : c ∈ D := hγ.2.1 hc
  let d := g₁⁻¹ * ((a * x) * c * (a * x)⁻¹) * g₁
  have hdD : d ∈ D := by
    have hc'D : (a * x) * c * (a * x)⁻¹ ∈ D := hN (a * x) c hcD
    have hconj := hN g₁⁻¹ ((a * x) * c * (a * x)⁻¹) hc'D
    simpa only [d, inv_inv] using hconj
  have hdS : d ∈ Subgroup.zpowers a ⊔ Q := by
    have hcommQ : h * a * h⁻¹ * a ∈ Q := by
      have h1 : a * h⁻¹ * a⁻¹ ∈ Q := SK.normal a haK h⁻¹ (Subgroup.inv_mem _ hhQ)
      have h2 : h * (a * h⁻¹ * a⁻¹) ∈ Q := Subgroup.mul_mem _ hhQ h1
      simpa [mul_assoc, hD.inv_eq haD] using h2
    have haa : (h * a * h⁻¹ * a) * a = h * a * h⁻¹ := by
      calc (h * a * h⁻¹ * a) * a = (h * a * h⁻¹) * (a * a) := by group
        _ = (h * a * h⁻¹) * 1 := by rw [ha2]
        _ = h * a * h⁻¹ := mul_one _
    have hd_eq : d = (h * a * h⁻¹ * a) * a := hhd.symm.trans haa.symm
    change d ∈ Subgroup.zpowers a ⊔ Q
    rw [hd_eq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hcommQ)
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
  exact mem_alpha_of_mem_sup_secondKind h86 hC hβ hγ hγβ ha hx hax hcomm hc h4
    hdD hhK hhd hdS

theorem conj_image_eq_of_secondKind (h86 : Lemma8_6) (hC : HypothesisC D)
    {β γ : Set G} (hβ : β ∈ Dalpha D hC.alpha) (hγ : γ ∈ Dalpha D hC.alpha)
    (hγβ : γ ∉ perp D β) {a x c : G} (ha : a ∈ β) (hx : x ∈ β)
    (hax : a ≠ x) (hcomm : Commute a x) (hc : c ∈ γ)
    (h4 : orderOf (a * x * c) = 4) :
    (fun y => (a * x) * y * (a * x)⁻¹) '' γ = γ := by
  classical
  have hD := hC.setup.oddT
  have htri : IsTriangle D a c x :=
    isTriangle_of_mem_of_notMem_perp hC hβ hγ hγβ ha hx hax hcomm hc
  have hnac : ¬ Commute a c := htri.2.2.2.2.2.1
  obtain ⟨g₁, hg₁X, hg₁⟩ := hD.exists_conj (hβ.2.1 ha) (hγ.2.1 hc) hnac
  let t := a * x
  have hdβ : g₁⁻¹ * (t * c * t⁻¹) * g₁ ∈ β := by
    dsimp only [t]
    exact mem_alpha_of_conj_mul_secondKind h86 hC hβ hγ hγβ ha hx hax hcomm hc h4
      hg₁X hg₁
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hβ.1
  have hβg : (fun y => g₁ * y * g₁⁻¹) '' β = γ := by
    have hclass : (fun y => g₁ * y * g₁⁻¹) '' β ∈ blockClass hC.alpha := by
      rw [hg]
      refine mem_blockClass_iff.mpr ⟨g₁ * g, ?_⟩
      rw [Set.image_image]
      congr 1
      funext y
      group
    exact eq_of_mem_of_mem_blockClass hC.isBlock_alpha hclass hγ.1 ⟨c, ⟨a, ha, hg₁⟩, hc⟩
  have hc'γ : t * c * t⁻¹ ∈ γ := by
    have hd_image : g₁ * (g₁⁻¹ * (t * c * t⁻¹) * g₁) * g₁⁻¹ ∈
        (fun y => g₁ * y * g₁⁻¹) '' β :=
      ⟨g₁⁻¹ * (t * c * t⁻¹) * g₁, hdβ, rfl⟩
    rw [hβg] at hd_image
    have hc'_eq : t * c * t⁻¹ = g₁ * (g₁⁻¹ * (t * c * t⁻¹) * g₁) * g₁⁻¹ := by
      group
    rwa [hc'_eq]
  exact Subgroup.mem_normalizer_iff_conj_image_eq.mp
    (mem_normalizer_block_of_conj_mem hC hγ.1 hc hc'γ)

theorem exists_odd_or_isThirdKind_of_commute_of_mem (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {a x : G} (ha : a ∈ β) (hx : x ∈ β)
    (hax : a ≠ x) (hcomm : Commute a x) :
    ∃ γ ∈ Dalpha D hC.alpha, γ ∉ perp D β ∧
      ∀ c ∈ γ, IsTriangle D a c x ∧ (Odd (orderOf (a * x * c)) ∨ IsThirdKind a c x) := by
  classical
  obtain ⟨γ, hγ, hγβ, hmoved⟩ :=
    exists_conj_image_ne_of_commute_of_mem h87 hC hrad hO4 hF hβ ha hx hax
  refine ⟨γ, hγ, hγβ, ?_⟩
  intro c hc
  have htri : IsTriangle D a c x :=
    isTriangle_of_mem_of_notMem_perp hC hβ hγ hγβ ha hx hax hcomm hc
  rcases htri.orderOf_cases hC.setup.oddT hC.setup.normal with h1 | h4 | h3
  · exact ⟨htri, Or.inl h1.1⟩
  · exact absurd (conj_image_eq_of_secondKind h86 hC hβ hγ hγβ ha hx hax hcomm hc h4) hmoved
  · exact ⟨htri, Or.inr h3⟩

theorem exists_isThirdKind_of_commute_of_mem (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {a x : G} (ha : a ∈ β) (hx : x ∈ β)
    (hax : a ≠ x) (hcomm : Commute a x) :
    ∃ γ ∈ Dalpha D hC.alpha, γ ∉ perp D β ∧
      ∀ c ∈ γ, IsTriangle D a c x ∧ IsThirdKind a c x := by
  classical
  obtain ⟨γ, hγ, hγβ, hmain⟩ :=
    exists_odd_or_isThirdKind_of_commute_of_mem h86 h87 hC hrad hO4 hF hβ ha hx hax hcomm
  refine ⟨γ, hγ, hγβ, ?_⟩
  intro c hc
  obtain ⟨htri, hodd | h3⟩ := hmain c hc
  · exact absurd hodd
      (not_odd_orderOf_of_derivedSeries_ne hC hne ⟨β, hβ, ha⟩ ⟨β, hβ, hx⟩ htri)
  · exact ⟨htri, h3⟩

end CFSG.OddTranspositions.PartThree.EightEight
