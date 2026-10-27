module

public import CFSG.OddTranspositions.PartFour.LineVmem
public import CFSG.OddTranspositions.PartFour.LineSpan
public import CFSG.OddTranspositions.PartFour.Fourteen.RootBlock
public import CFSG.OddTranspositions.PartThree.Eleven.Injective
import CFSG.OddTranspositions.PartThree.Ten.DalphaBlocks
import CFSG.OddTranspositions.WidthSylow
public import CFSG.OddTranspositions.PartFour.LineStabilizer
import CFSG.OddTranspositions.O4PairTenWidth
import CFSG.OddTranspositions.Width
import Certificates.Certificate1
import Certificates.Certificate2

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.PartFour
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

@[expose] def lineImage (hC : HypothesisC D) (β : Set G) :
    Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) :=
  ⋃ γ ∈ blockLine D hC.alpha β \ {hC.alpha}, blockImage hC γ

theorem subset_rootBlock_conj {X : Type} [Group X] {E : Set X} (hE : IsNormalSet E) {s : X}
    (hb1 : ∀ B, IsBlock E B → s ∈ B → B ⊆ rootBlock E s) (g : X) (B : Set X)
    (hB : IsBlock E B) (hgs : g * s * g⁻¹ ∈ B) : B ⊆ rootBlock E (g * s * g⁻¹) := by
  have himg : ConjAct.toConjAct g⁻¹ • B = (fun x => g⁻¹ * x * g⁻¹⁻¹) '' B := by
    rw [← Set.image_smul]
    rfl
  have hB' : IsBlock E ((fun x => g⁻¹ * x * g⁻¹⁻¹) '' B) := himg ▸ hB.conj hE _
  have h1 := hb1 _ hB' ⟨g * s * g⁻¹, hgs, by group⟩
  rw [← image_conj_rootBlock hE g s]
  intro x hx
  exact ⟨g⁻¹ * x * g⁻¹⁻¹, h1 ⟨x, hx, rfl⟩, by group⟩

theorem rootBlock_conj_ne {X : Type} [Group X] {E : Set X} (hE : IsNormalSet E) {s : X}
    (hne : rootBlock E s ≠ E) (g : X) : rootBlock E (g * s * g⁻¹) ≠ E := by
  rw [← image_conj_rootBlock hE g s]
  intro h
  apply hne
  refine (rootBlock_subset E s).antisymm fun x hx => ?_
  have hx' : g * x * g⁻¹ ∈ (fun x => g * x * g⁻¹) '' rootBlock E s := by
    rw [h]
    exact hE g x hx
  obtain ⟨y, hy, hyx⟩ := hx'
  rwa [show y = x by simpa using hyx] at hy

theorem imageClass_isNormalSet (hC : HypothesisC D) : IsNormalSet (imageClass hC) := by
  obtain ⟨d₀, hd₀⟩ := imageClass_isClass hC
  intro g x hx
  rw [hd₀] at hx ⊢
  exact hx.trans (isConj_iff.mpr ⟨g, rfl⟩)

theorem rootBlock_input_of_mem (hC : HypothesisC D)
    {s₀ t : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hs₀ : s₀ ∈ imageClass hC) (ht : t ∈ imageClass hC)
    (hb1 : ∀ B, IsBlock (imageClass hC) B → s₀ ∈ B → B ⊆ rootBlock (imageClass hC) s₀)
    (hne : rootBlock (imageClass hC) s₀ ≠ imageClass hC) :
    (∀ B, IsBlock (imageClass hC) B → t ∈ B → B ⊆ rootBlock (imageClass hC) t) ∧
      rootBlock (imageClass hC) t ≠ imageClass hC := by
  have hN := imageClass_isNormalSet hC
  obtain ⟨d₀, hd₀⟩ := imageClass_isClass hC
  have hst : IsConj s₀ t := by
    rw [hd₀] at hs₀ ht
    exact (isConj_comm.mp hs₀).trans ht
  obtain ⟨g, rfl⟩ := isConj_iff.mp hst
  exact ⟨subset_rootBlock_conj hN hb1 g, rootBlock_conj_ne hN hne g⟩

theorem commute_of_commute_mk_of_le_center (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {d v : Halpha D hC.alpha} (hd : d ∈ DstarH hC) (hv : v ∈ DstarH hC)
    (hdv : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) v)) :
    Commute d v := by
  by_contra hnc
  have hcen : d * v ∈ Subgroup.center (Halpha D hC.alpha) :=
    hMZ ((QuotientGroup.eq_one_iff _).mp (mk_mul_eq_one_of_not_commute hC hd hv hdv hnc))
  have hd2 : d * d = 1 := (DstarH_isOddTransp hC).mul_self_eq_one hd
  have h1 : d * (d * v) = d * v * d := Subgroup.mem_center_iff.mp hcen d
  rw [← mul_assoc, hd2, one_mul] at h1
  apply hnc
  calc d * v = d * (d * v * d) := by rw [← h1]
    _ = v * d := by rw [← mul_assoc, ← mul_assoc, hd2, one_mul]

theorem injOn_mk_DstarH_of_rootBlock_ne (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {s₀ : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hs₀ : s₀ ∈ imageClass hC) (hne : rootBlock (imageClass hC) s₀ ≠ imageClass hC) :
    Set.InjOn (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) (DstarH hC) :=
  injOn_mk_DstarH hC (le_antisymm hMZ (center_le_solvableRadical _))
    (exists_not_commute_of_rootBlock_ne (imageClass_isClass hC) hs₀ hne)

theorem exists_ne_mem_Dalpha (hC : HypothesisC D) {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    ∃ δ ∈ Dalpha D hC.alpha, δ ≠ β := by
  by_contra h
  push Not at h
  have hDα : Dalpha D hC.alpha = {β} := Set.eq_singleton_iff_unique_mem.2 ⟨hβ, h⟩
  have hDsub := subset_alpha_union_of_Dalpha_eq_singleton hC hβ hDα
  have hαH := alpha_subset_Halpha hC hβ h
  have hcentH : Halpha D hC.alpha ≤ Subgroup.centralizer {hC.d} := by
    rw [Halpha, Subgroup.closure_le]
    rintro z ⟨γ, hγ, hzγ⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (hγ.2.2.2 _ hC.d_mem_alpha z hzγ).eq.symm
  have htop : Subgroup.centralizer {hC.d} = ⊤ := by
    rw [eq_top_iff, ← hC.setup.gen, Subgroup.closure_le]
    intro x hx
    rcases hDsub x hx with hxα | hxβ
    · exact hcentH (hαH hxα)
    · exact hcentH (Subgroup.subset_closure ⟨β, hβ, hxβ⟩)
  obtain ⟨x, hx⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hβ.1
  obtain ⟨k, hk⟩ := isConj_iff.1 (hC.setup.isConj hC.hd (hβ.2.1 hx))
  have hkc : k ∈ Subgroup.centralizer {hC.d} := by
    rw [htop]
    exact Subgroup.mem_top k
  rw [Subgroup.mem_centralizer_singleton_iff.1 hkc, mul_inv_cancel_right] at hk
  rcases eq_or_disjoint_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hβ.1
      (mem_blockClass_self _) with h' | h'
  · exact hβ.2.2.1 h'
  · exact Set.disjoint_left.mp h' hx (hk ▸ hC.d_mem_alpha)

theorem isBlock_blockImage (hC : HypothesisC D)
    (hinj : Set.InjOn (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) (DstarH hC))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    IsBlock (imageClass hC) (blockImage hC β) := by
  have hstar : ∀ c : Halpha D hC.alpha, (c : G) ∈ β → c ∈ DstarH hC := fun c hc =>
    ⟨β, hβ, hc⟩
  have hβB : IsBlock D β := isBlock_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hβ.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact ⟨c, hstar c hc, rfl⟩
  · obtain ⟨x, hx⟩ := hβB.nonempty
    exact ⟨_, ⟨x, Subgroup.subset_closure ⟨β, hβ, hx⟩⟩, hx, rfl⟩
  · intro hEq
    obtain ⟨δ, hδ, hδβ⟩ := exists_ne_mem_Dalpha hC hβ
    obtain ⟨y, hy⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hδ.1
    let yH : Halpha D hC.alpha := ⟨y, Subgroup.subset_closure ⟨δ, hδ, hy⟩⟩
    have hyH : yH ∈ DstarH hC := ⟨δ, hδ, hy⟩
    have hmem : QuotientGroup.mk' _ yH ∈ blockImage hC β := by
      rw [hEq]
      exact ⟨yH, hyH, rfl⟩
    obtain ⟨c, hc, hcy⟩ := hmem
    have hcy' : c = yH := hinj (hstar c hc) hyH hcy
    rcases eq_or_disjoint_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hδ.1 hβ.1 with
      h | h
    · exact hδβ h
    · exact Set.disjoint_left.mp h hy (by rw [show y = (c : G) by rw [hcy']]; exact hc)
  · intro g hg
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ g
    have hnot : (h : G) ∉ Subgroup.normalizer β := by
      intro hN
      apply hg
      rw [Subgroup.mem_set_normalizer_iff]
      intro n
      constructor
      · rintro ⟨c, hc, rfl⟩
        refine ⟨h * c * h⁻¹, ?_, by simp⟩
        exact (Subgroup.mem_set_normalizer_iff.mp hN c).mp hc
      · rintro ⟨c, hc, hcn⟩
        refine ⟨h⁻¹ * c * h, ?_, ?_⟩
        · refine (Subgroup.mem_set_normalizer_iff.mp hN _).mpr ?_
          simpa [mul_assoc] using hc
        · rw [map_mul, map_mul, map_inv, hcn]
          group
    have hdisj := hβB.2.2.2 (h : G) hnot
    rw [Set.disjoint_left]
    rintro _ ⟨c, hc, rfl⟩ ⟨_, ⟨c', hc', rfl⟩, hcc'⟩
    have hconj : h * c' * h⁻¹ ∈ DstarH hC := DstarH_conj_mem hC (hstar c' hc')
    have heq : h * c' * h⁻¹ = c := hinj hconj (hstar c hc) (by simpa using hcc')
    exact Set.disjoint_left.mp hdisj hc ⟨c', hc', by rw [← heq]; simp⟩

theorem commute_of_mem_of_rootBlock (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {s₀ : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hs₀ : s₀ ∈ imageClass hC)
    (hb1 : ∀ B, IsBlock (imageClass hC) B → s₀ ∈ B → B ⊆ rootBlock (imageClass hC) s₀)
    (hne : rootBlock (imageClass hC) s₀ ≠ imageClass hC) {β : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) {x y : G} (hx : x ∈ β) (hy : y ∈ β) : Commute x y := by
  let xH : Halpha D hC.alpha := ⟨x, Subgroup.subset_closure ⟨β, hβ, hx⟩⟩
  let yH : Halpha D hC.alpha := ⟨y, Subgroup.subset_closure ⟨β, hβ, hy⟩⟩
  have hxs : xH ∈ DstarH hC := ⟨β, hβ, hx⟩
  have hys : yH ∈ DstarH hC := ⟨β, hβ, hy⟩
  have hxD : QuotientGroup.mk' _ xH ∈ imageClass hC := ⟨xH, hxs, rfl⟩
  obtain ⟨hb1x, -⟩ := rootBlock_input_of_mem hC hs₀ hxD hb1 hne
  have hsub := hb1x _
    (isBlock_blockImage hC (injOn_mk_DstarH_of_rootBlock_ne hC hMZ hs₀ hne) hβ) ⟨xH, hx, rfl⟩
  have hc := commute_of_mem_rootBlock hxD (hsub ⟨xH, hx, rfl⟩) (hsub ⟨yH, hy, rfl⟩)
  exact (commute_of_commute_mk_of_le_center hC hMZ hxs hys hc).map (Subgroup.subtype _)

theorem lineImage_eq_rootBlock_of_commute (hC : HypothesisC D)
    (hK : ∀ d ∈ DstarH hC, ∀ v ∈ DstarH hC,
      Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) v) → Commute d v)
    (hF : ∀ δ ∈ Dalpha D hC.alpha, ∀ x ∈ δ, ∀ y ∈ δ, Commute x y)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {b : Halpha D hC.alpha} (hb : (b : G) ∈ β) :
    lineImage hC β = rootBlock (imageClass hC)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) := by
  have hcp : ∀ δ ∈ Dalpha D hC.alpha, ∀ γ ∈ Dalpha D hC.alpha, ∀ d c : Halpha D hC.alpha,
      (d : G) ∈ δ → (c : G) ∈ γ →
      (Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c) ↔ γ ∈ perp D δ) := by
    intro δ hδ γ hγ d c hd hc
    constructor
    · intro h
      exact mem_perp_of_commute hC hδ.1 hγ.1 hd hc
        ((hK d ⟨δ, hδ, hd⟩ c ⟨γ, hγ, hc⟩ h).map (Subgroup.subtype _))
    · intro h
      have hG : Commute (d : G) (c : G) := by
        rcases mem_perp_iff.mp h with h' | h'
        · exact (mem_Dalpha_iff.mp h').2.2.2 _ hd _ hc
        · exact hF δ hδ _ hd _ (h' ▸ hc)
      exact (show Commute d c from Subtype.ext hG.eq).map _
  ext z
  constructor
  · intro hz
    obtain ⟨γ, ⟨hγl, hγα⟩, hz⟩ := Set.mem_iUnion₂.mp hz
    obtain ⟨c, hc, rfl⟩ := hz
    have hγD : γ ∈ Dalpha D hC.alpha := mem_Dalpha_of_mem_blockLine hC.isBlock_alpha.1 hβ hγl hγα
    refine ⟨⟨c, ⟨γ, hγD, hc⟩, rfl⟩, fun u hu => ?_⟩
    obtain ⟨d, hd, rfl⟩ := hu
    obtain ⟨δ, hδ, hdδ⟩ := mem_DalphaStar_iff.mp ((mem_DstarH_iff hC).mp hd)
    rw [hcp δ hδ γ hγD d c hdδ hc, hcp δ hδ β hβ d b hdδ hb]
    have hδα : δ ∈ perp D hC.alpha := mem_perp_iff.mpr (Or.inl hδ)
    constructor
    · intro h
      have hβl : β ∈ blockLine D hC.alpha γ := by
        rw [blockLine_eq_of_mem hC hβ hγD hγl]
        exact right_mem_blockLine hβ.1 hβ.2.1
      exact hβl.2 δ ⟨hδα, mem_perp_symm h hδ.2.1⟩
    · intro h
      exact hγl.2 δ ⟨hδα, mem_perp_symm h hδ.2.1⟩
  · rintro ⟨⟨e, he, rfl⟩, hze⟩
    obtain ⟨ε, hε, heε⟩ := mem_DalphaStar_iff.mp ((mem_DstarH_iff hC).mp he)
    have hεl : ε ∈ blockLine D hC.alpha β := by
      refine ⟨hε.1, fun δ hδ => ?_⟩
      by_cases hδα : δ = hC.alpha
      · rw [hδα]
        exact mem_perp_iff.mpr (Or.inl hε)
      have hδD : δ ∈ Dalpha D hC.alpha := (mem_perp_iff.mp hδ.1).resolve_right hδα
      obtain ⟨d, hdδ⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hδD.1
      let dH : Halpha D hC.alpha := ⟨d, Subgroup.subset_closure ⟨δ, hδD, hdδ⟩⟩
      have hdH : dH ∈ DstarH hC := ⟨δ, hδD, hdδ⟩
      have h1 := (hcp δ hδD β hβ dH b hdδ hb).mpr (mem_perp_symm hδ.2 hβ.2.1)
      exact (hcp δ hδD ε hε dH e hdδ heε).mp ((hze _ ⟨dH, hdH, rfl⟩).mpr h1)
    exact Set.mem_iUnion₂.mpr ⟨ε, ⟨hεl, hε.2.2.1⟩, ⟨e, heε, rfl⟩⟩

theorem lineImage_eq_rootBlock (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {s₀ : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hs₀ : s₀ ∈ imageClass hC)
    (hb1 : ∀ B, IsBlock (imageClass hC) B → s₀ ∈ B → B ⊆ rootBlock (imageClass hC) s₀)
    (hne : rootBlock (imageClass hC) s₀ ≠ imageClass hC) {β : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) {b : Halpha D hC.alpha} (hb : (b : G) ∈ β) :
    lineImage hC β = rootBlock (imageClass hC)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) :=
  lineImage_eq_rootBlock_of_commute hC
    (fun _ hd _ hv => commute_of_commute_mk_of_le_center hC hMZ hd hv)
    (fun _ hδ _ hx _ hy => commute_of_mem_of_rootBlock hC hMZ hs₀ hb1 hne hδ hx hy) hβ hb

end CFSG.OddTranspositions.PartThree

end
