module

public import CFSG.OddTranspositions.TheoremTwo.PropFourSeven.Labelling
public import CFSG.OddTranspositions.O4FibresMOrbit
public import CFSG.OddTranspositions.O4FibresAssembly

public section

namespace CFSG.OddTranspositions.PropFourSeven

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
  CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ CFSG.GroupTheory Equiv

variable {G : Type} [Group G] [Finite G] {D : Set G} {u w v z a : G} {K₁ S' : Subgroup G}

theorem labelOf_of_mem (hC : HypothesisC D)
    (ε : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* Perm (Fin 5))
    {x : G} (hx : x ∈ Halpha D hC.alpha) :
    labelOf ε x = ε (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) ⟨x, hx⟩) :=
  piG_mem hx

theorem labelOf_eq_starImage (hC : HypothesisC D)
    (ε : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* Perm (Fin 5))
    {d : G} (hd : d ∈ DalphaStar D hC.alpha) :
    labelOf ε d = ε (starImage hC d hd) :=
  labelOf_of_mem hC ε (Subgroup.subset_closure hd)

theorem labelOf_conj (hC : HypothesisC D)
    (ε : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* Perm (Fin 5))
    {h x : G} (hh : h ∈ Halpha D hC.alpha) (hx : x ∈ Halpha D hC.alpha) :
    labelOf ε (h * x * h⁻¹) = labelOf ε h * labelOf ε x * (labelOf ε h)⁻¹ :=
  piG_conj hh hx

theorem labelOf_eq_iff (hC : HypothesisC D)
    (ε : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* Perm (Fin 5))
    {x y : G} (hx : x ∈ Halpha D hC.alpha) (hy : y ∈ Halpha D hC.alpha) :
    labelOf ε x = labelOf ε y ↔
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) ⟨x, hx⟩ =
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) ⟨y, hy⟩ := by
  rw [labelOf_of_mem hC ε hx, labelOf_of_mem hC ε hy]
  exact ε.injective.eq_iff

theorem commute_labelOf_iff (hC : HypothesisC D)
    (ε : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* Perm (Fin 5))
    {x y : G} (hx : x ∈ Halpha D hC.alpha) (hy : y ∈ Halpha D hC.alpha) :
    Commute (labelOf ε x) (labelOf ε y) ↔
      Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) ⟨x, hx⟩)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) ⟨y, hy⟩) := by
  rw [labelOf_of_mem hC ε hx, labelOf_of_mem hC ε hy]
  exact ⟨fun h => by simpa using h.map ε.symm, fun h => h.map ε⟩

theorem labelOf_mem_transpositions (hC : HypothesisC D)
    (ε : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* Perm (Fin 5))
    (hε : ε '' imageClass hC = transpositions) {x : G} (hx : x ∈ DalphaStar D hC.alpha) :
    labelOf ε x ∈ transpositions := by
  rw [labelOf_eq_starImage hC ε hx, ← hε]
  exact ⟨_, ⟨⟨x, Subgroup.subset_closure hx⟩, hx, rfl⟩, rfl⟩

theorem exists_labelOf_eq (hC : HypothesisC D)
    (ε : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* Perm (Fin 5))
    (hε : ε '' imageClass hC = transpositions) {σ : Perm (Fin 5)} (hσ : σ ∈ transpositions) :
    ∃ x ∈ DalphaStar D hC.alpha, labelOf ε x = σ := by
  rw [← hε] at hσ
  obtain ⟨q, ⟨d, hd, rfl⟩, rfl⟩ := hσ
  exact ⟨d, hd, labelOf_of_mem hC ε d.2⟩

theorem commute_iff_labelOf (hC : HypothesisC D) (hQ : Config D u w v z a K₁ S')
    (ε : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* Perm (Fin 5))
    (hε : ε '' imageClass hC = transpositions) {x y : G} (hx : x ∈ DalphaStar D hC.alpha)
    (hy : y ∈ DalphaStar D hC.alpha) :
    Commute x y ↔ x = y ∨ (labelOf ε x ≠ labelOf ε y ∧ Commute (labelOf ε x) (labelOf ε y)) := by
  have hxH : x ∈ Halpha D hC.alpha := Subgroup.subset_closure hx
  have hyH : y ∈ Halpha D hC.alpha := Subgroup.subset_closure hy
  rw [ne_eq, labelOf_eq_iff hC ε hxH hyH, commute_labelOf_iff hC ε hxH hyH]
  constructor
  · intro hc
    by_cases hxy : x = y
    · exact Or.inl hxy
    have hcH : Commute (⟨x, hxH⟩ : Halpha D hC.alpha) ⟨y, hyH⟩ := Subtype.ext hc
    refine Or.inr ⟨fun hmk => ?_, hcH.map _⟩
    exact not_commute_of_mk_eq hC hQ hε (d := ⟨⟨x, hxH⟩, hx⟩) (d' := ⟨⟨y, hyH⟩, hy⟩) hmk
      (fun h => hxy (congrArg (fun d : DstarH hC => ((d : Halpha D hC.alpha) : G)) h)) hcH
  · rintro (rfl | ⟨hne, hc⟩)
    · exact Commute.refl x
    · exact congrArg Subtype.val
        (commute_of_commute_mk_of_ne_H hC (a := ⟨x, hxH⟩) (b := ⟨y, hyH⟩) hx hy hc hne)

theorem labelOf_conj_DalphaStar (hC : HypothesisC D)
    (ε : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* Perm (Fin 5))
    {x y : G} (hx : x ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) :
    labelOf ε (x * y * x⁻¹) = labelOf ε x * labelOf ε y * (labelOf ε x)⁻¹ :=
  labelOf_conj hC ε (Subgroup.subset_closure hx) (Subgroup.subset_closure hy)

omit [Finite G] in
theorem false_of_widthLe_three {E : Set G} (hW : WidthLe E 3) {a b c d : G} (ha : a ∈ E)
    (hb : b ∈ E) (hc : c ∈ E) (hd : d ∈ E) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (cab : Commute a b) (cac : Commute a c)
    (cad : Commute a d) (cbc : Commute b c) (cbd : Commute b d) (ccd : Commute c d) : False := by
  classical
  have h := hW {a, b, c, d}
    (by
      intro t ht
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl | rfl | rfl <;> assumption)
    (by
      intro s hs t ht hst
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs ht
      rcases hs with rfl | rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl | rfl <;>
        first | exact absurd rfl hst | assumption | (apply Commute.symm; assumption))
  rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
    Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd] at h
  omega

theorem eq_of_commute_of_mem_block_config (hC : HypothesisC D) (hQ : Config D u w v z a K₁ S')
    (ε : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* Perm (Fin 5))
    (hε : ε '' imageClass hC = transpositions) {β : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    {x y : G} (hx : x ∈ β) (hy : y ∈ β) (hxy : Commute x y) : x = y := by
  by_contra hne
  have hN := hC.setup.normal
  obtain ⟨p₀, hp₀, hp₀l⟩ := exists_labelOf_eq hC ε hε (σ := swap 0 1) ⟨0, 1, by decide, rfl⟩
  obtain ⟨q₀, hq₀, hq₀l⟩ := exists_labelOf_eq hC ε hε (σ := swap 2 3) ⟨2, 3, by decide, rfl⟩
  have hne₀ : labelOf ε p₀ ≠ labelOf ε q₀ := by rw [hp₀l, hq₀l]; decide
  have hc₀ : Commute (labelOf ε p₀) (labelOf ε q₀) := by
    rw [hp₀l, hq₀l]
    show swap (0 : Fin 5) 1 * swap 2 3 = swap 2 3 * swap 0 1
    decide
  have hpq₀ : Commute p₀ q₀ :=
    (commute_iff_labelOf hC hQ ε hε hp₀ hq₀).mpr (Or.inr ⟨hne₀, hc₀⟩)
  have hpq₀' : p₀ ≠ q₀ := fun h => hne₀ (by rw [h])
  obtain ⟨k, hk⟩ := mem_blockClass_iff.mp hβ.1
  have hp : k * p₀ * k⁻¹ ∈ DalphaStar D β := hk ▸ DalphaStar.conj hN hp₀ k
  have hq : k * q₀ * k⁻¹ ∈ DalphaStar D β := hk ▸ DalphaStar.conj hN hq₀ k
  obtain ⟨γ, hγ, hpγ⟩ := hp
  obtain ⟨δ, hδ, hqδ⟩ := hq
  have hpβ : k * p₀ * k⁻¹ ∉ β := fun h => hγ.2.2.1
    (eq_of_mem_of_mem_blockClass hC.isBlock_alpha
      (mem_blockClass_of_mem_blockClass (mem_blockClass_of_mem_blockClass hβ.1
        (mem_blockClass_self _)) hγ.1) hβ.1 ⟨_, hpγ, h⟩)
  have hqβ : k * q₀ * k⁻¹ ∉ β := fun h => hδ.2.2.1
    (eq_of_mem_of_mem_blockClass hC.isBlock_alpha
      (mem_blockClass_of_mem_blockClass (mem_blockClass_of_mem_blockClass hβ.1
        (mem_blockClass_self _)) hδ.1) hβ.1 ⟨_, hqδ, h⟩)
  exact false_of_widthLe_three (widthLe_three_of_config hQ) (hβ.2.1 hx) (hβ.2.1 hy)
    (hγ.2.1 hpγ) (hδ.2.1 hqδ) hne (fun h => hpβ (h ▸ hx)) (fun h => hqβ (h ▸ hx))
    (fun h => hpβ (h ▸ hy)) (fun h => hqβ (h ▸ hy))
    (fun h => hpq₀' (mul_left_cancel (mul_right_cancel h))) hxy
    (hγ.2.2.2 x hx _ hpγ) (hδ.2.2.2 x hx _ hqδ) (hγ.2.2.2 y hy _ hpγ) (hδ.2.2.2 y hy _ hqδ)
    (hpq₀.conj k)

theorem exists_swap_conj_commute_fin5 : ∀ a b c d : Fin 5, a ≠ b → c ≠ d →
    swap a b * swap c d ≠ swap c d * swap a b → ∃ e f : Fin 5, e ≠ f ∧ swap e f ≠ swap a b ∧
      swap e f * swap a b = swap a b * swap e f ∧
      swap a b * swap c d * swap a b ≠ swap e f * swap c d * swap e f ∧
      swap a b * swap c d * swap a b * (swap e f * swap c d * swap e f) =
        swap e f * swap c d * swap e f * (swap a b * swap c d * swap a b) := by
  decide

theorem exists_transposition_conj_commute {σ₁ σ₂ : Perm (Fin 5)} (h₁ : σ₁ ∈ transpositions)
    (h₂ : σ₂ ∈ transpositions) (hnc : ¬ Commute σ₁ σ₂) :
    ∃ σ₃ ∈ transpositions, σ₃ ≠ σ₁ ∧ Commute σ₃ σ₁ ∧
      σ₁ * σ₂ * σ₁⁻¹ ≠ σ₃ * σ₂ * σ₃⁻¹ ∧ Commute (σ₁ * σ₂ * σ₁⁻¹) (σ₃ * σ₂ * σ₃⁻¹) := by
  obtain ⟨a, b, hab, rfl⟩ := h₁
  obtain ⟨c, d, hcd, rfl⟩ := h₂
  obtain ⟨e, f, hef, h1, h2, h3, h4⟩ := exists_swap_conj_commute_fin5 a b c d hab hcd hnc
  refine ⟨swap e f, ⟨e, f, hef, rfl⟩, h1, h2, ?_, ?_⟩ <;> simp only [swap_inv]
  · exact h3
  · exact h4

omit [Finite G] in
theorem conj_mem_of_commute_of_isBlock {E β : Set G} (hβ : IsBlock E β) {x t y : G}
    (hx : x ∈ β) (htx : Commute t x) (hy : y ∈ β) : t * y * t⁻¹ ∈ β := by
  have htN : t ∈ Subgroup.normalizer β := by
    by_contra h
    refine Set.disjoint_left.mp (hβ.2.2.2 t h) hx ⟨x, hx, ?_⟩
    show t * x * t⁻¹ = x
    rw [htx.eq, mul_inv_cancel_right]
  exact (Subgroup.mem_set_normalizer_iff.mp htN y).mp hy

theorem labelOf_eq_of_mem_block (hC : HypothesisC D) (hQ : Config D u w v z a K₁ S')
    (ε : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* Perm (Fin 5))
    (hε : ε '' imageClass hC = transpositions) {β : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    {x y : G} (hx : x ∈ β) (hy : y ∈ β) : labelOf ε x = labelOf ε y := by
  by_contra hne
  have hxs := subset_DalphaStar hβ hx
  have hys := subset_DalphaStar hβ hy
  have hcomm := fun {x y : G} (hx : x ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) =>
    commute_iff_labelOf hC hQ ε hε hx hy
  have hnl : ¬ Commute (labelOf ε x) (labelOf ε y) := fun h =>
    hne (by rw [eq_of_commute_of_mem_block_config hC hQ ε hε hβ hx hy
      ((hcomm hxs hys).mpr (Or.inr ⟨hne, h⟩))])
  obtain ⟨σ₃, hσ₃, hne₃, hc₃, hne', hc'⟩ := exists_transposition_conj_commute
    (labelOf_mem_transpositions hC ε hε hxs) (labelOf_mem_transpositions hC ε hε hys) hnl
  obtain ⟨t, ht, rfl⟩ := exists_labelOf_eq hC ε hε hσ₃
  have hβb : IsBlock D β := isBlock_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hβ.1
  have htx : Commute t x := (hcomm ht hxs).mpr (Or.inr ⟨hne₃, hc₃⟩)
  have h1 : x * y * x⁻¹ ∈ β := conj_mem_of_commute_of_isBlock hβb hx (Commute.refl x) hy
  have h2 : t * y * t⁻¹ ∈ β := conj_mem_of_commute_of_isBlock hβb hx htx hy
  rw [← labelOf_conj_DalphaStar hC ε hxs hys, ← labelOf_conj_DalphaStar hC ε ht hys] at hne' hc'
  exact hne' (by
    rw [eq_of_commute_of_mem_block_config hC hQ ε hε hβ h1 h2
      ((hcomm (subset_DalphaStar hβ h1) (subset_DalphaStar hβ h2)).mpr (Or.inr ⟨hne', hc'⟩))])

theorem s5Labelling_alpha (hC : HypothesisC D) (hQ : Config D u w v z a K₁ S')
    (ε : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* Perm (Fin 5))
    (hε : ε '' imageClass hC = transpositions) : S5Labelling D hC.alpha (labelOf ε) :=
  ⟨fun _ hx => labelOf_mem_transpositions hC ε hε hx,
    fun _ hσ => exists_labelOf_eq hC ε hε hσ,
    fun _ hx _ hy => commute_iff_labelOf hC hQ ε hε hx hy,
    fun _ hx _ hy => labelOf_conj_DalphaStar hC ε hx hy,
    fun _ hβ _ hx _ hy => labelOf_eq_of_mem_block hC hQ ε hε hβ hx hy⟩

theorem exists_other_block (hC : HypothesisC D) (hQ : Config D u w v z a K₁ S')
    (ε : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* Perm (Fin 5))
    (hε : ε '' imageClass hC = transpositions) {θ₀ : Set G} (hθ₀ : θ₀ ∈ Dalpha D hC.alpha)
    {x₀ y₀ : G} (hx₀ : x₀ ∈ θ₀) (hy₀ : y₀ ∈ DalphaStar D hC.alpha)
    (hlab : labelOf ε y₀ = labelOf ε x₀) (hny : y₀ ∉ θ₀) :
    ∀ θ ∈ Dalpha D hC.alpha, ∃ θ' ∈ Dalpha D hC.alpha, θ' ≠ θ ∧
      ∀ x ∈ θ, ∀ y ∈ θ', labelOf ε y = labelOf ε x := by
  have hN := hC.setup.normal
  have hL := s5Labelling_alpha hC hQ ε hε
  intro θ hθ
  obtain ⟨c, hc⟩ := blockClass_nonempty hC.isBlock_alpha.2.1 hθ.1
  have hx₀s := subset_DalphaStar hθ₀ hx₀
  obtain ⟨h, hh, hhc⟩ := hC.Halpha_transitive x₀ hx₀s c (subset_DalphaStar hθ hc)
  have hy₀H : y₀ ∈ Halpha D hC.alpha := Subgroup.subset_closure hy₀
  obtain ⟨θ₁, hθ₁, hy₀θ₁⟩ := hy₀
  have hhN : h ∈ Subgroup.normalizer hC.alpha := by
    refine (Subgroup.closure_le _).mpr ?_ hh
    rintro s ⟨β, hβ, hsβ⟩
    refine Subgroup.mem_set_normalizer_iff.mpr fun r => ?_
    by_cases hr : r ∈ hC.alpha
    · rw [(hβ.2.2.2 r hr s hsβ).symm.eq, mul_inv_cancel_right]
    · have hr' : s * r * s⁻¹ ∉ hC.alpha := by
        intro hr'
        apply hr
        have hc := (hβ.2.2.2 _ hr' s hsβ).eq
        have e : s * r * s⁻¹ = r :=
          mul_left_cancel (hc.symm.trans (by group : s * r * s⁻¹ * s = s * r))
        rwa [e] at hr'
      simp only [hr, hr']
  have hhα : (fun t => h * t * h⁻¹) '' hC.alpha = hC.alpha := by
    ext r
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact (Subgroup.mem_set_normalizer_iff.mp hhN t).mp ht
    · intro hr
      refine ⟨h⁻¹ * r * h, (Subgroup.mem_set_normalizer_iff.mp hhN _).mpr ?_, by group⟩
      rwa [show h * (h⁻¹ * r * h) * h⁻¹ = r by group]
  have hconj : ∀ γ ∈ Dalpha D hC.alpha, (fun t => h * t * h⁻¹) '' γ ∈ Dalpha D hC.alpha :=
    fun γ hγ => by
      have := Dalpha.conj hN hγ h
      rwa [hhα] at this
  have hθeq : (fun t => h * t * h⁻¹) '' θ₀ = θ :=
    eq_of_mem_of_mem_blockClass hC.isBlock_alpha (hconj θ₀ hθ₀).1 hθ.1 ⟨c, ⟨x₀, hx₀, hhc⟩, hc⟩
  refine ⟨_, hconj θ₁ hθ₁, ?_, ?_⟩
  · intro heq
    have hmem : h * y₀ * h⁻¹ ∈ θ := by rw [← heq]; exact ⟨y₀, hy₀θ₁, rfl⟩
    rw [← hθeq] at hmem
    obtain ⟨y', hy', hyy⟩ := hmem
    have : y' = y₀ := mul_left_cancel (mul_right_cancel hyy)
    exact hny (this ▸ hy')
  · intro x hx y hy
    have hx₀H : x₀ ∈ Halpha D hC.alpha := Subgroup.subset_closure hx₀s
    calc labelOf ε y = labelOf ε (h * y₀ * h⁻¹) :=
          hL.block _ (hconj θ₁ hθ₁) y hy _ ⟨y₀, hy₀θ₁, rfl⟩
      _ = labelOf ε h * labelOf ε y₀ * (labelOf ε h)⁻¹ := labelOf_conj hC ε hh hy₀H
      _ = labelOf ε h * labelOf ε x₀ * (labelOf ε h)⁻¹ := by rw [hlab]
      _ = labelOf ε (h * x₀ * h⁻¹) := (labelOf_conj hC ε hh hx₀H).symm
      _ = labelOf ε c := by rw [hhc]
      _ = labelOf ε x := hL.block θ hθ c hc x hx

end CFSG.OddTranspositions.PropFourSeven

