module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmModel
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import CFSG.RankThree.PartOne.KC.OrthogonalBinaryDickson
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct

public section

namespace CFSG.StandardType

namespace RCSTOm

open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (commSpace mem_commSpace omegaGroup mem_omegaGroup)
open CFSG.RankThree.PartOne.KCOrthogonal (glue glue_apply glue_mul glue_one restrictEquiv)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {P₁ P₂ : HypPair Q}

section Split

variable (P₁ P₂) in
@[expose] def wSub : Submodule K V := P₁.perp ⊓ P₂.perp

theorem mem_wSub {x : V} : x ∈ wSub P₁ P₂ ↔ InW P₁ P₂ x := by
  rw [wSub, Submodule.mem_inf, HypPair.mem_perp, HypPair.mem_perp]
  exact ⟨fun ⟨⟨a, b⟩, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨⟨a, b⟩, c, d⟩⟩

theorem uPart_eq_zero_of_inW {x : V} (hx : InW P₁ P₂ x) : uPart P₁ P₂ x = 0 := by
  obtain ⟨a1, a2, a3, a4⟩ := hx
  rw [uPart, polar_comm Q x P₁.f, a2, polar_comm Q x P₁.e, a1, polar_comm Q x P₂.f, a4,
    polar_comm Q x P₂.e, a3]
  simp

theorem isCompl_wSub_spanU₄ (h₁₂ : P₁.Orth P₂) : IsCompl (wSub P₁ P₂) (spanU₄ P₁ P₂) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro v hvW hvU
    rw [← uPart_eq_of_mem_spanU₄ h₁₂ hvU]
    exact uPart_eq_zero_of_inW (mem_wSub.mp hvW)
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    exact Submodule.mem_sup.mpr ⟨_, mem_wSub.mpr (inW_sub_uPart h₁₂ v), _, uPart_mem_spanU₄ v,
      sub_add_cancel v _⟩

theorem polar_eq_zero_of_inW_of_mem_spanU₄ (h₁₂ : P₁.Orth P₂) {w u : V} (hw : InW P₁ P₂ w)
    (hu : u ∈ spanU₄ P₁ P₂) : polar Q w u = 0 := by
  obtain ⟨a1, a2, a3, a4⟩ := hw
  rw [← uPart_eq_of_mem_spanU₄ h₁₂ hu, uPart]
  simp only [polar_add_right, polar_smul_right_eq, polar_comm Q w P₁.e, polar_comm Q w P₁.f,
    polar_comm Q w P₂.e, polar_comm Q w P₂.f, a1, a2, a3, a4, mul_zero, add_zero]

end Split

section Extend

variable (P₁ P₂) in
@[expose] noncomputable def extW (h₁₂ : P₁.Orth P₂) :
    (wSub P₁ P₂ ≃ₗ[K] wSub P₁ P₂) →* (V ≃ₗ[K] V) where
  toFun g := glue (isCompl_wSub_spanU₄ h₁₂) g 1
  map_one' := glue_one _
  map_mul' g g' := by rw [← glue_mul, one_mul]

theorem extW_apply (h₁₂ : P₁.Orth P₂) (g : wSub P₁ P₂ ≃ₗ[K] wSub P₁ P₂) (v : V) :
    extW P₁ P₂ h₁₂ g v =
      (g ⟨v - uPart P₁ P₂ v, mem_wSub.mpr (inW_sub_uPart h₁₂ v)⟩ : V) + uPart P₁ P₂ v := by
  have h := glue_apply (isCompl_wSub_spanU₄ h₁₂) g 1
    ⟨v - uPart P₁ P₂ v, mem_wSub.mpr (inW_sub_uPart h₁₂ v)⟩ ⟨uPart P₁ P₂ v, uPart_mem_spanU₄ v⟩
  simp only [sub_add_cancel, LinearEquiv.coe_one, id_eq] at h
  exact h

theorem extW_apply_w (h₁₂ : P₁.Orth P₂) (g : wSub P₁ P₂ ≃ₗ[K] wSub P₁ P₂) (w : wSub P₁ P₂) :
    extW P₁ P₂ h₁₂ g w = g w := by
  have h0 : uPart P₁ P₂ (w : V) = 0 := uPart_eq_zero_of_inW (mem_wSub.mp w.2)
  have hw' : (⟨(w : V) - uPart P₁ P₂ w, mem_wSub.mpr (inW_sub_uPart h₁₂ w)⟩ : wSub P₁ P₂) = w :=
    Subtype.ext (show (w : V) - uPart P₁ P₂ w = w by rw [h0, sub_zero])
  rw [extW_apply, hw', h0, add_zero]

theorem extW_apply_u (h₁₂ : P₁.Orth P₂) (g : wSub P₁ P₂ ≃ₗ[K] wSub P₁ P₂) {u : V}
    (hu : u ∈ spanU₄ P₁ P₂) : extW P₁ P₂ h₁₂ g u = u := by
  have h0 : (⟨u - uPart P₁ P₂ u, mem_wSub.mpr (inW_sub_uPart h₁₂ u)⟩ : wSub P₁ P₂) = 0 :=
    Subtype.ext (show u - uPart P₁ P₂ u = 0 by rw [uPart_eq_of_mem_spanU₄ h₁₂ hu, sub_self])
  rw [extW_apply, h0, map_zero, Submodule.coe_zero, zero_add, uPart_eq_of_mem_spanU₄ h₁₂ hu]

theorem mem_spanU₄_e₁ : P₁.e ∈ spanU₄ P₁ P₂ := Submodule.subset_span (by simp)
theorem mem_spanU₄_e₂ : P₂.e ∈ spanU₄ P₁ P₂ := Submodule.subset_span (by simp)
theorem mem_spanU₄_f₁ : P₁.f ∈ spanU₄ P₁ P₂ := Submodule.subset_span (by simp)
theorem mem_spanU₄_f₂ : P₂.f ∈ spanU₄ P₁ P₂ := Submodule.subset_span (by simp)

theorem extW_mem_orthogonalGroup (h₁₂ : P₁.Orth P₂) {g : wSub P₁ P₂ ≃ₗ[K] wSub P₁ P₂}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (wSub P₁ P₂))) :
    extW P₁ P₂ h₁₂ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  set w : wSub P₁ P₂ := ⟨v - uPart P₁ P₂ v, mem_wSub.mpr (inW_sub_uPart h₁₂ v)⟩ with hw
  have hR := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg w
  rw [restrict_apply', restrict_apply'] at hR
  have h1 := polar_eq_zero_of_inW_of_mem_spanU₄ (Q := Q) h₁₂ (mem_wSub.mp (g w).2)
    (uPart_mem_spanU₄ (P₁ := P₁) (P₂ := P₂) v)
  have h2 := polar_eq_zero_of_inW_of_mem_spanU₄ (Q := Q) h₁₂ (mem_wSub.mp w.2)
    (uPart_mem_spanU₄ (P₁ := P₁) (P₂ := P₂) v)
  rw [extW_apply, QuadraticMap.map_add Q, h1, add_zero, hR]
  conv_rhs => rw [eq_sub_uPart_add (P₁ := P₁) (P₂ := P₂) v]
  rw [QuadraticMap.map_add Q, h2, add_zero]

theorem extW_mem_orthDerived (h₁₂ : P₁.Orth P₂) {g : wSub P₁ P₂ ≃ₗ[K] wSub P₁ P₂}
    (hg : g ∈ orthDerived (Q.restrict (wSub P₁ P₂))) : extW P₁ P₂ h₁₂ g ∈ orthDerived Q := by
  have hle : (TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (wSub P₁ P₂))).map
      (extW P₁ P₂ h₁₂) ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨g', hg', rfl⟩
    exact extW_mem_orthogonalGroup h₁₂ hg'
  have hmap : (orthDerived (Q.restrict (wSub P₁ P₂))).map (extW P₁ P₂ h₁₂) ≤ orthDerived Q := by
    rw [orthDerived, Subgroup.map_commutator]
    exact Subgroup.commutator_mono hle hle
  exact hmap ⟨g, hg, rfl⟩

end Extend

section Restrict

theorem apply_mem_wSub_of_mem_omFix {g : V ≃ₗ[K] V} (hg : g ∈ omFix Q P₁ P₂) {x : V}
    (hx : x ∈ wSub P₁ P₂) : g x ∈ wSub P₁ P₂ := by
  obtain ⟨hgE, h1, h2, h3, h4⟩ := mem_omFix.mp hg
  exact RootCentOmega.apply_mem_perpTwo (elementaryGroup_le_orthogonalGroup Q hgE) h1 h2 h3 h4 hx

variable (Q P₁ P₂) in
@[expose] noncomputable def resW : omFix Q P₁ P₂ →* (wSub P₁ P₂ ≃ₗ[K] wSub P₁ P₂) where
  toFun g := restrictEquiv (wSub P₁ P₂) g.1 (fun _ hx => apply_mem_wSub_of_mem_omFix g.2 hx)
    (fun _ hx => apply_mem_wSub_of_mem_omFix (inv_mem g.2) hx)
  map_one' := by
    ext u
    rfl
  map_mul' g h := by
    ext u
    rfl

theorem coe_resW_apply (g : omFix Q P₁ P₂) (w : wSub P₁ P₂) :
    (resW Q P₁ P₂ g w : V) = (g : V ≃ₗ[K] V) w :=
  rfl

theorem apply_uPart_of_mem_omFix {g : V ≃ₗ[K] V} (hg : g ∈ omFix Q P₁ P₂) (v : V) :
    g (uPart P₁ P₂ v) = uPart P₁ P₂ v := by
  obtain ⟨-, h1, h2, h3, h4⟩ := mem_omFix.mp hg
  simp only [uPart, map_add, map_smul, h1, h2, h3, h4]

theorem extW_resW (h₁₂ : P₁.Orth P₂) (g : omFix Q P₁ P₂) :
    extW P₁ P₂ h₁₂ (resW Q P₁ P₂ g) = g := by
  refine LinearEquiv.ext fun v => ?_
  rw [extW_apply, coe_resW_apply]
  conv_rhs => rw [eq_sub_uPart_add (P₁ := P₁) (P₂ := P₂) v]
  rw [map_add, apply_uPart_of_mem_omFix g.2]

theorem resW_injective (h₁₂ : P₁.Orth P₂) : Function.Injective (resW Q P₁ P₂) := by
  intro g g' h
  apply Subtype.ext
  rw [← extW_resW h₁₂ g, ← extW_resW h₁₂ g', h]

theorem resW_mem_orthogonalGroup (g : omFix Q P₁ P₂) :
    resW Q P₁ P₂ g ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (wSub P₁ P₂)) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro w
  rw [restrict_apply', restrict_apply', coe_resW_apply]
  exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
    (elementaryGroup_le_orthogonalGroup Q (mem_omFix.mp g.2).1) w

theorem commSpace_eq_map_resW (h₁₂ : P₁.Orth P₂) (g : omFix Q P₁ P₂) :
    commSpace (g : V ≃ₗ[K] V) = (commSpace (resW Q P₁ P₂ g)).map (wSub P₁ P₂).subtype := by
  ext x
  rw [mem_commSpace, Submodule.mem_map]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨resW Q P₁ P₂ g ⟨v - uPart P₁ P₂ v, mem_wSub.mpr (inW_sub_uPart h₁₂ v)⟩ -
      ⟨v - uPart P₁ P₂ v, mem_wSub.mpr (inW_sub_uPart h₁₂ v)⟩, mem_commSpace.mpr ⟨_, rfl⟩, ?_⟩
    simp only [Submodule.subtype_apply, Submodule.coe_sub, coe_resW_apply]
    conv_rhs => rw [eq_sub_uPart_add (P₁ := P₁) (P₂ := P₂) v]
    rw [map_add, apply_uPart_of_mem_omFix g.2]
    abel
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨u, rfl⟩ := mem_commSpace.mp hz
    exact ⟨u, by simp [coe_resW_apply]⟩

variable [CharP K 2] [FiniteDimensional K V]

theorem resW_mem_orthDerived (h₁₂ : P₁.Orth P₂) (hQ : (polarBilin Q).Nondegenerate)
    (hEΩ : elementaryGroup Q ≤ omegaGroup Q hQ)
    (hR : (polarBilin (Q.restrict (wSub P₁ P₂))).Nondegenerate)
    (hΩ : omegaGroup (Q.restrict (wSub P₁ P₂)) hR ≤ orthDerived (Q.restrict (wSub P₁ P₂)))
    (g : omFix Q P₁ P₂) : resW Q P₁ P₂ g ∈ orthDerived (Q.restrict (wSub P₁ P₂)) := by
  have hev : Even (finrank K (commSpace (g : V ≃ₗ[K] V))) :=
    (mem_omegaGroup.mp (hEΩ (mem_omFix.mp g.2).1)).2
  apply hΩ
  refine mem_omegaGroup.mpr ⟨resW_mem_orthogonalGroup g, ?_⟩
  rw [commSpace_eq_map_resW h₁₂ g, Submodule.finrank_map_subtype_eq] at hev
  exact hev

@[expose] noncomputable def omFixEquiv (h₁₂ : P₁.Orth P₂) (hQ : (polarBilin Q).Nondegenerate)
    (hEΩ : elementaryGroup Q ≤ omegaGroup Q hQ) (hOE : orthDerived Q ≤ elementaryGroup Q)
    (hR : (polarBilin (Q.restrict (wSub P₁ P₂))).Nondegenerate)
    (hΩ : omegaGroup (Q.restrict (wSub P₁ P₂)) hR ≤ orthDerived (Q.restrict (wSub P₁ P₂))) :
    omFix Q P₁ P₂ ≃* orthDerived (Q.restrict (wSub P₁ P₂)) where
  toFun g := ⟨resW Q P₁ P₂ g, resW_mem_orthDerived h₁₂ hQ hEΩ hR hΩ g⟩
  invFun h := ⟨extW P₁ P₂ h₁₂ h.1, mem_omFix.mpr ⟨hOE (extW_mem_orthDerived h₁₂ h.2),
    extW_apply_u h₁₂ _ mem_spanU₄_e₁, extW_apply_u h₁₂ _ mem_spanU₄_f₁,
    extW_apply_u h₁₂ _ mem_spanU₄_e₂, extW_apply_u h₁₂ _ mem_spanU₄_f₂⟩⟩
  left_inv g := Subtype.ext (extW_resW h₁₂ g)
  right_inv h := Subtype.ext (LinearEquiv.ext fun w => Subtype.ext (by
    rw [coe_resW_apply]
    exact extW_apply_w h₁₂ h.1 w))
  map_mul' g g' := Subtype.ext (map_mul (resW Q P₁ P₂) g g')

end Restrict

end RCSTOm

end CFSG.StandardType
