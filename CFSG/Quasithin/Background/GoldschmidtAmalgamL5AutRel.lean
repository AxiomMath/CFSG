module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL5AutTr
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL5Rel

public section

namespace CFSG.Quasithin.F6.GoldAmL5

open CFSG.Quasithin.F6.GoldAmL4

variable {D E : Type*} [Group D] [Group E]

structure TauRel (a b s ρ x y τ : E) : Prop where
  hτ : τ * τ = 1
  hτa : τ * a * τ = a⁻¹ * b * b
  hτb : τ * b * τ = a * a * b
  hτs : τ * s * τ = s * ρ
  hτρ : τ * ρ * τ = ρ
  hτx : τ * x * τ = x
  hτy : τ * y * τ = y⁻¹

section Rel

variable {a b s x y ρ τ : E}

theorem TauRel.conj_embR (hT : TRel a b s) (hR : RhoRel a b s ρ) (h : TauRel a b s ρ x y τ)
    (w : Tr) : τ * embR hT hR w * τ = embR hT hR (thetaStd w) := by
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right h.hτ
  let κ : E →* E := (MulAut.conj τ).toMonoidHom
  have hκ : ∀ g, κ g = τ * g * τ := fun g => by
    show τ * g * τ⁻¹ = _
    rw [hτinv]
  have key : κ.comp (embR hT hR) = (embR hT hR).comp thetaStd := by
    apply tr_hom_ext
    · simp only [MonoidHom.comp_apply, embR_rA hT hR, embR_rB hT hR, hκ, thetaStd_rA, map_mul,
        map_inv]
      exact h.hτa
    · simp only [MonoidHom.comp_apply, embR_rB hT hR, hκ, thetaStd_rB, map_mul, embR_rA hT hR]
      exact h.hτb
    · simp only [MonoidHom.comp_apply, embR_rS hT hR, hκ, thetaStd_rS, map_mul, embR_rR hT hR]
      exact h.hτs
    · simp only [MonoidHom.comp_apply, embR_rR hT hR, hκ, thetaStd_rR]
      exact h.hτρ
  have := congrArg (fun f : Tr →* E => f w) key
  simpa only [MonoidHom.comp_apply, hκ] using this

end Rel

section Ext

variable {P : Type*} [Group P]

theorem vertex_ext_aut {emb : P →* D} {emb' : P →* E} {θ : P →* P} {y : D} {y' : E} {τ : D}
    {τ' : E} {B : Subgroup D} {B' : Subgroup E}
    (hB : B = Subgroup.closure ((emb.range : Set D) ∪ {y}))
    (hB' : B' = Subgroup.closure ((emb'.range : Set E) ∪ {y'})) (ε : ℤ)
    (hemb : ∀ w : P, emb w ∈ B) (hemb' : ∀ w : P, emb' w ∈ B') (hyB : y ∈ B) (hyB' : y' ∈ B')
    (φ : ↥B ≃* ↥B')
    (hφ : ∀ w : P, ((φ ⟨emb w, hemb w⟩ : ↥B') : E) = emb' w)
    (hφy : ((φ ⟨y, hyB⟩ : ↥B') : E) = y')
    (hτ : τ * τ = 1) (hτ' : τ' * τ' = 1)
    (hτe : ∀ w : P, τ * emb w * τ = emb (θ w)) (hτe' : ∀ w : P, τ' * emb' w * τ' = emb' (θ w))
    (hτy : τ * y * τ = y ^ ε) (hτy' : τ' * y' * τ' = y' ^ ε)
    (hτB : τ ∉ B) (hτB' : τ' ∉ B') :
    ∃ Φ : ↥(Subgroup.closure ((B : Set D) ∪ {τ})) ≃* ↥(Subgroup.closure ((B' : Set E) ∪ {τ'})),
      (∀ w : P, ((Φ ⟨emb w, Subgroup.subset_closure (Or.inl (hemb w))⟩ :
          ↥(Subgroup.closure ((B' : Set E) ∪ {τ'}))) : E) = emb' w) ∧
      ((Φ ⟨y, Subgroup.subset_closure (Or.inl hyB)⟩ :
          ↥(Subgroup.closure ((B' : Set E) ∪ {τ'}))) : E) = y' ∧
      ((Φ ⟨τ, Subgroup.subset_closure (Or.inr rfl)⟩ :
          ↥(Subgroup.closure ((B' : Set E) ∪ {τ'}))) : E) = τ' := by
  have hgen : ∀ g ∈ ((emb.range : Set D) ∪ {y}), τ * g * τ ∈ B := by
    rintro g (⟨w, rfl⟩ | hg)
    · rw [hτe w]; exact hemb _
    · rw [Set.mem_singleton_iff] at hg
      rw [hg, hτy]
      exact B.zpow_mem hyB ε
  have hgen' : ∀ g ∈ ((emb'.range : Set E) ∪ {y'}), τ' * g * τ' ∈ B' := by
    rintro g (⟨w, rfl⟩ | hg)
    · rw [hτe' w]; exact hemb' _
    · rw [Set.mem_singleton_iff] at hg
      rw [hg, hτy']
      exact B'.zpow_mem hyB' ε
  have hφcomp : ∀ (g : D) (hg : g ∈ B), g ∈ ((emb.range : Set D) ∪ {y}) →
      ((φ ⟨τ * g * τ, normalizes_of_gens hB hτ hgen g hg⟩ : ↥B') : E) =
        τ' * ((φ ⟨g, hg⟩ : ↥B') : E) * τ' := by
    rintro g hg (⟨w, rfl⟩ | hg')
    · have e1 : (⟨τ * emb w * τ, normalizes_of_gens hB hτ hgen _ hg⟩ : ↥B) =
          ⟨emb (θ w), hemb _⟩ := Subtype.ext (hτe w)
      have e0 : (⟨emb w, hg⟩ : ↥B) = ⟨emb w, hemb w⟩ := rfl
      rw [e1, e0, hφ (θ w), hφ w, hτe' w]
    · have hgy : g = y := hg'
      have e1 : (⟨τ * g * τ, normalizes_of_gens hB hτ hgen _ hg⟩ : ↥B) =
          ⟨y ^ ε, B.zpow_mem hyB ε⟩ :=
        Subtype.ext (by rw [hgy]; exact hτy : τ * g * τ = y ^ ε)
      have e0 : (⟨g, hg⟩ : ↥B) = ⟨y, hyB⟩ := Subtype.ext hgy
      have e2 : (⟨y ^ ε, B.zpow_mem hyB ε⟩ : ↥B) = (⟨y, hyB⟩ : ↥B) ^ ε := rfl
      rw [e1, e2, e0, map_zpow, Subgroup.coe_zpow, hφy, hτy']
  obtain ⟨Φ, hΦ, hΦτ⟩ := exists_vertex_ext hB hB' hτ hτ' hgen hgen' hτB hτB' φ hφcomp
  refine ⟨Φ, fun w => ?_, ?_, hΦτ⟩
  · rw [hΦ (emb w) (hemb w)]; exact hφ w
  · rw [hΦ y hyB]; exact hφy

end Ext

section Uniq

theorem closure_five_union_eq (a b s ρ v τ : D) :
    Subgroup.closure ((Subgroup.closure ({a, b, s, ρ, v} : Set D) : Set D) ∪ {τ}) =
      Subgroup.closure ({a, b, s, ρ, v, τ} : Set D) := by
  rw [← closure_union_closure]
  congr 1
  ext g
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

variable {a b s x y ρ τ : D} {a' b' s' x' y' ρ' τ' : E}

theorem isAmalgamIso_of_tuples_aut
    (hA : ARel a b s x) (hAρ : ARho a b s x ρ) (hB : MRelB a b s ρ y)
    (hτ : TauRel a b s ρ x y τ)
    (hA' : ARel a' b' s' x') (hAρ' : ARho a' b' s' x' ρ') (hB' : MRelB a' b' s' ρ' y')
    (hτ' : TauRel a' b' s' ρ' x' y' τ')
    (hcard : Nat.card (Subgroup.closure ({a, b, s, ρ} : Set D)) = 64)
    (hcard' : Nat.card (Subgroup.closure ({a', b', s', ρ'} : Set E)) = 64)
    (hτy : τ ∉ Subgroup.closure ({a, b, s, ρ, y} : Set D))
    (hτx : τ ∉ Subgroup.closure ({a, b, s, ρ, x} : Set D))
    (hτy' : τ' ∉ Subgroup.closure ({a', b', s', ρ', y'} : Set E))
    (hτx' : τ' ∉ Subgroup.closure ({a', b', s', ρ', x'} : Set E))
    (hT : Subgroup.closure ({a, b, s, ρ, y, τ} : Set D) ⊓
      Subgroup.closure ({a, b, s, ρ, x, τ} : Set D) = Subgroup.closure ({a, b, s, ρ, τ} : Set D))
    (hT' : Subgroup.closure ({a', b', s', ρ', y', τ'} : Set E) ⊓
      Subgroup.closure ({a', b', s', ρ', x', τ'} : Set E) =
        Subgroup.closure ({a', b', s', ρ', τ'} : Set E)) :
    CFSG.Quasithin.F6.IsAmalgamIso (Subgroup.closure ({a, b, s, ρ, y, τ} : Set D))
      (Subgroup.closure ({a, b, s, ρ, x, τ} : Set D))
      (Subgroup.closure ({a', b', s', ρ', y', τ'} : Set E))
      (Subgroup.closure ({a', b', s', ρ', x', τ'} : Set E)) := by
  have hT0 := hA.toTRel
  have hR := hAρ.toRhoRel
  have hT0' := hA'.toTRel
  have hR' := hAρ'.toRhoRel
  have hinj := embR_injective hT0 hR hcard
  have hinj' := embR_injective hT0' hR' hcard'
  have eY := closure_range_union_R hT0 hR y
  have eX := closure_range_union_R hT0 hR x
  have eY' := closure_range_union_R hT0' hR' y'
  have eX' := closure_range_union_R hT0' hR' x'
  have eTτ := closure_range_union_R hT0 hR τ
  have eTτ' := closure_range_union_R hT0' hR' τ'
  obtain ⟨φy, hφy, hφyy⟩ := (hB.vertexSpec hT0 hR hinj).vertex_iso hinj hinj' Q2_or'
    (hB'.vertexSpec hT0' hR' hinj')
  obtain ⟨φx, hφx, hφxx⟩ := (aRho_vertexSpec hA hAρ hinj).vertex_iso hinj hinj' Q1_or'
    (aRho_vertexSpec hA' hAρ' hinj')
  have hembY : ∀ w : Tr, embR hT0 hR w ∈ Subgroup.closure (((embR hT0 hR).range : Set D) ∪ {y}) :=
    fun w => Subgroup.subset_closure (Or.inl ⟨w, rfl⟩)
  have hembX : ∀ w : Tr, embR hT0 hR w ∈ Subgroup.closure (((embR hT0 hR).range : Set D) ∪ {x}) :=
    fun w => Subgroup.subset_closure (Or.inl ⟨w, rfl⟩)
  have hembY' : ∀ w : Tr,
      embR hT0' hR' w ∈ Subgroup.closure (((embR hT0' hR').range : Set E) ∪ {y'}) :=
    fun w => Subgroup.subset_closure (Or.inl ⟨w, rfl⟩)
  have hembX' : ∀ w : Tr,
      embR hT0' hR' w ∈ Subgroup.closure (((embR hT0' hR').range : Set E) ∪ {x'}) :=
    fun w => Subgroup.subset_closure (Or.inl ⟨w, rfl⟩)
  have hyY : y ∈ Subgroup.closure (((embR hT0 hR).range : Set D) ∪ {y}) :=
    Subgroup.subset_closure (Or.inr rfl)
  have hxX : x ∈ Subgroup.closure (((embR hT0 hR).range : Set D) ∪ {x}) :=
    Subgroup.subset_closure (Or.inr rfl)
  have hyY' : y' ∈ Subgroup.closure (((embR hT0' hR').range : Set E) ∪ {y'}) :=
    Subgroup.subset_closure (Or.inr rfl)
  have hxX' : x' ∈ Subgroup.closure (((embR hT0' hR').range : Set E) ∪ {x'}) :=
    Subgroup.subset_closure (Or.inr rfl)
  obtain ⟨Φy, hΦye, hΦyy, hΦyτ⟩ := vertex_ext_aut (θ := thetaStd) rfl rfl (-1) hembY hembY' hyY
    hyY' φy hφy hφyy hτ.hτ hτ'.hτ (fun w => hτ.conj_embR hT0 hR w)
    (fun w => hτ'.conj_embR hT0' hR' w) (by rw [zpow_neg_one]; exact hτ.hτy)
    (by rw [zpow_neg_one]; exact hτ'.hτy) (by rw [eY]; exact hτy) (by rw [eY']; exact hτy')
  obtain ⟨Φx, hΦxe, hΦxx, hΦxτ⟩ := vertex_ext_aut (θ := thetaStd) rfl rfl 1 hembX hembX' hxX
    hxX' φx hφx hφxx hτ.hτ hτ'.hτ (fun w => hτ.conj_embR hT0 hR w)
    (fun w => hτ'.conj_embR hT0' hR' w) (by rw [zpow_one]; exact hτ.hτx)
    (by rw [zpow_one]; exact hτ'.hτx) (by rw [eX]; exact hτx) (by rw [eX']; exact hτx')
  have eHy : Subgroup.closure ((Subgroup.closure (((embR hT0 hR).range : Set D) ∪ {y}) : Set D) ∪
      {τ}) = Subgroup.closure ({a, b, s, ρ, y, τ} : Set D) := by
    rw [eY]; exact closure_five_union_eq a b s ρ y τ
  have eHx : Subgroup.closure ((Subgroup.closure (((embR hT0 hR).range : Set D) ∪ {x}) : Set D) ∪
      {τ}) = Subgroup.closure ({a, b, s, ρ, x, τ} : Set D) := by
    rw [eX]; exact closure_five_union_eq a b s ρ x τ
  have eHy' : Subgroup.closure ((Subgroup.closure (((embR hT0' hR').range : Set E) ∪ {y'}) :
      Set E) ∪ {τ'}) = Subgroup.closure ({a', b', s', ρ', y', τ'} : Set E) := by
    rw [eY']; exact closure_five_union_eq a' b' s' ρ' y' τ'
  have eHx' : Subgroup.closure ((Subgroup.closure (((embR hT0' hR').range : Set E) ∪ {x'}) :
      Set E) ∪ {τ'}) = Subgroup.closure ({a', b', s', ρ', x', τ'} : Set E) := by
    rw [eX']; exact closure_five_union_eq a' b' s' ρ' x' τ'
  rw [← eHy, ← eHx, ← eHy', ← eHx']
  rw [← eHy, ← eHx] at hT
  rw [← eHy', ← eHx'] at hT'
  have hn : ∀ g ∈ (embR hT0 hR).range, τ * g * τ ∈ (embR hT0 hR).range := by
    rintro _ ⟨w, rfl⟩
    rw [hτ.conj_embR hT0 hR w]
    exact ⟨thetaStd w, rfl⟩
  have hn' : ∀ g ∈ (embR hT0' hR').range, τ' * g * τ' ∈ (embR hT0' hR').range := by
    rintro _ ⟨w, rfl⟩
    rw [hτ'.conj_embR hT0' hR' w]
    exact ⟨thetaStd w, rfl⟩
  have memT : ∀ g : D, g ∈ Subgroup.closure ({a, b, s, ρ, τ} : Set D) →
      g ∈ (embR hT0 hR).range ∨ g * τ ∈ (embR hT0 hR).range := by
    intro g hg
    rw [← eTτ, closure_union_eq hτ.hτ hn] at hg
    exact hg
  have memT' : ∀ g : E, g ∈ Subgroup.closure ({a', b', s', ρ', τ'} : Set E) →
      g ∈ (embR hT0' hR').range ∨ g * τ' ∈ (embR hT0' hR').range := by
    intro g hg
    rw [← eTτ', closure_union_eq hτ'.hτ hn'] at hg
    exact hg
  have mY : ∀ w : Tr, embR hT0 hR w ∈ Subgroup.closure ((Subgroup.closure (((embR hT0 hR).range :
      Set D) ∪ {y}) : Set D) ∪ {τ}) := fun w => Subgroup.subset_closure (Or.inl (hembY w))
  have mX : ∀ w : Tr, embR hT0 hR w ∈ Subgroup.closure ((Subgroup.closure (((embR hT0 hR).range :
      Set D) ∪ {x}) : Set D) ∪ {τ}) := fun w => Subgroup.subset_closure (Or.inl (hembX w))
  have tY : τ ∈ Subgroup.closure ((Subgroup.closure (((embR hT0 hR).range : Set D) ∪ {y}) :
      Set D) ∪ {τ}) := Subgroup.subset_closure (Or.inr rfl)
  have tX : τ ∈ Subgroup.closure ((Subgroup.closure (((embR hT0 hR).range : Set D) ∪ {x}) :
      Set D) ∪ {τ}) := Subgroup.subset_closure (Or.inr rfl)
  refine isAmalgamIso_of_agree Φy Φx ?_ ?_
  · intro g hgy hgx
    have hgT : g ∈ Subgroup.closure ({a, b, s, ρ, τ} : Set D) := by
      rw [← hT]; exact ⟨hgy, hgx⟩
    rcases memT g hgT with ⟨w, rfl⟩ | ⟨w, hw⟩
    · exact (hΦye w).trans (hΦxe w).symm
    · have e : g = embR hT0 hR w * τ := by
        calc g = g * τ * τ := by rw [mul_assoc, hτ.hτ, mul_one]
          _ = embR hT0 hR w * τ := by rw [← hw]
      rw [iso_value_mul Φy hgy (mY w) tY e, iso_value_mul Φx hgx (mX w) tX e, hΦye w, hΦyτ,
        hΦxe w, hΦxτ]
  · intro z hzy hzx
    have hzT : z ∈ Subgroup.closure ({a', b', s', ρ', τ'} : Set E) := by
      rw [← hT']; exact ⟨hzy, hzx⟩
    rcases memT' z hzT with ⟨w, rfl⟩ | ⟨w, hw⟩
    · exact ⟨embR hT0 hR w, mY w, mX w, hΦye w⟩
    · have e : z = embR hT0' hR' w * τ' := by
        calc z = z * τ' * τ' := by rw [mul_assoc, hτ'.hτ, mul_one]
          _ = embR hT0' hR' w * τ' := by rw [← hw]
      refine ⟨embR hT0 hR w * τ, Subgroup.mul_mem _ (mY w) tY, Subgroup.mul_mem _ (mX w) tX, ?_⟩
      rw [iso_value_mul Φy (Subgroup.mul_mem _ (mY w) tY) (mY w) tY rfl, hΦye w, hΦyτ, e]

end Uniq

end CFSG.Quasithin.F6.GoldAmL5
