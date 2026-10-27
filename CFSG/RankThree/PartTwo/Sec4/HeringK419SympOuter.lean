module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419SympModel
public import CFSG.RankThree.PartTwo.KFacts.K71Sp4

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringK419

open CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.RankThree.PartTwo.KFacts

section Transvections

variable {F : Type} [Field F] [Finite F] [CharP F 2]

@[expose] def e₁ : Fin 2 ⊕ Fin 2 → F := Pi.single (Sum.inl 0) 1

theorem β_e₁ (w : Fin 2 ⊕ Fin 2 → F) : (spForm 2 F).β e₁ w = w (Sum.inr 0) := by
  rw [spForm_β, dotProduct_spJ_mulVec]
  simp [e₁, dotProduct, Pi.single_apply, Fintype.sum_unique]

theorem β_e₁_self : (spForm 2 F).β e₁ e₁ = 0 := spForm_self 2 F e₁

theorem exists_tr (d : F) : ∃ h : StatedSp 2 F, ∀ v : Fin 2 ⊕ Fin 2 → F,
    natRep (StatedSp 2 F) h v = v + (d * (spForm 2 F).β e₁ v) • e₁ := by
  obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) d
  obtain ⟨h, hh⟩ := (statedSpData 2 F).trans (c • e₁)
  refine ⟨h, fun v => ?_⟩
  have := hh v
  change natRep (StatedSp 2 F) h v = v + (spForm 2 F).β (c • e₁) v • c • e₁ at this
  have h1 : (spForm 2 F).β (c • e₁) v = c * (spForm 2 F).β e₁ v :=
    (spForm 2 F).smul_left c e₁ v
  rw [this, h1, smul_smul, hc]
  congr 2
  ring

noncomputable def tr (d : F) : StatedSp 2 F := Classical.choose (exists_tr d)

theorem tr_apply (d : F) (v : Fin 2 ⊕ Fin 2 → F) :
    natRep (StatedSp 2 F) (tr d) v = v + (d * (spForm 2 F).β e₁ v) • e₁ :=
  Classical.choose_spec (exists_tr d) v

theorem tr_add (d d' : F) : tr d * tr d' = tr (d + d') := by
  apply natRep_injective
  refine LinearMap.ext fun v => ?_
  rw [map_mul, Module.End.mul_apply, tr_apply, tr_apply, tr_apply, (spForm 2 F).add_right,
    (spForm 2 F).smul_right, β_e₁_self]
  module

theorem tr_zero : tr (0 : F) = 1 := by
  apply natRep_injective
  refine LinearMap.ext fun v => ?_
  rw [tr_apply, zero_mul, zero_smul, add_zero, map_one, Module.End.one_apply]

theorem tr_sq (d : F) : tr d * tr d = 1 := by
  rw [tr_add, CharTwo.add_self_eq_zero, tr_zero]

theorem tr_injective : Function.Injective (tr : F → StatedSp 2 F) := by
  intro d d' h
  have h1 := congrArg (fun g => natRep (StatedSp 2 F) g (Pi.single (Sum.inr 0) 1)) h
  simp only [tr_apply, β_e₁] at h1
  have h2 := congrFun h1 (Sum.inl 0)
  simpa [e₁] using h2

theorem natRep_fieldSp (σ : F ≃+* F) (g : StatedSp 2 F) (v : Fin 2 ⊕ Fin 2 → F) :
    natRep (StatedSp 2 F) (fieldSp 2 F σ g) v =
      fun i => σ (natRep (StatedSp 2 F) g (fun j => σ.symm (v j)) i) := by
  funext i
  rw [natRep_apply, coe_fieldSp, natRep_apply]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul,
    RingEquiv.apply_symm_apply]

theorem fieldSp_tr (σ : F ≃+* F) (d : F) : fieldSp 2 F σ (tr d) = tr (σ d) := by
  apply natRep_injective
  refine LinearMap.ext fun v => ?_
  rw [natRep_fieldSp, tr_apply, tr_apply]
  funext i
  simp only [β_e₁, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul,
    RingEquiv.apply_symm_apply]
  by_cases h : i = Sum.inl 0
  · subst h
    simp [e₁]
  · simp [e₁, Pi.single_apply, h]

@[expose] noncomputable def trHom : Multiplicative F →* StatedSp 2 F where
  toFun d := tr (Multiplicative.toAdd d)
  map_one' := tr_zero
  map_mul' a b := (tr_add _ _).symm

theorem isPGroup_trHom_range : IsPGroup 2 (trHom (F := F)).range := by
  rintro ⟨_, ⟨d, rfl⟩⟩
  refine ⟨1, Subtype.ext ?_⟩
  change tr (Multiplicative.toAdd d) ^ 2 ^ 1 = 1
  rw [pow_one, sq, tr_sq]

theorem fieldSp_mem_trHom_range (σ : F ≃+* F) {g : StatedSp 2 F} (hg : g ∈ (trHom (F := F)).range) :
    fieldSp 2 F σ g ∈ (trHom (F := F)).range := by
  obtain ⟨d, rfl⟩ := hg
  exact ⟨Multiplicative.ofAdd (σ (Multiplicative.toAdd d)), (fieldSp_tr σ _).symm⟩

end Transvections

section Aut

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem conj_apply_conj {P : Type*} [Group P] (c f : MulAut P) (x : P) :
    (c * f * c⁻¹) (c x) = c (f x) := by
  simp [MulAut.mul_apply]

theorem exists_two_subgroup_of_field (σ : F ≃+* F) (hσ : σ ≠ 1) (H : gsp 2 F) :
    ∃ T : Subgroup (StatedProj (StatedSp 2 F)), IsPGroup 2 T ∧
      (∀ y ∈ T, (conjAut 2 F H * fieldAut 2 F σ * (conjAut 2 F H)⁻¹) y ∈ T) ∧
      ∃ y ∈ T, (conjAut 2 F H * fieldAut 2 F σ * (conjAut 2 F H)⁻¹) y ≠ y := by
  set c : MulAut (StatedProj (StatedSp 2 F)) := conjAut 2 F H with hc
  let φ : StatedSp 2 F →* StatedProj (StatedSp 2 F) :=
    (c : StatedProj (StatedSp 2 F) ≃* StatedProj (StatedSp 2 F)).toMonoidHom.comp (proj 2 F)
  refine ⟨(trHom (F := F)).range.map φ, isPGroup_trHom_range.map φ, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    change (c * fieldAut 2 F σ * c⁻¹) (c (proj 2 F g)) ∈ _
    rw [conj_apply_conj, fieldAut_proj]
    exact ⟨_, fieldSp_mem_trHom_range σ hg, rfl⟩
  · obtain ⟨d, hd⟩ : ∃ d : F, σ d ≠ d := by
      by_contra hcon
      push Not at hcon
      exact hσ (RingEquiv.ext hcon)
    refine ⟨φ (tr d), ⟨tr d, ⟨Multiplicative.ofAdd d, rfl⟩, rfl⟩, fun h => ?_⟩
    change (c * fieldAut 2 F σ * c⁻¹) (c (proj 2 F (tr d))) = c (proj 2 F (tr d)) at h
    rw [conj_apply_conj, fieldAut_proj, fieldSp_tr] at h
    exact hd (tr_injective (proj_injective_of_charTwo (c.injective h)))

theorem exists_two_subgroup_outer {X : Type*} [Group X]
    (E : StatedProj (StatedSp 2 F) ≃* X) (β : MulAut X) (hβ3 : β ^ 3 = 1)
    (hβ : ¬ IsInnerAut β) :
    ∃ T : Subgroup X, IsPGroup 2 T ∧ (∀ t ∈ T, β t ∈ T) ∧ ∃ t ∈ T, β t ≠ t := by
  set β' : MulAut (StatedProj (StatedSp 2 F)) := MulAut.congr E.symm β with hβ'
  have hβ'3 : β' ^ 3 = 1 := by rw [hβ', ← map_pow, hβ3, map_one]
  have hnot : β' ∉ (conjAut 2 F).range := by
    rintro ⟨A, hA⟩
    apply hβ
    rw [← isInnerAut_congr E.symm, ← hβ', ← hA]
    exact conjAut_mem_inner_of_charTwo A
  obtain ⟨σ, hσ3, H, hH⟩ := sp4_even_order_three_field_descent β' hβ'3 hnot
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ3
    omega
  obtain ⟨T, hT, hTn, y, hyT, hy⟩ := exists_two_subgroup_of_field σ hσ1 H
  rw [← hH] at hTn hy
  have hβE : ∀ t, β (E t) = E (β' t) := fun t => by
    have h : β' t = E.symm (β (E t)) := rfl
    rw [h, MulEquiv.apply_symm_apply]
  refine ⟨T.map E.toMonoidHom, hT.map _, ?_, E y, ⟨y, hyT, rfl⟩, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, hβE]
    exact ⟨_, hTn t ht, rfl⟩
  · intro h
    rw [hβE] at h
    exact hy (E.injective h)

end Aut

end CFSG.RankThree.PartTwo.Sec4.HeringK419
