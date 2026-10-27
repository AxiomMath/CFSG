module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

@[expose] def NoncyclicDatum {S : Type} [Group S] (β' : MulAut S) : Prop :=
  ∃ R P : Subgroup S, P ≤ R ∧ IsPGroup 2 P ∧ ¬ IsCyclic P ∧ Group.IsSolvable R ∧
    (∀ r ∈ R, β' r = r) ∧ (∀ c : S, β' c = c → ∀ r ∈ R, c * r * c⁻¹ ∈ R) ∧
    Subgroup.center S ≤ R ∧ ¬ 9 ∣ Nat.card R

theorem NoncyclicDatum.conj {S : Type} [Group S] {β' : MulAut S} (h : NoncyclicDatum β')
    (γ : MulAut S) : NoncyclicDatum (γ * β' * γ⁻¹) := by
  obtain ⟨R, P, hPR, hP2, hPnc, hRs, hfix, hnorm, hZR, h9⟩ := h
  let eP : P ≃* P.map γ.toMonoidHom := Subgroup.equivMapOfInjective P γ.toMonoidHom γ.injective
  let eR : R ≃* R.map γ.toMonoidHom := Subgroup.equivMapOfInjective R γ.toMonoidHom γ.injective
  have hinv : ∀ x : S, γ (γ⁻¹ x) = x := fun x => MulAut.apply_inv_self S γ x
  have hinv' : ∀ x : S, γ⁻¹ (γ x) = x := fun x => MulAut.inv_apply_self S γ x
  refine ⟨R.map γ.toMonoidHom, P.map γ.toMonoidHom, Subgroup.map_mono hPR,
    IsPGroup.of_surjective hP2 eP.toMonoidHom eP.surjective,
    fun hc => hPnc (eP.isCyclic.mpr hc),
    Group.isSolvable_of_surjective (f := eR.toMonoidHom) eR.surjective, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨r, hr, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.mul_apply, hinv', hfix r hr]
  · rintro c hc _ ⟨r, hr, rfl⟩
    have hc' : β' (γ⁻¹ c) = γ⁻¹ c := by
      apply γ.injective
      have := hc
      simp only [MulAut.mul_apply] at this
      rw [this, hinv]
    refine ⟨γ⁻¹ c * r * (γ⁻¹ c)⁻¹, hnorm _ hc' r hr, ?_⟩
    simp [hinv]
  · intro z hz
    have hz' : γ⁻¹ z ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := Subgroup.mem_center_iff.mp hz (γ g)
      apply γ.injective
      simp only [map_mul, hinv]
      rw [this]
    exact ⟨γ⁻¹ z, hZR hz', by simp [hinv]⟩
  · rw [Subgroup.card_map_of_injective γ.injective]
    exact h9

@[expose] def fixedSub {S : Type} [Group S] (β' : MulAut S) : Subgroup S :=
  MonoidHom.eqLocus β'.toMonoidHom (MonoidHom.id S)

theorem mem_fixedSub {S : Type} [Group S] {β' : MulAut S} {s : S} :
    s ∈ fixedSub β' ↔ β' s = s := Iff.rfl

@[expose] def FixedDatum (F : Type) [Group F] : Prop :=
  ∃ R P : Subgroup F, P ≤ R ∧ IsPGroup 2 P ∧ ¬ IsCyclic P ∧ Group.IsSolvable R ∧
    ∀ c : F, ∀ r ∈ R, c * r * c⁻¹ ∈ R

@[expose] def FixedDatumZ (F : Type) [Group F] : Prop :=
  ∃ R P : Subgroup F, P ≤ R ∧ IsPGroup 2 P ∧ ¬ IsCyclic P ∧ Group.IsSolvable R ∧
    (∀ c : F, ∀ r ∈ R, c * r * c⁻¹ ∈ R) ∧ Subgroup.center F ≤ R ∧ ¬ 9 ∣ Nat.card R

theorem FixedDatumZ.fixedDatum {F : Type} [Group F] (h : FixedDatumZ F) : FixedDatum F := by
  obtain ⟨R, P, hPR, hP2, hPnc, hRs, hRn, -, -⟩ := h
  exact ⟨R, P, hPR, hP2, hPnc, hRs, hRn⟩

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end
