module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G44Main
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G44Mod
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GR41Trans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LargeExtraspecial.O62

theorem s16c1G44_kappa_surjective {W : Type} [CommGroup W] (β : W ≃* Multiplicative V₀) :
    Function.Surjective (s16c1G_kappa β) := by
  intro e
  let A : V₀ ≃+ V₀ :=
    { toFun := fun v => Multiplicative.toAdd (β (e (β.symm (Multiplicative.ofAdd v))))
      invFun := fun v => Multiplicative.toAdd (β (e.symm (β.symm (Multiplicative.ofAdd v))))
      left_inv := fun v => by simp
      right_inv := fun v => by simp
      map_add' := fun x y => by simp [ofAdd_add, map_mul, toAdd_mul] }
  let g : V₀ ≃ₗ[ZMod 2] V₀ := { A with map_smul' := fun c x => ZMod.map_smul A c x }
  refine ⟨g, ?_⟩
  ext x
  apply β.injective
  rw [s16c1G_kappa_apply]
  simp [g, A]

theorem s16c1G44_quadF2_one_of {W : Type*} [CommGroup W] {Q : W → ZMod 2} (hQ : IsQuadF2 Q) :
    Q 1 = 0 := by
  have h := hQ.1 1 1 1
  simp only [polarQ, mul_one] at h
  generalize Q 1 = a at h ⊢
  revert a
  decide

theorem s16c1G44_modelForm {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {β : W ≃* Multiplicative V₀} (hβ : IsOmegaModel H β) :
    IsMinusQuadF2 (fun x => qModel true (Multiplicative.toAdd (β x))) ∧
      QuadInvariant (fun x => qModel true (Multiplicative.toAdd (β x))) H := by
  refine ⟨s16c1G_isMinusQuadF2_comp β s16c1G_isMinusQuadF2_qMul, fun φ hφ x => ?_⟩
  obtain ⟨g, hg, hgφ⟩ := (hβ φ).1 hφ
  show qModel true (Multiplicative.toAdd (β (φ x))) = qModel true (Multiplicative.toAdd (β x))
  rw [hgφ x]
  exact s16c1G_qModel_map hg _

theorem s16c1G44_form_eq {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {β : W ≃* Multiplicative V₀} (hβ : IsOmegaModel H β) (hsing : OmegaFormSing H)
    {Q : W → ZMod 2} (hQ : IsMinusQuadF2 Q) (hQH : QuadInvariant Q H) (x : W) :
    Q x = qModel true (Multiplicative.toAdd (β x)) := by
  obtain ⟨hQ₀, hQ₀H⟩ := s16c1G44_modelForm hβ
  by_cases hx : x = 1
  · subst hx
    rw [s16c1G44_quadF2_one_of hQ.1.1]
    simp
  · have h1 := hsing Q hQ hQH x hx
    have h2 := hsing _ hQ₀ hQ₀H x hx
    have h3 : Q x = 0 ↔ qModel true (Multiplicative.toAdd (β x)) = 0 := h1.trans h2.symm
    rcases s16c1G_qModel_cases (Multiplicative.toAdd (β x)) with h | h
    · rw [h]
      exact h3.2 h
    · rw [h]
      rcases zmod2_eq_zero_or_eq_one (Q x) with h' | h'
      · exact absurd (h3.1 h') (by rw [h]; exact one_ne_zero)
      · exact h'

theorem omegaKitD_of_kitC (hkitC : OmegaKitC) : OmegaKitD := by
  intro W _ _ H h
  obtain ⟨hsing, hnorm, -, -, -⟩ := hkitC W H h
  obtain ⟨β, hβ⟩ := natOmegaMinus_exists_model h
  intro Q hQ hQH E hEN hEab P hP t htE ht1 htP hgood
  have hQeq : ∀ x, Q x = qModel true (Multiplicative.toAdd (β x)) :=
    s16c1G44_form_eq hβ hsing hQ hQH
  let κe : (V₀ ≃ₗ[ZMod 2] V₀) ≃* MulAut W :=
    MulEquiv.ofBijective (s16c1G_kappa β)
      ⟨s16c1G_kappa_injective β, s16c1G44_kappa_surjective β⟩
  let E' : Subgroup (V₀ ≃ₗ[ZMod 2] V₀) := E.comap κe.toMonoidHom
  have hmemE' : ∀ g, g ∈ E' ↔ s16c1G_kappa β g ∈ E := fun g => Iff.rfl
  have hcard : Nat.card E' = Nat.card E := by
    have h1 : E' = E.map κe.symm.toMonoidHom := Subgroup.comap_equiv_eq_map_symm κe E
    rw [h1]
    exact Subgroup.card_map_of_injective κe.symm.injective
  have hiso : ∀ g ∈ E', ∀ v, qModel true (g v) = qModel true v := by
    intro g hg v
    have h1 := hnorm Q hQ hQH (s16c1G_kappa β g) (hEN ((hmemE' g).1 hg))
      (β.symm (Multiplicative.ofAdd v))
    rw [hQeq, hQeq, s16c1G_kappa_apply] at h1
    simpa using h1
  have hab : ∀ g ∈ E', ∀ k ∈ E', g * k = k * g := by
    intro g hg k hk
    apply s16c1G_kappa_injective β
    rw [map_mul, map_mul]
    exact hEab.1 _ ((hmemE' g).1 hg) _ ((hmemE' k).1 hk)
  have hP' : (P.map β.toMonoidHom).index = 2 :=
    (Subgroup.index_map_equiv P β).trans hP
  obtain ⟨t', ht'⟩ := s16c1G44_kappa_surjective β t
  have ht'E : t' ∈ E' := by
    rw [hmemE', ht']
    exact htE
  have ht'1 : t' ≠ 1 := by
    rintro rfl
    apply ht1
    rw [← ht', map_one]
  have ht'P : ∀ p ∈ P.map β.toMonoidHom, t' (Multiplicative.toAdd p) = Multiplicative.toAdd p := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := congrArg β (htP x hx)
    rw [← ht', s16c1G_kappa_apply] at h1
    exact congrArg Multiplicative.toAdd h1
  have hgood' : ∀ g ∈ E', ∀ u ∈ P.map β.toMonoidHom,
      qModel true (g (Multiplicative.toAdd u) + Multiplicative.toAdd u) = 0 := by
    intro g hg u
    rintro ⟨x, hx, rfl⟩
    have h1 := hgood _ ((hmemE' g).1 hg) x hx
    rw [hQeq, map_mul, map_inv, s16c1G_kappa_apply] at h1
    have h2 : Multiplicative.toAdd (Multiplicative.ofAdd (g (Multiplicative.toAdd (β x))) *
        (β x)⁻¹) = g (Multiplicative.toAdd (β x)) + Multiplicative.toAdd (β x) := by
      rw [toAdd_mul, toAdd_inv, toAdd_ofAdd, CFSG.LargeExtraspecial.OrthoF2.vec_neg]
    rw [h2] at h1
    exact h1
  rw [← hcard]
  exact s16c1G44_axisBound_lin E' hiso hab hP' ht'E ht'1 ht'P hgood'

section Result

variable {G : Type} [Group G] [Finite G]

theorem r16_44_of_kitC (D : Data G) (h22 : R1622 D) (h41 : R16_41 D) (h42 : R16_42 D)
    (hkitB : OmegaKitB) (hkitC : OmegaKitC) : R16_44 D :=
  r16_44_of D h22 h41 h42 hkitB (omegaKitD_of_kitC hkitC)

end Result

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
