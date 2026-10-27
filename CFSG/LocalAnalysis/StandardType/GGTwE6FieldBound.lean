module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6ThreeRank
public import CFSG.LocalAnalysis.StandardType.GGBstarLemmaC

public section

namespace CFSG.StandardType.TwE6FieldCore

open CFSG.Assembly

theorem le_sup_zpowers_of_card_le_mul {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Eb Eh : Subgroup G} (hle : Eb ≤ Eh) (hEh : IsElemAbelian p Eh)
    (hcard : Nat.card Eh ≤ p * Nat.card Eb) {φ : G} (hφ : φ ∈ Eh) (hφb : φ ∉ Eb) :
    Eh ≤ Eb ⊔ Subgroup.zpowers φ := by
  have := Fact.mk hp
  set H := Eb ⊔ Subgroup.zpowers φ with hH
  have hHEh : H ≤ Eh := sup_le hle ((Subgroup.zpowers_le).2 hφ)
  have hHp : IsPGroup p H := (TableB.isPGroup_of_isElemAbelian hEh).to_le hHEh
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hHp
  have hr := Subgroup.relIndex_mul_card Eb H
  rw [inf_of_le_left le_sup_left] at hr
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (hk ▸ Subgroup.relIndex_dvd_card Eb H)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.relIndex_eq_one] at hj
    exact hφb (hj (Subgroup.mem_sup_right (Subgroup.mem_zpowers φ)))
  have hpj : p ≤ Eb.relIndex H := hj ▸ Nat.le_self_pow hj0 p
  have hcardH : Nat.card Eh ≤ Nat.card H := by
    rw [← hr]
    exact hcard.trans (Nat.mul_le_mul_right _ hpj)
  exact (Subgroup.eq_of_le_of_card_ge hHEh hcardH).ge


variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem ggInnerDiagBound2L_of_field (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {p r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hcore : ∀ f ∈ LargeEvenChevFieldImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n),
      orderOf f = p → ∀ Y : Subgroup (MulAut (TwE6Delta.RecipeR K n)), IsElemAbelian p Y →
      (Y : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n →
      p ^ r ≤ Nat.card Y → (∀ φ ∈ Y, φ * f = f * φ) →
      (∃ V : Subgroup (TwE6Delta.RecipeR K n), V ≠ ⊥ ∧ IsPGroup 2 V ∧
        ∀ φ ∈ Y, ∀ v ∈ V, φ v ∈ V) →
      ∃ V : Subgroup (TwE6Delta.RecipeR K n), V ≠ ⊥ ∧ IsPGroup 2 V ∧
        ∀ φ ∈ Y ⊔ Subgroup.zpowers f, ∀ v ∈ V, φ v ∈ V) :
    GGInnerDiagBound2L p r (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  intro Eb Eh hEbI hEb hr _ hle hEh hcard hnot ⟨V, hV1, hV2, hVst⟩
  have := TwE6Delta.finite_mulAut_recipeR hK
  obtain ⟨τ, hτ, hτI⟩ := Set.not_subset.mp hnot
  obtain ⟨f, hf, hord, u, hu, he⟩ := TwE6Dvd.exists_conj_field hn hK hp hp2 hτI (hEh.2 τ hτ)
  have huJ : u ∈ TwE6Three.recipeJ K n := hu
  set c : MulAut (TwE6Delta.RecipeR K n) →* MulAut (TwE6Delta.RecipeR K n) :=
    (MulAut.conj u⁻¹).toMonoidHom with hcdef
  have hc : ∀ φ, c φ = u⁻¹ * φ * u := fun φ => by
    rw [hcdef, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hcτ : c τ = f := by
    rw [hc, he]
    group
  have hYI : ((Eb.map c : Subgroup _) : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆
      TwE6Delta.RecipeI K n := by
    rintro _ ⟨φ, hφ, rfl⟩
    rw [hc]
    exact (TwE6Three.recipeJ K n).mul_mem ((TwE6Three.recipeJ K n).mul_mem
      ((TwE6Three.recipeJ K n).inv_mem huJ) (TwE6Three.mem_recipeJ_iff.mpr (hEbI hφ))) huJ
  have hYc : Nat.card (Eb.map c) = Nat.card Eb :=
    Subgroup.card_map_of_injective (MulAut.conj u⁻¹).injective
  have hYf : ∀ ψ ∈ Eb.map c, ψ * f = f * ψ := by
    rintro _ ⟨φ, hφ, rfl⟩
    have hcomm := TableB.IsElemAbelian.comm hEh (hle hφ) hτ
    rw [he] at hcomm
    rw [hc]
    calc u⁻¹ * φ * u * f = u⁻¹ * (φ * (u * f * u⁻¹)) * u := by group
      _ = u⁻¹ * (u * f * u⁻¹ * φ) * u := by rw [hcomm]
      _ = f * (u⁻¹ * φ * u) := by group
  have hYV : ∀ ψ ∈ Eb.map c, ∀ v ∈ V.map (u⁻¹ : MulAut (TwE6Delta.RecipeR K n)).toMonoidHom,
      ψ v ∈ V.map (u⁻¹ : MulAut (TwE6Delta.RecipeR K n)).toMonoidHom := by
    rintro _ ⟨φ, hφ, rfl⟩ _ ⟨v, hv, rfl⟩
    refine ⟨φ v, hVst φ hφ v hv, ?_⟩
    rw [hc]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.mul_apply, MulAut.apply_inv_self]
  obtain ⟨W, hW1, hW2, hWst⟩ := hcore f hf hord _ (TableB.isElemAbelian_map hEb c) hYI
    (hYc ▸ hr) hYf ⟨_, fun h => hV1 ((Subgroup.map_eq_bot_iff_of_injective _
      (u⁻¹ : MulAut (TwE6Delta.RecipeR K n)).injective).mp h), hV2.map _, hYV⟩
  have hmap : (Eb ⊔ Subgroup.zpowers τ).map c = Eb.map c ⊔ Subgroup.zpowers f := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hcτ]
  have hEh' := le_sup_zpowers_of_card_le_mul hp hle hEh hcard hτ fun h => hτI (hEbI h)
  refine ⟨W.map (u : MulAut (TwE6Delta.RecipeR K n)).toMonoidHom, fun h => hW1
    ((Subgroup.map_eq_bot_iff_of_injective _ u.injective).mp h), hW2.map _, ?_⟩
  rintro ψ hψ _ ⟨w, hw, rfl⟩
  have hψ' : c ψ ∈ Eb.map c ⊔ Subgroup.zpowers f := by
    rw [← hmap]
    exact ⟨ψ, hEh' hψ, rfl⟩
  refine ⟨c ψ w, hWst _ hψ' w hw, ?_⟩
  rw [hc]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.mul_apply, MulAut.apply_inv_self]

end CFSG.StandardType.TwE6FieldCore

end
