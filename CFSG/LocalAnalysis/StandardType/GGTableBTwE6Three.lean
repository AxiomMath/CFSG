module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6ThreeDelta

public section

namespace CFSG.StandardType

open CFSG.Assembly RecipeFieldE6

@[expose] def GGTwE6ThreeRootKernelInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → 3 ∣ 2 ^ n + 1 →
    ∀ X Y : Subgroup (MulAut (TwE6Delta.RecipeR K n)), IsElemAbelian 3 X →
      (X : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n →
      Nat.card X = 3 ^ 6 → Y ≤ X → Nat.card Y = 3 ^ 4 →
      (∃ V : Subgroup (TwE6Delta.RecipeR K n), V ≠ ⊥ ∧ IsPGroup 2 V ∧
        ∀ φ ∈ Y, ∀ v ∈ V, φ v ∈ V) →
      ∃ Y' : Subgroup (MulAut (TwE6Delta.RecipeR K n)), Y < Y' ∧ Y' ≤ X ∧
        ∃ V : Subgroup (TwE6Delta.RecipeR K n), V ≠ ⊥ ∧ IsPGroup 2 V ∧
          ∀ φ ∈ Y', ∀ v ∈ V, φ v ∈ V

@[expose] def GGTwE6ThreeFieldInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → 3 ∣ 2 ^ n + 1 →
    ∀ f ∈ LargeEvenChevFieldImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n),
      orderOf f = 3 →
    ∀ Y : Subgroup (MulAut (TwE6Delta.RecipeR K n)), IsElemAbelian 3 Y →
      (Y : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n →
      3 ^ 4 ≤ Nat.card Y → (∀ φ ∈ Y, φ * f = f * φ) →
      (∃ V : Subgroup (TwE6Delta.RecipeR K n), V ≠ ⊥ ∧ IsPGroup 2 V ∧
        ∀ φ ∈ Y, ∀ v ∈ V, φ v ∈ V) →
      ∃ V : Subgroup (TwE6Delta.RecipeR K n), V ≠ ⊥ ∧ IsPGroup 2 V ∧
        ∀ φ ∈ Y ⊔ Subgroup.zpowers f, ∀ v ∈ V, φ v ∈ V

namespace TwE6Three


variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem ggBstarBoundInnR_three (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (h3 : 3 ∣ 2 ^ n + 1) (hX : GGTwE6ThreeInndiagRankInput) (hB1 : GGTwE6ThreeRootKernelInput)
    (hB2 : GGTwE6ThreeFieldInput) :
    GGBstarBoundInnR 3 4 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  intro Eb Eh hEbI hEb h4 _ hV hle hEh hcard
  by_cases hsub : (Eh : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n
  ·
    have hE6 := hX K n hn hK h3 Eh hEh hsub
    have hEb4 : Nat.card Eb = 3 ^ 4 := by
      refine le_antisymm (Nat.le_of_mul_le_mul_left ?_ (by norm_num : 0 < 3 ^ 2)) h4
      calc 3 ^ 2 * Nat.card Eb ≤ Nat.card Eh := hcard
        _ ≤ 3 ^ 6 := hE6
        _ = 3 ^ 2 * 3 ^ 4 := by norm_num
    have hEh6 : Nat.card Eh = 3 ^ 6 := by
      refine le_antisymm hE6 ?_
      calc 3 ^ 6 = 3 ^ 2 * 3 ^ 4 := by norm_num
        _ = 3 ^ 2 * Nat.card Eb := by rw [hEb4]
        _ ≤ Nat.card Eh := hcard
    exact hB1 K n hn hK h3 Eh Eb hEh hsub hEh6 hle hEb4 hV
  ·
    obtain ⟨τ, hτ, hτI⟩ := Set.not_subset.mp hsub
    have hτ3 : τ ^ 3 = 1 := hEh.2 τ hτ
    obtain ⟨f, hf, hord, u, hu, he⟩ :=
      TwE6Dvd.exists_conj_field hn hK Nat.prime_three (by norm_num) hτI hτ3
    have huJ : u ∈ recipeJ K n := hu
    set c : MulAut (TwE6Delta.RecipeR K n) →* MulAut (TwE6Delta.RecipeR K n) :=
      (MulAut.conj u⁻¹).toMonoidHom with hcdef
    have hc : ∀ φ, c φ = u⁻¹ * φ * u := fun φ => by
      rw [hcdef, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hcτ : c τ = f := by
      rw [hc, he]
      group
    set Y := Eb.map c with hYdef
    have hYab : IsElemAbelian 3 Y := TableB.isElemAbelian_map hEb c
    have hYI : (Y : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n := by
      rintro _ ⟨φ, hφ, rfl⟩
      rw [hc]
      exact (recipeJ K n).mul_mem ((recipeJ K n).mul_mem ((recipeJ K n).inv_mem huJ)
        (mem_recipeJ_iff.mpr (hEbI hφ))) huJ
    have hYc : Nat.card Y = Nat.card Eb :=
      Subgroup.card_map_of_injective (MulAut.conj u⁻¹).injective
    have hYf : ∀ ψ ∈ Y, ψ * f = f * ψ := by
      rintro _ ⟨φ, hφ, rfl⟩
      have hcomm := TableB.IsElemAbelian.comm hEh (hle hφ) hτ
      rw [he] at hcomm
      rw [hc]
      calc u⁻¹ * φ * u * f = u⁻¹ * (φ * (u * f * u⁻¹)) * u := by group
        _ = u⁻¹ * (u * f * u⁻¹ * φ) * u := by rw [hcomm]
        _ = f * (u⁻¹ * φ * u) := by group
    obtain ⟨V, hV1, hV2, hVst⟩ := hV
    have hYV : ∃ V' : Subgroup (TwE6Delta.RecipeR K n), V' ≠ ⊥ ∧ IsPGroup 2 V' ∧
        ∀ ψ ∈ Y, ∀ v ∈ V', ψ v ∈ V' := by
      refine ⟨V.map (u⁻¹ : MulAut (TwE6Delta.RecipeR K n)).toMonoidHom, fun h => hV1 ?_,
        hV2.map _, ?_⟩
      · exact (Subgroup.map_eq_bot_iff_of_injective _ (u⁻¹ :
          MulAut (TwE6Delta.RecipeR K n)).injective).mp h
      · rintro _ ⟨φ, hφ, rfl⟩ _ ⟨v, hv, rfl⟩
        refine ⟨φ v, hVst φ hφ v hv, ?_⟩
        rw [hc]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.mul_apply, MulAut.apply_inv_self]
    obtain ⟨W, hW1, hW2, hWst⟩ :=
      hB2 K n hn hK h3 f hf hord Y hYab hYI (hYc ▸ h4) hYf hYV
    have hmap : (Eb ⊔ Subgroup.zpowers τ).map c = Y ⊔ Subgroup.zpowers f := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, hcτ]
    refine ⟨Eb ⊔ Subgroup.zpowers τ, lt_of_le_of_ne le_sup_left fun h => hτI (hEbI ?_),
      sup_le hle ((Subgroup.zpowers_le).2 hτ),
      W.map (u : MulAut (TwE6Delta.RecipeR K n)).toMonoidHom, fun h => hW1 ?_, hW2.map _, ?_⟩
    · rw [h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers τ)
    · exact (Subgroup.map_eq_bot_iff_of_injective _ u.injective).mp h
    · rintro ψ hψ _ ⟨w, hw, rfl⟩
      have hψ' : c ψ ∈ Y ⊔ Subgroup.zpowers f := by
        rw [← hmap]
        exact ⟨ψ, hψ, rfl⟩
      refine ⟨c ψ w, hWst _ hψ' w hw, ?_⟩
      rw [hc]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.mul_apply, MulAut.apply_inv_self]

end TwE6Three

theorem ggTwE6BstarThreeInput_of_inputs
    (hX : GGTwE6ThreeInndiagRankInput) (hC : GGTwE6ThreeCoverRankInput)
    (hD : GGTwE6ThreeDeltaTwoInput) (hB1 : GGTwE6ThreeRootKernelInput)
    (hB2 : GGTwE6ThreeFieldInput) : GGTwE6BstarThreeInput := by
  intro K _ _ n p hn hK _ hpn hp3
  subst hp3
  exact ⟨TwE6Three.ggBstarBoundInnR_three hn hK hpn hX hB1 hB2,
    TwE6Three.ggBstarBoundDelta_three hn hK hpn hX hC hD⟩

end CFSG.StandardType
