module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeE8
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoRank

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace TableBExcTwo

section BaseChange

variable
  {τ : Tag} {K K' : Type} [Field K] [Field K']

theorem baseChangeGL_mem_adjointGroup (f : K →+* K') {g : ModGL τ K}
    (hg : g ∈ adjointGroup τ K) : baseChangeGL f g ∈ adjointGroup τ K' := by
  have hle : (adjointGroup τ K).map (baseChangeGL f) ≤ adjointGroup τ K' := by
    rw [map_baseChangeGL_adjointGroup, Subgroup.closure_le]
    rintro _ ⟨i, c, rfl | rfl⟩
    exacts [xUnit_mem_adjointGroup i _, yUnit_mem_adjointGroup i _]
  exact hle (Subgroup.mem_map_of_mem _ hg)

variable (τ) in
@[expose] noncomputable def adjointMap (f : K →+* K') : adjointGroup τ K →* adjointGroup τ K' :=
  ((baseChangeGL f).comp (adjointGroup τ K).subtype).codRestrict _ fun g =>
    baseChangeGL_mem_adjointGroup f g.2

theorem coe_adjointMap (f : K →+* K') (g : adjointGroup τ K) :
    (adjointMap τ f g : ModGL τ K') = baseChangeGL f (g : ModGL τ K) :=
  rfl

theorem adjointMap_injective (f : K →+* K') : Function.Injective (adjointMap τ f) := by
  intro g g' h
  apply Subtype.ext
  apply baseChangeGL_injective f
  have := congrArg Subtype.val h
  simpa [coe_adjointMap] using this

end BaseChange

theorem three_dvd_card_galoisField_sub_one : 3 ∣ Nat.card (GaloisField 2 2) - 1 := by
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num

section Rank

variable
  {K : Type} [Field K] [Finite K]

theorem card_le_of_galoisField {τ : Tag} {r : ℕ}
    (h4 : ∀ E : Subgroup (adjointGroup τ (GaloisField 2 2)), IsElemAbelian 3 E →
      Nat.card E ≤ 3 ^ r)
    (hK : Nat.card K = 2) {E : Subgroup (adjointGroup τ K)} (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 ^ r := by
  have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK]; norm_num)
  obtain ⟨f⟩ := TableBF4Two.exists_ringHom_galoisField K hK
  have h1 := h4 (E.map (adjointMap τ f)) (TableB.isElemAbelian_map hE _)
  rwa [Subgroup.card_map_of_injective (adjointMap_injective f)] at h1

theorem card_le_adjoint_E7 (hK : Nat.card K = 2) {E : Subgroup (adjointGroup .E7 K)}
    (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 7 := by
  refine card_le_of_galoisField (fun E hE => ?_) hK hE
  have h3 := three_dvd_card_galoisField_sub_one
  exact (ggE7ThreeToralRankInput_holds (GaloisField 2 2) h3).card_le
    (TableBExc.card_torusPow_E7 Nat.prime_three h3) hE

theorem card_le_adjoint_E8 (hK : Nat.card K = 2) {E : Subgroup (adjointGroup .E8 K)}
    (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 8 := by
  refine card_le_of_galoisField (fun E hE => ?_) hK hE
  have h3 := three_dvd_card_galoisField_sub_one
  exact (ggE8ThreeToralRankInput_holds (GaloisField 2 2) h3).card_le
    (TableBExc.card_torusPow_E8 Nat.prime_three h3) hE

theorem card_le_recipe_E7 (hK : Nat.card K = 2) {E : Subgroup (TableBExc.RecipeGroup .E7 K)}
    (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 7 := by
  have h := card_le_adjoint_E7 hK (E := E.map (TableBExc.recipeEquiv .E7 K).toMonoidHom)
    (TableB.isElemAbelian_map hE _)
  rwa [Subgroup.card_map_of_injective (TableBExc.recipeEquiv .E7 K).injective] at h

theorem card_le_recipe_E8 (hK : Nat.card K = 2) {E : Subgroup (TableBExc.RecipeGroup .E8 K)}
    (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 8 := by
  have h := card_le_adjoint_E8 hK (E := E.map (TableBExc.recipeEquiv .E8 K).toMonoidHom)
    (TableB.isElemAbelian_map hE _)
  rwa [Subgroup.card_map_of_injective (TableBExc.recipeEquiv .E8 K).injective] at h

end Rank

end TableBExcTwo

end CFSG.StandardType
