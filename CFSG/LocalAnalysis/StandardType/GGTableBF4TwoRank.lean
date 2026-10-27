module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4Three
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace TableBF4Two

section BaseChange

variable
  {K K' : Type} [Field K] [Field K']

theorem baseChangeGL_mem_adjointGroup_F4 (f : K →+* K') {g : ModGL .F4 K}
    (hg : g ∈ adjointGroup .F4 K) : baseChangeGL f g ∈ adjointGroup .F4 K' := by
  have hle : (adjointGroup .F4 K).map (baseChangeGL f) ≤ adjointGroup .F4 K' := by
    rw [map_baseChangeGL_adjointGroup, Subgroup.closure_le]
    rintro _ ⟨i, c, rfl | rfl⟩
    exacts [xUnit_mem_adjointGroup i _, yUnit_mem_adjointGroup i _]
  exact hle (Subgroup.mem_map_of_mem _ hg)

@[expose] noncomputable def adjointMap (f : K →+* K') :
    adjointGroup .F4 K →* adjointGroup .F4 K' :=
  ((baseChangeGL f).comp (adjointGroup .F4 K).subtype).codRestrict _ fun g =>
    baseChangeGL_mem_adjointGroup_F4 f g.2

theorem coe_adjointMap (f : K →+* K') (g : adjointGroup .F4 K) :
    (adjointMap f g : ModGL .F4 K') = baseChangeGL f (g : ModGL .F4 K) :=
  rfl

theorem adjointMap_injective (f : K →+* K') : Function.Injective (adjointMap f) := by
  intro g g' h
  apply Subtype.ext
  apply baseChangeGL_injective f
  have := congrArg Subtype.val h
  simpa [coe_adjointMap] using this

end BaseChange

theorem exists_ringHom_galoisField (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) : Nonempty (K →+* GaloisField 2 2) := by
  have : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  exact ⟨(algebraMap (ZMod 2) (GaloisField 2 2)).comp (ZMod.ringEquiv K hK').symm.toRingHom⟩

section Rank


theorem card_le_adjointF4 {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 4 := by
  obtain ⟨f⟩ := exists_ringHom_galoisField K hK
  have h4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have h3 : 3 ∣ Nat.card (GaloisField 2 2) - 1 := by
    rw [h4]
  have hT := TableBF4.ggF4ToralRankInput_three (K := GaloisField 2 2) h3
  have h1 := hT.card_le Nat.prime_three h3 (E := E.map (adjointMap f))
    (TableB.isElemAbelian_map hE _)
  rwa [Subgroup.card_map_of_injective (adjointMap_injective f)] at h1

theorem card_le_recipeGroup {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {E : Subgroup (TableBF4.RecipeGroup K)} (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 4 := by
  have h := card_le_adjointF4 hK (E := E.map (TableBF4.recipeEquiv K).toMonoidHom)
    (TableB.isElemAbelian_map hE _)
  rwa [Subgroup.card_map_of_injective (TableBF4.recipeEquiv K).injective] at h

end Rank

end TableBF4Two

end CFSG.StandardType
