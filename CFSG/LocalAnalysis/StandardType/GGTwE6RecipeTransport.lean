module

public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Recipe
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootKillDefs
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType.TwE6Transport

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.TwE6RootKill

section Elt

variable {K : Type} [Field K]
  (σ : K ≃+* K) {R : Type*} [Group R] (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* R)

theorem twNormTwo_of_conj {A : Subgroup (ModGL TwistTag.E6.tag K)} {V : Subgroup R} (hV : V ≠ ⊥)
    (hV2 : IsPGroup 2 V) (h : ∀ x ∈ A, ∀ v ∈ V, ∃ v' ∈ V,
      x * (ε.symm v : ModGL TwistTag.E6.tag K) * x⁻¹ = ε.symm v') : TwNormTwo K σ A := by
  refine ⟨(V.map ε.symm.toMonoidHom).map (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype,
    Subgroup.map_subtype_le _, fun hbot => hV ?_, (hV2.map _).map _, ?_⟩
  · rwa [Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _),
      Subgroup.map_eq_bot_iff_of_injective (f := ε.symm.toMonoidHom) _ ε.symm.injective] at hbot
  · rintro x hx _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    obtain ⟨v', hv', he⟩ := h x hx v hv
    exact ⟨_, ⟨v', hv', rfl⟩, he.symm⟩

@[expose] noncomputable def eltMat (B : Subgroup R) : Subgroup (ModGL TwistTag.E6.tag K) :=
  (B.comap ε.toMonoidHom).map (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype

theorem mem_eltMat {B : Subgroup R} {x : ModGL TwistTag.E6.tag K} :
    x ∈ eltMat σ ε B ↔ ∃ h : x ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom, ε ⟨x, h⟩ ∈ B :=
  ⟨by rintro ⟨c, hc, rfl⟩; exact ⟨c.2, hc⟩, fun ⟨h, hB⟩ => ⟨⟨x, h⟩, hB, rfl⟩⟩

theorem eltMat_le_twistedE6RootGroup (B : Subgroup R) : eltMat σ ε B ≤ twistedE6RootGroup K σ :=
  Subgroup.map_subtype_le _

theorem card_eltMat (B : Subgroup R) : Nat.card (eltMat σ ε B) = Nat.card B := by
  rw [eltMat, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact Nat.card_congr (ε.toEquiv.subtypeEquiv fun _ => Iff.rfl)

theorem isElemAbelian_eltMat {p : ℕ} {B : Subgroup R} (hB : IsElemAbelian p B) :
    IsElemAbelian p (eltMat σ ε B) :=
  (hB.comap (f := ε.toMonoidHom) ε.injective).map _

theorem twNormTwo_eltMat {B U : Subgroup R} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hBU : B ≤ Subgroup.normalizer (U : Set R)) : TwNormTwo K σ (eltMat σ ε B) := by
  refine twNormTwo_of_conj σ ε hU hU2 ?_
  rintro _ ⟨c, hc, rfl⟩ v hv
  refine ⟨ε c * v * (ε c)⁻¹, (Subgroup.mem_normalizer_iff.1 (hBU hc) v).1 hv, ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  rfl

theorem commute_of_forall_commute_eltMat {B : Subgroup R} {u : ModGL TwistTag.E6.tag K}
    (hu : u ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    (h : ∀ x ∈ eltMat σ ε B, Commute u x) {b : R} (hb : b ∈ B) : Commute (ε ⟨u, hu⟩) b := by
  have hb' : ε (ε.symm b) ∈ B := by rwa [MulEquiv.apply_symm_apply]
  have hc : Commute (⟨u, hu⟩ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) (ε.symm b) :=
    Subtype.ext (h _ ⟨ε.symm b, hb', rfl⟩).eq
  have := hc.map ε
  rwa [MulEquiv.apply_symm_apply] at this

end Elt

section Aut


variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {R : Type*} [Group R]
  (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* R)

omit [Finite K] in
theorem eltMat_le (B : Subgroup R) : eltMat σ ε B ≤ twistedE6InndiagGL K σ :=
  (eltMat_le_twistedE6RootGroup σ ε B).trans le_sup_left

@[expose] noncomputable def recipeConj : RecipeExcLang.twInndiagGroup K σ →* MulAut R :=
  (MulAut.congr ε).toMonoidHom.comp (RecipeExcLang.twConj K σ)

theorem recipeConj_eq (w : RecipeExcLang.twInndiagGroup K σ) :
    recipeConj σ ε w = MulAut.congr ε (RecipeExcLang.twConj K σ w) := rfl

theorem recipeConj_apply (w : RecipeExcLang.twInndiagGroup K σ) (r : R) :
    recipeConj σ ε w r = ε (RecipeExcLang.twConj K σ w (ε.symm r)) := rfl

@[expose] noncomputable def recipeMat (Y : Subgroup (MulAut R)) :
    Subgroup (ModGL TwistTag.E6.tag K) :=
  (Y.comap (recipeConj σ ε)).map (RecipeExcLang.twInndiagGroup K σ).subtype

@[expose] noncomputable def matRecipe (A : Subgroup (ModGL TwistTag.E6.tag K)) :
    Subgroup (MulAut R) :=
  (A.comap (RecipeExcLang.twInndiagGroup K σ).subtype).map (recipeConj σ ε)

theorem mem_recipeMat {Y : Subgroup (MulAut R)} {x : ModGL TwistTag.E6.tag K} :
    x ∈ recipeMat σ ε Y ↔
      ∃ h : x ∈ RecipeExcLang.twInndiagGroup K σ, recipeConj σ ε ⟨x, h⟩ ∈ Y :=
  ⟨by rintro ⟨w, hw, rfl⟩; exact ⟨w.2, hw⟩, fun ⟨h, hY⟩ => ⟨⟨x, h⟩, hY, rfl⟩⟩

theorem recipeMat_le_twInndiagGroup (Y : Subgroup (MulAut R)) :
    recipeMat σ ε Y ≤ RecipeExcLang.twInndiagGroup K σ :=
  Subgroup.map_subtype_le _

theorem recipeMat_le (Y : Subgroup (MulAut R)) : recipeMat σ ε Y ≤ twistedE6InndiagGL K σ :=
  (recipeMat_le_twInndiagGroup σ ε Y).trans
    (NoOffTwE6Three.twInndiagGroup_le_twistedE6InndiagGL σ)

theorem recipeMat_mono {Y Y' : Subgroup (MulAut R)} (h : Y ≤ Y') :
    recipeMat σ ε Y ≤ recipeMat σ ε Y' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem twNormTwo_recipeMat {Y : Subgroup (MulAut R)} {V : Subgroup R} (hV : V ≠ ⊥)
    (hV2 : IsPGroup 2 V) (hYV : ∀ φ ∈ Y, ∀ v ∈ V, φ v ∈ V) : TwNormTwo K σ (recipeMat σ ε Y) := by
  refine twNormTwo_of_conj σ ε hV hV2 ?_
  rintro _ ⟨w, hw, rfl⟩ v hv
  refine ⟨recipeConj σ ε w v, hYV _ hw v hv, ?_⟩
  rw [recipeConj_apply, MulEquiv.symm_apply_apply, RecipeExcLang.coe_twConj]
  rfl

theorem matRecipe_le {A : Subgroup (ModGL TwistTag.E6.tag K)} {Y : Subgroup (MulAut R)}
    (hA : A ≤ recipeMat σ ε Y) : matRecipe σ ε A ≤ Y := by
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨w', hw', he⟩ := hA hw
  exact (Subtype.ext he : w' = w) ▸ hw'

theorem le_matRecipe {A : Subgroup (ModGL TwistTag.E6.tag K)} {Y : Subgroup (MulAut R)}
    (hY : Y ≤ (recipeConj σ ε).range) (hA : recipeMat σ ε Y ≤ A) : Y ≤ matRecipe σ ε A := by
  intro φ hφ
  obtain ⟨w, rfl⟩ := hY hφ
  exact ⟨w, hA ⟨w, hφ, rfl⟩, rfl⟩

theorem apply_eq_of_forall_commute {A : Subgroup (ModGL TwistTag.E6.tag K)}
    {u : ModGL TwistTag.E6.tag K} (hu : u ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    (h : ∀ x ∈ A, Commute u x) {φ : MulAut R} (hφ : φ ∈ matRecipe σ ε A) :
    φ (ε ⟨u, hu⟩) = ε ⟨u, hu⟩ := by
  obtain ⟨w, hw, rfl⟩ := hφ
  have hc : (w : ModGL TwistTag.E6.tag K) * u = u * w := (h _ (Subgroup.mem_comap.1 hw)).symm.eq
  rw [recipeConj_apply, MulEquiv.symm_apply_apply]
  refine congrArg ε (Subtype.ext ?_)
  rw [RecipeExcLang.coe_twConj]
  exact (congrArg (· * (w : ModGL TwistTag.E6.tag K)⁻¹) hc).trans (mul_inv_cancel_right u _)

theorem apply_eq_of_forall_commute_recipeMat {Y : Subgroup (MulAut R)}
    (hY : Y ≤ (recipeConj σ ε).range) {u : ModGL TwistTag.E6.tag K}
    (hu : u ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    (h : ∀ x ∈ recipeMat σ ε Y, Commute u x) {φ : MulAut R} (hφ : φ ∈ Y) :
    φ (ε ⟨u, hu⟩) = ε ⟨u, hu⟩ :=
  apply_eq_of_forall_commute σ ε hu h (le_matRecipe σ ε hY le_rfl hφ)

theorem comap_congr_le_range {Y : Subgroup (MulAut R)} (hY : Y ≤ (recipeConj σ ε).range) :
    Y.comap (MulAut.congr ε).toMonoidHom ≤ (RecipeExcLang.twConj K σ).range := by
  intro φ hφ
  obtain ⟨w, hw⟩ := hY hφ
  have hw' : MulAut.congr ε (RecipeExcLang.twConj K σ w) = MulAut.congr ε φ := hw
  exact ⟨w, (MulAut.congr ε).injective hw'⟩

section Injective

variable {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ n)
include hn hK hσ

theorem recipeConj_injective : Function.Injective (recipeConj σ ε) :=
  (MulAut.congr ε).injective.comp (NoOffTwE6Three.twConj_injective hn hK σ hσ)

theorem card_recipeMat {Y : Subgroup (MulAut R)} (hY : Y ≤ (recipeConj σ ε).range) :
    Nat.card (recipeMat σ ε Y) = Nat.card Y := by
  rw [recipeMat, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
    ← Subgroup.card_map_of_injective (recipeConj_injective σ ε hn hK hσ),
    Subgroup.map_comap_eq, inf_eq_right.2 hY]

theorem card_matRecipe {A : Subgroup (ModGL TwistTag.E6.tag K)}
    (hA : A ≤ RecipeExcLang.twInndiagGroup K σ) : Nat.card (matRecipe σ ε A) = Nat.card A := by
  rw [matRecipe, Subgroup.card_map_of_injective (recipeConj_injective σ ε hn hK hσ)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv

theorem isElemAbelian_recipeMat {p : ℕ} {Y : Subgroup (MulAut R)} (hY : IsElemAbelian p Y) :
    IsElemAbelian p (recipeMat σ ε Y) :=
  (hY.comap (recipeConj_injective σ ε hn hK hσ)).map _

end Injective

theorem exists_recipeConj {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    ∃ σ : K ≃+* K, (∀ c, σ c = c ^ 2 ^ n) ∧
      ∃ ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n,
        ∀ φ, φ ∈ (recipeConj σ ε).range ↔ φ ∈ TwE6Delta.RecipeI K n := by
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  have hσ : ∀ c, iterateFrobeniusEquiv K 2 n c = c ^ 2 ^ n := fun c => by
    rw [iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv hn hK _ hσ
  refine ⟨_, hσ, ε, fun φ => ⟨?_, fun hφ => ?_⟩⟩
  · rintro ⟨w, rfl⟩
    rw [recipeConj_eq]
    exact (hε _).2 ⟨w, rfl⟩
  · obtain ⟨w, hw⟩ := (hε ((MulAut.congr ε).symm φ)).1 (by rwa [MulEquiv.apply_symm_apply])
    exact ⟨w, by rw [recipeConj_eq, hw, MulEquiv.apply_symm_apply]⟩

end Aut

end CFSG.StandardType.TwE6Transport

end
