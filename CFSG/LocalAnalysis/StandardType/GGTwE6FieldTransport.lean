module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport

public section

namespace CFSG.StandardType.TwE6FieldCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TwE6Transport

section Transport

variable {K : Type} [Field K]

theorem exists_twistedTransport_field_of_eq (n : ℕ) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (S : (Fin TwistTag.E6.tag.rank → ℤ) → Prop) (hS : S = IsRoot TwistTag.E6.tag) :
    ∃ (e : Module.End K (RootModule TwistTag.E6.tag K) ≃* Module.End K (MarkChev.Space S K))
      (T : ↥⁅twistedFixedGroup .E6 K σ, twistedFixedGroup .E6 K σ⁆ ≃*
        ↥(MarkChev.twistedH TwistTag.E6.tag.cartan S K TwistTag.E6.perm n)),
      (∀ g, ((T g : MarkChev.GLS S K) : Module.End K (MarkChev.Space S K)) =
        e ((g : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K))) ∧
      (∀ b : Fin TwistTag.E6.tag.rank → Kˣ, e (rootDiag b) = TableB.markDiag S K b) ∧
      ∀ (δ : K ≃+* K) A, e (entrywise δ.toRingHom A) =
        MarkChev.entrywise S K δ (map_zero δ) (e A) := by
  subst hS
  exact ⟨MulEquiv.refl _, MulEquiv.subgroupCongr (twistedH_eq_commutator K .E6 n σ hσ).symm,
    fun _ => rfl, fun b => (TableB.TwE6.markDiag_isRoot b).symm, fun _ _ => rfl⟩

theorem exists_twistedTransport_field (n : ℕ) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    ∃ (e : Module.End K (RootModule TwistTag.E6.tag K) ≃*
        Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K))
      (T : ↥⁅twistedFixedGroup .E6 K σ, twistedFixedGroup .E6 K σ⁆ ≃*
        ↥(LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n)),
      (∀ g, ((T g : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
          Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) =
        e ((g : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K))) ∧
      (∀ b : Fin TwistTag.E6.tag.rank → Kˣ,
        e (rootDiag b) = LargeEvenDiagMap TwistTag.E6.tag.cartan K b) ∧
      ∀ (δ : K ≃+* K) A, e (entrywise δ.toRingHom A) =
        LargeEvenEntrywise TwistTag.E6.tag.cartan K δ (map_zero δ) (e A) := by
  obtain ⟨e, T, hT, he, hF⟩ := exists_twistedTransport_field_of_eq n σ hσ _
    (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag)
  refine ⟨e, T.trans (MulEquiv.subgroupCongr (largeEvenTwistedH_eq _ K _ n).symm),
    fun g => hT g, fun b => ?_, hF⟩
  rw [he, TableB.largeEvenDiagMap_eq_markDiag]

end Transport


variable {K : Type} [Field K] [Finite K]

theorem exists_recipeConj_field {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    ∃ ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n,
      (∀ φ, φ ∈ (recipeConj σ ε).range ↔ φ ∈ TwE6Delta.RecipeI K n) ∧
      ∀ f ∈ LargeEvenChevFieldImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n),
        ∃ δ : K ≃+* K, f = MulAut.congr ε (fieldActor σ δ) := by
  have hσ' : ∀ c, σ.toRingHom c = c ^ 2 ^ n := hσ
  obtain ⟨e, T₀, hT₀, he, hF⟩ := exists_twistedTransport_field (K := K) n σ.toRingHom hσ'
  have hΓ :=
    (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hn K hK σ.toRingHom hσ').2.2.1
  have hZ : Subgroup.center ↥(SmallKG.twH K n) = ⊥ := TwE6Delta.center_recipeH_eq_bot hn hK
  set T : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* ↥(SmallKG.twH K n) :=
    (MulEquiv.subgroupCongr hΓ.symm).trans T₀ with hTdef
  have hT : ∀ g : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      ((T g : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
          Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) =
        e ((g : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) :=
    fun g => hT₀ _
  refine ⟨SmallKG.recipeEquiv T hZ, fun φ => ⟨?_, fun hφ => ?_⟩, fun f hf => ?_⟩
  · rintro ⟨w, rfl⟩
    have hw := TwE6DD2.twInndiag_le_compatHat σ w.2
    have h1 := TwE6DD2.recipeKappa_mem_recipeI T hZ e hT he ⟨w, hw⟩
    rw [(MulEquiv.symm_apply_eq _).1 (TwE6DD2.congr_symm_recipeKappa σ T hZ ⟨w, hw⟩)] at h1
    exact h1
  · obtain ⟨m, hm⟩ := SmallKG.recipeI_subset_range T hZ e hT he hφ
    exact ⟨⟨m, TwE6DD2.compatHat_le_twInndiag σ m.2⟩, ((MulEquiv.symm_apply_eq _).1
      (TwE6DD2.congr_symm_recipeKappa σ T hZ m)).symm.trans hm⟩
  obtain ⟨δ, hδ⟩ := hf
  refine ⟨δ, MulEquiv.ext fun r => ?_⟩
  obtain ⟨g, rfl⟩ := (SmallKG.recipeEquiv T hZ).surjective r
  have hrel : ((T (fieldActor σ δ g) : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
      Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) =
      LargeEvenEntrywise TwistTag.E6.tag.cartan K δ (map_zero δ)
        ((T g : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
          Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) := by
    rw [hT, hT]
    exact hF δ _
  refine (hδ _ _ hrel).trans ?_
  show SmallKG.recipeEquiv T hZ (fieldActor σ δ g) = SmallKG.recipeEquiv T hZ
    (fieldActor σ δ ((SmallKG.recipeEquiv T hZ).symm (SmallKG.recipeEquiv T hZ g)))
  rw [MulEquiv.symm_apply_apply]

theorem orderOf_fieldActor {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ n) (δ : K ≃+* K) :
    orderOf (fieldActor (t := TwistTag.E6) σ δ) = orderOf δ := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hn K hK σ hσ
  have hinj : Function.Injective (fieldActorHom (t := TwistTag.E6) σ) :=
    Function.LeftInverse.injective (g := Θ) fun γ =>
      hΘ (fieldActor σ γ) 1 1 γ (by rw [map_one, map_one, one_mul, one_mul])
  exact orderOf_injective _ hinj δ

end CFSG.StandardType.TwE6FieldCore

end
