module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangInner
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherE6
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace RecipeExcLang

set_option linter.unusedSectionVars false

section RootSet

variable {r : ℕ} (S : (Fin r → ℤ) → Prop) (K : Type) [Field K]

@[expose] def markDiagImage (H : Subgroup (MarkChev.GLS S K)) :
    Set (MulAut (LargeEvenCenterQuot H)) :=
  {φ | ∃ a : Fin r → Kˣ,
    (∀ h : H, ∃ h' : H, ((h' : MarkChev.GLS S K) : Module.End K (MarkChev.Space S K)) *
      TableB.markDiag S K a = TableB.markDiag S K a * ((h : MarkChev.GLS S K) : Module.End K _)) ∧
    (∀ h' : H, ∃ h : H, ((h' : MarkChev.GLS S K) : Module.End K (MarkChev.Space S K)) *
      TableB.markDiag S K a = TableB.markDiag S K a * ((h : MarkChev.GLS S K) : Module.End K _)) ∧
    LargeEvenGraphAut (LargeEvenCenterMk H)
      (fun h h' => ((h' : MarkChev.GLS S K) : Module.End K (MarkChev.Space S K)) *
        TableB.markDiag S K a =
          TableB.markDiag S K a * ((h : MarkChev.GLS S K) : Module.End K _)) φ}

@[expose] def markIDImage (H : Subgroup (MarkChev.GLS S K)) :
    Set (MulAut (LargeEvenCenterQuot H)) :=
  (Subgroup.closure (LargeEvenInnSet _ ∪ markDiagImage S K H) :
    Set (MulAut (LargeEvenCenterQuot H)))

theorem largeEvenChevIDImage_eq (A : Matrix (Fin r) (Fin r) ℤ)
    (H : Subgroup (LargeEvenChevGL A K)) :
    LargeEvenChevIDImage A K H = markIDImage (LargeEvenIsRoot A) K H := by
  unfold LargeEvenChevIDImage markIDImage LargeEvenChevDiagImage markDiagImage
  simp only [TableB.largeEvenDiagMap_eq_markDiag]

end RootSet

@[expose] def ChevConjOn (K : Type) [Field K] (τ : Tag) (S : (Fin τ.rank → ℤ) → Prop) (p : ℕ) :
    Prop :=
  GGRawFieldConj p (LargeEvenCenterQuot (MarkChev.chevH τ.cartan S K false))
    (markIDImage S K (MarkChev.chevH τ.cartan S K false))
    (RecipeFieldExcInn.markFieldImage S K (MarkChev.chevH τ.cartan S K false))

theorem ChevConjOn.of_eq {K : Type} [Field K] {τ : Tag} {S S' : (Fin τ.rank → ℤ) → Prop} {p : ℕ}
    (hS : S = S') (h : ChevConjOn K τ S p) : ChevConjOn K τ S' p :=
  hS ▸ h


section Adjoint

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem markDiag_rel_iff (b : Fin τ.rank → Kˣ) (g g' : ModGL τ K) :
    (g' : Module.End K (RootModule τ K)) * TableB.markDiag (IsRoot τ) K b =
        TableB.markDiag (IsRoot τ) K b * (g : Module.End K (RootModule τ K)) ↔
      g' = rootDiagUnit τ b * g * (rootDiagUnit τ b)⁻¹ := by
  rw [TableB.TwE6.markDiag_isRoot]
  change (g' : Module.End K (RootModule τ K)) * (rootDiagUnit τ b : ModGL τ K) =
      (rootDiagUnit τ b : ModGL τ K) * (g : Module.End K (RootModule τ K)) ↔ _
  rw [← Units.val_mul, ← Units.val_mul, Units.val_inj]
  constructor
  · intro h
    rw [← h, mul_inv_cancel_right]
  · intro h
    rw [h, inv_mul_cancel_right]

@[expose] noncomputable def autEquiv (τ : Tag) (K : Type) [Field K] [Finite K] :
    MulAut (LargeEvenCenterQuot (adjointGroup τ K)) ≃* MulAut (adjointGroup τ K) :=
  MulAut.congr (centerQuotEquivOfBot center_adjointGroup_eq_bot)

theorem autEquiv_apply (φ : MulAut (LargeEvenCenterQuot (adjointGroup τ K)))
    (h : adjointGroup τ K) :
    LargeEvenCenterMk (adjointGroup τ K) (autEquiv τ K φ h) =
      φ (LargeEvenCenterMk (adjointGroup τ K) h) :=
  (congr_centerQuotEquivOfBot_mk center_adjointGroup_eq_bot φ h).symm

theorem autEquiv_symm_apply (α : MulAut (adjointGroup τ K)) (h : adjointGroup τ K) :
    (autEquiv τ K).symm α (LargeEvenCenterMk (adjointGroup τ K) h) =
      LargeEvenCenterMk (adjointGroup τ K) (α h) := by
  rw [← autEquiv_apply, MulEquiv.apply_symm_apply]

theorem mk_injective : Function.Injective (LargeEvenCenterMk (adjointGroup τ K)) := by
  rw [← MonoidHom.ker_eq_bot_iff, LargeEvenCenterMk, QuotientGroup.ker_mk',
    center_adjointGroup_eq_bot]

theorem inndiagConj_of_mem (g : adjointGroup τ K) :
    inndiagConj τ K ⟨g, adjointGroup_le_inndiagGroup g.2⟩ = MulAut.conj g :=
  MulEquiv.ext fun h => Subtype.ext (by rw [coe_inndiagConj]; rfl)

theorem exists_inndiagConj_of_mem_markID {u : MulAut (LargeEvenCenterQuot (adjointGroup τ K))}
    (hu : u ∈ markIDImage (IsRoot τ) K (adjointGroup τ K)) :
    ∃ w : inndiagGroup τ K, autEquiv τ K u = inndiagConj τ K w := by
  have hle : Subgroup.closure (LargeEvenInnSet _ ∪ markDiagImage (IsRoot τ) K (adjointGroup τ K)) ≤
      (inndiagConj τ K).range.comap (autEquiv τ K).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro φ (⟨x, rfl⟩ | ⟨a, -, -, hG⟩)
    · refine ⟨⟨_, adjointGroup_le_inndiagGroup
        (centerQuotEquivOfBot center_adjointGroup_eq_bot x).2⟩, ?_⟩
      rw [inndiagConj_of_mem]
      exact (mulAut_congr_conj _ x).symm
    · refine ⟨⟨_, rootDiagUnit_mem_inndiagGroup a⟩, MulEquiv.ext fun h => ?_⟩
      apply mk_injective
      change LargeEvenCenterMk _ (inndiagConj τ K ⟨_, rootDiagUnit_mem_inndiagGroup a⟩ h) =
        LargeEvenCenterMk _ (autEquiv τ K φ h)
      rw [autEquiv_apply]
      refine (hG h ⟨_, conj_rootDiagUnit_mem_adjointGroup a h.2⟩ ?_).symm
      exact (markDiag_rel_iff a _ _).2 rfl
  obtain ⟨w, hw⟩ := hle hu
  exact ⟨w, hw.symm⟩

theorem autEquiv_symm_conj (g : adjointGroup τ K) :
    (autEquiv τ K).symm (MulAut.conj g) =
      MulAut.conj ((centerQuotEquivOfBot center_adjointGroup_eq_bot).symm g) := by
  rw [MulEquiv.symm_apply_eq, autEquiv, mulAut_congr_conj, MulEquiv.apply_symm_apply]

theorem inndiagConj_mem_markID (w : inndiagGroup τ K) :
    (autEquiv τ K).symm (inndiagConj τ K w) ∈ markIDImage (IsRoot τ) K (adjointGroup τ K) := by
  obtain ⟨w, b, j, hj, rfl⟩ := w
  have hsplit : (⟨rootDiagUnit τ b * j, ⟨b, j, hj, rfl⟩⟩ : inndiagGroup τ K) =
      ⟨rootDiagUnit τ b, rootDiagUnit_mem_inndiagGroup b⟩ *
        ⟨j, adjointGroup_le_inndiagGroup hj⟩ := rfl
  have hinn : inndiagConj τ K ⟨j, adjointGroup_le_inndiagGroup hj⟩ = MulAut.conj ⟨j, hj⟩ :=
    inndiagConj_of_mem ⟨j, hj⟩
  rw [hsplit, map_mul, map_mul, hinn, autEquiv_symm_conj]
  refine Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr ⟨b, ?_, ?_, ?_⟩))
    (Subgroup.subset_closure (Or.inl ⟨_, rfl⟩))
  · intro h
    exact ⟨⟨_, conj_rootDiagUnit_mem_adjointGroup b h.2⟩, (markDiag_rel_iff b _ _).2 rfl⟩
  · intro h'
    have hmem : (rootDiagUnit τ b)⁻¹ * (h' : ModGL τ K) * rootDiagUnit τ b ∈ adjointGroup τ K := by
      have := conj_rootDiagUnit_mem_adjointGroup b⁻¹ h'.2
      rwa [← rootDiagUnit_inv, inv_inv] at this
    refine ⟨⟨_, hmem⟩, (markDiag_rel_iff b _ _).2 ?_⟩
    change (h' : ModGL τ K) = rootDiagUnit τ b * ((rootDiagUnit τ b)⁻¹ * (h' : ModGL τ K) *
      rootDiagUnit τ b) * (rootDiagUnit τ b)⁻¹
    group
  · intro h h' hrel
    rw [autEquiv_symm_apply]
    congr 1
    apply Subtype.ext
    rw [coe_inndiagConj]
    exact ((markDiag_rel_iff b _ _).1 hrel).symm

theorem autEquiv_eq_entrywise_of_mem_markField {φ : MulAut (LargeEvenCenterQuot (adjointGroup τ K))}
    (hφ : φ ∈ RecipeFieldExcInn.markFieldImage (IsRoot τ) K (adjointGroup τ K)) :
    ∃ σ : K ≃+* K, autEquiv τ K φ = entrywiseAdjointAut τ σ := by
  obtain ⟨σ, hG⟩ := hφ
  refine ⟨σ, MulEquiv.ext fun h => mk_injective ?_⟩
  rw [autEquiv_apply]
  refine hG h (entrywiseAdjointAut τ σ h) ?_
  show ((entrywiseAdjointAut τ σ h : ModGL τ K) : Module.End K (RootModule τ K)) = _
  rw [coe_entrywiseAdjointAut]
  rfl

theorem exists_eq_entrywise_of_mem_closure_markField
    {f : MulAut (LargeEvenCenterQuot (adjointGroup τ K))}
    (hf : f ∈ Subgroup.closure (RecipeFieldExcInn.markFieldImage (IsRoot τ) K (adjointGroup τ K))) :
    ∃ σ : K ≃+* K, autEquiv τ K f = entrywiseAdjointAut τ σ := by
  have hle : Subgroup.closure (RecipeFieldExcInn.markFieldImage (IsRoot τ) K (adjointGroup τ K)) ≤
      (entrywiseAdjointAutHom (τ := τ) (K := K)).range.comap (autEquiv τ K).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro φ hφ
    obtain ⟨σ, hσ⟩ := autEquiv_eq_entrywise_of_mem_markField hφ
    exact ⟨σ, hσ.symm⟩
  obtain ⟨σ, hσ⟩ := hle hf
  exact ⟨σ, hσ.symm⟩

theorem markField_of_entrywise (σ : K ≃+* K) :
    (autEquiv τ K).symm (entrywiseAdjointAut τ σ) ∈
      RecipeFieldExcInn.markFieldImage (IsRoot τ) K (adjointGroup τ K) := by
  refine ⟨σ, fun h h' hrel => ?_⟩
  rw [autEquiv_symm_apply]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [coe_entrywiseAdjointAut]
  exact hrel.symm

end Adjoint

end RecipeExcLang

end CFSG.StandardType
