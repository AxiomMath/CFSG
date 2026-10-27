module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsOmegaReg
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivOmegaCent

public section

namespace CFSG.StandardType

namespace LayerExcThree

open Matrix LayerCores

open QuadraticMap CFSG.ClassicalGroups.Orthogonal in
theorem exists_coreFamily_orthFree_excThree {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type}
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {Q : QuadraticForm K W}
    (hQ : (polarBilin Q).Nondegenerate) {A : Subgroup (W ≃ₗ[K] W)}
    (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hodd : Odd (Nat.card A))
    (hfree : ∀ w : W, (∀ a ∈ A, a w = w) → w = 0) (hK4 : 4 ≤ Nat.card K) :
    ∃ (β : Type) (S : β → Subgroup (W ≃ₗ[K] W)),
      IsCoreFamily (Subgroup.centralizer (A : Set (W ≃ₗ[K] W)) ⊓
        TauCeti.QuadraticMap.orthogonalGroup Q) S ∧ ∀ c, GGNotExcThreeOrder (ggCQ (S c)) := by
  classical
  have := finite_linearEquiv (K := K) (V := W)
  have : Fintype A := Fintype.ofFinite A
  have hA : (Fintype.card A : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact natCast_card_ne_zero_of_odd hodd
  set b := Module.finBasis K W with hb
  set M := LinearMap.BilinForm.toMatrix b (polarBilin Q) with hM
  have hMt : Mᵀ = M := by
    ext i j
    rw [Matrix.transpose_apply, hM, LinearMap.BilinForm.toMatrix_apply,
      LinearMap.BilinForm.toMatrix_apply, polarBilin_apply_apply, polarBilin_apply_apply,
      polar_comm]
  have hd : ∀ i, M i i = 0 := fun i => by
    rw [hM, LinearMap.BilinForm.toMatrix_apply, polarBilin_apply_apply, polar_self, two_nsmul,
      CharTwo.add_self_eq_zero]
  have hMd : IsUnit M.det :=
    isUnit_iff_ne_zero.mpr ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hQ)
  have hadj := isInvol_gramAdj hMd hMt
  have hU := mem_unitaryOf_gramAdj_iff b hM hMd hMt
  set A' := A.map (matEquiv b).toMonoidHom with hA'
  have hA'U : A' ≤ unitaryOf hadj := by
    rintro _ ⟨a, ha, rfl⟩
    exact (hU a).mpr (polar_map_of_mem (hAO ha))
  have hcard : (Nat.card A' : K) ≠ 0 := by
    rw [hA', Nat.card_congr (A.equivMapOfInjective _ (matEquiv b).injective).toEquiv.symm]
    exact natCast_card_ne_zero_of_odd hodd
  obtain ⟨Y₀, hY₀⟩ := exists_add_gramAdj_eq_one hMd hMt hd
  obtain ⟨Y, hYc, hY⟩ := exists_avg_add_eq_one hadj (gramAdj_smul M) hA'U hcard hY₀
  obtain ⟨β, S, hS, hSp⟩ := exists_coreFamily_adjCent_excThree hcard hadj
    (fun X hX g hg => hadj.mul_comm_of_le_unitaryOf hA'U hX hg) ⟨Y, hYc, hY⟩ hK4
    (Or.inr (gramAdj_smul M))
  have hsurj : ∀ T : Subgroup (GL (Fin (Module.finrank K W)) K),
      T ≤ ((matEquiv b).toMonoidHom).range := fun _ g _ =>
    ⟨(matEquiv b).symm g, (matEquiv b).apply_symm_apply g⟩
  have h := hS.comap (matEquiv b).toMonoidHom (matEquiv b).injective (hsurj _)
  have hC : (adjCent A' hadj).comap (matEquiv b).toMonoidHom =
      Subgroup.centralizer (A : Set (W ≃ₗ[K] W)) ⊓ TauCeti.QuadraticMap.orthogonalGroup Q := by
    ext g
    rw [Subgroup.mem_comap, adjCent, Subgroup.mem_inf, Subgroup.mem_inf]
    have hcent : (matEquiv b).toMonoidHom g ∈ Subgroup.centralizer (A' : Set (GL (Fin _) K)) ↔
        g ∈ Subgroup.centralizer (A : Set (W ≃ₗ[K] W)) := by
      rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
      constructor
      · intro h a ha
        exact (matEquiv b).injective (by
          rw [map_mul, map_mul]
          exact h _ ⟨a, ha, rfl⟩)
      · rintro h _ ⟨a, ha, rfl⟩
        show (matEquiv b) a * (matEquiv b) g = (matEquiv b) g * (matEquiv b) a
        rw [← map_mul, ← map_mul, h a ha]
    rw [hcent]
    constructor
    · rintro ⟨hgc, hgu⟩
      exact ⟨hgc, isometry_of_polar hAO hA hfree hgc ((hU g).mp hgu)⟩
    · rintro ⟨hgc, hgO⟩
      exact ⟨hgc, (hU g).mpr (polar_map_of_mem hgO)⟩
  rw [hC] at h
  refine ⟨β, _, h, fun c => ?_⟩
  rw [ggCQ_comap_of_injective _ (matEquiv b).injective (hsurj _)]
  exact hSp c

open QuadraticMap CFSG.ClassicalGroups.Orthogonal LayerCores.OrthSplit

theorem ggNotExcThree_prodFamily {G₁ G₂ : Type*} [Group G₁] [Group G₂] {β₁ β₂ : Type}
    (S₁ : β₁ → Subgroup G₁) (S₂ : β₂ → Subgroup G₂)
    (h₁ : ∀ c, GGNotExcThreeOrder (ggCQ (S₁ c))) (h₂ : ∀ c, GGNotExcThreeOrder (ggCQ (S₂ c)))
    (c : β₁ ⊕ β₂) : GGNotExcThreeOrder (ggCQ (prodFamily S₁ S₂ c)) := by
  rcases c with c | c
  · show GGNotExcThreeOrder (ggCQ ((S₁ c).map (MonoidHom.inl G₁ G₂)))
    rw [ggCQ_map_of_injective _ (fun a b h => congrArg Prod.fst h)]
    exact h₁ c
  · show GGNotExcThreeOrder (ggCQ ((S₂ c).map (MonoidHom.inr G₁ G₂)))
    rw [ggCQ_map_of_injective _ (fun a b h => congrArg Prod.snd h)]
    exact h₂ c

theorem exists_subCoreFamily_orthCent_excThree {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {A : Subgroup (V ≃ₗ[K] V)}
    (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hodd : Odd (Nat.card A))
    (hK4 : 4 ≤ Nat.card K) :
    ∃ (β : Type) (S : β → Subgroup (V ≃ₗ[K] V)),
      IsSubCoreFamily (Subgroup.centralizer (A : Set (V ≃ₗ[K] V)) ⊓
        TauCeti.QuadraticMap.orthogonalGroup Q) S ∧ ∀ c, GGNotExcThreeOrder (ggCQ (S c)) := by
  classical
  have := finite_linearEquiv (K := K) (V := V)
  have : Fintype A := Fintype.ofFinite A
  have hA : (Fintype.card A : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact natCast_card_ne_zero_of_odd hodd
  obtain ⟨β₀, S₀, hS₀, hp₀⟩ := exists_subCoreFamily_orthRegular_excThree (Q.restrict (fixSp A))
    (nondegenerate_polarBilin_restrict (polarNondegOn_fixSp hQ hA hAO)) hK4
  have hA₁O : freeGroup A ≤ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (freeSp A)) := by
    rintro _ ⟨a, ha, rfl⟩
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun y =>
      map_of_mem (hAO (Subgroup.mem_subgroupOf.mp ha)) (y : V)
  have hA₁odd : Odd (Nat.card (freeGroup A)) := by
    refine Odd.of_dvd_nat ?_ (Subgroup.card_map_dvd _ _)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_stab).toEquiv]
    exact hodd
  have hA₁free : ∀ w : freeSp A, (∀ a ∈ freeGroup A, a w = w) → w = 0 := by
    intro w hw
    have h1 : (w : V) ∈ fixSp A := (mem_fixSp_iff hA).mpr fun a ha =>
      congrArg Subtype.val (hw (restrFree A ⟨a, le_stab ha⟩)
        ⟨⟨a, le_stab ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩)
    exact Subtype.ext ((Submodule.disjoint_def.mp (isCompl_fixSp_freeSp hA).disjoint) _ h1 w.2)
  obtain ⟨β₁, S₁, hS₁, hp₁⟩ := exists_coreFamily_orthFree_excThree
    (nondegenerate_polarBilin_restrict (polarNondegOn_freeSp hQ hA hAO)) hA₁O hA₁odd hA₁free
    hK4
  refine ⟨β₀ ⊕ β₁, fun c => (prodFamily S₀ S₁ c).map (split hA), ?_, fun c => ?_⟩
  · rw [centralizer_eq_map_split hA hAO]
    exact (hS₀.prod hS₁.toSub).map _ (split_injective hA)
  · rw [ggCQ_map_of_injective _ (split_injective hA)]
    exact ggNotExcThree_prodFamily S₀ S₁ hp₀ hp₁ c

end LayerExcThree

end CFSG.StandardType
