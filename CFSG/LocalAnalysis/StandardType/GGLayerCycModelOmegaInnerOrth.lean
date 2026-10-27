module

public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelOmegaInnerCore
public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelAssembly
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaFree
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaRegular

public section

namespace CFSG.StandardType

namespace LayerCyc

open Module Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.PartOne.KCOrthogonal LayerCores LayerCores.OrthRegular LayerCores.OrthSplit
  CFSG.Assembly

theorem exists_subCycCoreFamily_orthogonalGroup {K : Type} [Field K] [Finite K] [CharP K 2]
    {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W] {Q : QuadraticForm K W}
    (hQ : (polarBilin Q).Nondegenerate) :
    ∃ (β : Type) (S : β → Subgroup (W ≃ₗ[K] W)),
      IsSubCycCoreFamily (TauCeti.QuadraticMap.orthogonalGroup Q) S := by
  classical
  have := finite_linearEquiv (K := K) (V := W)
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  by_cases h3 : 3 ≤ finrank K W
  · obtain ⟨hexc, hcov⟩ := orthogonal_regular_space_coverage Q hQ h3
    by_cases hsmall : SmallFixedException Q
    · exact ⟨Empty, _, isSubCycCoreFamily_of_isSolvable
        (isSolvable_of_no_prime_gt_three' (hexc hsmall))⟩
    · obtain ⟨-, ⟨n, L, -, -, hsup, hL, hLc⟩, -⟩ := hcov hsmall
      have hcomm_eq : (⨆ i, (L i).map O.subtype) = ⁅O, O⁆ := by
        rw [← Subgroup.map_iSup, hsup, Subgroup.map_subtype_commutator]
      refine ⟨Fin n, fun i => (L i).map O.subtype, fun i => Subgroup.map_subtype_le _,
        fun i => ?_, fun i => ?_, ⟨1, ?_⟩, fun i => ?_⟩
      · have hnorm : ((commutator ↥O).subgroupOf (⊤ : Subgroup ↥O)).Normal :=
          (Subgroup.normal_subgroupOf_iff le_top).mpr fun x k hx _ =>
            (inferInstance : (commutator ↥O).Normal).conj_mem x hx k
        have h1 : IsSubnormal (L i) ⊤ := IsSubnormal.step (hL i).2.1 (hL i).2.2
          (IsSubnormal.step le_top hnorm (IsSubnormal.refl ⊤))
        have h2 := ggSubnormal_map O.subtype h1
        rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
      · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
          ((L i).equivMapOfInjective _ O.subtype_injective) (hL i).1
      · rw [LayerFacts.ggDer_succ, LayerFacts.ggDer_zero, hcomm_eq]
      ·
        have htriv : ∀ z : Subgroup.center ((L i).map O.subtype), z = 1 := by
          intro z
          have hzL : ((z : (L i).map O.subtype) : W ≃ₗ[K] W) ∈ (L i).map O.subtype :=
            (z : (L i).map O.subtype).2
          obtain ⟨x, hx, hxz⟩ := hzL
          have hgc : (⨆ j, (L j).map O.subtype) ≤
              Subgroup.centralizer {((z : (L i).map O.subtype) : W ≃ₗ[K] W)} := by
            refine iSup_le fun j => ?_
            intro y hy
            rw [Subgroup.mem_centralizer_singleton_iff]
            by_cases hij : j = i
            · subst hij
              exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩)
            · obtain ⟨y', hy', rfl⟩ := hy
              rw [← hxz]
              exact congrArg Subtype.val (hLc j i hij y' hy' x hx)
          have h1 : ((z : (L i).map O.subtype) : W ≃ₗ[K] W) = 1 := by
            refine eq_one_of_commute_orthDerived hQ h3 hsmall
              (Subgroup.map_subtype_le _ (z : (L i).map O.subtype).2) fun y hy => ?_
            rw [← hcomm_eq] at hy
            exact (Subgroup.mem_centralizer_singleton_iff.mp (hgc hy)).symm
          exact Subtype.ext (Subtype.ext h1)
        have : Subsingleton (Subgroup.center ((L i).map O.subtype)) :=
          ⟨fun z₁ z₂ => by rw [htriv z₁, htriv z₂]⟩
        infer_instance
  · exact ⟨Empty, _, isSubCycCoreFamily_of_isSolvable
      (isSolvable_orthogonalGroup_of_finrank_le_two hQ (by omega))⟩

theorem exists_cycCoreFamily_orthFree {K : Type} [Field K] [Finite K] [CharP K 2]
    {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W] {Q : QuadraticForm K W}
    (hQ : (polarBilin Q).Nondegenerate) {A : Subgroup (W ≃ₗ[K] W)}
    (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hodd : Odd (Nat.card A))
    (hfree : ∀ w : W, (∀ a ∈ A, a w = w) → w = 0) :
    ∃ (β : Type) (S : β → Subgroup (W ≃ₗ[K] W)),
      IsCycCoreFamily (Subgroup.centralizer (A : Set (W ≃ₗ[K] W)) ⊓
        TauCeti.QuadraticMap.orthogonalGroup Q) S := by
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
  obtain ⟨β, S, hS⟩ := exists_cycCoreFamily_adjCent hcard hadj
    (fun X hX g hg => hadj.mul_comm_of_le_unitaryOf hA'U hX hg) ⟨Y, hYc, hY⟩
  have h := hS.comap (matEquiv b).toMonoidHom (matEquiv b).injective fun g _ =>
    ⟨(matEquiv b).symm g, (matEquiv b).apply_symm_apply g⟩
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
  exact ⟨β, _, h⟩

theorem exists_subCycCoreFamily_orthCentralizer {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {A : Subgroup (V ≃ₗ[K] V)}
    (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hodd : Odd (Nat.card A)) :
    ∃ (β : Type) (S : β → Subgroup (V ≃ₗ[K] V)),
      IsSubCycCoreFamily (Subgroup.centralizer (A : Set (V ≃ₗ[K] V)) ⊓
        TauCeti.QuadraticMap.orthogonalGroup Q) S := by
  classical
  have := finite_linearEquiv (K := K) (V := V)
  have : Fintype A := Fintype.ofFinite A
  have hA : (Fintype.card A : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact natCast_card_ne_zero_of_odd hodd
  obtain ⟨β₀, S₀, hS₀⟩ := exists_subCycCoreFamily_orthogonalGroup
    (Q := Q.restrict (fixSp A)) (nondegenerate_polarBilin_restrict (polarNondegOn_fixSp hQ hA hAO))
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
  obtain ⟨β₁, S₁, hS₁⟩ := exists_cycCoreFamily_orthFree
    (nondegenerate_polarBilin_restrict (polarNondegOn_freeSp hQ hA hAO)) hA₁O hA₁odd hA₁free
  refine ⟨β₀ ⊕ β₁, fun c => (prodFamily S₀ S₁ c).map (split hA), ?_⟩
  rw [centralizer_eq_map_split hA hAO]
  exact (hS₀.prod hS₁.toSub).map _ (split_injective hA)

end LayerCyc

end CFSG.StandardType

end
