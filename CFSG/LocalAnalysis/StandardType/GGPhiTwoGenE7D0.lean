module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenE7Defs
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenE7D0Aux
public import CFSG.LieType.AlgebraicGroups.KernelRootDescent
public import CFSG.LieType.Chevalley.ParabolicRootFactorData
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs
public import CFSG.LieType.Chevalley.E7SupportedBruhat

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.CurtisTits CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.ComponentClassification.CatLeafProof
open CFSG.LieType.AlgebraicGroups
open scoped Pointwise

@[expose] def e7D6IndexSet : Set (Fin (Tag.rank .E7)) := {i | i ≠ 0}

private lemma e7D6Roots_eq_parabolicRoots :
    e7D6Roots = parabolicRoots .E7 e7D6IndexSet := by
  ext γ
  constructor
  · rintro ⟨hγ, h0⟩
    refine ⟨hγ, fun i hi => ?_⟩
    have hi0 : i = 0 := by simpa [e7D6IndexSet] using hi
    simpa [hi0] using h0
  · rintro ⟨hγ, h⟩
    refine ⟨hγ, ?_⟩
    have := h 0 (by simp [e7D6IndexSet])
    simpa using this

private lemma e7D6Node_ne_zero (k : Fin 6) : e7D6Node k ≠ 0 := by
  fin_cases k <;> decide

private lemma e7D6Node_mem_indexSet (k : Fin 6) : e7D6Node k ∈ e7D6IndexSet :=
  e7D6Node_ne_zero k

private lemma e7_artifactRoots_even_theta :
    ∀ r ∈ Tag.E7.artifactRoots,
      (Even (r.getD 0 0) → r.getD 0 0 ≠ 0 →
        r = ([2, 2, 3, 4, 3, 2, 1] : List ℤ) ∨
          r = -([2, 2, 3, 4, 3, 2, 1] : List ℤ)) := by
  decide +kernel

private lemma e7A1D6Roots_eq_union :
    e7A1D6Roots = e7D6Roots ∪ {e7Theta, -e7Theta} := by
  ext γ
  simp only [e7A1D6Roots, e7D6Roots, Set.mem_setOf_eq, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨hγ, hev⟩
    by_cases h0 : γ 0 = 0
    · exact Or.inl ⟨hγ, h0⟩
    · right
      have h := e7_artifactRoots_even_theta (List.ofFn γ)
        ((isRoot_iff_mem_artifactRoots (τ := .E7)).mp hγ)
      have htheta : List.ofFn e7Theta = ([2, 2, 3, 4, 3, 2, 1] : List ℤ) := rfl
      have hneg : List.ofFn (-e7Theta) = -([2, 2, 3, 4, 3, 2, 1] : List ℤ) := rfl
      have hget : (List.ofFn γ).getD 0 0 = γ 0 := rfl
      rw [hget] at h
      rcases h hev h0 with hθ | hθ
      · left
        exact List.ofFn_inj.mp (hθ.trans htheta.symm)
      · right
        exact List.ofFn_inj.mp (hθ.trans hneg.symm)
  · rintro (⟨hγ, h0⟩ | hγ | hγ)
    · exact ⟨hγ, by rw [h0]; exact ⟨0, by norm_num⟩⟩
    · subst hγ
      exact ⟨isRoot_e7Theta, by decide⟩
    · subst hγ
      exact ⟨IsRoot.neg isRoot_e7Theta, by decide⟩

theorem ggPhiTwoD0_structural
    {K : Type} [Field K] :
    rootSpan .E7 K e7D6Roots = (e7D6Group K).map (adjointGroup .E7 K).subtype ∧
    rootSpan .E7 K {e7Theta, -e7Theta} =
      (rootPairE7 K e7Theta).map (adjointGroup .E7 K).subtype ∧
    e7A1D6Roots = e7D6Roots ∪ {e7Theta, -e7Theta} := by
  have map_rootGroup_eq_rootSubgroup : ∀ {γ : Fin (Tag.rank .E7) → ℤ}, IsRoot .E7 γ →
      ((adjDatum (rootOperatorFamily .E7) K).rootGroup γ).map
        (adjointGroup .E7 K).subtype = rootSubgroup .E7 K γ := by
    intro γ hγ
    change ((rootGroup (rootOperatorFamily .E7) K γ).map
      (adjointGroup .E7 K).subtype) = rootSubgroup .E7 K γ
    rw [rootGroup_of_isRoot (F := rootOperatorFamily .E7) (K := K) hγ,
      ← RootOperatorFamily.subgroupOf_rootSubgroup_eq (F := rootOperatorFamily .E7)
        (K := K) ⟨γ, hγ⟩,
      Subgroup.map_subgroupOf_eq_of_le (rootSubgroup_le_adjointGroup γ)]
  have rootSubgroup_single_le_subsystemGroup : ∀ (i : Fin (Tag.rank .E7)),
      i ∈ e7D6IndexSet →
      rootSubgroup .E7 K (Pi.single i 1) ≤ subsystemGroup .E7 K e7D6IndexSet := by
    intro i hi
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    rw [pinnedX_single]
    exact xUnit_mem_subsystemGroup hi c
  have rootSubgroup_neg_single_le_subsystemGroup : ∀ (i : Fin (Tag.rank .E7)),
      i ∈ e7D6IndexSet →
      rootSubgroup .E7 K (-Pi.single i 1) ≤ subsystemGroup .E7 K e7D6IndexSet := by
    intro i hi
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    rw [pinnedX_neg_single]
    exact yUnit_mem_subsystemGroup hi c
  have rankOne_map_le_subsystemGroup : ∀ (i : Fin (Tag.rank .E7)),
      i ∈ e7D6IndexSet →
      (rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup i).map
        (adjointGroup .E7 K).subtype ≤ subsystemGroup .E7 K e7D6IndexSet := by
    intro i hi
    rw [rankOne, Subgroup.map_sup,
      map_rootGroup_eq_rootSubgroup (isRoot_single .E7 i),
      map_rootGroup_eq_rootSubgroup (isRoot_neg_single .E7 i)]
    exact sup_le (rootSubgroup_single_le_subsystemGroup i hi)
      (rootSubgroup_neg_single_le_subsystemGroup i hi)
  have e7D6Group_map_le_subsystemGroup :
      (e7D6Group K).map (adjointGroup .E7 K).subtype ≤
        subsystemGroup .E7 K e7D6IndexSet := by
    rw [e7D6Group, Subgroup.map_iSup]
    refine iSup_le fun k => ?_
    exact rankOne_map_le_subsystemGroup (e7D6Node k) (e7D6Node_mem_indexSet k)
  have subsystemGroup_le_e7D6Group_map :
      subsystemGroup .E7 K e7D6IndexSet ≤
        (e7D6Group K).map (adjointGroup .E7 K).subtype := by
    rw [subsystemGroup, Subgroup.closure_le]
    rintro _ ⟨i, hi, c, rfl | rfl⟩
    · obtain ⟨k, rfl⟩ := exists_e7D6Node_eq i hi
      let α : Fin (Tag.rank .E7) → ℤ := Pi.single (e7D6Node k) 1
      have hα : IsRoot .E7 α := isRoot_single .E7 (e7D6Node k)
      have hx : xUnit .E7 K (e7D6Node k) c ∈ rootSubgroup .E7 K α := by
        rw [show xUnit .E7 K (e7D6Node k) c = pinnedX .E7 K α c from
          (pinnedX_single (τ := .E7) (R := K) (e7D6Node k) c).symm]
        exact Subgroup.subset_closure ⟨c, rfl⟩
      have hxadj : xUnit .E7 K (e7D6Node k) c ∈ adjointGroup .E7 K :=
        xUnit_mem_adjointGroup (e7D6Node k) c
      let g : adjointGroup .E7 K := ⟨xUnit .E7 K (e7D6Node k) c, hxadj⟩
      refine Subgroup.mem_map.2 ⟨g, ?_, rfl⟩
      have hsub : g ∈ (rootSubgroup .E7 K α).subgroupOf (adjointGroup .E7 K) := by
        rw [Subgroup.mem_subgroupOf]
        exact hx
      rw [RootOperatorFamily.subgroupOf_rootSubgroup_eq (F := rootOperatorFamily .E7)
        (K := K) ⟨α, hα⟩] at hsub
      refine Subgroup.mem_iSup_of_mem k (Subgroup.mem_sup_left ?_)
      change g ∈ rootGroup (rootOperatorFamily .E7) K (Pi.single (e7D6Node k) 1)
      rw [rootGroup_of_isRoot (F := rootOperatorFamily .E7) (K := K)
        (isRoot_single .E7 (e7D6Node k))]
      simpa [g, α] using hsub
    · obtain ⟨k, rfl⟩ := exists_e7D6Node_eq i hi
      let α : Fin (Tag.rank .E7) → ℤ := -Pi.single (e7D6Node k) 1
      have hα : IsRoot .E7 α := isRoot_neg_single .E7 (e7D6Node k)
      have hx : yUnit .E7 K (e7D6Node k) c ∈ rootSubgroup .E7 K α := by
        rw [show yUnit .E7 K (e7D6Node k) c = pinnedX .E7 K α c from
          (pinnedX_neg_single (τ := .E7) (R := K) (e7D6Node k) c).symm]
        exact Subgroup.subset_closure ⟨c, rfl⟩
      have hxadj : yUnit .E7 K (e7D6Node k) c ∈ adjointGroup .E7 K :=
        yUnit_mem_adjointGroup (e7D6Node k) c
      let g : adjointGroup .E7 K := ⟨yUnit .E7 K (e7D6Node k) c, hxadj⟩
      refine Subgroup.mem_map.2 ⟨g, ?_, rfl⟩
      have hsub : g ∈ (rootSubgroup .E7 K α).subgroupOf (adjointGroup .E7 K) := by
        rw [Subgroup.mem_subgroupOf]
        exact hx
      rw [RootOperatorFamily.subgroupOf_rootSubgroup_eq (F := rootOperatorFamily .E7)
        (K := K) ⟨α, hα⟩] at hsub
      refine Subgroup.mem_iSup_of_mem k (Subgroup.mem_sup_right ?_)
      change g ∈ rootGroup (rootOperatorFamily .E7) K (-Pi.single (e7D6Node k) 1)
      rw [rootGroup_of_isRoot (F := rootOperatorFamily .E7) (K := K)
        (isRoot_neg_single .E7 (e7D6Node k))]
      simpa [g, α] using hsub
  have rootSpan_e7D6Roots_eq_e7D6Group :
      rootSpan .E7 K e7D6Roots = (e7D6Group K).map (adjointGroup .E7 K).subtype := by
    refine le_antisymm ?_ ?_
    · rw [e7D6Roots_eq_parabolicRoots, ← subsystemGroup_eq_rootSpan]
      exact subsystemGroup_le_e7D6Group_map
    · rw [e7D6Roots_eq_parabolicRoots, ← subsystemGroup_eq_rootSpan]
      exact e7D6Group_map_le_subsystemGroup
  have rootSpan_theta_eq_rootPair :
      rootSpan .E7 K {e7Theta, -e7Theta} =
        (rootPairE7 K e7Theta).map (adjointGroup .E7 K).subtype := by
    have hspan : rootSpan .E7 K {e7Theta, -e7Theta} =
        rootSubgroup .E7 K e7Theta ⊔ rootSubgroup .E7 K (-e7Theta) := by
      rw [rootSpan, iSup_insert, iSup_singleton]
    rw [hspan, rootPairE7, Subgroup.map_sup,
      map_rootGroup_eq_rootSubgroup (isRoot_e7Theta),
      map_rootGroup_eq_rootSubgroup (IsRoot.neg isRoot_e7Theta)]
  exact ⟨rootSpan_e7D6Roots_eq_e7D6Group, rootSpan_theta_eq_rootPair,
    e7A1D6Roots_eq_union⟩

private lemma rootSpan_e7A1D6Roots_eq_sup {K : Type} [Field K] :
    rootSpan .E7 K e7A1D6Roots =
      rootSpan .E7 K e7D6Roots ⊔ rootSpan .E7 K {e7Theta, -e7Theta} := by
  rw [e7A1D6Roots_eq_union]
  refine le_antisymm ?_ ?_
  · rw [rootSpan]
    refine iSup_le fun α => ?_
    rw [iSup_le_iff]
    intro hα
    rcases hα with hα | hα
    · exact le_sup_of_le_left (le_iSup₂_of_le α hα le_rfl)
    · exact le_sup_of_le_right (le_iSup₂_of_le α hα le_rfl)
  · exact sup_le (rootSpan_mono Set.subset_union_left)
      (rootSpan_mono Set.subset_union_right)

theorem commute_rootSpan_D6_theta
    {K : Type} [Field K] {a b : ModGL .E7 K} (ha : a ∈ rootSpan .E7 K e7D6Roots)
    (hb : b ∈ rootSpan .E7 K {e7Theta, -e7Theta}) : Commute a b := by
  obtain ⟨hD, hA, -⟩ := ggPhiTwoD0_structural (K := K)
  rw [hD] at ha
  rw [hA] at hb
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
  exact ((commute_rootPairE7_theta_of_mem_e7D6Group hy hx).symm).map (adjointGroup .E7 K).subtype

private lemma exists_sq_of_finite_charTwo {K : Type} [Field K] [Finite K] [CharP K 2] :
    ∀ x : K, ∃ z : K, z ^ 2 = x := by
  haveI : ExpChar K 2 := ExpChar.prime Nat.prime_two
  intro x
  obtain ⟨z, hz⟩ := Finite.surjective_of_injective (frobenius_inj K 2) x
  exact ⟨z, by simpa [frobenius_def] using hz⟩

theorem phiTwoA1D6Subgroup_eq_e7A1D6
    {K : Type} [Field K] [Finite K] [CharP K 2] :
    phiTwoA1D6Subgroup K = (e7A1D6 K).map (adjointGroup .E7 K).subtype := by
  obtain ⟨hD, hA, -⟩ := ggPhiTwoD0_structural (K := K)
  rw [phiTwoA1D6Subgroup,
    sup_eq_right.mpr (ggPhiTwoD0_torus_le_rootSpan (exists_sq_of_finite_charTwo (K := K))),
    rootSpan_e7A1D6Roots_eq_sup, hD, hA, ← Subgroup.map_sup]
  rfl

theorem exists_mul_eq_of_mem_phiTwoA1D6Subgroup
    {L : Type} [Field L] [CharP L 2] (hsq : ∀ x : L, ∃ y : L, y * y = x)
    {g : ModGL .E7 L} (hg : g ∈ phiTwoA1D6Subgroup L) :
    ∃ a ∈ rootSpan .E7 L e7D6Roots, ∃ b ∈ rootSpan .E7 L {e7Theta, -e7Theta},
      g = a * b ∧ a * b = b * a := by
  have hsq' : ∀ x : L, ∃ z : L, z ^ 2 = x := fun x => by
    obtain ⟨y, hy⟩ := hsq x
    exact ⟨y, by rw [pow_two]; exact hy⟩
  rw [phiTwoA1D6Subgroup, sup_eq_right.mpr (ggPhiTwoD0_torus_le_rootSpan hsq'),
    rootSpan_e7A1D6Roots_eq_sup] at hg
  have hle : rootSpan .E7 L e7D6Roots ≤
      Subgroup.normalizer (rootSpan .E7 L {e7Theta, -e7Theta} : Set (ModGL .E7 L)) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h := commute_rootSpan_D6_theta ha hx
      rw [h.eq, mul_assoc, mul_inv_cancel, mul_one]
      exact hx
    · intro hx
      have h := (commute_rootSpan_D6_theta (inv_mem ha) hx).eq
      have hxe : x = a * x * a⁻¹ := by
        calc x = a⁻¹ * (a * x * a⁻¹) * a := by group
          _ = (a * x * a⁻¹) * a⁻¹ * a := by rw [h]
          _ = a * x * a⁻¹ := by group
      rwa [← hxe] at hx
  have hg2 : g ∈ (rootSpan .E7 L e7D6Roots : Set (ModGL .E7 L)) *
      (rootSpan .E7 L {e7Theta, -e7Theta} : Set (ModGL .E7 L)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle]
    exact hg
  obtain ⟨a, ha, b, hb, rfl⟩ := hg2
  exact ⟨a, ha, b, hb, rfl, (commute_rootSpan_D6_theta ha hb).eq⟩

private noncomputable def e7Chi0 : Multiplicative (Fin Tag.E7.rank → ℤ) →* Multiplicative ℤ :=
  AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ : Fin Tag.E7.rank => ℤ) 0)

private lemma kernelRoots_e7Chi0 : kernelRoots e7Chi0 = e7D6Roots := by
  ext α
  simp [kernelRoots, e7D6Roots, e7Chi0]

private noncomputable def e7ChiTheta : Multiplicative (Fin Tag.E7.rank → ℤ) →*
    (Multiplicative (Fin Tag.E7.rank → ℤ) ⧸ Subgroup.zpowers (Multiplicative.ofAdd e7Theta)) :=
  QuotientGroup.mk' (Subgroup.zpowers (Multiplicative.ofAdd e7Theta))

private lemma kernelRoots_e7ChiTheta :
    kernelRoots e7ChiTheta = {e7Theta, -e7Theta} := by
  ext α
  constructor
  · rintro ⟨hα, h1⟩
    have h : Multiplicative.ofAdd α ∈ Subgroup.zpowers (Multiplicative.ofAdd e7Theta) :=
      (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    have hαk : α = k • e7Theta := by
      have := congrArg Multiplicative.toAdd hk
      simpa using this.symm
    rcases hα.eq_one_or_neg_one_of_eq_smul hαk with rfl | rfl
    · left
      simpa using hαk
    · right
      simpa using hαk
  · rintro (rfl | rfl)
    · exact ⟨isRoot_e7Theta, (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)⟩
    · refine ⟨IsRoot.neg isRoot_e7Theta, (QuotientGroup.eq_one_iff _).mpr ?_⟩
      have := Subgroup.inv_mem _ (Subgroup.mem_zpowers (Multiplicative.ofAdd e7Theta))
      simpa using this

theorem mem_e7D6Group_of_baseChangeGL_mem_rootSpan
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : Nat.Coprime n (Nat.card K - 1))
    {x : adjointGroup .E7 K} (hxn : x ^ n = 1)
    (hx : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E7 K) ∈
      rootSpan .E7 (AlgebraicClosure K) e7D6Roots) : x ∈ e7D6Group K := by
  have hbase : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E7 K) ∈
      torusGroup .E7 (AlgebraicClosure K) ⊔
        rootSpan .E7 (AlgebraicClosure K) (kernelRoots e7Chi0) := by
    rw [kernelRoots_e7Chi0]
    exact Subgroup.mem_sup_right hx
  have h1 := mem_torus_sup_rootSpan_of_baseChangeGL_mem (K := K) (L := AlgebraicClosure K)
    (algebraMap K (AlgebraicClosure K)) e7Chi0 x.2 hbase
  rw [kernelRoots_e7Chi0] at h1
  have hxn' : (x : ModGL .E7 K) ^ n = 1 := by
    have := congrArg Subtype.val hxn
    simpa using this
  have h2 := mem_rootSpan_of_mem_torus_sup_of_pow_eq_one (τ := .E7) (S := e7D6Roots)
    (fun α hα => hα.1) hn h1 hxn'
  obtain ⟨hD, -, -⟩ := ggPhiTwoD0_structural (K := K)
  rw [hD] at h2
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h2
  have hyx' : y = x := Subtype.ext hyx
  rwa [hyx'] at hy

theorem mem_rootPairE7_of_baseChangeGL_mem_rootSpan
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : Nat.Coprime n (Nat.card K - 1))
    {x : adjointGroup .E7 K} (hxn : x ^ n = 1)
    (hx : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E7 K) ∈
      rootSpan .E7 (AlgebraicClosure K) {e7Theta, -e7Theta}) : x ∈ rootPairE7 K e7Theta := by
  have hbase : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E7 K) ∈
      torusGroup .E7 (AlgebraicClosure K) ⊔
        rootSpan .E7 (AlgebraicClosure K) (kernelRoots e7ChiTheta) := by
    rw [kernelRoots_e7ChiTheta]
    exact Subgroup.mem_sup_right hx
  have h1 := mem_torus_sup_rootSpan_of_baseChangeGL_mem (K := K) (L := AlgebraicClosure K)
    (algebraMap K (AlgebraicClosure K)) e7ChiTheta x.2 hbase
  rw [kernelRoots_e7ChiTheta] at h1
  have hxn' : (x : ModGL .E7 K) ^ n = 1 := by
    have := congrArg Subtype.val hxn
    simpa using this
  have h2 := mem_rootSpan_of_mem_torus_sup_of_pow_eq_one (τ := .E7) (S := {e7Theta, -e7Theta})
    (fun α hα => by rcases hα with rfl | rfl; exacts [isRoot_e7Theta, IsRoot.neg isRoot_e7Theta])
    hn h1 hxn'
  obtain ⟨-, hA, -⟩ := ggPhiTwoD0_structural (K := K)
  rw [hA] at h2
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h2
  have hyx' : y = x := Subtype.ext hyx
  rwa [hyx'] at hy

end CFSG.StandardType.PhiTwoRootGen

end
