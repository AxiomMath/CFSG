module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRootGenRefl
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwRootC
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeAd
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveFrameCentralizer
public import CFSG.LocalAnalysis.StandardType.GGTwE6PlusRootGenFrame

public section

namespace CFSG.StandardType.TwE6ThreeRootGen

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableBExc.E6Three
  CFSG.HardMathSupport.Timmesfeld.Torality

private theorem rootChar_zetaVec_eq_one_iff {L : Type} [Field L] {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) (x : Fin Tag.E6.rank → ZMod 3) (γ : Fin Tag.E6.rank → ℤ) :
    rootChar (zetaVec (τ := Tag.E6) ζ hζ x) γ = 1 ↔
      ∑ j, (γ j : ZMod 3) * x j = 0 := by
  rw [NoOffE8Five.rootChar_zetaVec hζ x γ]
  constructor
  · intro h
    have h1 : Multiplicative.ofAdd (∑ j, (γ j : ZMod 3) * x j) = 1 := by
      apply CFSG.RankThree.CentralCover.zmodPowHom_injective hζo hζ
      rw [h, map_one]
    exact Multiplicative.ofAdd.injective (by rw [h1, ofAdd_zero])
  · intro h
    rw [h, ofAdd_zero, map_one]

theorem familyKernel_zetaVec_eq
    {L : Type} [Field L] {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {V : Set (Fin Tag.E6.rank → ZMod 3)}
    (hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)))
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    familyKernel (τ := Tag.E6)
        (fun x : {x : Fin Tag.E6.rank → ZMod 3 //
            x ∈ V ∧ ExcSplitRootGen.excRefl (p := 3) γ x = x} =>
          zetaVec (τ := Tag.E6) ζ hζ x.1) = {γ, -γ} := by
  apply Set.Subset.antisymm
  · intro δ hδ
    rw [familyKernel] at hδ
    obtain ⟨hδroot, hδker⟩ := hδ
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    refine eq_or_eq_neg_of_forall_mem_sum_eq_zero hV hγ hδroot ?_
    intro x hxV hxγ
    have hxr : ExcSplitRootGen.excRefl (p := 3) γ x = x :=
      (ExcSplitRootGen.excRefl_eq_self_iff (p := 3) (by norm_num) hγ x).2 hxγ
    exact (rootChar_zetaVec_eq_one_iff hζ hζo x δ).1 (hδker ⟨x, hxV, hxr⟩)
  · intro δ hδ
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hδ
    rw [familyKernel]
    rcases hδ with hδ | hδ
    · rw [hδ]
      refine ⟨hγ, fun x => (rootChar_zetaVec_eq_one_iff hζ hζo x.1 γ).2 ?_⟩
      exact (ExcSplitRootGen.excRefl_eq_self_iff (p := 3) (by norm_num) hγ x.1).1 x.2.2
    · rw [hδ]
      refine ⟨IsRoot.neg hγ, fun x => (rootChar_zetaVec_eq_one_iff hζ hζo x.1 (-γ)).2 ?_⟩
      have h := (ExcSplitRootGen.excRefl_eq_self_iff (p := 3) (by norm_num) hγ x.1).1 x.2.2
      simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, h, neg_zero]

theorem ggKGTwJ_le_centralizer_three
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {t : (Fin 6 → ZMod 3) → ModGL TwistTag.E6.tag K}
    (ht : ∀ x, baseChangeGL (algebraMap K (AlgebraicClosure K)) (t x) =
      F.g0 * rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ x) * F.g0⁻¹)
    {V : Set (Fin Tag.E6.rank → ZMod 3)} {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    ggKGTwJ F γ ≤ (Subgroup.centralizer
        (t '' {x | x ∈ V ∧ ExcSplitRootGen.excRefl (p := 3) γ x = x})).comap
          (twistedE6RootGroup K σ).subtype := by
  intro j hj
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hj' := hj
  rw [ggKGTwJ, Subgroup.mem_comap, ggKGTwLhat, Subgroup.mem_inf] at hj'
  obtain ⟨M, hM⟩ := MonoidHom.mem_range.1 hj'.1
  set d : ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ x) with hd
  set Y : ModGL TwistTag.E6.tag (AlgebraicClosure K) := ggKGTwY F j with hY
  have hYj : Y = rootSL2 TwistTag.E6.tag (AlgebraicClosure K) γ M := by
    rw [hY]
    exact hM.symm
  have hsum : ∑ i, (γ i : ZMod 3) * x i = 0 :=
    (ExcSplitRootGen.excRefl_eq_self_iff (p := 3) (by norm_num) hγ x).1 hx.2
  have hχ : rootChar (zetaVec (τ := Tag.E6) ζ hζ x) γ = 1 :=
    (rootChar_zetaVec_eq_one_iff hζ hζo x γ).2 hsum
  have hcommd : d * Y * d⁻¹ = Y := by
    rw [hd, hYj]
    change rootDiagUnit Tag.E6 (zetaVec (τ := Tag.E6) ζ hζ x) *
      rootSL2 Tag.E6 (AlgebraicClosure K) γ M *
      (rootDiagUnit Tag.E6 (zetaVec (τ := Tag.E6) ζ hζ x))⁻¹ =
        rootSL2 Tag.E6 (AlgebraicClosure K) γ M
    rw [CFSG.RankThree.Chevalley.rootDiagUnit_conj_rootSL2 _ hγ M, hχ,
      CFSG.RankThree.Chevalley.conjSL_diagUnitOne_one]
  have hdY : d * Y = Y * d := by
    have h := congrArg (fun z => z * d) hcommd
    simpa [mul_assoc] using h
  have hbase : baseChangeGL (algebraMap K (AlgebraicClosure K)) (t x) *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (j : ModGL TwistTag.E6.tag K) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (j : ModGL TwistTag.E6.tag K) *
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (t x) := by
    have hB : baseChangeGL (algebraMap K (AlgebraicClosure K))
        (j : ModGL TwistTag.E6.tag K) = F.g0 * Y * F.g0⁻¹ := by
      have hYdef : Y = F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (j : ModGL TwistTag.E6.tag K) * F.g0 := by
        rw [hY, ggKGTwY_apply]
      rw [hYdef]
      group
    rw [ht x, hB]
    calc (F.g0 * d * F.g0⁻¹) * (F.g0 * Y * F.g0⁻¹) = F.g0 * (d * Y) * F.g0⁻¹ := by
          group
      _ = F.g0 * (Y * d) * F.g0⁻¹ := by rw [hdY]
      _ = (F.g0 * Y * F.g0⁻¹) * (F.g0 * d * F.g0⁻¹) := by group
  exact baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
    (by rw [map_mul, map_mul]; exact hbase)

theorem ggKGTwJ_mem_familyCentralizer_three
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ 3 = 1)
    {t : (Fin 6 → ZMod 3) → ModGL TwistTag.E6.tag K}
    (ht : ∀ x, baseChangeGL (algebraMap K (AlgebraicClosure K)) (t x) =
      F.g0 * rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ x) * F.g0⁻¹)
    {V : Set (Fin Tag.E6.rank → ZMod 3)} {γ : Fin Tag.E6.rank → ℤ}
    {c : twistedE6RootGroup K σ}
    (hc : (c : ModGL TwistTag.E6.tag K) ∈ Subgroup.centralizer
      (t '' {x | x ∈ V ∧ ExcSplitRootGen.excRefl (p := 3) γ x = x})) :
    ggKGTwY F c ∈ familyCentralizer TwistTag.E6.tag (AlgebraicClosure K)
      (fun x : {x : Fin Tag.E6.rank → ZMod 3 //
          x ∈ V ∧ ExcSplitRootGen.excRefl (p := 3) γ x = x} =>
        zetaVec (τ := TwistTag.E6.tag) ζ hζ x.1) := by
  rw [mem_familyCentralizer]
  refine ⟨?_, fun i => ?_⟩
  · rw [ggKGTwY_apply]
    exact mul_mem (mul_mem (inv_mem F.g0_mem)
      (CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _
        (ggKGTc_coe_mem_adjointGroup c))) F.g0_mem
  · have hct : t i.1 * (c : ModGL TwistTag.E6.tag K) =
        (c : ModGL TwistTag.E6.tag K) * t i.1 :=
      (Subgroup.mem_centralizer_iff.1 hc) (t i.1) (Set.mem_image_of_mem t i.2)
    have hbase : baseChangeGL (algebraMap K (AlgebraicClosure K)) (t i.1) *
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL TwistTag.E6.tag K) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL TwistTag.E6.tag K) *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (t i.1) := by
      rw [← map_mul, ← map_mul, hct]
    set d : ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
      rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ i.1) with hd
    set B : ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL TwistTag.E6.tag K) with hB
    have hbase' : (F.g0 * d * F.g0⁻¹) * B = B * (F.g0 * d * F.g0⁻¹) := by
      rw [hd, ← ht i.1]
      exact hbase
    have hcomm : d * (F.g0⁻¹ * B * F.g0) = (F.g0⁻¹ * B * F.g0) * d := by
      calc d * (F.g0⁻¹ * B * F.g0) = F.g0⁻¹ * ((F.g0 * d * F.g0⁻¹) * B) * F.g0 := by
            group
        _ = F.g0⁻¹ * (B * (F.g0 * d * F.g0⁻¹)) * F.g0 := by rw [hbase']
        _ = (F.g0⁻¹ * B * F.g0) * d := by group
    show d * (F.g0⁻¹ * B * F.g0) * d⁻¹ = F.g0⁻¹ * B * F.g0
    rw [hcomm]
    group

private theorem rootSpan_pair_le_normalizer
    {τ : Tag} {L : Type} [Field L] {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    rootSpan τ L ({γ, -γ} : Set (Fin τ.rank → ℤ)) ≤ Subgroup.normalizer
      ((rootRankOneGroup τ L γ : Subgroup (ModGL τ L)) : Set (ModGL τ L)) := by
  rw [CFSG.LieType.HighestRoot.rootSpan_pair_eq γ,
    ← (CFSG.LieType.Chevalley.exceptional_Lang_root_rank_one_torus_transport τ L hγ).1]
  exact Subgroup.le_normalizer

private theorem ggKGTwJ_Y_mem_normalizer_three
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {t : (Fin 6 → ZMod 3) → ModGL TwistTag.E6.tag K}
    (ht : ∀ x, baseChangeGL (algebraMap K (AlgebraicClosure K)) (t x) =
      F.g0 * rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ x) * F.g0⁻¹)
    {V : Set (Fin Tag.E6.rank → ZMod 3)}
    (hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)))
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    {c : twistedE6RootGroup K σ}
    (hc : (c : ModGL TwistTag.E6.tag K) ∈ Subgroup.centralizer
      (t '' {x | x ∈ V ∧ ExcSplitRootGen.excRefl (p := 3) γ x = x})) :
    ggKGTwY F c ∈ Subgroup.normalizer
      ((rootRankOneGroup TwistTag.E6.tag (AlgebraicClosure K) γ : Subgroup
        (ModGL TwistTag.E6.tag (AlgebraicClosure K))) :
        Set (ModGL TwistTag.E6.tag (AlgebraicClosure K))) := by
  let γT : Fin TwistTag.E6.tag.rank → ℤ := γ
  have hγT : IsRoot TwistTag.E6.tag γT := hγ
  change ggKGTwY F c ∈ Subgroup.normalizer
      ((rootRankOneGroup TwistTag.E6.tag (AlgebraicClosure K) γT : Subgroup
        (ModGL TwistTag.E6.tag (AlgebraicClosure K))) :
        Set (ModGL TwistTag.E6.tag (AlgebraicClosure K)))
  have hcT : (c : ModGL TwistTag.E6.tag K) ∈ Subgroup.centralizer
      (t '' {x | x ∈ V ∧ ExcSplitRootGen.excRefl (p := 3) γT x = x}) := hc
  let a : {x : Fin Tag.E6.rank → ZMod 3 // x ∈ V ∧
      ExcSplitRootGen.excRefl (p := 3) γT x = x} → Fin TwistTag.E6.tag.rank →
        (AlgebraicClosure K)ˣ := fun x => zetaVec (τ := TwistTag.E6.tag) ζ hζ x.1
  have hfam : ggKGTwY F c ∈ familyCentralizer TwistTag.E6.tag (AlgebraicClosure K) a :=
    ggKGTwJ_mem_familyCentralizer_three F hζ ht hcT
  obtain ⟨w, hwstab, m, hm, hc_eq⟩ :=
    familyCentralizer_le_mul TwistTag.E6.tag (AlgebraicClosure K) a hfam
  have hfker : familyKernel a = {γT, -γT} := by
    change familyKernel (τ := Tag.E6)
      (fun x : {x : Fin Tag.E6.rank → ZMod 3 // x ∈ V ∧
        ExcSplitRootGen.excRefl (p := 3) γ x = x} =>
          zetaVec (τ := Tag.E6) ζ hζ x.1) = {γ, -γ}
    exact familyKernel_zetaVec_eq hζ hζo hV hγ
  have himg := image_familyKernel (a := a) hwstab
  rw [hfker] at himg
  have hwγ : w • γT = γT ∨ w • γT = -γT := by
    have hmem : w • γT ∈ ({γT, -γT} : Set (Fin TwistTag.E6.tag.rank → ℤ)) := by
      rw [← himg]
      exact ⟨γT, by simp, rfl⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  have hm_norm : m ∈ Subgroup.normalizer
      ((rootRankOneGroup TwistTag.E6.tag (AlgebraicClosure K) γT : Subgroup
        (ModGL TwistTag.E6.tag (AlgebraicClosure K))) :
        Set (ModGL TwistTag.E6.tag (AlgebraicClosure K))) := by
    rw [familyGroup, hfker] at hm
    refine (sup_le (CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootRankOneGroup
      (τ := TwistTag.E6.tag) (L := AlgebraicClosure K) hγT) ?_) hm
    exact rootSpan_pair_le_normalizer (τ := TwistTag.E6.tag)
      (L := AlgebraicClosure K) hγT
  have hw_norm : canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w ∈
      Subgroup.normalizer ((rootRankOneGroup TwistTag.E6.tag (AlgebraicClosure K) γT :
        Subgroup (ModGL TwistTag.E6.tag (AlgebraicClosure K))) :
        Set (ModGL TwistTag.E6.tag (AlgebraicClosure K))) := by
    rw [(CFSG.LieType.Chevalley.exceptional_Lang_root_rank_one_torus_transport
      TwistTag.E6.tag (AlgebraicClosure K) hγT).1]
    exact CFSG.LieType.HighestRoot.canonicalRep_mem_normalizer_pair hγT hwγ
  rw [hc_eq]
  exact Subgroup.mul_mem _ hm_norm hw_norm

private theorem ggKGTwJ_subnormal_three
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) (F : TwE6Frame K σ n p E)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {t : (Fin 6 → ZMod 3) → ModGL TwistTag.E6.tag K}
    (ht : ∀ x, baseChangeGL (algebraMap K (AlgebraicClosure K)) (t x) =
      F.g0 * rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ x) * F.g0⁻¹)
    {V : Set (Fin Tag.E6.rank → ZMod 3)}
    (hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)))
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    Assembly.IsSubnormal (ggKGTwJ F γ)
      ((Subgroup.centralizer
        (t '' {x | x ∈ V ∧ ExcSplitRootGen.excRefl (p := 3) γ x = x})).comap
          (twistedE6RootGroup K σ).subtype) := by
  have hle : ggKGTwJ F γ ≤ (Subgroup.centralizer
      (t '' {x | x ∈ V ∧ ExcSplitRootGen.excRefl (p := 3) γ x = x})).comap
        (twistedE6RootGroup K σ).subtype :=
    ggKGTwJ_le_centralizer_three F hζ hζo ht hγ
  refine Assembly.IsSubnormal.step hle ?_ (Assembly.IsSubnormal.refl _)
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro j c hj hc
  have hnorm := ggKGTwJ_Y_mem_normalizer_three F hζ hζo ht hV hγ hc
  have hconj_root : ggKGTwY F c * ggKGTwY F j * (ggKGTwY F c)⁻¹ ∈
      rootRankOneGroup TwistTag.E6.tag (AlgebraicClosure K) γ :=
    ((Subgroup.mem_normalizer_iff.1 hnorm) (ggKGTwY F j)).1
      ((TwE6PlusRootGen.mem_ggKGTwJ_iff hσ F).1 hj)
  refine (TwE6PlusRootGen.mem_ggKGTwJ_iff hσ F).2 ?_
  simpa only [map_mul, map_inv] using hconj_root

theorem isComponentOf_ggKGTwJ_three
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hq : 4 ≤ 2 ^ n)
    (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {t : (Fin 6 → ZMod 3) → ModGL TwistTag.E6.tag K}
    (ht : ∀ x, baseChangeGL (algebraMap K (AlgebraicClosure K)) (t x) =
      F.g0 * rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ x) * F.g0⁻¹)
    {V : Set (Fin Tag.E6.rank → ZMod 3)}
    (hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)))
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    Assembly.IsComponentOf (ggKGTwJ F γ)
      ((Subgroup.centralizer
        (t '' {x | x ∈ V ∧ ExcSplitRootGen.excRefl (p := 3) γ x = x})).comap
          (twistedE6RootGroup K σ).subtype) := by
  exact ⟨ggKGTwJ_le_centralizer_three F hζ hζo ht hγ,
    ggKGTwJ_subnormal_three hσ F hζ hζo ht hV hγ,
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2
      (ggKGTwJ_quasisimple hK hσ F hv hγ hq)⟩

end CFSG.StandardType.TwE6ThreeRootGen

end
