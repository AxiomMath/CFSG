module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortDefs
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneTableData
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerMark
public import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
public import CFSG.LocalAnalysis.StandardType.GGTPLayerTwE6
public import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeThreeCoroot
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
public import CFSG.Mathlib.GroupTheory.CyclicPrimeExponent
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenOACheck
public import CFSG.GroupTheory.DiagonalTwentySeven
public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27DiagTorus
public import TauCeti.GroupTheory.FixedSubgroup

public section

namespace CFSG.StandardType.FrameRoute.TwE6Model

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.E6Descent
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three CFSG.StandardType.TwE6DD2
  CFSG.StandardType.NTPlane

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_isRoot_corootVec_eq {v : X3}
    (hv : (kerRoots v).ncard = 30) :
    ∃ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ ∧ TwE6EndNode3.corootVec γ = v := by
  have hcard : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.e6KerCount v =
      (kerRoots v).ncard := by
    let S := (rootFinset Tag.E6).filter fun α =>
      ∑ i, v i * ((α i : ℤ) : ZMod 3) = 0
    have hS : kerRoots v = ↑S := by
      ext α
      simp only [kerRoots, Set.mem_setOf_eq, S, Finset.mem_coe, Finset.mem_filter,
        mem_rootFinset, pairVec]
    rw [CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.e6KerCount, hS,
      Set.ncard_coe_finset]
  have hx : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.e6KerCount v = 30 := by
    rw [hcard, hv]
  obtain ⟨ρ, hρroot, hρv⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.e6Cen_coroot_of_kerCount v hx
  refine ⟨ρ, hρroot, ?_⟩
  funext j
  have hcartan_symm : ∀ i j : Fin Tag.E6.rank, Tag.E6.cartan i j = Tag.E6.cartan j i := by
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  have hsingle : CFSG.LieType.Steinberg.Adjoint.iform ρ (Pi.single j 1) =
      ∑ l, Tag.E6.cartan j l * ρ l := by
    simp only [CFSG.LieType.Steinberg.Adjoint.iform, Tag.symmetrizedCartan, Tag.symmetrizer,
      one_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_eq_single j]
    · simp only [Pi.single_eq_same, mul_one]
      rw [hcartan_symm i j, mul_comm]
    · intro x _ hx
      simp [hx]
    · intro hj
      simp at hj
  rw [TwE6EndNode3.corootVec, ← hsingle]
  exact (hρv j).symm

private noncomputable def torusPowHom {K : Type} [Field K]
    {R : Subgroup (ModGL Tag.E6 (AlgebraicClosure K))}
    {g : ModGL Tag.E6 (AlgebraicClosure K)} {ζ : (AlgebraicClosure K)ˣ}
    (hζ : orderOf ζ = 3)
    (hR : ∀ w : X3, g * rootDiagUnit Tag.E6 (fun i => ζ ^ (w i).val) * g⁻¹ ∈ R) :
    Multiplicative X3 →* ↥R where
  toFun w := ⟨g * rootDiagUnit Tag.E6 (fun i => ζ ^ (w.toAdd i).val) * g⁻¹, hR w.toAdd⟩
  map_one' := by
    apply Subtype.ext
    change g * rootDiagUnit Tag.E6
      (fun i => ζ ^ ((Multiplicative.toAdd (1 : Multiplicative X3)) i).val) * g⁻¹ = 1
    have h1 : (fun i => ζ ^ ((Multiplicative.toAdd (1 : Multiplicative X3)) i).val) = 1 := by
      funext i
      simp
    rw [h1, rootDiagUnit_one]
    simp
  map_mul' w w' := by
    apply Subtype.ext
    change g * rootDiagUnit Tag.E6 (fun i => ζ ^ ((w * w').toAdd i).val) * g⁻¹ =
      (g * rootDiagUnit Tag.E6 (fun i => ζ ^ (w.toAdd i).val) * g⁻¹) *
        (g * rootDiagUnit Tag.E6 (fun i => ζ ^ (w'.toAdd i).val) * g⁻¹)
    have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
    have hfun : (fun i => ζ ^ ((w * w').toAdd i).val) =
        (fun i => ζ ^ (w.toAdd i).val) * (fun i => ζ ^ (w'.toAdd i).val) := by
      funext i
      exact CFSG.GroupTheory.DiagonalTwentySeven.pow_add_zmod3 ζ hζ3 (w.toAdd i) (w'.toAdd i)
    rw [hfun, rootDiagUnit_mul]
    group

private theorem torusPowHom_apply {K : Type} [Field K]
    {R : Subgroup (ModGL Tag.E6 (AlgebraicClosure K))}
    {g : ModGL Tag.E6 (AlgebraicClosure K)} {ζ : (AlgebraicClosure K)ˣ}
    (hζ : orderOf ζ = 3)
    (hR : ∀ w : X3, g * rootDiagUnit Tag.E6 (fun i => ζ ^ (w i).val) * g⁻¹ ∈ R)
    (w : Multiplicative X3) :
    ((torusPowHom (R := R) (g := g) (ζ := ζ) hζ hR w : ↥R) :
      ModGL Tag.E6 (AlgebraicClosure K)) =
      g * rootDiagUnit Tag.E6 (fun i => ζ ^ (w.toAdd i).val) * g⁻¹ := rfl

private theorem rootDiagUnit_pow_injective {K : Type} [Field K]
    {ζ : (AlgebraicClosure K)ˣ} (hζ : orderOf ζ = 3) :
    Function.Injective fun w : X3 => rootDiagUnit Tag.E6 (fun i => ζ ^ (w i).val) := by
  intro w w' h
  have hzeta : (fun i => ζ ^ (w i).val) = (fun i => ζ ^ (w' i).val) :=
    CFSG.LieType.Chevalley.rootDiagUnit_injective h
  funext i
  have hζ_eq : ζ ^ (w i).val = ζ ^ (w' i).val := congrFun hzeta i
  have hmod : (w i).val ≡ (w' i).val [MOD 3] := by
    have := pow_eq_pow_iff_modEq.mp hζ_eq
    rwa [hζ] at this
  exact ZMod.val_injective 3 (Nat.ModEq.eq_of_lt_of_lt hmod (ZMod.val_lt _) (ZMod.val_lt _))

private theorem conj_rootDiagUnit_pow_injective {K : Type} [Field K]
    {g : ModGL Tag.E6 (AlgebraicClosure K)} {ζ : (AlgebraicClosure K)ˣ}
    (hζ : orderOf ζ = 3) :
    Function.Injective fun w : X3 =>
      g * rootDiagUnit Tag.E6 (fun i => ζ ^ (w i).val) * g⁻¹ := by
  intro w w' h
  exact rootDiagUnit_pow_injective hζ (mul_left_cancel (mul_right_cancel h))

theorem exists_torusHom_twInndiag
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ 2 ^ n) {g : ModGL Tag.E6 (AlgebraicClosure K)}
    {ζ : (AlgebraicClosure K)ˣ} (hζ : orderOf ζ = 3)
    (hR : ∀ w : X3, g * rootDiagUnit Tag.E6 (fun i => ζ ^ (w i).val) * g⁻¹ ∈
      TwistedDiag.Rgrp (AlgebraicClosure K) Fr) :
    ∃ τ : Multiplicative X3 →* ↥(RecipeExcLang.twInndiagGroup K σ), Function.Injective τ ∧
      ∀ w : X3, twInndiagEquivRgrp hn hK σ hσ Fr hFr (τ (Multiplicative.ofAdd w)) = ⟨_, hR w⟩ := by
  let dHom : Multiplicative X3 →* ↥(TwistedDiag.Rgrp (AlgebraicClosure K) Fr) :=
    torusPowHom (R := TwistedDiag.Rgrp (AlgebraicClosure K) Fr) (g := g) hζ hR
  let τ : Multiplicative X3 →* ↥(RecipeExcLang.twInndiagGroup K σ) :=
    (twInndiagEquivRgrp hn hK σ hσ Fr hFr).symm.toMonoidHom.comp dHom
  have hτ_inj : Function.Injective τ := by
    intro w w' h
    have hd : dHom w = dHom w' := by
      simpa [τ, MulEquiv.apply_symm_apply] using
        congrArg (twInndiagEquivRgrp hn hK σ hσ Fr hFr) h
    have hval : ((torusPowHom (R := TwistedDiag.Rgrp (AlgebraicClosure K) Fr) (g := g)
        hζ hR w : ↥(TwistedDiag.Rgrp (AlgebraicClosure K) Fr)) :
        ModGL Tag.E6 (AlgebraicClosure K)) =
        ((torusPowHom (R := TwistedDiag.Rgrp (AlgebraicClosure K) Fr) (g := g)
        hζ hR w' : ↥(TwistedDiag.Rgrp (AlgebraicClosure K) Fr)) :
        ModGL Tag.E6 (AlgebraicClosure K)) := by
      simpa only [dHom] using congrArg Subtype.val hd
    have hww : w.toAdd = w'.toAdd := by
      simpa only [torusPowHom_apply] using
        conj_rootDiagUnit_pow_injective (g := g) hζ hval
    exact Multiplicative.toAdd.injective hww
  refine ⟨τ, hτ_inj, ?_⟩
  intro w
  simp [τ, dHom, torusPowHom, MulEquiv.apply_symm_apply]

theorem fixedSubgroup_twConj_eq
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (s : ↥(RecipeExcLang.twInndiagGroup K σ)) :
    TauCeti.fixedSubgroup (RecipeExcLang.twConj K σ s).toMonoidHom =
      (Subgroup.centralizer
        ({(s : ModGL TwistTag.E6.tag K)} : Set (ModGL TwistTag.E6.tag K))).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
  ext h
  rw [TauCeti.mem_fixedSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hh
    have h1 := congrArg (fun x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom =>
      (x : ModGL TwistTag.E6.tag K)) hh
    simp only [MulEquiv.coe_toMonoidHom, RecipeExcLang.coe_twConj] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  · intro hh
    apply Subtype.ext
    simp only [MulEquiv.coe_toMonoidHom, RecipeExcLang.coe_twConj]
    exact mul_inv_eq_iff_eq_mul.mpr hh.symm

theorem normal_solvable_of_eq_sup_cyclic {G : Type*} [Group G] {C X D : Subgroup G}
    (hC : C = X ⊔ D) (hX : IsCyclic X) (hXD : X ≤ Subgroup.centralizer (D : Set G)) :
    D ≤ C ∧ (D.subgroupOf C).Normal ∧
      ∀ _ : (D.subgroupOf C).Normal, IsSolvable (↥C ⧸ D.subgroupOf C) := by
  subst hC
  have hXn : X ≤ Subgroup.normalizer (D : Set G) :=
    hXD.trans (Subgroup.centralizer_le_normalizer (D : Set G))
  refine ⟨le_sup_right, ?_, ?_⟩
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
      (sup_le hXn Subgroup.le_normalizer)
  · intro hN
    let N := D.subgroupOf (X ⊔ D)
    let Q := ↥(X ⊔ D) ⧸ N
    let f : X →* Q := (QuotientGroup.mk' N).comp (Subgroup.inclusion le_sup_left)
    have hf : Function.Surjective f := by
      intro q
      obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (N := N) q
      obtain ⟨x, hx, d, hd, hcd⟩ : ∃ x ∈ X, ∃ d ∈ D, x * d = (c : G) := by
        have hc : (c : G) ∈ (↑(X ⊔ D) : Set G) := c.2
        rw [Subgroup.coe_mul_of_left_le_normalizer_right X D hXn] at hc
        simpa only [SetLike.mem_coe] using Set.mem_mul.mp hc
      refine ⟨⟨x, hx⟩, ?_⟩
      have hsplit : c = (⟨x, Subgroup.mem_sup_left hx⟩ : ↥(X ⊔ D)) *
          ⟨d, Subgroup.mem_sup_right hd⟩ := Subtype.ext hcd.symm
      rw [hsplit, map_mul]
      have hd1 : (QuotientGroup.mk' N) ⟨d, Subgroup.mem_sup_right hd⟩ = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact hd
      rw [hd1, mul_one]
      rfl
    refine isSolvable_of_comm fun a b => ?_
    obtain ⟨x, rfl⟩ := hf a
    obtain ⟨y, rfl⟩ := hf b
    simpa only [map_mul] using congrArg f (hX.isMulCommutative.is_comm.comm x y)

theorem largeEvenMarking_twA5_of_statedModel {D : Type} [Group D] (hD : CFSG.IsQuasisimple D)
    (hZ : Subgroup.center D = ⊥) (hM : StatedClassicalModel D .PSU 6 2 1) :
    LargeEvenMarking D fun lab _ _ _ _ _ => lab = ⟨.twA, 5, 1⟩ := by
  have hsimple : IsSimpleGroup (D ⧸ Subgroup.center D) := hD.2.1
  have hscm : StatedClassicalModel (D ⧸ Subgroup.center D) .PSU 6 2 1 :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm hM
  have hlab : LargeEvenInLambda2 (⟨.twA, 5, 1⟩ : LargeEvenLabel) := by
    refine ⟨le_rfl, ?_⟩
    norm_num
  exact @D4Inner.largeEvenMarking_of_rawDatum D _ hD.1.commutator_eq_top hsimple
    ⟨.twA, 5, 1⟩ hlab (recipeUnitary_of_statedClassicalModel hscm)
    (fun lab => lab = ⟨.twA, 5, 1⟩) rfl

theorem eq_smul_of_mem_cyclic {G : Type*} [Group G] {X : Subgroup G} [Finite X] (hX : IsCyclic X)
    {V : Type*} [AddCommGroup V] [Module (ZMod 3) V] (τ : Multiplicative V →* G)
    (hτ : Function.Injective τ) {v w : V} (hv : v ≠ 0) (hvX : τ (Multiplicative.ofAdd v) ∈ X)
    (hwX : τ (Multiplicative.ofAdd w) ∈ X) : ∃ c : ZMod 3, w = c • v := by
  have h3 : ∀ x : V, (3 : ℕ) • x = 0 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3) 3 x, show ((3 : ℕ) : ZMod 3) = 0 by decide, zero_smul]
  have hpow : ∀ (x : V) (hx : τ (Multiplicative.ofAdd x) ∈ X), (⟨_, hx⟩ : X) ^ 3 = 1 :=
    fun x hx => Subtype.ext (by
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← map_pow, ← ofAdd_nsmul, h3 x, ofAdd_zero, map_one])
  have hy1 : (⟨_, hvX⟩ : X) ≠ 1 := fun h => hv (Multiplicative.ofAdd.injective (hτ (by
    rw [ofAdd_zero, map_one]; exact congrArg Subtype.val h)))
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (CFSG.GroupTheory.mem_zpowers_of_pow_eq_one_of_prime Nat.prime_three (hpow v hvX) hy1
      (hpow w hwX))
  refine ⟨(k : ZMod 3), Multiplicative.ofAdd.injective (hτ ?_)⟩
  have hk' := congrArg Subtype.val hk
  simp only [Subgroup.coe_zpow] at hk'
  rw [Int.cast_smul_eq_zsmul (ZMod 3), ofAdd_zsmul, map_zpow, hk']

section TorusActor


theorem rgrpConjAut_torusHom {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    {g : ModGL Tag.E6 (AlgebraicClosure K)} {ζ : (AlgebraicClosure K)ˣ}
    (hR : ∀ w : X3, g * rootDiagUnit Tag.E6 (fun i => ζ ^ (w i).val) * g⁻¹ ∈
      TwistedDiag.Rgrp (AlgebraicClosure K) Fr)
    {τ : Multiplicative X3 →* ↥(RecipeExcLang.twInndiagGroup K σ)}
    (hτ : ∀ w : X3, twInndiagEquivRgrp hn hK σ hσ Fr hFr (τ (Multiplicative.ofAdd w)) =
      ⟨_, hR w⟩) (w : X3) :
    rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hR w⟩ =
      RecipeExcLang.twConj K σ (τ (Multiplicative.ofAdd w)) := by
  rw [← hτ w, rgrpConjAut_apply_baseChange]

theorem conj_baseChangeGL_torusHom {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    {g : ModGL Tag.E6 (AlgebraicClosure K)} {ζ : (AlgebraicClosure K)ˣ}
    (hR : ∀ w : X3, g * rootDiagUnit Tag.E6 (fun i => ζ ^ (w i).val) * g⁻¹ ∈
      TwistedDiag.Rgrp (AlgebraicClosure K) Fr)
    {τ : Multiplicative X3 →* ↥(RecipeExcLang.twInndiagGroup K σ)}
    (hτ : ∀ w : X3, twInndiagEquivRgrp hn hK σ hσ Fr hFr (τ (Multiplicative.ofAdd w)) =
      ⟨_, hR w⟩) (w : X3) :
    g⁻¹ * baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
      ((τ (Multiplicative.ofAdd w) : ↥(RecipeExcLang.twInndiagGroup K σ)) :
        ModGL TwistTag.E6.tag K) * g =
      rootDiagUnit Tag.E6 (fun i => ζ ^ (w i).val) := by
  have hbase : baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
      ((τ (Multiplicative.ofAdd w) : ↥(RecipeExcLang.twInndiagGroup K σ)) :
        ModGL TwistTag.E6.tag K) =
      g * rootDiagUnit Tag.E6 (fun i => ζ ^ (w i).val) * g⁻¹ := by
    have h := congrArg (fun x : ↥(TwistedDiag.Rgrp (AlgebraicClosure K) Fr) =>
      (x : ModGL Tag.E6 (AlgebraicClosure K))) (hτ w)
    rwa [twInndiagEquivRgrp_apply] at h
  rw [hbase]
  group

theorem fixedSubgroup_rgrpConjAut_torusHom {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    {g : ModGL Tag.E6 (AlgebraicClosure K)} {ζ : (AlgebraicClosure K)ˣ}
    (hR : ∀ w : X3, g * rootDiagUnit Tag.E6 (fun i => ζ ^ (w i).val) * g⁻¹ ∈
      TwistedDiag.Rgrp (AlgebraicClosure K) Fr)
    {τ : Multiplicative X3 →* ↥(RecipeExcLang.twInndiagGroup K σ)}
    (hτ : ∀ w : X3, twInndiagEquivRgrp hn hK σ hσ Fr hFr (τ (Multiplicative.ofAdd w)) =
      ⟨_, hR w⟩) (v : X3) :
    TauCeti.fixedSubgroup (rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hR v⟩).toMonoidHom =
      (Subgroup.centralizer
        ({(τ (Multiplicative.ofAdd v) : ModGL TwistTag.E6.tag K)} :
          Set (ModGL TwistTag.E6.tag K))).subgroupOf (twistedE6RootGroup K σ) := by
  rw [rgrpConjAut_torusHom hn hK σ hσ Fr hFr hR hτ v]
  exact fixedSubgroup_twConj_eq σ (τ (Multiplicative.ofAdd v))

theorem twConj_torusHom_apply_of_mem_line {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (τ : Multiplicative X3 →* ↥(RecipeExcLang.twInndiagGroup K σ)) {v : X3}
    {D : Subgroup ↥(twistedE6RootGroup K σ)}
    (hD : ∀ d ∈ D, ((d : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) *
        ((τ (Multiplicative.ofAdd v) : ↥(RecipeExcLang.twInndiagGroup K σ)) :
          ModGL TwistTag.E6.tag K) =
      ((τ (Multiplicative.ofAdd v) : ↥(RecipeExcLang.twInndiagGroup K σ)) :
        ModGL TwistTag.E6.tag K) * ((d : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K))
    {w : X3} (hw : ∃ c : ZMod 3, w = c • v) {j : ↥(twistedE6RootGroup K σ)} (hj : j ∈ D) :
    RecipeExcLang.twConj K σ (τ (Multiplicative.ofAdd w)) j = j := by
  obtain ⟨c, rfl⟩ := hw
  have hcv : (c • v : X3) = c.val • v := by
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    rw [Nat.cast_smul_eq_nsmul]
  have hfixv : RecipeExcLang.twConj K σ (τ (Multiplicative.ofAdd v)) j = j := by
    apply Subtype.ext
    rw [RecipeExcLang.coe_twConj, ← hD j hj]
    group
  have hpow : ∀ m : ℕ, ((RecipeExcLang.twConj K σ (τ (Multiplicative.ofAdd v))) ^ m) j = j := by
    intro m
    induction m with
    | zero => rw [pow_zero, MulAut.one_apply]
    | succ m ih => rw [pow_succ, MulAut.mul_apply, hfixv, ih]
  rw [hcv, ofAdd_nsmul, map_pow, map_pow]
  exact hpow c.val

end TorusActor

end CFSG.StandardType.FrameRoute.TwE6Model

end
