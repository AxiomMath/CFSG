module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6BridgeRoots
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6Sp4Factors
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Sub

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.Sp6Bridge

open Matrix Module Representation CFSG.Open
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.QuasithinUnique.Setup.X7b CFSG.Theory.Representation
open scoped MatrixGroups TensorProduct

variable {K k : Type} [Field K] [Fintype K] [CharP K 2]
  [Field k] [CharP k 2] [IsAlgClosed k] [Algebra (ZMod 2) K] [Algebra (ZMod 2) k]

@[expose] noncomputable def rootBlock (b : Bool) : SL(2, K) →* StatedSp 2 K :=
  if b then longBlock K 2 1 else shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1)

omit [CharP k 2] in
theorem factorsFinrankLe_binary_natural_root (b : Bool) (j : ℕ) :
    FactorsFinrankLe (extendScalars k (matrixRestrictRep (F := ZMod 2)
      { toFun := fun g : SL(2, K) =>
          glMat (((minorAut K ^ j) ((antiSpEquiv K).symm (rootBlock b g)) : antiSp K) :
            GL (Fin 4) K)
        map_one' := by simp
        map_mul' g h := by simp [map_mul] })) 2 := by
  let A : SL(2, K) →* Matrix (Fin 4) (Fin 4) K :=
    { toFun := fun g => glMat (((minorAut K ^ j)
        ((antiSpEquiv K).symm (rootBlock b g)) : antiSp K) : GL (Fin 4) K)
      map_one' := by simp
      map_mul' g h := by simp [map_mul] }
  change FactorsFinrankLe (extendScalars k (matrixRestrictRep (F := ZMod 2) A)) 2
  apply factorsFinrankLe_extend_matrixRestrict
  intro φ
  have hconj : ∀ g : StatedSp 2 K,
      antiSpEquiv K ((minorAut K ^ j) ((antiSpEquiv K).symm g)) =
        (exceptionalSpAut K ^ j) g := by
    induction j with
    | zero => intro g; simp
    | succ j ih =>
      intro g
      dsimp only at ih
      have hg : minorAut K ((antiSpEquiv K).symm g) =
          (antiSpEquiv K).symm (exceptionalSpAut K g) := by
        simp [exceptionalSpAut]
      rw [pow_succ, MulAut.mul_apply, hg, ih]
      rw [pow_succ, MulAut.mul_apply]
  have hA : ∀ g, (A g).submatrix antiIdx antiIdx =
      symplecticMatrices ((exceptionalSpAut K ^ j).toMonoidHom.comp (rootBlock b)) g := by
    intro g
    dsimp only [A, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [← spMat_antiSpEquiv, hconj]
    rfl
  let B := symplecticMatrices ((exceptionalSpAut K ^ j).toMonoidHom.comp (rootBlock b))
  let C : SL(2, K) →* Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
    { toFun := fun g => (A g).submatrix antiIdx antiIdx
      map_one' := by ext i j; simp [Matrix.one_apply, antiIdx.injective.eq_iff]
      map_mul' g h := by rw [map_mul, Matrix.submatrix_mul_equiv] }
  have hCB : C = B := MonoidHom.ext hA
  have heq : (matrixMapRep A φ).Equiv (matrixMapRep B φ) := by
    let β := reindexMatrixRepEquiv A φ antiIdx
    change (matrixMapRep A φ).Equiv (matrixMapRep C φ) at β
    rw [hCB] at β
    exact β
  apply factorsFinrankLe_of_equiv heq.symm
  cases b
  · exact (factorsFinrankLe_exceptional_pow_blocks j φ).1
  · exact (factorsFinrankLe_exceptional_pow_blocks j φ).2

@[expose] noncomputable def topQuotBotEquiv
    {G W : Type} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) :
    (⊥ : Subrepresentation (⊤ : Subrepresentation ρ).toRepresentation).quotient.Equiv ρ :=
  Representation.Equiv.mk
    ((Submodule.quotEquivOfEqBot (⊥ : Submodule (ZMod 2)
        (⊤ : Subrepresentation ρ).toSubmodule) rfl).trans Submodule.topEquiv) fun g => by
      apply LinearMap.ext
      intro v
      induction v using Submodule.Quotient.induction_on with
      | _ v => rfl

omit [CharP k 2] in
theorem factorsFinrankLe_extend_root_of_irreducible
    {e : ℕ} (hK : Fintype.card K = 2 ^ e) (he : 1 ≤ e)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (antiSp K) W) (hirr : ρ.IsIrreducible)
    {z : antiSp K} (hz : z * z = 1) (hz1 : z ≠ 1)
    (hsmall : finrank (ZMod 2) (LinearMap.range (ρ z - 1)) < 3 * e) (b : Bool) :
    FactorsFinrankLe (extendScalars k (ρ.comp
      ((antiSpEquiv K).symm.toMonoidHom.comp (rootBlock b)))) 2 := by
  classical
  by_cases hnt : ∃ g, ρ g ≠ 1
  · let A : Subrepresentation ρ := ⊤
    let B : Subrepresentation A.toRepresentation := ⊥
    let β := topQuotBotEquiv ρ
    have hBirr : B.quotient.IsIrreducible := by
      have : Nontrivial (A.toSubmodule ⧸ B.toSubmodule) :=
        (Equiv.nontrivial_congr β.toLinearEquiv.toEquiv).mpr
          ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp hirr).1
      exact (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff B.quotient).mpr
        ⟨inferInstance, fun U hU => by
          let U' : Subrepresentation ρ :=
            { toSubmodule := U.map β.toLinearEquiv.toLinearMap
              apply_mem_toSubmodule := by
                rintro g v ⟨w, hw, rfl⟩
                exact ⟨B.quotient g w, hU g w hw,
                  LinearMap.congr_fun (β.isIntertwining' g) w⟩ }
          rcases hirr.eq_bot_or_eq_top U' with h | h
          · left
            rw [Submodule.eq_bot_iff]
            intro w hw
            have hmem : β w ∈ U' := Submodule.mem_map_of_mem hw
            rw [h] at hmem
            exact β.toLinearEquiv.injective (hmem.trans β.toLinearEquiv.map_zero.symm)
          · right
            rw [eq_top_iff]
            intro w _
            have hmem : β w ∈ U' := by rw [h]; exact Submodule.mem_top
            obtain ⟨w', hw', heq⟩ := hmem
            exact β.toLinearEquiv.injective heq ▸ hw'⟩
    have hBnt : ∃ g, B.quotient g ≠ 1 := by
      obtain ⟨g, hg⟩ := hnt
      refine ⟨g, fun h => hg ?_⟩
      apply LinearMap.ext
      intro w
      obtain ⟨v, rfl⟩ := β.surjective w
      have hβ := LinearMap.congr_fun (β.isIntertwining' g) v
      rw [h] at hβ
      exact hβ.symm
    obtain ⟨j, φ, hφ⟩ := natural_subquotient_of_sp4_displacement_lt_three_mul
      hK he ρ A B hBirr hBnt z hz hz1 hsmall
    let θ : W ≃+ (Fin 4 → K) := β.symm.toLinearEquiv.toAddEquiv.trans φ
    have hθ : ∀ g w, θ (ρ g w) =
        (glMat (((minorAut K ^ j) g : antiSp K) : GL (Fin 4) K)).mulVec (θ w) := by
      intro g w
      exact (congrArg φ (LinearMap.congr_fun (β.symm.isIntertwining' g) w)).trans
        (hφ g (β.symm w))
    let R : SL(2, K) →* Matrix (Fin 4) (Fin 4) K :=
      { toFun := fun g => glMat (((minorAut K ^ j)
          ((antiSpEquiv K).symm (rootBlock b g)) : antiSp K) : GL (Fin 4) K)
        map_one' := by simp
        map_mul' g h := by simp [map_mul] }
    let τ : Representation (ZMod 2) SL(2, K) W :=
      ρ.comp ((antiSpEquiv K).symm.toMonoidHom.comp (rootBlock b))
    let θlin : W ≃ₗ[ZMod 2] (Fin 4 → K) :=
      LinearEquiv.ofBijective (θ.toAddMonoidHom.toZModLinearMap 2) θ.bijective
    let γ : Representation.Equiv τ (matrixRestrictRep (F := ZMod 2) R) :=
      Representation.Equiv.mk θlin fun g => by
        apply LinearMap.ext
        intro w
        exact hθ _ w
    have htarget : FactorsFinrankLe (extendScalars k (matrixRestrictRep (F := ZMod 2) R)) 2 :=
      factorsFinrankLe_binary_natural_root b j
    let f := extendScalars_map k γ.toIntertwiningMap
    have hf : Function.Injective f := by
      change Function.Injective (γ.toLinearEquiv.toLinearMap.baseChange k)
      rw [LinearMap.baseChange_eq_ltensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap _ γ.toLinearEquiv.injective
    exact factorsFinrankLe_of_injective f hf htarget
  · push Not at hnt
    obtain ⟨β⟩ := CFSG.LocalAnalysis.RankThreeUC.S15.equiv_trivial_of_trivial_isIrreducible
      ρ hirr hnt
    have hdim : finrank (ZMod 2) W = 1 := by
      rw [β.toLinearEquiv.finrank_eq, Module.finrank_self]
    apply factorsFinrankLe_of_finrank_le
    change finrank k (k ⊗[ZMod 2] W) ≤ 2
    rw [Module.finrank_tensorProduct, Module.finrank_self, one_mul, hdim]
    omega

omit [Fintype K] [CharP K 2] [CharP k 2] [IsAlgClosed k] [Algebra (ZMod 2) K] in
private theorem extend_root_factors_sub_quot
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (ρ : Representation (ZMod 2) (antiSp K) W) (A : Subrepresentation ρ)
    (π : SL(2, K) →* antiSp K)
    (hA : FactorsFinrankLe (extendScalars k (A.toRepresentation.comp π)) 2)
    (hQ : FactorsFinrankLe (extendScalars k (A.quotient.comp π)) 2) :
    FactorsFinrankLe (extendScalars k (ρ.comp π)) 2 := by
  let f₀ : IntertwiningMap (A.toRepresentation.comp π) (ρ.comp π) :=
    ⟨A.toSubmodule.subtype, fun _ => rfl⟩
  let g₀ : IntertwiningMap (ρ.comp π) (A.quotient.comp π) :=
    ⟨A.toSubmodule.mkQ, fun _ => rfl⟩
  let f := extendScalars_map k f₀
  let g := extendScalars_map k g₀
  have hf : Function.Injective f := by
    change Function.Injective (A.toSubmodule.subtype.baseChange k)
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ A.toSubmodule.injective_subtype
  have hg : Function.Surjective g := by
    change Function.Surjective (A.toSubmodule.mkQ.baseChange k)
    exact LinearMap.baseChange_surjective k A.toSubmodule.mkQ_surjective
  have hex : Function.Exact f g := by
    change Function.Exact (A.toSubmodule.subtype.baseChange k) (A.toSubmodule.mkQ.baseChange k)
    simpa only [LinearMap.baseChange_eq_ltensor] using
      Module.Flat.lTensor_exact (M := k) (LinearMap.exact_subtype_mkQ A.toSubmodule)
  exact factorsFinrankLe_of_exact f g hf hg hex hA hQ

omit [Fintype K] [CharP K 2] [CharP k 2] [Algebra (ZMod 2) K] in
private theorem zero_extend_root_factors
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (ρ : Representation (ZMod 2) (antiSp K) W) (π : SL(2, K) →* antiSp K)
    (hzero : Subsingleton W) : FactorsFinrankLe (extendScalars k (ρ.comp π)) 2 := by
  have : Subsingleton W := hzero
  apply factorsFinrankLe_of_finrank_le (extendScalars k (ρ.comp π))
  change finrank k (k ⊗[ZMod 2] W) ≤ 2
  rw [Module.finrank_tensorProduct]
  simp [Module.finrank_zero_of_subsingleton]

omit [CharP k 2] in
private theorem simple_extend_root_factors
    {e : ℕ} (hK : Fintype.card K = 2 ^ e) (he : 1 ≤ e)
    {z : antiSp K} (hz : z * z = 1) (hz1 : z ≠ 1) (b : Bool)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (ρ : Representation (ZMod 2) (antiSp K) W) (hirr : ρ.IsIrreducible)
    (hsmall : finrank (ZMod 2) (LinearMap.range (ρ z - 1)) < 3 * e) :
    FactorsFinrankLe (extendScalars k (ρ.comp
      ((antiSpEquiv K).symm.toMonoidHom.comp (rootBlock b)))) 2 := by
  have : Finite W := Module.finite_of_finite (ZMod 2)
  exact factorsFinrankLe_extend_root_of_irreducible hK he ρ hirr hz hz1 hsmall b

omit [Fintype K] [CharP k 2] [IsAlgClosed k] [Algebra (ZMod 2) K] in
private theorem extend_root_factors_induction_step
    {e : ℕ} {z : antiSp K} (b : Bool)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (ρ : Representation (ZMod 2) (antiSp K) W) (A : Subrepresentation ρ)
    (hA : finrank (ZMod 2) (LinearMap.range (A.toRepresentation z - 1)) < 3 * e →
      FactorsFinrankLe (extendScalars k (A.toRepresentation.comp
        ((antiSpEquiv K).symm.toMonoidHom.comp (rootBlock b)))) 2)
    (hQ : finrank (ZMod 2) (LinearMap.range (A.quotient z - 1)) < 3 * e →
      FactorsFinrankLe (extendScalars k (A.quotient.comp
        ((antiSpEquiv K).symm.toMonoidHom.comp (rootBlock b)))) 2)
    (hsmall : finrank (ZMod 2) (LinearMap.range (ρ z - 1)) < 3 * e) :
    FactorsFinrankLe (extendScalars k (ρ.comp
      ((antiSpEquiv K).symm.toMonoidHom.comp (rootBlock b)))) 2 := by
  have : Finite W := Module.finite_of_finite (ZMod 2)
  have hb : finrank (ZMod 2) (LinearMap.range (A.toRepresentation z - 1)) < 3 * e :=
    lt_of_le_of_lt (CFSG.QuasithinUnique.Setup.X7.finrank_range_toRepresentation_le A z) hsmall
  have hq : finrank (ZMod 2) (LinearMap.range (A.quotient z - 1)) < 3 * e :=
    lt_of_le_of_lt (CFSG.QuasithinUnique.Setup.X7.finrank_range_quotient_le A z) hsmall
  exact extend_root_factors_sub_quot ρ A _ (hA hb) (hQ hq)

omit [CharP k 2] in
theorem factorsFinrankLe_extend_root_of_displacement_lt
    {e : ℕ} (hK : Fintype.card K = 2 ^ e) (he : 1 ≤ e)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (ρ : Representation (ZMod 2) (antiSp K) W)
    {z : antiSp K} (hz : z * z = 1) (hz1 : z ≠ 1)
    (hsmall : finrank (ZMod 2) (LinearMap.range (ρ z - 1)) < 3 * e) (b : Bool) :
    FactorsFinrankLe (extendScalars k (ρ.comp
      ((antiSpEquiv K).symm.toMonoidHom.comp (rootBlock b)))) 2 := by
  let π : SL(2, K) →* antiSp K := (antiSpEquiv K).symm.toMonoidHom.comp (rootBlock b)
  have key : finrank (ZMod 2) (LinearMap.range (ρ z - 1)) < 3 * e →
      FactorsFinrankLe (extendScalars k (ρ.comp π)) 2 :=
    rep_induction (k := ZMod 2) (G := antiSp K)
      (fun {W} _ _ _ ρ => finrank (ZMod 2) (LinearMap.range (ρ z - 1)) < 3 * e →
        FactorsFinrankLe (extendScalars k (ρ.comp π)) 2)
      (fun {W} _ _ _ ρ hzero _ => zero_extend_root_factors ρ π hzero)
      (fun {W} _ _ _ ρ hirr hsmall => simple_extend_root_factors hK he hz hz1 b ρ hirr hsmall)
      (fun {W} _ _ _ ρ A hA hQ hsmall =>
        extend_root_factors_induction_step b ρ A hA hQ hsmall)
      (finrank (ZMod 2) W) ρ rfl
  exact key hsmall

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.Sp6Bridge
