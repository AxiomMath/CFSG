module

public import CFSG.OddTranspositions.PartFour.ThirteenCompFactorModels
import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypesForms
import CFSG.Fischer.Classification.O4Minus2S5
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupProofsC
import CFSG.LocalAnalysis.WeakClosure81.W18ASNineOrthPlus
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.Quasithin.Background.B5FinSp
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.OddTranspositions.PartFour

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Open CFSG.LocalAnalysis.WeakClosure81 CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.ComponentInitial (bilinIsometryGroup mem_bilinIsometryGroup)
open CFSG.Blueprint (LieModel)
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus)
open Matrix

section Rank

variable {K : Type} [Field K]

theorem rank_toMatrix_sub_one {κ V : Type} [Fintype κ] [DecidableEq κ] [AddCommGroup V]
    [Module K V] (b : Module.Basis κ K V) (f : V →ₗ[K] V) :
    (LinearMap.toMatrix b b f - 1).rank =
      Module.finrank K (LinearMap.range (f - LinearMap.id)) := by
  rw [← LinearMap.toMatrix_id (v₁ := b), ← map_sub, Matrix.rank_eq_finrank_range_toLin _ b b,
    Matrix.toLin_toMatrix]

theorem rank_sub_one_eq_finrank {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) :
    (A - 1).rank = Module.finrank K (LinearMap.range (Matrix.toLin' A - LinearMap.id)) := by
  rw [← rank_toMatrix_sub_one (Pi.basisFun K ι), LinearMap.toMatrix_eq_toMatrix',
    LinearMap.toMatrix'_toLin']

theorem rank_sub_one_eq_one_of_transvection {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K} (β : (ι → K) →ₗ[K] K) {v : ι → K} (hA : ∀ x, A *ᵥ x = x + β x • v)
    (hv : v ≠ 0) {x₀ : ι → K} (hx₀ : β x₀ ≠ 0) : (A - 1).rank = 1 := by
  have hr : LinearMap.range (Matrix.toLin' A - LinearMap.id) = K ∙ v := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [LinearMap.sub_apply, Matrix.toLin'_apply, hA, LinearMap.id_apply, add_sub_cancel_left]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      refine ⟨(β x₀)⁻¹ • x₀, ?_⟩
      rw [LinearMap.sub_apply, Matrix.toLin'_apply, hA, LinearMap.id_apply, add_sub_cancel_left,
        map_smul, smul_eq_mul, inv_mul_cancel₀ hx₀, one_smul]
  rw [rank_sub_one_eq_finrank, hr, finrank_span_singleton hv]

end Rank

section Transport

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

private theorem glMatrixEquiv_symm_apply (A : GL ι K) (v : ι → K) :
    ((((mclt_glMatrixEquiv (Pi.basisFun K ι)).symm A :
        LinearMap.GeneralLinearGroup K (ι → K)) : (ι → K) →ₗ[K] (ι → K)) v) =
      (A : Matrix ι ι K) *ᵥ v := by
  have h := mclt_glMatrixEquiv_mulVec (Pi.basisFun K ι)
    ((mclt_glMatrixEquiv (Pi.basisFun K ι)).symm A) v
  rw [MulEquiv.apply_symm_apply, Pi.basisFun_equivFun, LinearEquiv.refl_apply,
    LinearEquiv.refl_apply] at h
  exact h.symm

private theorem glMatrixEquiv_symm_toLin (A : GL ι K) :
    (((mclt_glMatrixEquiv (Pi.basisFun K ι)).symm A : LinearMap.GeneralLinearGroup K (ι → K)) :
      (ι → K) →ₗ[K] (ι → K)) = Matrix.toLin' (A : Matrix ι ι K) :=
  LinearMap.ext fun v => by rw [glMatrixEquiv_symm_apply, Matrix.toLin'_apply]

private theorem rank_toMatrix_glMatrixEquiv_symm {κ : Type} [Fintype κ] [DecidableEq κ]
    (b : Module.Basis κ K (ι → K)) (A : GL ι K) :
    (LinearMap.toMatrix b b (((mclt_glMatrixEquiv (Pi.basisFun K ι)).symm A :
      LinearMap.GeneralLinearGroup K (ι → K)) : (ι → K) →ₗ[K] (ι → K)) - 1).rank =
      ((A : Matrix ι ι K) - 1).rank := by
  rw [glMatrixEquiv_symm_toLin, rank_toMatrix_sub_one, rank_sub_one_eq_finrank]

private theorem coe_glMatrixEquiv {κ V : Type} [Fintype κ] [DecidableEq κ] [AddCommGroup V]
    [Module K V] (b : Module.Basis κ K V) (g : LinearMap.GeneralLinearGroup K V) :
    ((mclt_glMatrixEquiv b g : GL κ K) : Matrix κ κ K) =
      LinearMap.toMatrix b b (g : V →ₗ[K] V) := by
  have h : ∀ w : κ → K, ((mclt_glMatrixEquiv b g : GL κ K) : Matrix κ κ K) *ᵥ w =
      LinearMap.toMatrix b b (g : V →ₗ[K] V) *ᵥ w := by
    intro w
    obtain ⟨v, rfl⟩ := b.equivFun.surjective w
    rw [mclt_glMatrixEquiv_mulVec]
    simp only [Module.Basis.equivFun_apply]
    rw [LinearMap.toMatrix_mulVec_repr]
  exact Matrix.toLin'.injective (LinearMap.ext h)

private theorem map_bilinIsometryGroup_eq_fischerMatrixGroup (B : LinearMap.BilinForm K (ι → K)) :
    (bilinIsometryGroup B).map (mclt_glMatrixEquiv (Pi.basisFun K ι)).toMonoidHom =
      fischerMatrixGroup fun A : Matrix ι ι K => ∀ x y, B (A *ᵥ x) (A *ᵥ y) = B x y := by
  have hset : {g : GL ι K | ∀ x y, B ((g : Matrix ι ι K) *ᵥ x) ((g : Matrix ι ι K) *ᵥ y) =
      B x y} = ((bilinIsometryGroup B).map
        (mclt_glMatrixEquiv (Pi.basisFun K ι)).toMonoidHom : Set (GL ι K)) := by
    ext A
    rw [Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_map_equiv, mem_bilinIsometryGroup]
    simp only [glMatrixEquiv_symm_apply]
  rw [fischerMatrixGroup, hset, Subgroup.closure_eq]

private theorem map_orthogonalGroup_eq_fischerMatrixGroup (Q : QuadraticForm K (ι → K)) :
    ((TauCeti.QuadraticMap.orthogonalGroup Q).comap
        (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K)).toMonoidHom).map
      (mclt_glMatrixEquiv (Pi.basisFun K ι)).toMonoidHom =
    fischerMatrixGroup fun A : Matrix ι ι K => ∀ x, Q (A *ᵥ x) = Q x :=
  mclt_map_glMatrixEquiv_eq_closure (Q := fun v => Q v) (Q₀ := fun v => Q v) (Pi.basisFun K ι)
    (fun v => by rw [Pi.basisFun_equivFun, LinearEquiv.refl_apply])
    (fun g => by rw [Subgroup.mem_comap, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]; rfl)

end Transport

theorem exists_fischerSp_equiv_statedSp {m : ℕ}
    (b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)) (halt : ∀ x, b x x = 0)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) :
    ∃ e : ↥(fischerMatrixGroup fun A : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 2) =>
        ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y) ≃* ↥(StatedSp m (ZMod 2)),
      ∀ g, ((((e g : ↥(StatedSp m (ZMod 2))) : GL (Fin m ⊕ Fin m) (ZMod 2)) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 2)) - 1).rank =
        (((g : GL (Fin (2 * m)) (ZMod 2)) : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 2)) -
          1).rank := by
  have hb : b.Nondegenerate := by
    refine ⟨hnd, fun y hy => hnd y fun x => ?_⟩
    have h := (show b.IsAlt from halt).neg_eq x y
    rw [hy x, neg_zero] at h
    exact h.symm
  obtain ⟨m', b', hdim, hb'⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_symplectic_basis b halt hb
  have hmm : m' = m := by
    rw [Module.finrank_fin_fun] at hdim
    omega
  subst hmm
  set e₁ := ((bilinIsometryGroup b).equivMapOfInjective _
      (mclt_glMatrixEquiv (Pi.basisFun (ZMod 2) (Fin (2 * m')))).injective).trans
    (MulEquiv.subgroupCongr (map_bilinIsometryGroup_eq_fischerMatrixGroup b)) with he₁
  have he₁v : ∀ g, ((e₁.symm g : ↥(bilinIsometryGroup b)) :
      LinearMap.GeneralLinearGroup (ZMod 2) (Fin (2 * m') → ZMod 2)) =
      (mclt_glMatrixEquiv (Pi.basisFun (ZMod 2) (Fin (2 * m')))).symm
        (g : GL (Fin (2 * m')) (ZMod 2)) := by
    intro g
    rw [MulEquiv.eq_symm_apply]
    exact congrArg Subtype.val (e₁.apply_symm_apply g)
  have hiso : (bilinIsometryGroup b).map (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
      (Fin (2 * m') → ZMod 2)).toMonoidHom = TauCeti.BilinForm.isometryGroup b := by
    ext e
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [TauCeti.BilinForm.mem_isometryGroup_iff]
      exact mem_bilinIsometryGroup.mp hg
    · intro he
      refine ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _).symm e, ?_,
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _).apply_symm_apply e⟩
      refine mem_bilinIsometryGroup.mpr ?_
      rw [TauCeti.BilinForm.mem_isometryGroup_iff] at he
      exact he
  let e₂ : ↥(bilinIsometryGroup b) ≃* ↥(TauCeti.BilinForm.isometryGroup b) :=
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin (2 * m') → ZMod 2)).subgroupMap
      (bilinIsometryGroup b)).trans (MulEquiv.subgroupCongr hiso)
  refine ⟨((e₁.symm.trans e₂).trans
    (CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryMatrixEquiv b' b hb')).trans
      (MulEquiv.subgroupCongr CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic.symm),
    fun g => ?_⟩
  have hval : (((((e₁.symm.trans e₂).trans
      (CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryMatrixEquiv b' b
        hb')).trans
        (MulEquiv.subgroupCongr CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic.symm) g :
          ↥(StatedSp m' (ZMod 2))) : GL (Fin m' ⊕ Fin m') (ZMod 2)) :
            Matrix (Fin m' ⊕ Fin m') (Fin m' ⊕ Fin m') (ZMod 2)) =
      LinearMap.toMatrix b' b' (((e₁.symm g : ↥(bilinIsometryGroup b)) :
        LinearMap.GeneralLinearGroup (ZMod 2) (Fin (2 * m') → ZMod 2)) :
          (Fin (2 * m') → ZMod 2) →ₗ[ZMod 2] (Fin (2 * m') → ZMod 2)) :=
    rfl
  rw [hval, he₁v, rank_toMatrix_glMatrixEquiv_symm]

theorem oddTranspFactors_statedSp_zmod_two {m : ℕ} (hm : 2 ≤ m) :
    OddTranspFactors ↥(StatedSp m (ZMod 2)) := by
  rcases (by omega : m = 2 ∨ 3 ≤ m) with rfl | hm3
  · exact (oddTranspFactors_perm 6).of_mulEquiv (CFSG.Quasithin.B5FinSp.theta (RingEquiv.refl _))
  · have hM : StatedClassicalModel (StatedProj (StatedSp m (ZMod 2))) .PSp m 2 1 :=
      ⟨⟨Nat.prime_two, le_rfl, hm, fun h => by have := (Prod.mk.inj h).1; omega⟩, ZMod 2,
        inferInstance, inferInstance, by rw [Nat.card_zmod]; norm_num, ⟨MulEquiv.refl _⟩⟩
    exact OddTranspFactors.of_statedProj _ (OddTranspFactors.of_statedClassicalModel hM
      (Or.inr (Or.inl ⟨m, 1, Or.inl (Or.inl ⟨by decide, hM⟩)⟩)))

private theorem card_zmod_two : Nat.card (ZMod 2) = 2 ^ 1 := by
  rw [Nat.card_zmod]
  norm_num

theorem oddTranspFactors_orthogonalPlus_zmod_two {k : ℕ} (hk : 3 ≤ k) :
    OddTranspFactors ↥(CFSG.PGLModel.orthogonalPlus k (ZMod 2)) := by
  rcases (by omega : k = 3 ∨ 4 ≤ k) with rfl | hk4
  · refine OddTranspFactors.of_commutator
      ((?_ : OddTranspFactors ↥(StatedOmega (StatedQuadPlus 3 (ZMod 2)))).of_mulEquiv
        (commutatorOrthogonalPlusEquiv 3 (ZMod 2)).symm)
    obtain ⟨hnd, hts⟩ :=
      CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := ZMod 2) (n := 3) le_rfl
    obtain ⟨eK⟩ := kleinCommutatorOrthogonalSix (quadPlus 3 (ZMod 2)) hnd (by simp) hts
    exact (oddTranspFactors_statedSL_four card_zmod_two le_rfl).of_mulEquiv
      ((statedOmegaEquivCommutator (coe_quadPlus 3 (ZMod 2))).trans eK).symm
  · refine OddTranspFactors.of_commutator
      ((?_ : OddTranspFactors ↥(StatedOmega (StatedQuadPlus k (ZMod 2)))).of_mulEquiv
        (commutatorOrthogonalPlusEquiv k (ZMod 2)).symm)
    have hM : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus k (ZMod 2))))
        .POmegaPlus k 2 1 :=
      ⟨⟨Nat.prime_two, le_rfl, hk4⟩, ZMod 2, inferInstance, inferInstance, card_zmod_two,
        ⟨MulEquiv.refl _⟩⟩
    exact OddTranspFactors.of_statedProj _ (OddTranspFactors.of_statedClassicalModel hM
      (Or.inr (Or.inl ⟨k, 1, Or.inr (Or.inr (Or.inl (Or.inl ⟨by decide, hM⟩)))⟩)))

theorem oddTranspFactors_orthogonalMinus_zmod_two {k : ℕ} (hk : 2 ≤ k) :
    OddTranspFactors ↥(CFSG.PGLModel.orthogonalMinus k (ZMod 2) 1 1) := by
  have hbc : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
  refine OddTranspFactors.of_commutator
    ((?_ : OddTranspFactors ↥(StatedOmega (StatedQuadMinus (k + 1) (ZMod 2) 1 1))).of_mulEquiv
      (commutatorOrthogonalMinusEquiv k (ZMod 2) 1 1).symm)
  rcases (by omega : k = 2 ∨ 3 ≤ k) with rfl | hk3
  · have hL : LieModel (StatedProj (StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1))) .PSU 4 2 1 :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.kOmega6MinusU4_holds _ 1 (ZMod 2) 1 1
        card_zmod_two hbc ⟨MulEquiv.refl _⟩
    exact OddTranspFactors.of_statedProj _ (OddTranspFactors.of_statedClassicalModel
      (hL.statedClassicalModel (by decide)) (Or.inr (Or.inl ⟨4, 1, Or.inr (Or.inl hL)⟩)))
  · have hM : StatedClassicalModel
        (StatedProj (StatedOmega (StatedQuadMinus (k + 1) (ZMod 2) 1 1)))
        .POmegaMinus (k + 1) 2 1 :=
      ⟨⟨Nat.prime_two, le_rfl, by omega⟩, ZMod 2, inferInstance, inferInstance, card_zmod_two,
        1, 1, hbc, ⟨MulEquiv.refl _⟩⟩
    exact OddTranspFactors.of_statedProj _ (OddTranspFactors.of_statedClassicalModel hM
      (Or.inr (Or.inl ⟨k + 1, 1, Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨by decide, hM⟩))))⟩)))

private theorem quadMinus_reindex {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (k : ℕ)
    (b : Module.Basis (GLAMinusIdx (k - 1)) (ZMod 2) V) (v : V) :
    GLAQMinus (k - 1) (1 : ZMod 2) 1 (b.equivFun v) =
      StatedQuadMinus k (ZMod 2) 1 1
        ((b.reindex (Equiv.sumAssoc (Fin (k - 1)) (Fin (k - 1)) (Fin 2))).equivFun v) := by
  set e : (Fin (k - 1) ⊕ Fin (k - 1)) ⊕ Fin 2 ≃ Fin (k - 1) ⊕ (Fin (k - 1) ⊕ Fin 2) :=
    Equiv.sumAssoc (Fin (k - 1)) (Fin (k - 1)) (Fin 2) with he
  set w : (Fin (k - 1) ⊕ Fin (k - 1)) ⊕ Fin 2 → ZMod 2 := b.equivFun v with hw
  have hw' : (b.reindex e).equivFun v = w ∘ e.symm := by
    funext x
    simp only [hw, Function.comp_apply, Module.Basis.equivFun_apply,
      Module.Basis.repr_reindex_apply]
  rw [hw']
  change (∑ i : Fin (k - 1), w (Sum.inl (Sum.inl i)) * w (Sum.inl (Sum.inr i))) +
      w (Sum.inr 0) ^ 2 + 1 * w (Sum.inr 0) * w (Sum.inr 1) + 1 * w (Sum.inr 1) ^ 2 =
    (∑ i : Fin (k - 1), (w ∘ e.symm) (Sum.inl i) * (w ∘ e.symm) (Sum.inr (Sum.inl i))) +
      (w ∘ e.symm) (Sum.inr (Sum.inr 0)) ^ 2 +
      1 * (w ∘ e.symm) (Sum.inr (Sum.inr 0)) * (w ∘ e.symm) (Sum.inr (Sum.inr 1)) +
      1 * (w ∘ e.symm) (Sum.inr (Sum.inr 1)) ^ 2
  simp only [he, Function.comp_apply, Equiv.sumAssoc_symm_apply_inl,
    Equiv.sumAssoc_symm_apply_inr_inl, Equiv.sumAssoc_symm_apply_inr_inr]

private theorem plus_singular {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (k : ℕ)
    (b : Module.Basis (Fin k ⊕ Fin k) (ZMod 2) V) (Q : QuadraticForm (ZMod 2) V)
    (hb : ∀ v, Q v = GLAQPlus (ZMod 2) k (b.equivFun v)) :
    Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range fun i : Fin k => b (Sum.inl i))) = k ∧
      ∀ u ∈ Submodule.span (ZMod 2) (Set.range fun i : Fin k => b (Sum.inl i)), Q u = 0 := by
  have hli : LinearIndependent (ZMod 2) (fun i : Fin k => b (Sum.inl i)) :=
    b.linearIndependent.comp (fun i : Fin k => Sum.inl i) Sum.inl_injective
  refine ⟨?_, ?_⟩
  · rw [finrank_span_eq_card hli, Fintype.card_fin]
  · intro u hu
    have hsupp : ((b.repr u).support : Set (Fin k ⊕ Fin k)) ⊆
        Set.range (fun i : Fin k => Sum.inl i) := by
      have hu' : u ∈ Submodule.span (ZMod 2)
          (b '' Set.range (fun i : Fin k => Sum.inl i)) := by
        simpa only [Set.range_comp'] using hu
      exact (b.mem_span_image).1 hu'
    have hzero : ∀ j : Fin k, b.equivFun u (Sum.inr j) = 0 := by
      intro j
      have hmem : Sum.inr j ∉ (b.repr u).support := by
        intro hmem
        obtain ⟨i, hi⟩ := hsupp hmem
        exact Sum.inl_ne_inr hi
      simpa only [Module.Basis.equivFun_apply] using Finsupp.notMem_support_iff.mp hmem
    rw [hb u]
    change (∑ i : Fin k, b.equivFun u (Sum.inl i) * b.equivFun u (Sum.inr i)) = 0
    exact Finset.sum_eq_zero fun i _ => by rw [hzero i, mul_zero]

theorem exists_fischerOrth_equiv {m : ℕ} (hm : 2 ≤ m)
    (Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2))
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hex : m = 2 → ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * m) → ZMod 2),
      Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0) :
    (3 ≤ m ∧ ∃ e : ↥(fischerMatrixGroup fun A : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 2) =>
          ∀ x, Q (A *ᵥ x) = Q x) ≃* ↥(CFSG.PGLModel.orthogonalPlus m (ZMod 2)),
        ∀ g, ((((e g : ↥(CFSG.PGLModel.orthogonalPlus m (ZMod 2))) :
            GL (Fin m ⊕ Fin m) (ZMod 2)) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 2)) -
            1).rank =
          (((g : GL (Fin (2 * m)) (ZMod 2)) : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 2)) -
            1).rank) ∨
      ∃ e : ↥(fischerMatrixGroup fun A : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 2) =>
          ∀ x, Q (A *ᵥ x) = Q x) ≃* ↥(CFSG.PGLModel.orthogonalMinus (m - 1) (ZMod 2) 1 1),
        ∀ g, ((((e g : ↥(CFSG.PGLModel.orthogonalMinus (m - 1) (ZMod 2) 1 1)) :
            GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (ZMod 2)) :
              Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
                (ZMod 2)) - 1).rank =
          (((g : GL (Fin (2 * m)) (ZMod 2)) : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 2)) -
            1).rank := by
  have hQ : (QuadraticMap.polarBilin Q).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall hnd
  have hdim : Module.finrank (ZMod 2) (Fin (2 * m) → ZMod 2) = 2 * m :=
    Module.finrank_fin_fun _
  set G := (TauCeti.QuadraticMap.orthogonalGroup Q).comap
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin (2 * m) → ZMod 2)).toMonoidHom
    with hGdef
  have hG : ∀ g : LinearMap.GeneralLinearGroup (ZMod 2) (Fin (2 * m) → ZMod 2),
      g ∈ G ↔ ∀ v, Q ((g : (Fin (2 * m) → ZMod 2) →ₗ[ZMod 2] (Fin (2 * m) → ZMod 2)) v) =
        Q v := by
    intro g
    rw [hGdef, Subgroup.mem_comap, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    rfl
  set e₀ := (G.equivMapOfInjective _
      (mclt_glMatrixEquiv (Pi.basisFun (ZMod 2) (Fin (2 * m)))).injective).trans
    (MulEquiv.subgroupCongr (map_orthogonalGroup_eq_fischerMatrixGroup Q)) with he₀
  have he₀v : ∀ g, ((e₀.symm g : ↥G) :
      LinearMap.GeneralLinearGroup (ZMod 2) (Fin (2 * m) → ZMod 2)) =
      (mclt_glMatrixEquiv (Pi.basisFun (ZMod 2) (Fin (2 * m)))).symm
        (g : GL (Fin (2 * m)) (ZMod 2)) := by
    intro g
    rw [MulEquiv.eq_symm_apply]
    exact congrArg Subtype.val (e₀.apply_symm_apply g)
  rcases mclt_exists_basis_quadratic Q hQ (n := m) (by omega) hdim with ⟨b, hb⟩ | ⟨b, hb⟩
  · left
    have h3 : 3 ≤ m := by
      by_contra h
      have hm2 : m = 2 := by omega
      obtain ⟨hfin, hsing⟩ := plus_singular m b Q hb
      exact hex hm2 ⟨_, by rw [hfin, hm2], hsing⟩
    have hΓ : G.map (mclt_glMatrixEquiv b).toMonoidHom =
        CFSG.PGLModel.orthogonalPlus m (ZMod 2) :=
      mclt_map_glMatrixEquiv_eq_closure (Q := fun v => Q v) b hb hG
    refine ⟨h3, e₀.symm.trans ((G.equivMapOfInjective _ (mclt_glMatrixEquiv b).injective).trans
      (MulEquiv.subgroupCongr hΓ)), fun g => ?_⟩
    have hval : (((e₀.symm.trans ((G.equivMapOfInjective _ (mclt_glMatrixEquiv b).injective).trans
        (MulEquiv.subgroupCongr hΓ)) g : ↥(CFSG.PGLModel.orthogonalPlus m (ZMod 2))) :
          GL (Fin m ⊕ Fin m) (ZMod 2)) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 2)) =
        ((mclt_glMatrixEquiv b ((e₀.symm g : ↥G) :
          LinearMap.GeneralLinearGroup (ZMod 2) (Fin (2 * m) → ZMod 2)) :
            GL (Fin m ⊕ Fin m) (ZMod 2)) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 2)) :=
      rfl
    rw [hval, coe_glMatrixEquiv, he₀v, rank_toMatrix_glMatrixEquiv_symm]
  · right
    let b' : Module.Basis (Fin (m - 1) ⊕ (Fin (m - 1) ⊕ Fin 2)) (ZMod 2)
        (Fin (2 * m) → ZMod 2) :=
      b.reindex (Equiv.sumAssoc (Fin (m - 1)) (Fin (m - 1)) (Fin 2))
    have hb' : ∀ v, Q v = StatedQuadMinus m (ZMod 2) 1 1 (b'.equivFun v) := fun v => by
      rw [hb v]
      exact quadMinus_reindex m b v
    have hΓ : G.map (mclt_glMatrixEquiv b').toMonoidHom =
        CFSG.PGLModel.orthogonalMinus (m - 1) (ZMod 2) 1 1 :=
      mclt_map_glMatrixEquiv_eq_closure (Q := fun v => Q v) b' hb' hG
    refine ⟨e₀.symm.trans ((G.equivMapOfInjective _ (mclt_glMatrixEquiv b').injective).trans
      (MulEquiv.subgroupCongr hΓ)), fun g => ?_⟩
    have hval : (((e₀.symm.trans ((G.equivMapOfInjective _ (mclt_glMatrixEquiv b').injective).trans
        (MulEquiv.subgroupCongr hΓ)) g :
          ↥(CFSG.PGLModel.orthogonalMinus (m - 1) (ZMod 2) 1 1)) :
          GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (ZMod 2)) =
        ((mclt_glMatrixEquiv b' ((e₀.symm g : ↥G) :
          LinearMap.GeneralLinearGroup (ZMod 2) (Fin (2 * m) → ZMod 2)) :
            GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (ZMod 2)) :
              Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
                (ZMod 2)) :=
      rfl
    rw [hval, coe_glMatrixEquiv, he₀v, rank_toMatrix_glMatrixEquiv_symm]

theorem oddTranspFactors_fischerOrth {m : ℕ} (hm : 2 ≤ m)
    (Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2))
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hex : m = 2 → ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * m) → ZMod 2),
      Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0) :
    OddTranspFactors ↥(fischerMatrixGroup fun A : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 2) =>
      ∀ x, Q (A *ᵥ x) = Q x) := by
  rcases (by omega : m = 2 ∨ 3 ≤ m) with rfl | hm3
  ·
    let Q4 : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2) := Q
    obtain ⟨e, -⟩ := CFSG.Fischer.Classification.o4minus2_equiv_s5 (Q := Q4) hnd (hex rfl)
    exact (oddTranspFactors_perm 5).of_mulEquiv e.symm
  · rcases exists_fischerOrth_equiv hm Q hnd hex with ⟨h3, e, -⟩ | ⟨e, -⟩
    · exact (oddTranspFactors_orthogonalPlus_zmod_two h3).of_mulEquiv e.symm
    · exact (oddTranspFactors_orthogonalMinus_zmod_two (k := m - 1) (by omega)).of_mulEquiv
        e.symm

end CFSG.OddTranspositions.PartFour
