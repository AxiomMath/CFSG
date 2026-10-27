module

public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofGlueSwap
public import CFSG.LocalAnalysis.StandardType.GGTypeACompatDiagLin
public import CFSG.LocalAnalysis.StandardType.GGLinearSemisimple
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenLift
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenTypeABlock
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthLift
public import TauCeti.GroupTheory.PGroup
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocleBasic
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityLinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal.SpecialLinear Matrix
open CFSG.SeitzReduction.LinearPilot
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section MatrixAux

variable {m : ℕ} {F : Type} [Field F]

theorem diagAt_pow {p : ℕ} (k : Fin m) (τ : Fˣ) :
    diagAt k τ ^ p = diagAt k (τ ^ p) := by
  funext i
  by_cases hi : i = k
  · subst hi
    simp [diagAt]
  · rw [Pi.pow_apply, diagAt_apply_of_ne hi, diagAt_apply_of_ne hi, one_pow]

theorem diagAt_inv (k : Fin m) (τ : Fˣ) : (diagAt k τ)⁻¹ = diagAt k τ⁻¹ := by
  funext i
  by_cases hi : i = k
  · subst hi
    simp [diagAt]
  · rw [Pi.inv_apply, diagAt_apply_of_ne hi, diagAt_apply_of_ne hi, inv_one]

theorem prod_diagAt (k : Fin m) (τ : Fˣ) : ∏ i, diagAt k τ i = τ := by
  rw [show diagAt k τ = Function.update (1 : Fin m → Fˣ) k τ from rfl,
    Finset.prod_update_of_mem (Finset.mem_univ k)]
  simp

theorem prod_diagAt_mul_diagAt_inv (k l : Fin m) (τ : Fˣ) :
    ∏ i, (diagAt k τ * diagAt l τ⁻¹) i = 1 := by
  simp only [Pi.mul_apply]
  rw [Finset.prod_mul_distrib, prod_diagAt, prod_diagAt, mul_inv_cancel]

theorem diagAt_apply_pow_eq_one {p : ℕ} (k : Fin m) {τ : Fˣ} (hτ : τ ^ p = 1)
    (i : Fin m) : (diagAt k τ i) ^ p = 1 := by
  by_cases hi : i = k
  · subst hi
    rw [diagAt_apply_self, hτ]
  · rw [diagAt_apply_of_ne hi, one_pow]

theorem diagAt_inv_apply_pow_eq_one {p : ℕ} (k : Fin m) {τ : Fˣ} (hτ : τ ^ p = 1)
    (i : Fin m) : (diagAt k τ⁻¹ i) ^ p = 1 :=
  diagAt_apply_pow_eq_one k (by rw [inv_pow, hτ, inv_one]) i

theorem eq_of_mem_center_of_diagonal {u : SpecialLinearGroup (Fin m) F} {t : Fin m → F}
    (hu : (u : Matrix (Fin m) (Fin m) F) = diagonal t)
    (hc : u ∈ Subgroup.center (SpecialLinearGroup (Fin m) F)) (i j : Fin m) : t i = t j := by
  have hscalar := Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hc i
  have h1 : (u : Matrix (Fin m) (Fin m) F) i i =
      (u : Matrix (Fin m) (Fin m) F) j j := by
    have h := congrFun (congrFun hscalar j) j
    simpa [Matrix.scalar_apply] using h
  rw [hu, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at h1
  exact h1

@[expose] noncomputable def slDiagUnits (d : Fin m → Fˣ) (h : ∏ i, d i = 1) :
    SpecialLinearGroup (Fin m) F :=
  ⟨Matrix.diagonal (fun i => (d i : F)), by
    rw [Matrix.det_diagonal, ← Units.coe_prod, h]
    simp⟩

theorem coe_slDiagUnits (d : Fin m → Fˣ) (h : ∏ i, d i = 1) :
    ((slDiagUnits d h : SpecialLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      Matrix.diagonal (fun i => (d i : F)) :=
  rfl

theorem slDiagUnits_inv (d : Fin m → Fˣ) (h : ∏ i, d i = 1) :
    (slDiagUnits d h)⁻¹ = slDiagUnits d⁻¹ (by
      rw [show (∏ i, (d⁻¹) i) = (∏ i, d i)⁻¹ by
        simp only [Pi.inv_apply, Finset.prod_inv_distrib], h, inv_one]) := by
  refine inv_eq_of_mul_eq_one_right ?_
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_slDiagUnits, coe_slDiagUnits,
    Matrix.SpecialLinearGroup.coe_one, Matrix.diagonal_mul_diagonal]
  have hfun : (fun i => (d i : F) * ((d⁻¹ : Fin m → Fˣ) i : F)) = (1 : Fin m → F) := by
    funext i
    simp
  rw [hfun]
  exact Matrix.diagonal_one

theorem mul_slDiagUnits_eq_ggDiagConj (d : Fin m → Fˣ) (h : ∏ i, d i = 1)
    (s : SpecialLinearGroup (Fin m) F) :
    slDiagUnits d h * s * (slDiagUnits d h)⁻¹ = ggDiagConj d s := by
  rw [slDiagUnits_inv]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_slDiagUnits, coe_ggDiagConj,
    Pi.inv_apply]

theorem ggActsVec_slDiagUnits {X : Type*} [Group X]
    {φ : SpecialLinearGroup (Fin m) F →* X} (d : Fin m → Fˣ) (h : ∏ i, d i = 1) :
    GGActsVec φ (φ (slDiagUnits d h)) d := by
  intro s
  rw [← map_mul, ← map_inv, ← map_mul, mul_slDiagUnits_eq_ggDiagConj]

theorem commute_slDiagUnits (d d' : Fin m → Fˣ) (h : ∏ i, d i = 1)
    (h' : ∏ i, d' i = 1) :
    slDiagUnits d h * slDiagUnits d' h' = slDiagUnits d' h' * slDiagUnits d h := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_slDiagUnits,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem slDiagUnits_pow_eq_one {p : ℕ} (d : Fin m → Fˣ) (h : ∏ i, d i = 1)
    (hd : ∀ i, d i ^ p = 1) : slDiagUnits d h ^ p = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_slDiagUnits, Matrix.diagonal_pow,
    Matrix.SpecialLinearGroup.coe_one]
  have hfun : ((fun i => (d i : F)) ^ p) = (1 : Fin m → F) := by
    funext i
    rw [Pi.pow_apply, ← Units.val_pow_eq_pow_val, hd i]
    simp
  rw [hfun]
  exact Matrix.diagonal_one

private theorem ggDiagConj_eq_conjSL_diagGL' {m : ℕ} (d : Fin (m + 1) → Fˣ)
    (s : SpecialLinearGroup (Fin (m + 1)) F) :
    ggDiagConj d s = InnerDiagA.conjSL (InnerDiagA.diagGL d) s := by
  apply Subtype.ext
  rw [coe_ggDiagConj, InnerDiagA.coe_conjSL, InnerDiagA.coe_diagGL,
    InnerDiagA.coe_diagGL_inv]

end MatrixAux

private theorem exists_notMem_pair {m : ℕ} (hm : 3 ≤ m) (a b : Fin m) :
    ∃ k : Fin m, k ≠ a ∧ k ≠ b := by
  have hcard : ({a, b} : Finset (Fin m)).card < (Finset.univ : Finset (Fin m)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt Finset.card_le_two (by omega)
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨k, by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hk⟩

private theorem exists_notMem_three {m : ℕ} (hm : 4 ≤ m) (a b c : Fin m) :
    ∃ k : Fin m, k ≠ a ∧ k ≠ b ∧ k ≠ c := by
  have hcard : ({a, b, c} : Finset (Fin m)).card <
      (Finset.univ : Finset (Fin m)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt Finset.card_le_three (by omega)
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨k, by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hk⟩

theorem slPerm_mem_blockSpecialLinear_pair {F : Type} [Field F] {m : ℕ} (h2 : (2 : F) = 0)
    {a b : Fin m} (hab : a ≠ b) :
    slPerm h2 (Equiv.swap a b) ∈ blockSpecialLinear ({a, b} : Finset (Fin m)) := by
  rw [mem_blockSpecialLinear]
  intro i j hij
  rw [coe_slPerm, signedPerm_apply, Pi.one_apply]
  by_cases hi : i ∈ ({a, b} : Finset (Fin m))
  · have hj : j ∉ ({a, b} : Finset (Fin m)) := by
      rcases hij with h | h
      · exact absurd hi h
      · exact h
    have hπj : Equiv.swap a b j = j := by
      rw [Equiv.swap_apply_of_ne_of_ne]
      · exact fun h => hj (by rw [h]; simp)
      · exact fun h => hj (by rw [h]; simp)
    rw [hπj]
    by_cases hij' : i = j
    · subst hij'
      rw [if_pos rfl, Matrix.one_apply_eq]
    · rw [if_neg hij', Matrix.one_apply_ne hij']
  · by_cases hj : j ∈ ({a, b} : Finset (Fin m))
    · have hπj : Equiv.swap a b j ∈ ({a, b} : Finset (Fin m)) := by
        rcases Finset.mem_insert.mp hj with rfl | hj'
        · simp
        · rw [Finset.mem_singleton.mp hj']
          simp
      have hne1 : i ≠ Equiv.swap a b j := fun h => hi (h ▸ hπj)
      have hne2 : i ≠ j := fun h => hi (h ▸ hj)
      rw [if_neg hne1, Matrix.one_apply_ne hne2]
    · have hπj : Equiv.swap a b j = j := by
        rw [Equiv.swap_apply_of_ne_of_ne]
        · exact fun h => hj (by rw [h]; simp)
        · exact fun h => hj (by rw [h]; simp)
      rw [hπj]
      by_cases hij' : i = j
      · subst hij'
        rw [if_pos rfl, Matrix.one_apply_eq]
      · rw [if_neg hij', Matrix.one_apply_ne hij']

theorem blockSpecialLinear_eq_coordBlockSL {F : Type} [Field F] {m : ℕ}
    (I : Finset (Fin m)) :
    CFSG.RankThree.CALinearPlane.coordBlockSL F I = blockSpecialLinear I := by
  ext A
  simp only [CFSG.RankThree.CALinearPlane.mem_coordBlockSL_iff, mem_blockSpecialLinear,
    Matrix.one_apply]

section RootOfUnity

variable {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G} {n : ℕ} {F : Type} [Field F]
  {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) F →* G} {x y : G}

theorem GGFarCtx.exists_rootOfUnity (hC : GGFarCtx p Bs φ₁ φ₂ x y) :
    ∃ τ : Fˣ, τ ≠ 1 ∧ τ ^ p = 1 := by
  have hn : 3 ≤ n := hC.three_le
  obtain ⟨τ, hτ, hvecs⟩ := hC.exists_vecs₁
  let i0 : Fin (n + 1) := ⟨0, by omega⟩
  obtain ⟨z, hz, hzvec⟩ := hvecs i0
  have hvec : GGActsVec φ₁ (z ^ p) ((diagAt i0 τ) ^ p) := GGActsDiag.pow hzvec p
  rw [hC.exp z hz] at hvec
  have hone : GGActsVec φ₁ (1 : G) 1 :=
    GGActsVec.one_of_commute (φ := φ₁) (g := (1 : G)) (fun s => by simp)
  have he : GGVecEq ((diagAt i0 τ) ^ p) 1 := GGActsVec.vecEq hC.lifts.ker₁ hvec hone
  rw [diagAt_pow] at he
  exact ⟨τ, hτ, (ggVecEq_diagAt_one_iff (m := n + 1) (by omega) i0 (τ ^ p)).mp he⟩

theorem GGFarCtx.natCard_ne_two [Finite F] (hC : GGFarCtx p Bs φ₁ φ₂ x y) :
    Nat.card F ≠ 2 := by
  obtain ⟨τ, hτ, -⟩ := hC.exists_rootOfUnity
  intro h2
  haveI : Finite Fˣ := inferInstance
  have hcard : Nat.card Fˣ = 1 := by
    rw [Nat.card_units, h2]
  have hsub : Subsingleton Fˣ :=
    (Finite.card_le_one_iff_subsingleton (α := Fˣ)).mp (by omega)
  exact hτ (Subsingleton.elim τ 1)

private theorem exists_notMemPair_of_three {n : ℕ} (hn : 3 ≤ n) (a b : Fin (n + 1)) :
    ∃ k : Fin (n + 1), k ≠ a ∧ k ≠ b :=
  exists_notMem_pair (by omega) a b

theorem GGFarCtx.permAut₁_swap_fix_imp_lamHom [Finite F] (hC : GGFarCtx p Bs φ₁ φ₂ x y)
    {a b : Fin (n + 1)} (hab : a ≠ b) {u : ↥Bs}
    (hfix : hC.permAut₁ (Equiv.swap a b) u = u) : hC.lamHom a b u = 1 := by
  classical
  have hn : 3 ≤ n := hC.three_le
  obtain ⟨h, ha⟩ := hC.lifts.diag₁ (u : G) u.2
  have hconj : φ₁ (slPerm hC.two (Equiv.swap a b)) * (u : G) *
      (φ₁ (slPerm hC.two (Equiv.swap a b)))⁻¹ = (u : G) := by
    have h1 := hC.permAut₁_apply (Equiv.swap a b) u
    rw [hfix] at h1
    exact h1.symm
  have hconjvec : GGActsVec φ₁ (u : G) (h ∘ (Equiv.swap a b).symm) := by
    have h2 := GGActsVec.conj_perm hC.two (φ := φ₁) ha (Equiv.swap a b)
    rwa [hconj] at h2
  have e : GGVecEq h (h ∘ (Equiv.swap a b).symm) :=
    GGActsVec.vecEq hC.lifts.ker₁ ha hconjvec
  obtain ⟨k, hka, hkb⟩ := exists_notMemPair_of_three hn a b
  have hsymma : (Equiv.swap a b).symm a = b := by
    rw [Equiv.symm_apply_eq]
    exact (Equiv.swap_apply_right a b).symm
  have hsymmk : (Equiv.swap a b).symm k = k := by
    rw [Equiv.symm_apply_eq]
    exact (Equiv.swap_apply_of_ne_of_ne hka hkb).symm
  have hb : h b = h a := by
    have h1 : h a * (h b)⁻¹ = 1 := by
      have h' := e a k
      rw [Function.comp_apply, hsymma, Function.comp_apply, hsymmk] at h'
      simpa using h'
    exact (mul_inv_eq_one.mp h1).symm
  rw [hC.lamHom_apply, hC.lamFun_eq a b ha, hb]
  exact mul_inv_cancel (h a)

theorem GGFarCtx.permAut₁_swap_fix_iff_ker [Finite ↥Bs] [Finite F]
    (hC : GGFarCtx p Bs φ₁ φ₂ x y) {a b : Fin (n + 1)} (hab : a ≠ b) (u : ↥Bs) :
    hC.permAut₁ (Equiv.swap a b) u = u ↔ hC.lamHom a b u = 1 := by
  haveI : Finite ↥(hC.lamHom a b).ker := Subtype.finite
  haveI : Finite ↥(ggFix (hC.permAut₁ (Equiv.swap a b))) := Subtype.finite
  constructor
  · exact hC.permAut₁_swap_fix_imp_lamHom hab
  · intro hlam
    have hle : ggFix (hC.permAut₁ (Equiv.swap a b)) ≤ (hC.lamHom a b).ker :=
      fun v hv => hC.permAut₁_swap_fix_imp_lamHom hab hv
    have hcardFix : Nat.card (ggFix (hC.permAut₁ (Equiv.swap a b))) * p = Nat.card ↥Bs :=
      (hC.permAut₁_swap_isReflection hab).2
    have hcardKer : Nat.card (hC.lamHom a b).ker * p = Nat.card ↥Bs := by
      have hci := Subgroup.card_mul_index (hC.lamHom a b).ker
      rw [Subgroup.index_ker, hC.natCard_range_lamHom hab] at hci
      exact hci
    have heqcard : Nat.card (ggFix (hC.permAut₁ (Equiv.swap a b))) =
        Nat.card (hC.lamHom a b).ker :=
      Nat.eq_of_mul_eq_mul_right hC.prime.pos (hcardFix.trans hcardKer.symm)
    have heq : ggFix (hC.permAut₁ (Equiv.swap a b)) = (hC.lamHom a b).ker :=
      Subgroup.eq_of_le_of_card_ge hle heqcard.ge
    have : u ∈ (hC.lamHom a b).ker := MonoidHom.mem_ker.mpr hlam
    rwa [← heq] at this

theorem GGFarCtx.apply_eq_of_mem_ggFixG [Finite F] (hC : GGFarCtx p Bs φ₁ φ₂ x y)
    {a b : Fin (n + 1)} (hab : a ≠ b) {c : G}
    (hc : c ∈ ggFixG Bs (hC.permAut₁ (Equiv.swap a b)))
    {h : Fin (n + 1) → Fˣ} (hv : GGActsVec φ₁ c h) : h a = h b := by
  obtain ⟨u, hu, rfl⟩ := hc
  have hlam : hC.lamHom a b u = 1 := hC.permAut₁_swap_fix_imp_lamHom hab hu
  rw [hC.lamHom_apply] at hlam
  have h1 := hC.lamFun_eq a b hv
  rw [hlam] at h1
  exact (mul_inv_eq_one.mp h1.symm).symm

theorem ggDiagConj_eq_self_of_const_on_block {F : Type} [Field F] {m : ℕ}
    {I : Finset (Fin m)} {u : SpecialLinearGroup (Fin m) F} (hu : u ∈ blockSpecialLinear I)
    {h : Fin m → Fˣ} (hconst : ∀ i ∈ I, ∀ j ∈ I, h i = h j) :
    ggDiagConj h u = u := by
  apply Subtype.ext
  ext a b
  rw [ggDiagConj_apply]
  by_cases hab : a ∈ I ∧ b ∈ I
  · rw [hconst a hab.1 b hab.2, Units.val_inv_eq_inv_val]
    rw [mul_comm ((h b : Fˣ) : F), mul_assoc, mul_inv_cancel₀ (h b).ne_zero, mul_one]
  · rw [(mem_blockSpecialLinear.mp hu) a b (by tauto)]
    by_cases hab' : a = b
    · subst hab'
      rw [Matrix.one_apply_eq]
      simp
    · rw [Matrix.one_apply_ne hab']
      simp

theorem GGFarCtx.block_le_centralizer_ggFixG [Finite F] (hC : GGFarCtx p Bs φ₁ φ₂ x y)
    {a b : Fin (n + 1)} (hab : a ≠ b) :
    (blockSpecialLinear ({a, b} : Finset (Fin (n + 1)))).map φ₁ ≤
      Subgroup.centralizer (ggFixG Bs (hC.permAut₁ (Equiv.swap a b)) : Set G) := by
  intro g hg
  obtain ⟨u, hu, rfl⟩ := hg
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  obtain ⟨x, hx, rfl⟩ := hc
  obtain ⟨h, hv⟩ := hC.lifts.diag₁ (x : G) x.2
  have hxE : (x : G) ∈ ggFixG Bs (hC.permAut₁ (Equiv.swap a b)) :=
    Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hconst : ∀ i ∈ ({a, b} : Finset (Fin (n + 1))),
      ∀ j ∈ ({a, b} : Finset (Fin (n + 1))), h i = h j := by
    intro i hi j hj
    rw [Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · rfl
    · exact hC.apply_eq_of_mem_ggFixG hab hxE hv
    · exact (hC.apply_eq_of_mem_ggFixG hab hxE hv).symm
    · rfl
  have hdiag : ggDiagConj h u = u := ggDiagConj_eq_self_of_const_on_block hu hconst
  have hconj : (x : G) * φ₁ u * (x : G)⁻¹ = φ₁ u := by
    rw [hv u, hdiag]
  calc (x : G) * φ₁ u = (x * φ₁ u * (x : G)⁻¹) * (x : G) := by group
    _ = φ₁ u * (x : G) := by rw [hconj]

theorem GGFarCtx.exists_mem_ggFixG_vec_ne [Finite ↥Bs] [Finite F]
    (hC : GGFarCtx p Bs φ₁ φ₂ x y)
    {a b : Fin (n + 1)} (hab : a ≠ b) {j : Fin (n + 1)} (hja : j ≠ a) (hjb : j ≠ b) :
    ∃ c : G, c ∈ ggFixG Bs (hC.permAut₁ (Equiv.swap a b)) ∧
      ∃ d : Fin (n + 1) → Fˣ, GGActsVec φ₁ c d ∧ d j ≠ d a := by
  classical
  have hn : 3 ≤ n := hC.three_le
  obtain ⟨τ, hτ, hvecs⟩ := hC.exists_vecs₁
  obtain ⟨j', hj'a, hj'b, hj'j⟩ := exists_notMem_three (by omega) a b j
  obtain ⟨zj, hzj, hvj⟩ := hvecs j
  obtain ⟨zj', hzj', hvj'⟩ := hvecs j'
  let d : Fin (n + 1) → Fˣ := diagAt j τ * diagAt j' τ⁻¹
  have hvj' : GGActsVec φ₁ (zj')⁻¹ (diagAt j' τ⁻¹) := by
    have h := GGActsVec.inv hvj'
    rwa [diagAt_inv] at h
  have hv : GGActsVec φ₁ (zj * (zj')⁻¹) d := GGActsVec.mul hvj hvj'
  have hmem : zj * (zj')⁻¹ ∈ Bs := Bs.mul_mem hzj (Bs.inv_mem hzj')
  have hd_a : d a = 1 := by
    simp only [d, Pi.mul_apply, diagAt_apply_of_ne (k := j) (l := a) (Ne.symm hja),
      diagAt_apply_of_ne (k := j') (l := a) (Ne.symm hj'a), mul_one]
  have hd_b : d b = 1 := by
    simp only [d, Pi.mul_apply, diagAt_apply_of_ne (k := j) (l := b) (Ne.symm hjb),
      diagAt_apply_of_ne (k := j') (l := b) (Ne.symm hj'b), mul_one]
  have hd_j : d j = τ := by
    simp only [d, Pi.mul_apply, diagAt_apply_self,
      diagAt_apply_of_ne (k := j') (l := j) hj'j.symm, mul_one]
  have hne : d j ≠ d a := by
    rw [hd_j, hd_a]
    exact hτ
  refine ⟨zj * (zj')⁻¹, ?_, d, hv, hne⟩
  refine Subgroup.mem_map.mpr ⟨⟨zj * (zj')⁻¹, hmem⟩, ?_, rfl⟩
  have hlam : hC.lamHom a b ⟨zj * (zj')⁻¹, hmem⟩ = 1 := by
    rw [hC.lamHom_apply, hC.lamFun_eq a b hv, hd_b, hd_a, inv_one, mul_one]
  exact (hC.permAut₁_swap_fix_iff_ker hab ⟨zj * (zj')⁻¹, hmem⟩).mpr hlam

theorem GGFarCtx.isComponentOf_block_fix [Finite G] [Finite F] (hC : GGFarCtx p Bs φ₁ φ₂ x y)
    {a b : Fin (n + 1)} (hab : a ≠ b) :
    CFSG.Assembly.IsComponentOf
      ((blockSpecialLinear ({a, b} : Finset (Fin (n + 1)))).map φ₁)
      (φ₁.range ⊓ Subgroup.centralizer
        (ggFixG Bs (hC.permAut₁ (Equiv.swap a b)) : Set G)) := by
  classical
  have hn : 3 ≤ n := hC.three_le
  haveI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero hC.two
  let Et : Subgroup G := ggFixG Bs (hC.permAut₁ (Equiv.swap a b))
  have hEtBs : ∀ c : ↥Et, (c : G) ∈ Bs := fun c =>
    Subgroup.map_subtype_le (ggFix (hC.permAut₁ (Equiv.swap a b))) c.2
  let dvec : ↥Et → Fin (n + 1) → Fˣ := fun c =>
    Classical.choose (hC.lifts.diag₁ (c : G) (hEtBs c))
  have hdvec : ∀ c : ↥Et, GGActsVec φ₁ (c : G) (dvec c) := fun c =>
    Classical.choose_spec (hC.lifts.diag₁ (c : G) (hEtBs c))
  have hb : ∀ c : ↥Et, ((c : G), InnerDiagA.diagGL (dvec c)) ∈
      LinFusion.ggInducedPairs φ₁ := by
    intro c
    rw [LinFusion.mem_ggInducedPairs]
    intro u
    rw [hdvec c u, ggDiagConj_eq_conjSL_diagGL' (m := n)]
  have hb_mem : b ∈ LinSemisimple.eigClass dvec a := by
    rw [LinSemisimple.mem_eigClass]
    intro c
    exact (hC.apply_eq_of_mem_ggFixG hab c.2 (hdvec c)).symm
  have hsep : ∀ j : Fin (n + 1), j ≠ a → j ≠ b →
      j ∉ LinSemisimple.eigClass dvec a := by
    intro j hja hjb
    rw [LinSemisimple.mem_eigClass]
    push Not
    obtain ⟨c, hc, d, hv, hne⟩ := hC.exists_mem_ggFixG_vec_ne hab hja hjb
    refine ⟨⟨c, hc⟩, ?_⟩
    have hvcan : GGActsVec φ₁ c (dvec ⟨c, hc⟩) := hdvec ⟨c, hc⟩
    have he := GGActsVec.vecEq hC.lifts.ker₁ hvcan hv
    intro heq
    apply hne
    have h := he j a
    rw [heq] at h
    exact inv_injective (mul_left_cancel h)
  have heig : LinSemisimple.eigClass dvec a =
      ({a, b} : Finset (Fin (n + 1))) := by
    ext z
    rw [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hz
      by_contra h
      push Not at h
      exact hsep z h.1 h.2 hz
    · rintro (hz | hz)
      · rw [hz]
        exact LinSemisimple.self_mem_eigClass dvec a
      · rw [hz]
        exact hb_mem
  have hcard : 2 ≤ (LinSemisimple.eigClass dvec a).card := by
    rw [heig, Finset.card_pair hab]
  have hcard' : (LinSemisimple.eigClass dvec a).card ≠ 2 ∨ Nat.card F ≠ 2 :=
    Or.inr hC.natCard_ne_two
  have h := (LinSemisimple.isComponentOf_iff_exists_eq_map_blockSpecialLinear
    (m := n) (F := F) (G := G) (ψ := φ₁) (ι := ↥Et) (d := dvec)
    (b := fun c : ↥Et => (c : G)) hC.lifts.ker₁ hb).mpr
    ⟨a, hcard, hcard', rfl⟩
  simpa [Et, heig, Subtype.range_val] using h

theorem GGFarCtx.realize_permAut₁_swap [Finite G] [Finite F]
    (hC : GGFarCtx p Bs φ₁ φ₂ x y)
    (hxN : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (φ₁.range : Set G))
    {a b : Fin (n + 1)} (hab : a ≠ b) :
    hC.permAut₁ (Equiv.swap a b) ∈
      ggInduced ((blockSpecialLinear ({a, b} : Finset (Fin (n + 1)))).map φ₁) Bs ∧
    (blockSpecialLinear ({a, b} : Finset (Fin (n + 1)))).map φ₁ ≤
      Subgroup.centralizer (ggFixG Bs (hC.permAut₁ (Equiv.swap a b)) : Set G) ∧
    IsPComponent p (((blockSpecialLinear ({a, b} : Finset (Fin (n + 1)))).map φ₁).subgroupOf
      (Subgroup.centralizer (ggFixG Bs (hC.permAut₁ (Equiv.swap a b)) : Set G))) ∧
    p ∣ Nat.card ((blockSpecialLinear ({a, b} : Finset (Fin (n + 1)))).map φ₁) := by
  classical
  have hn : 3 ≤ n := hC.three_le
  haveI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero hC.two
  haveI : Fact p.Prime := ⟨hC.prime⟩
  let t : MulAut ↥Bs := hC.permAut₁ (Equiv.swap a b)
  let Et : Subgroup G := ggFixG Bs t
  let C : Subgroup G := Subgroup.centralizer (Et : Set G)
  let Jt : Subgroup G := (blockSpecialLinear ({a, b} : Finset (Fin (n + 1)))).map φ₁
  have hreal : t ∈ ggInduced Jt Bs := by
    refine ⟨φ₁ (slPerm hC.two (Equiv.swap a b)), ?_, hC.perm_mem_normalizer₁ _, ?_⟩
    · exact Subgroup.mem_map.mpr
        ⟨slPerm hC.two (Equiv.swap a b), slPerm_mem_blockSpecialLinear_pair hC.two hab, rfl⟩
    · intro u
      exact hC.permAut₁_apply (Equiv.swap a b) u
  have hle : Jt ≤ C := hC.block_le_centralizer_ggFixG hab
  have hcomp : CFSG.Assembly.IsComponentOf Jt (φ₁.range ⊓ C) :=
    hC.isComponentOf_block_fix hab
  have hxEt : x ∈ Et := by
    refine Subgroup.mem_map.mpr ⟨⟨x, hC.x_mem⟩, ?_, rfl⟩
    exact hC.permAut₁_fix_x (Equiv.swap a b)
  have hCx : C ≤ Subgroup.normalizer (φ₁.range : Set G) :=
    (Subgroup.centralizer_le (s := ({x} : Set G)) (t := (Et : Set G))
      (fun z hz => by
        have hz' : z = x := Set.mem_singleton_iff.mp hz
        subst hz'
        exact hxEt)).trans hxN
  have hnormal : ((φ₁.range ⊓ C).subgroupOf C).Normal := by
    constructor
    intro y hy g
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hCx g.2) y).mp hy.1, ?_⟩
    exact C.mul_mem (C.mul_mem g.2 hy.2) (C.inv_mem g.2)
  have hcompC : CFSG.Assembly.IsComponentOf Jt C :=
    CFSG.ComponentClassification.OddClassSelector.isComponentOf_of_normal_le
      hcomp inf_le_right hnormal
  have hpJt : p ∣ Nat.card Jt := by
    obtain ⟨τ, hτ, hτp⟩ := hC.exists_rootOfUnity
    have hord : orderOf τ = p := orderOf_eq_prime hτp hτ
    have hdvd : p ∣ Nat.card Fˣ := by
      rw [← hord]
      exact orderOf_dvd_natCard τ
    have hpK : p ∣ Nat.card F - 1 := by
      rwa [Nat.card_units] at hdvd
    have hφker : ∀ g, φ₁ g = 1 → g ∈ scalars (n + 1) F := by
      intro g hg
      rw [scalars_eq_center]
      exact hC.lifts.ker₁ (MonoidHom.mem_ker.mpr hg)
    have hdvd' := CFSG.StandardType.TypeA.dvd_card_coordBlockSL_pair
      (p := p) (K := F) (d := n + 1) hC.prime hpK (by omega) hφker hab
    rwa [blockSpecialLinear_eq_coordBlockSL] at hdvd'
  have hpc : IsPComponent p (Jt.subgroupOf C) :=
    isPComponent_subgroupOf_of_isComponentOf_of_dvd hcompC hpJt
  exact ⟨hreal, hle, hpc, hpJt⟩

theorem GGFarCtx.exists_noncyclic_pSubgroup (hC : GGFarCtx p Bs φ₁ φ₂ x y) :
    ∃ S : Subgroup G, S ≤ φ₁.range ∧ IsPGroup p S ∧ ¬ IsCyclic S := by
  classical
  have hn : 3 ≤ n := hC.three_le
  haveI : Fact p.Prime := ⟨hC.prime⟩
  obtain ⟨τ, hτ, hτp⟩ := hC.exists_rootOfUnity
  let i0 : Fin (n + 1) := ⟨0, by omega⟩
  let i1 : Fin (n + 1) := ⟨1, by omega⟩
  let i2 : Fin (n + 1) := ⟨2, by omega⟩
  let i3 : Fin (n + 1) := ⟨3, by omega⟩
  have h01 : i0 ≠ i1 := by
    intro h
    exact absurd (congrArg Fin.val h) (by simp [i0, i1])
  have h02 : i0 ≠ i2 := by
    intro h
    exact absurd (congrArg Fin.val h) (by simp [i0, i2])
  have h03 : i0 ≠ i3 := by
    intro h
    exact absurd (congrArg Fin.val h) (by simp [i0, i3])
  have h12 : i1 ≠ i2 := by
    intro h
    exact absurd (congrArg Fin.val h) (by simp [i1, i2])
  have h13 : i1 ≠ i3 := by
    intro h
    exact absurd (congrArg Fin.val h) (by simp [i1, i3])
  have h23 : i2 ≠ i3 := by
    intro h
    exact absurd (congrArg Fin.val h) (by simp [i2, i3])
  let d₁ : Fin (n + 1) → Fˣ := diagAt i0 τ * diagAt i1 τ⁻¹
  let d₂ : Fin (n + 1) → Fˣ := diagAt i1 τ * diagAt i2 τ⁻¹
  have hprod₁ : ∏ i, d₁ i = 1 := prod_diagAt_mul_diagAt_inv i0 i1 τ
  have hprod₂ : ∏ i, d₂ i = 1 := prod_diagAt_mul_diagAt_inv i1 i2 τ
  let u₁ : G := φ₁ (slDiagUnits d₁ hprod₁)
  let u₂ : G := φ₁ (slDiagUnits d₂ hprod₂)
  have hv₁ : GGActsVec φ₁ u₁ d₁ := ggActsVec_slDiagUnits d₁ hprod₁
  have hv₂ : GGActsVec φ₁ u₂ d₂ := ggActsVec_slDiagUnits d₂ hprod₂
  have hd₁_0 : d₁ i0 = τ := by
    simp only [d₁, Pi.mul_apply, diagAt_apply_self,
      diagAt_apply_of_ne (k := i1) (l := i0) h01, mul_one]
  have hd₁_1 : d₁ i1 = τ⁻¹ := by
    simp only [d₁, Pi.mul_apply, diagAt_apply_of_ne (k := i0) (l := i1) h01.symm,
      diagAt_apply_self, one_mul]
  have hd₁_3 : d₁ i3 = 1 := by
    simp only [d₁, Pi.mul_apply, diagAt_apply_of_ne (k := i0) (l := i3) h03.symm,
      diagAt_apply_of_ne (k := i1) (l := i3) h13.symm, mul_one]
  have hd₂_0 : d₂ i0 = 1 := by
    simp only [d₂, Pi.mul_apply, diagAt_apply_of_ne (k := i1) (l := i0) h01,
      diagAt_apply_of_ne (k := i2) (l := i0) h02, mul_one]
  have hd₂_1 : d₂ i1 = τ := by
    simp only [d₂, Pi.mul_apply, diagAt_apply_self,
      diagAt_apply_of_ne (k := i2) (l := i1) h12, mul_one]
  have hd₂_3 : d₂ i3 = 1 := by
    simp only [d₂, Pi.mul_apply, diagAt_apply_of_ne (k := i1) (l := i3) h13.symm,
      diagAt_apply_of_ne (k := i2) (l := i3) h23.symm, mul_one]
  have hd₁p : ∀ i, d₁ i ^ p = 1 := by
    intro i
    rw [show d₁ i = (diagAt i0 τ * diagAt i1 τ⁻¹) i from rfl, Pi.mul_apply, mul_pow,
      diagAt_apply_pow_eq_one i0 hτp i, diagAt_inv_apply_pow_eq_one i1 hτp i, mul_one]
  have hd₂p : ∀ i, d₂ i ^ p = 1 := by
    intro i
    rw [show d₂ i = (diagAt i1 τ * diagAt i2 τ⁻¹) i from rfl, Pi.mul_apply, mul_pow,
      diagAt_apply_pow_eq_one i1 hτp i, diagAt_inv_apply_pow_eq_one i2 hτp i, mul_one]
  have hu₁p : u₁ ^ p = 1 := by
    show φ₁ (slDiagUnits d₁ hprod₁) ^ p = 1
    rw [← map_pow, slDiagUnits_pow_eq_one d₁ hprod₁ hd₁p, map_one]
  have hu₂p : u₂ ^ p = 1 := by
    show φ₁ (slDiagUnits d₂ hprod₂) ^ p = 1
    rw [← map_pow, slDiagUnits_pow_eq_one d₂ hprod₂ hd₂p, map_one]
  have hu₁ne : u₁ ≠ 1 := by
    intro h1
    have hcenter : slDiagUnits d₁ hprod₁ ∈
        Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F) :=
      hC.lifts.ker₁ (MonoidHom.mem_ker.mpr h1)
    have hentry := eq_of_mem_center_of_diagonal
      (u := slDiagUnits d₁ hprod₁) (t := fun i => ((d₁ i : Fˣ) : F))
      (coe_slDiagUnits d₁ hprod₁) hcenter i0 i3
    rw [hd₁_0, hd₁_3] at hentry
    exact hτ (Units.ext (by simpa using hentry))
  have hu₂ne : u₂ ≠ 1 := by
    intro h1
    have hcenter : slDiagUnits d₂ hprod₂ ∈
        Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F) :=
      hC.lifts.ker₁ (MonoidHom.mem_ker.mpr h1)
    have hentry := eq_of_mem_center_of_diagonal
      (u := slDiagUnits d₂ hprod₂) (t := fun i => ((d₂ i : Fˣ) : F))
      (coe_slDiagUnits d₂ hprod₂) hcenter i2 i3
    rw [hd₂_3] at hentry
    have h2 : d₂ i2 = τ⁻¹ := by
      simp only [d₂, Pi.mul_apply, diagAt_apply_of_ne (k := i1) (l := i2) h12.symm,
        diagAt_apply_self, one_mul]
    rw [h2] at hentry
    exact hτ (by
      have : τ⁻¹ = 1 := Units.ext (by simpa using hentry)
      exact inv_eq_one.mp this)
  have hnot : u₂ ∉ Subgroup.zpowers u₁ := by
    intro hmem
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hvpow : GGActsVec φ₁ (u₁ ^ m) (d₁ ^ m) := GGActsVec.zpow hv₁ m
    rw [hm] at hvpow
    have he := GGActsVec.vecEq hC.lifts.ker₁ hv₂ hvpow
    have h03 := he i0 i3
    rw [Pi.pow_apply, Pi.pow_apply, hd₁_0, hd₁_3, hd₂_0, hd₂_3] at h03
    have hτm : τ ^ m = 1 := by
      have h1 : (τ ^ m)⁻¹ = 1 := by simpa using h03
      exact inv_eq_one.mp h1
    have h13' := he i1 i3
    rw [Pi.pow_apply, Pi.pow_apply, hd₁_1, hd₁_3, hd₂_1, hd₂_3] at h13'
    have h2 : ((τ⁻¹ : Fˣ) ^ m)⁻¹ = τ ^ m := by
      rw [_root_.inv_zpow, inv_inv]
    exact hτ (by simpa [h2, hτm] using h13')
  have hcomm : Commute u₁ u₂ := by
    show u₁ * u₂ = u₂ * u₁
    show φ₁ (slDiagUnits d₁ hprod₁) * φ₁ (slDiagUnits d₂ hprod₂) =
      φ₁ (slDiagUnits d₂ hprod₂) * φ₁ (slDiagUnits d₁ hprod₁)
    rw [← map_mul, ← map_mul, commute_slDiagUnits]
  have hord₁ : orderOf u₁ = p := orderOf_eq_prime hu₁p hu₁ne
  have hord₂ : orderOf u₂ = p := orderOf_eq_prime hu₂p hu₂ne
  let H : Subgroup G := Subgroup.zpowers u₁
  let K : Subgroup G := Subgroup.zpowers u₂
  have hHp : IsPGroup p ↥H := by
    refine IsPGroup.of_card (n := 1) ?_
    show Nat.card ↥H = p ^ 1
    rw [show Nat.card ↥H = Nat.card (Subgroup.zpowers u₁) from rfl, Nat.card_zpowers,
      hord₁, pow_one]
  have hKp : IsPGroup p ↥K := by
    refine IsPGroup.of_card (n := 1) ?_
    show Nat.card ↥K = p ^ 1
    rw [show Nat.card ↥K = Nat.card (Subgroup.zpowers u₂) from rfl, Nat.card_zpowers,
      hord₂, pow_one]
  have hcommHK : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow hcomm m n).eq
  let f : ↥H × ↥K →* G :=
    { toFun := fun p => (p.1 : G) * (p.2 : G)
      map_one' := by simp
      map_mul' := by
        intro p q
        show ((p.1 * q.1 : ↥H) : G) * ((p.2 * q.2 : ↥K) : G) =
          ((p.1 : ↥H) : G) * ((p.2 : ↥K) : G) *
            (((q.1 : ↥H) : G) * ((q.2 : ↥K) : G))
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        calc ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G))
            = (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by group
          _ = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by
                rw [hcommHK (q.1 : G) q.1.2 (p.2 : G) p.2.2]
          _ = ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G)) := by group }
  let S : Subgroup G := f.range
  have hu₁S : u₁ ∈ S := by
    refine ⟨(⟨u₁, Subgroup.mem_zpowers u₁⟩, 1), ?_⟩
    show (u₁ : G) * 1 = u₁
    rw [mul_one]
  have hu₂S : u₂ ∈ S := by
    refine ⟨(1, ⟨u₂, Subgroup.mem_zpowers u₂⟩), ?_⟩
    show (1 : G) * u₂ = u₂
    rw [one_mul]
  have hHu : H ≤ φ₁.range :=
    Subgroup.zpowers_le.mpr ⟨slDiagUnits d₁ hprod₁, rfl⟩
  have hKu : K ≤ φ₁.range :=
    Subgroup.zpowers_le.mpr ⟨slDiagUnits d₂ hprod₂, rfl⟩
  have hSle : S ≤ φ₁.range := by
    intro x hx
    obtain ⟨q, rfl⟩ := MonoidHom.mem_range.mp hx
    exact φ₁.range.mul_mem (hHu q.1.2) (hKu q.2.2)
  refine ⟨S, hSle, ?_, ?_⟩
  · have hprod : IsPGroup p (↥H × ↥K) := IsPGroup.prod hHp hKp
    have hmap := (hprod.to_subgroup ⊤).map f
    rw [Subgroup.map_top] at hmap
    simpa [S] using hmap
  · intro hcyc
    haveI : IsCyclic ↥S := hcyc
    let u₁' : ↥S := ⟨u₁, hu₁S⟩
    let u₂' : ↥S := ⟨u₂, hu₂S⟩
    have hu₁'p : u₁' ^ p = 1 := Subtype.ext (by simpa [u₁'] using hu₁p)
    have hu₂'p : u₂' ^ p = 1 := Subtype.ext (by simpa [u₂'] using hu₂p)
    have hu₁'ne : u₁' ≠ 1 := by
      intro h
      exact hu₁ne (by simpa [u₁'] using congrArg Subtype.val h)
    have hu₂'ne : u₂' ≠ 1 := by
      intro h
      exact hu₂ne (by simpa [u₂'] using congrArg Subtype.val h)
    haveI : Finite (Subgroup.zpowers u₁') := IsOfFinOrder.finite_zpowers
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hC.prime.pos, hu₁'p⟩)
    haveI : Finite (Subgroup.zpowers u₂') := IsOfFinOrder.finite_zpowers
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hC.prime.pos, hu₂'p⟩)
    have hord₁' : orderOf u₁' = p := by
      rw [show u₁' = (⟨u₁, hu₁S⟩ : ↥S) from rfl, Subgroup.orderOf_mk, hord₁]
    have hord₂' : orderOf u₂' = p := by
      rw [show u₂' = (⟨u₂, hu₂S⟩ : ↥S) from rfl, Subgroup.orderOf_mk, hord₂]
    have hcard₁ : Nat.card (Subgroup.zpowers u₁') = p := by
      rw [Nat.card_zpowers, hord₁']
    have hcard₂ : Nat.card (Subgroup.zpowers u₂') = p := by
      rw [Nat.card_zpowers, hord₂']
    have heq : Subgroup.zpowers u₁' = Subgroup.zpowers u₂' :=
      (IsCyclic.subgroup_eq_iff_card_eq).mpr (by rw [hcard₁, hcard₂])
    have hmem' : u₂' ∈ Subgroup.zpowers u₁' := by
      rw [heq]
      exact Subgroup.mem_zpowers u₂'
    have hmap : (Subgroup.zpowers u₁').map S.subtype = Subgroup.zpowers u₁ := by
      rw [MonoidHom.map_zpowers]
      rfl
    have hmem : u₂ ∈ Subgroup.zpowers u₁ := by
      rw [← hmap]
      exact ⟨u₂', hmem', rfl⟩
    exact hnot hmem

theorem GGFarCtx.centralizer_x_le_normalizer [Finite G]
    (hC : GGFarCtx p Bs φ₁ φ₂ x y) {B : Subgroup G}
    (hS : CFSG.Assembly.LargeEvenSStar p B x φ₁.range) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (φ₁.range : Set G) := by
  intro g hg
  have hnc : ∃ S : Subgroup G, S ≤ φ₁.range ∧ IsPGroup p S ∧ ¬ IsCyclic S :=
    hC.exists_noncyclic_pSubgroup
  refine mem_normalizer_of_sstar' hS hnc ?_
  have hle : Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_left
      (Subgroup.mem_centralizer_singleton_iff.mp hy).symm k).eq
  exact hle.trans (Subgroup.centralizer_le_normalizer (Subgroup.zpowers x : Set G)) hg

end RootOfUnity

end CFSG.StandardType

end
