module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerModel
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaModel
import CFSG.HardMathSupport.Dickson.Bal207.OrthSU38Torus
import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
import CFSG.Adapters.ClassicalCatalogLinearUnitary
import CFSG.CharacterTheory.CyclicBlocks.Family
import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
import CFSG.Combinatorics.AperiodicCentralInvolution
import CFSG.Combinatorics.AperiodicFiveOfSix
import CFSG.Combinatorics.AperiodicOppositeComponents
import CFSG.Combinatorics.AperiodicSixteenGraphDistances
import CFSG.Combinatorics.OuterLayerPredecessors
import CFSG.HardMathSupport.Dickson.Bal207.Glue
import CFSG.HardMathSupport.Dickson.Bal207.OrthSU38Comp
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209F4
import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsBase
import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DHeis
import CFSG.LieType.SteinbergBRBlockParabolicDInf
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
import CFSG.LocalAnalysis.GLTheoremB.Lemma99Core
import CFSG.LocalAnalysis.GLTheoremB.Lemma99Inputs
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A3A3Perm
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Top
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Engine
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
import CFSG.Open.SplitBNPair
import CFSG.Permutation.UnitaryThreeRecognition.Model
import CFSG.Quasithin.Background.A3Structure314Defs
import CFSG.Quasithin.Background.A3Structure319
import CFSG.Quasithin.Background.C1PackS15212C
import CFSG.Quasithin.Background.C1PackS1531Top
import CFSG.Quasithin.Background.C2PushThree
import CFSG.Quasithin.Background.D2
import CFSG.Quasithin.Background.D2Cyclic
import CFSG.Quasithin.Background.E3
import CFSG.Quasithin.Background.E3Nprime
import CFSG.Quasithin.Background.E3Uniq
import CFSG.Quasithin.Background.F918H5
import CFSG.Quasithin.Background.FFC4Tr2
import CFSG.Quasithin.Background.GoldschmidtS146RBend1
import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructFieldExt
import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructPGL
import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructSimple
import CFSG.Quasithin.EmptyFaithful.S14110
import CFSG.Quasithin.EmptyFaithful.S14610Q1
import CFSG.Quasithin.EmptyFaithful.S14610Top
import CFSG.Quasithin.EmptyFaithful.S146F4
import CFSG.Quasithin.EmptyFaithful.S152N11
import CFSG.Quasithin.EmptyFaithful.S152UGen
import CFSG.Quasithin.EmptyFaithful.S152Y15
import CFSG.Quasithin.EmptyFaithful.S152Y19
import CFSG.Quasithin.EmptyFaithful.S153E59A
import CFSG.Quasithin.EmptyFaithful.T1515Der
import CFSG.Quasithin.EmptyFaithful.T1531Final
import CFSG.Quasithin.H13.J4Order
import CFSG.Quasithin.Recognition.ModelBridges
import CFSG.Quasithin.Vol2.Ch10SecB4
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
import CFSG.Quasithin.Vol2.Ch11SecA02Setup
import CFSG.Quasithin.Vol2.Ch11SecA04Glue
import CFSG.Quasithin.Vol2.Ch11SecA11Exists
import CFSG.Quasithin.Vol2.Ch11SecAFacts03
import CFSG.Quasithin.Vol2.Ch11SecAVi2
import CFSG.Quasithin.Vol2.Ch1EightFourChar2
import CFSG.Quasithin.Vol2.Ch3Sec3InspF618Tools
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3315R
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323B
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3329
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3330
import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
import CFSG.RankThree.PartOne.S15K.FixedWitt
import CFSG.RankThree.PartOne.S15K.LayerModel
import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
import CFSG.RankThree.PartTwo.Sec19.Step1914Split
import CFSG.RankThree.PartTwo.Sec19.Step1914TriSeitz434
import CFSG.RankThree.PartTwo.Sec19.Step199Proof
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.Triality
open Polynomial Module
open CFSG.RankThree.Classical2 (orthDerived ProjOrthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal

namespace D4Inner

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

private theorem semilin_trace_eq_add_of_isCompl {F W : Type*} [Field F] [AddCommGroup W]
    [Module F W] [FiniteDimensional F W] {p q : Submodule F W} (h : IsCompl p q)
    (f : W →ₗ[F] W) (hp : ∀ x ∈ p, f x ∈ p) (hq : ∀ x ∈ q, f x ∈ q) :
    LinearMap.trace F W f =
      LinearMap.trace F p (f.restrict hp) + LinearMap.trace F q (f.restrict hq) := by
  set e := Submodule.prodEquivOfIsCompl p q h
  have hconj : e.symm.conj f = (f.restrict hp).prodMap (f.restrict hq) := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    apply e.injective
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply, LinearMap.prodMap_apply]
    rw [Submodule.coe_prodEquivOfIsCompl', Submodule.coe_prodEquivOfIsCompl', map_add]
    rfl
  rw [← LinearMap.trace_conj' f e.symm, hconj, LinearMap.trace_prodMap']

private theorem semilin_trace_restrictScalars_toLin {F L W : Type*} [Field F] [Field L]
    [Algebra F L] [FiniteDimensional F L] [AddCommGroup W] [Module F W] [Module L W]
    [IsScalarTower F L W] {ι : Type*} [Fintype ι] [DecidableEq ι] (c : Module.Basis ι L W)
    (A : Matrix ι ι L) :
    LinearMap.trace F W ((Matrix.toLin c c A).restrictScalars F) = Algebra.trace F L A.trace := by
  classical
  let b := Module.finBasis F L
  have key : ∀ i j, (LinearMap.toMatrix (b.smulTower c) (b.smulTower c)
      ((Matrix.toLin c c A).restrictScalars F)) (i, j) (i, j) =
        Algebra.leftMulMatrix b (A j j) i i := by
    intro i j
    rw [LinearMap.toMatrix_apply, Module.Basis.smulTower_apply, LinearMap.restrictScalars_apply,
      LinearMap.map_smul, Matrix.toLin_self, Module.Basis.smulTower_repr_mk, map_smul,
      Finsupp.smul_apply, c.repr_sum_self, smul_eq_mul, Algebra.leftMulMatrix_eq_repr_mul,
      mul_comm]
  rw [LinearMap.trace_eq_matrix_trace F (b.smulTower c), Matrix.trace, Matrix.trace, map_sum,
    Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  exact Finset.sum_congr rfl fun i _ => key i j

private theorem semilin_exists_lt_frobenius_pow {K : Type} [Field K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (σ : K ≃+* K) : ∃ j < n, ∀ x : K, σ x = x ^ 2 ^ j := by
  obtain ⟨τ, hτ, hord, hz, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hn hK
  have hfin : IsOfFinOrder τ := orderOf_pos_iff.1 (by rw [hord]; omega)
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1
    (hfin.mem_powers_iff_mem_zpowers.2 (by rw [hz]; exact Subgroup.mem_top σ))
  have hσ : σ = τ ^ (k % n) := by rw [← hk, ← hord, pow_mod_orderOf]
  have hpow : ∀ (m : ℕ) (x : K), (τ ^ m) x = x ^ 2 ^ m := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ]
      show (τ ^ m) (τ x) = _
      rw [ih, hτ, ← pow_mul, ← pow_succ']
  exact ⟨k % n, Nat.mod_lt _ (by omega), fun x => by rw [hσ, hpow]⟩

private theorem semilin_exists_unit_pow {E : Type*} [Field E] [Finite E] {N : ℕ} (hN : 2 ≤ N)
    (hE : Nat.card E = N ^ 2) :
    ∃ u : Eˣ, u ^ (N + 1) = 1 ∧ ∀ k, u ^ k = 1 → N + 1 ∣ k := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Eˣ)
  have hfac : N ^ 2 - 1 = (N - 1) * (N + 1) := by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have h1 : (M + 1) ^ 2 = M * (M + 1 + 1) + 1 := by ring
    rw [h1, Nat.add_sub_cancel, Nat.add_sub_cancel]
  have hord : orderOf g = (N - 1) * (N + 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hE, hfac]
  refine ⟨g ^ (N - 1), ?_, fun k hk => ?_⟩
  · rw [← pow_mul, ← hord, pow_orderOf_eq_one]
  · have h1 : orderOf g ∣ (N - 1) * k := orderOf_dvd_of_pow_eq_one (by rw [pow_mul]; exact hk)
    rw [hord] at h1
    exact Nat.dvd_of_mul_dvd_mul_left (by omega) h1

private theorem semilin_eq_zero_of_pow_add {E : Type*} [Field E] [CharP E 2] {N : ℕ} {u : Eˣ}
    (hu1 : u ^ (N + 1) = 1) (hu2 : ∀ k, u ^ k = 1 → N + 1 ∣ k) {j : ℕ} (hj : 2 ^ j < N)
    (h : ((u : E) + (u : E) ^ N) ^ 2 ^ j = (u : E) + (u : E) ^ N) : j = 0 := by
  have hN : u ^ N = u⁻¹ := by rw [eq_inv_iff_mul_eq_one, ← pow_succ, hu1]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [add_pow_char_pow, ← Units.val_pow_eq_pow_val u N, hN, ← Units.val_pow_eq_pow_val u (2 ^ j),
    ← Units.val_pow_eq_pow_val u⁻¹ (2 ^ j), inv_pow] at h
  set v := u ^ 2 ^ j with hv
  have hu0 : (u : E) * ((u⁻¹ : Eˣ) : E) = 1 := Units.mul_inv u
  have hv0 : (v : E) * ((v⁻¹ : Eˣ) : E) = 1 := Units.mul_inv v
  have key : ((v : E) - u) * ((u : E) * v - 1) = 0 := by
    linear_combination ((u : E) * v) * h - (u : E) * hv0 + (v : E) * hu0
  rcases mul_eq_zero.1 key with h1 | h1
  · have hvu : v = u := Units.ext (sub_eq_zero.1 h1)
    have h2 : u ^ (2 ^ j - 1) = 1 := by
      have h3 : u ^ (2 ^ j - 1) * u = u := by
        rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, ← hv, hvu]
      exact mul_eq_right.1 h3
    have h4 := Nat.eq_zero_of_dvd_of_lt (hu2 _ h2) (by omega)
    by_contra hj0
    have := Nat.one_lt_two_pow hj0
    omega
  · have h2 : u ^ (2 ^ j + 1) = 1 := by
      rw [pow_succ, ← hv, mul_comm]
      exact Units.ext (by rw [Units.val_mul, Units.val_one]; exact sub_eq_zero.1 h1)
    have h3 := Nat.le_of_dvd (by positivity) (hu2 _ h2)
    omega

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem exists_mem_centDer_trace {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n)
    (hn3 : 3 ≤ n) {s : Om8 K} (hs3 : s ^ 3 = 1) (hd : D4Rank.omFixDim s = 2) :
    ∃ y ∈ centDer s, ∀ j < n,
      ((y : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K).trace ^ 2 ^ j =
        ((y : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K).trace → j = 0 := by
  classical
  set Q := coordinateQuadPlus 4 K with hQdef
  set xe : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K) :=
    ((omLift s : orthDerived Q) : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) with hxe
  have hx : OddOrderIsometry Q 3 xe := oddOrderIsometry_omLift hs3 hd
  have hmem := phi_mem_primaryFactors_omLift hK hn hs3 hd
  have hirr : Irreducible (X ^ 2 + X + 1 : K[X]) := irreducible_of_mem_primaryFactors hmem
  have : Fact (Irreducible (X ^ 2 + X + 1 : K[X])) := ⟨hirr⟩
  have hm := primaryMultiplicity_phi_omLift hK hn hs3 hd
  have hn1 : 1 ≤ n := by omega
  have hN8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  have hmq : ¬(3 = 3 ∧ 2 ^ n = 2) := fun h => by omega
  obtain ⟨hU, H, b, -, hb, hrange, hspec⟩ :=
    CFSG.HardMathSupport.Dickson.Bal207.OrthFix.exists_phiFrame hK hn1 hx rfl hmem hm le_rfl hmq
  have : Finite (AdjoinRoot (X ^ 2 + X + 1 : K[X])) := hU.finite
  have : CharP (AdjoinRoot (X ^ 2 + X + 1 : K[X])) 2 := hU.charP
  have : Module.Finite K (AdjoinRoot (X ^ 2 + X + 1 : K[X])) :=
    (AdjoinRoot.powerBasis hirr.ne_zero).finite
  have hfinE : Module.finrank K (AdjoinRoot (X ^ 2 + X + 1 : K[X])) = 2 := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim,
      CFSG.HardMathSupport.Dickson.Bal207.OrthFix.monic_phi.2]
  have hcardE : Nat.card (AdjoinRoot (X ^ 2 + X + 1 : K[X])) = (2 ^ n) ^ 2 := by
    rw [hU.card, ← pow_mul, mul_comm]
  obtain ⟨u, hu1, hu2⟩ := semilin_exists_unit_pow (by omega) hcardE
  obtain ⟨N', hN'⟩ : ∃ N', 2 ^ n = 2 * N' := ⟨2 ^ (n - 1), by rw [← pow_succ']; congr 1; omega⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ, ζ = u ^ N' := ⟨_, rfl⟩
  have hζ1 : ζ ^ (2 ^ n + 1) = 1 := by rw [hζ, ← pow_mul, mul_comm, pow_mul, hu1, one_pow]
  have hζζu : ζ * ζ * u = 1 := by
    rw [hζ, ← pow_add, ← pow_succ, show N' + N' + 1 = 2 ^ n + 1 by omega, hu1]
  obtain ⟨d, hddef⟩ : ∃ d : Fin 3 → AdjoinRoot (X ^ 2 + X + 1 : K[X]),
      d = ![(ζ : AdjoinRoot (X ^ 2 + X + 1 : K[X])), ζ, u] := ⟨_, rfl⟩
  have hd1 : ∀ i, d i ^ (2 ^ n + 1) = 1 := by
    have hζ1' : (ζ : AdjoinRoot (X ^ 2 + X + 1 : K[X])) ^ (2 ^ n + 1) = 1 := by
      rw [← Units.val_pow_eq_pow_val, hζ1, Units.val_one]
    have hu1' : (u : AdjoinRoot (X ^ 2 + X + 1 : K[X])) ^ (2 ^ n + 1) = 1 := by
      rw [← Units.val_pow_eq_pow_val, hu1, Units.val_one]
    intro i
    fin_cases i <;> simp [hddef, hζ1', hu1']
  have hdet : (Matrix.diagonal d).det = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_three, hddef]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [← Units.val_mul, ← Units.val_mul, hζζu, Units.val_one]
  have htrM : (Matrix.diagonal d).trace = (u : AdjoinRoot (X ^ 2 + X + 1 : K[X])) := by
    rw [Matrix.trace_diagonal, Fin.sum_univ_three, hddef]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [CharTwo.add_self_eq_zero, zero_add]
  obtain ⟨M, hMdef⟩ : ∃ M : GL (Fin 3) (AdjoinRoot (X ^ 2 + X + 1 : K[X])),
      M = Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal d)
        (by rw [hdet]; exact one_ne_zero) := ⟨_, rfl⟩
  have hMval : (M : Matrix (Fin 3) (Fin 3) (AdjoinRoot (X ^ 2 + X + 1 : K[X]))) =
      Matrix.diagonal d := by rw [hMdef]; rfl
  have hMU : M ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary hU
      (CFSG.HardMathSupport.Dickson.Bal207.FirstClaim.oneGram _ 3) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary, hMval,
      CFSG.HardMathSupport.Dickson.Bal207.FirstClaim.oneGram, Units.val_one, Matrix.mul_one,
      Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply, ← pow_succ]
    exact hd1 i
  obtain ⟨g, hg⟩ : ∃ g, g = CFSG.HardMathSupport.Dickson.Bal207.OrthFix.phiBlockEquiv hx hmem hU
      b hb hrange ⟨M, hMU⟩ := ⟨_, rfl⟩
  have htoLinb : ((Matrix.GeneralLinearGroup.toLin' b M :
      LinearMap.GeneralLinearGroup (AdjoinRoot (X ^ 2 + X + 1 : K[X]))
        (primaryComponent xe.toLinearMap (X ^ 2 + X + 1))) :
      primaryComponent xe.toLinearMap (X ^ 2 + X + 1) →ₗ[AdjoinRoot (X ^ 2 + X + 1 : K[X])]
        primaryComponent xe.toLinearMap (X ^ 2 + X + 1)) =
      Matrix.toLin b b (Matrix.diagonal d) := by
    refine LinearMap.ext fun w => ?_
    rw [Matrix.toLin_apply, CFSG.RankThree.CentralLift.toLin'_basis_apply,
      Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_apply, hMval]
  have hgapp : ∀ w : primaryComponent xe.toLinearMap (X ^ 2 + X + 1),
      (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) w =
        ((Matrix.toLin b b (Matrix.diagonal d) w :
          primaryComponent xe.toLinearMap (X ^ 2 + X + 1)) : Fin (2 * 4) → K) := fun w => by
    rw [hg, CFSG.HardMathSupport.Dickson.Bal207.OrthFix.phiBlockEquiv_apply, ← htoLinb]
  have hdetg : blockDet Q xe (X ^ 2 + X + 1) g = 1 := by
    rw [hg, blockDet_apply, CFSG.HardMathSupport.Dickson.Bal207.OrthFix.blockGL_phiBlockEquiv,
      CFSG.RankThree.CentralLift.det_toLin'_basis]
    change (M : Matrix (Fin 3) (Fin 3) (AdjoinRoot (X ^ 2 + X + 1 : K[X]))).det = 1
    rw [hMval, hdet]
  have hgS : (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ∈
      specialBlock Q xe (X ^ 2 + X + 1) := mem_specialBlock.mpr ⟨g.2, hdetg⟩
  have hgΩ := hspec hgS
  obtain ⟨y, hydef⟩ : ∃ y : Om8 K,
      y = (CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv Q).symm ⟨_, hgΩ⟩ := ⟨_, rfl⟩
  have hyg : omLift y = ⟨_, hgΩ⟩ := by rw [hydef]; exact MulEquiv.apply_symm_apply _ _
  have hyC : y ∈ centDer s := by
    have h1 : omBridge y ∈ (centDer s).map (omBridge (K := K)).toMonoidHom := by
      rw [map_centDer_eq_componentImage_phi hK hn hn3 hs3 hd, omBridge_apply, hyg]
      exact ⟨_, Subgroup.mem_subgroupOf.mpr hgS, rfl⟩
    obtain ⟨y', hy', hyy⟩ := h1
    rwa [omBridge.injective hyy] at hy'
  have hcompl : IsCompl (fixedSpace xe) (primaryComponent xe.toLinearMap (X ^ 2 + X + 1)) := by
    have h := hx.fixed_others.1
    rwa [CFSG.HardMathSupport.Dickson.Bal207.OrthFix.othersSpace_eq hx
      (three_dvd_card_add_one hK hn) hmem] at h
  have hW : ∀ v ∈ fixedSpace xe, (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) v = v :=
    fun v hv => CFSG.HardMathSupport.Dickson.Bal207.OrthFix.apply_fixed_of_mem_supportedBlock rfl
      g.2 hv
  have hpW : ∀ v ∈ fixedSpace xe,
      ((g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) : (Fin (2 * 4) → K) →ₗ[K] (Fin (2 * 4) → K))
        v ∈ fixedSpace xe := fun v hv => by
    rw [LinearEquiv.coe_coe, hW v hv]
    exact hv
  have hpΦ : ∀ v ∈ primaryComponent xe.toLinearMap (X ^ 2 + X + 1),
      ((g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) : (Fin (2 * 4) → K) →ₗ[K] (Fin (2 * 4) → K))
        v ∈ primaryComponent xe.toLinearMap (X ^ 2 + X + 1) := fun v hv => by
    have h : (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) v = _ := hgapp ⟨v, hv⟩
    rw [LinearEquiv.coe_coe, h]
    exact Subtype.property _
  have hrestrW : ((g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) :
      (Fin (2 * 4) → K) →ₗ[K] (Fin (2 * 4) → K)).restrict hpW = LinearMap.id :=
    LinearMap.ext fun w => Subtype.ext (by
      rw [LinearMap.restrict_coe_apply, LinearEquiv.coe_coe, hW _ w.2]
      rfl)
  have hrestrΦ : ((g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) :
      (Fin (2 * 4) → K) →ₗ[K] (Fin (2 * 4) → K)).restrict hpΦ =
        (Matrix.toLin b b (Matrix.diagonal d)).restrictScalars K :=
    LinearMap.ext fun w => Subtype.ext (by
      rw [LinearMap.restrict_coe_apply, LinearEquiv.coe_coe, hgapp]
      rfl)
  have htoLin : Matrix.toLin' ((y : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) =
      ((g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) :
        (Fin (2 * 4) → K) →ₗ[K] (Fin (2 * 4) → K)) := by
    refine LinearMap.ext fun v => ?_
    have h1 : ((omLift y : orthDerived Q) : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) =
        (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) := by rw [hyg]
    rw [LinearEquiv.coe_coe, ← h1, CFSG.RankThree.PartOne.KCOrthComm.coe_matrixDerivedEquiv,
      Matrix.toLin'_apply]
    rfl
  have htrace : ((y : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K).trace =
      Algebra.trace K (AdjoinRoot (X ^ 2 + X + 1 : K[X]))
        (u : AdjoinRoot (X ^ 2 + X + 1 : K[X])) := by
    rw [← Matrix.trace_toLin'_eq, htoLin, semilin_trace_eq_add_of_isCompl hcompl _ hpW hpΦ,
      hrestrW, hrestrΦ, LinearMap.trace_id, finrank_fixedSpace_omLift hd,
      semilin_trace_restrictScalars_toLin, htrM, Nat.cast_ofNat, CharTwo.two_eq_zero, zero_add]
  refine ⟨y, hyC, fun j hj hpow => ?_⟩
  rw [htrace] at hpow
  have h1 := congrArg (algebraMap K (AdjoinRoot (X ^ 2 + X + 1 : K[X]))) hpow
  rw [map_pow, FiniteField.algebraMap_trace_eq_sum_pow, hfinE, hK] at h1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] at h1
  exact semilin_eq_zero_of_pow_add hu1 hu2 (Nat.pow_lt_pow_right (by norm_num) hj) h1

theorem mem_inner_of_fix_centDer {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n) (hn3 : 3 ≤ n)
    {s : Om8 K} (hs3 : s ^ 3 = 1) (hd : D4Rank.omFixDim s = 2) {φ : MulAut (Om8 K)}
    (hφ : φ ∈ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range) (hfix : ∀ y ∈ centDer s, φ y = y) :
    φ ∈ Inn (Om8 K) := by
  obtain ⟨ι, ⟨γ, rfl⟩, _, ⟨σ, rfl⟩, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hφ
  suffices hσ : σ = 1 by
    subst hσ
    rw [map_one, mul_one]
    exact ⟨γ, rfl⟩
  obtain ⟨y, hy, hgen⟩ := exists_mem_centDer_trace hK hn hn3 hs3 hd
  have htr : σ ((y : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K).trace =
      ((y : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K).trace := by
    have h := congrArg (fun z : Om8 K =>
      ((z : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K).trace) (hfix y hy)
    simp only [MulAut.mul_apply, MulAut.conj_apply] at h
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul,
      Matrix.trace_units_conj, RecipeFieldOmega.fieldAutP_apply_val,
      RecipeFieldOmega.glFieldAut_apply_val] at h
    rw [AddMonoidHom.map_trace]
    exact h
  obtain ⟨j, hj, hσj⟩ := semilin_exists_lt_frobenius_pow (by omega) hK σ
  have hj0 : j = 0 := hgen j hj (by rw [← hσj]; exact htr)
  subst hj0
  exact RingEquiv.ext fun x => by rw [hσj, pow_zero, pow_one]; rfl

end D4Inner

end CFSG.StandardType

end
