module

public import CFSG.Quasithin.Background.JonesParshallG2Two
public import CFSG.Quasithin.Background.P3G2Zorn
public import CFSG.Quasithin.Background.FFC4CaseI
public import CFSG.Quasithin.Background.FFC4Ext
public import Certificates.Certificate8953
public import Certificates.Certificate17001
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Quasithin.Background.A3Structure36BCase3
public import CFSG.Quasithin.Background.A3Structure36BCases
public import CFSG.Quasithin.Background.A3Structure36BCommon
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStar
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3

public section

namespace CFSG.Quasithin

namespace FFC

open Matrix Matrix.SpecialLinearGroup CFSG.Quasithin.Explicit CFSG.Open CFSG.Quasithin.JonesParshall
open scoped commutatorElement

variable {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def phi2 (K : Type) [Field K] [CharP K 2] : ZMod 2 →+* K :=
  ZMod.castHom (dvd_refl 2) K

@[expose] noncomputable def bcM : Matrix (Fin 8) (Fin 8) (ZMod 2) →+* Matrix (Fin 8) (Fin 8) K :=
  (phi2 K).mapMatrix

theorem bcM_apply (A : Matrix (Fin 8) (Fin 8) (ZMod 2)) (i j : Fin 8) :
    bcM (K := K) A i j = phi2 K (A i j) := rfl

theorem bcM_injective : Function.Injective (bcM (K := K)) := by
  intro A B h
  ext i j
  have := congrFun (congrFun h i) j
  exact (phi2 K).injective this

theorem cmat_g2X_e0_K : cmat (g2X (![1, 0, 0] : Fin 3 → K)) = bcM matX2 := by
  refine zmat_eq_of_mulVec fun x => ?_
  funext i
  fin_cases i <;>
    simp [zornCoord_apply, g2X_apply, xaFun, matX2, bcM_apply, mulVec, dotProduct,
      Fin.sum_univ_eight, zmk, CharTwo.neg_eq] <;> ring

theorem cmat_g2Y_e1_K : cmat (g2Y (![0, 1, 0] : Fin 3 → K)) = bcM matY2 := by
  refine zmat_eq_of_mulVec fun x => ?_
  funext i
  fin_cases i <;>
    simp [zornCoord_apply, g2Y_apply, ybFun, matY2, bcM_apply, mulVec, dotProduct,
      Fin.sum_univ_eight, zmk, CharTwo.neg_eq] <;> ring

theorem bcM_zornBlockMat (A C : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    bcM (K := K) (zornBlockMat A C) = zornBlockMat (A.map (phi2 K)) (C.map (phi2 K)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zornBlockMat, bcM_apply]

theorem map_transvection_two (i j : Fin 3) :
    (Matrix.transvection i j (1 : K)) = (Matrix.transvection i j (1 : ZMod 2)).map (phi2 K) := by
  ext a b
  simp [Matrix.transvection, Matrix.single_apply, Matrix.one_apply]

@[expose] noncomputable def tK (i j : Fin 3) (hij : i ≠ j) : ↥(cayleyGroup K) :=
  g2A (transvection hij (1 : K))

theorem cmat_tK {i j : Fin 3} (hij : i ≠ j) :
    cmat (tK (K := K) i j hij) =
      bcM (zornBlockMat (Matrix.transvection i j 1) (Matrix.transvection j i 1)) := by
  rw [tK, cmat_g2A, bcM_zornBlockMat]
  have h1 : ((transvection hij (1 : K) : SL3 K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.transvection i j (1 : K) := rfl
  have hadj : ((Matrix.transvection i j (1 : ZMod 2)).map (phi2 K)).adjugate =
      (adjugate (Matrix.transvection i j (1 : ZMod 2))).map (phi2 K) :=
    (RingHom.map_adjugate (phi2 K) _).symm
  rw [h1, map_transvection_two, hadj, ← Matrix.transpose_map, adj_transvection_two hij]

@[expose] noncomputable def gens8K : Fin 8 → ↥(cayleyGroup K) :=
  ![g2X ![1, 0, 0], g2Y ![0, 1, 0], tK 0 1 (by decide), tK 0 2 (by decide), tK 1 0 (by decide),
    tK 1 2 (by decide), tK 2 0 (by decide), tK 2 1 (by decide)]

theorem cmat_gens8K
    (i : Fin 8) : cmat (gens8K (K := K) i) = bcM (mats8 i) := by
  fin_cases i
  · exact cmat_g2X_e0_K
  · exact cmat_g2Y_e1_K
  all_goals exact cmat_tK _

theorem bcM_wordEvalM {k : ℕ} (mats : Fin k → Matrix (Fin 8) (Fin 8) (ZMod 2)) (w : List (Fin k)) :
    wordEvalM (fun i => bcM (K := K) (mats i)) w = bcM (wordEvalM mats w) := by
  induction w with
  | nil => exact (map_one bcM).symm
  | cons i w ih =>
    change bcM (mats i) * wordEvalM (fun i => bcM (K := K) (mats i)) w = bcM (mats i * wordEvalM mats w)
    rw [ih, map_mul]

theorem cmat_wordEval_K (w : List (Fin 8)) :
    cmat (wordEval (gens8K (K := K)) w) = bcM (wordEvalM mats8 w) := by
  rw [cmat_wordEval gens8K (fun i => bcM (mats8 i)) cmat_gens8K, bcM_wordEvalM]

@[expose] noncomputable def aK : ↥(cayleyGroup K) := wordEval gens8K [6, 1, 5, 1, 6, 5]

@[expose] noncomputable def bK : ↥(cayleyGroup K) := wordEval gens8K [7, 5, 3, 7, 3, 5]

@[expose] def wordE9 : List (Fin 2) := [1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1]

@[expose] noncomputable def yK : ↥(cayleyGroup K) := wordEval ![aK, bK] wordE9

theorem wordA_eq : wordEvalM mats8 [6, 1, 5, 1, 6, 5] = matA2 := by decide +kernel

theorem wordB_eq : wordEvalM mats8 [7, 5, 3, 7, 3, 5] = matB2 := by decide +kernel

theorem mats8_sq : ∀ i : Fin 8, mats8 i * mats8 i = 1 := by decide +kernel

theorem cmat_aK : cmat (aK (K := K)) = bcM matA2 := by
  rw [aK, cmat_wordEval_K, wordA_eq]

theorem cmat_bK : cmat (bK (K := K)) = bcM matB2 := by
  rw [bK, cmat_wordEval_K, wordB_eq]

theorem cmat_yK
    : cmat (yK (K := K)) = bcM (wordEvalM ![matA2, matB2] wordE9) := by
  have h : ∀ i, cmat (![aK, bK] i : ↥(cayleyGroup K)) = bcM (![matA2, matB2] i) := by
    intro i
    fin_cases i
    · exact cmat_aK
    · exact cmat_bK
  rw [yK, cmat_wordEval ![aK, bK] (fun i => bcM (![matA2, matB2] i)) h, bcM_wordEvalM]

theorem matE9_a3 : matA2 ^ 3 = 1 := by decide +kernel

theorem matE9_y3 : (wordEvalM ![matA2, matB2] wordE9) ^ 3 = 1 := by decide +kernel

theorem matE9_comm : matA2 * wordEvalM ![matA2, matB2] wordE9 =
    wordEvalM ![matA2, matB2] wordE9 * matA2 := by decide +kernel

theorem matE9_a1 : matA2 ≠ 1 := by decide +kernel

theorem matE9_y1 : wordEvalM ![matA2, matB2] wordE9 ≠ 1 := by decide +kernel

theorem matE9_ya : wordEvalM ![matA2, matB2] wordE9 ≠ matA2 := by decide +kernel

theorem matE9_ya2 : wordEvalM ![matA2, matB2] wordE9 ≠ matA2 ^ 2 := by decide +kernel

theorem aK_pow3 : (aK (K := K)) ^ 3 = 1 :=
  cmat_injective (by rw [map_pow, map_one, cmat_aK, ← map_pow, matE9_a3, map_one])

theorem yK_pow3 : (yK (K := K)) ^ 3 = 1 :=
  cmat_injective (by rw [map_pow, map_one, cmat_yK, ← map_pow, matE9_y3, map_one])

theorem aK_comm : aK (K := K) * yK = yK * aK :=
  cmat_injective (by rw [map_mul, map_mul, cmat_aK, cmat_yK, ← map_mul, ← map_mul, matE9_comm])

theorem aK_ne_one
    : aK (K := K) ≠ 1 := fun h => matE9_a1 (bcM_injective (by
  have := congrArg cmat h
  rw [cmat_aK, map_one] at this
  rw [this, map_one]))

theorem yK_ne_one
    : yK (K := K) ≠ 1 := fun h => matE9_y1 (bcM_injective (by
  have := congrArg cmat h
  rw [cmat_yK, map_one] at this
  rw [this, map_one]))

theorem yK_ne_aK
    : yK (K := K) ≠ aK := fun h => matE9_ya (bcM_injective (by
  have := congrArg cmat h
  rw [cmat_yK, cmat_aK] at this
  exact this))

theorem yK_ne_aK2
    : yK (K := K) ≠ aK ^ 2 := fun h => matE9_ya2 (bcM_injective (by
  have := congrArg cmat h
  rw [cmat_yK, map_pow, cmat_aK, ← map_pow] at this
  exact this))

theorem gens8K_inv (i : Fin 8) : (gens8K (K := K) i)⁻¹ = gens8K i :=
  inv_eq_of_cmat (cmat_gens8K i) (by rw [← map_mul, mats8_sq, map_one])

theorem aK_eq
    : aK (K := K) = ⁅gens8K (K := K) 6 * gens8K 1, gens8K 5⁆ := by
  rw [commutatorElement_def, _root_.mul_inv_rev, gens8K_inv, gens8K_inv, gens8K_inv]
  simp only [aK, wordEval, mul_one, mul_assoc]

theorem bK_eq
    : bK (K := K) = ⁅gens8K (K := K) 7, gens8K 5 * gens8K 3⁆ := by
  rw [commutatorElement_def, _root_.mul_inv_rev, gens8K_inv, gens8K_inv, gens8K_inv]
  simp only [bK, wordEval, mul_one, mul_assoc]

omit [CharP K 2] in
theorem coe_mem_commutator_K (g h : ↥(cayleyGroup K)) :
    ((⁅g, h⁆ : ↥(cayleyGroup K)) : quasithinZorn K ≃ₗ[K] quasithinZorn K) ∈
      ⁅cayleyGroup K, cayleyGroup K⁆ := by
  rw [show ((⁅g, h⁆ : ↥(cayleyGroup K)) : quasithinZorn K ≃ₗ[K] quasithinZorn K) =
    ⁅(g : quasithinZorn K ≃ₗ[K] quasithinZorn K), (h : quasithinZorn K ≃ₗ[K] quasithinZorn K)⁆ from
    map_commutatorElement (cayleyGroup K).subtype g h]
  exact Subgroup.commutator_mem_commutator g.2 h.2

theorem aK_mem
    : (aK (K := K) : quasithinZorn K ≃ₗ[K] quasithinZorn K) ∈
    ⁅cayleyGroup K, cayleyGroup K⁆ := by
  rw [aK_eq]
  exact coe_mem_commutator_K _ _

theorem bK_mem
    : (bK (K := K) : quasithinZorn K ≃ₗ[K] quasithinZorn K) ∈
    ⁅cayleyGroup K, cayleyGroup K⁆ := by
  rw [bK_eq]
  exact coe_mem_commutator_K _ _

theorem yK_mem
    : (yK (K := K) : quasithinZorn K ≃ₗ[K] quasithinZorn K) ∈
    ⁅cayleyGroup K, cayleyGroup K⁆ := by
  rw [yK, coe_wordEval_sub]
  refine wordEval_mem (fun i => ?_) _
  fin_cases i
  · exact aK_mem
  · exact bK_mem

theorem threeRank2_sub {G : Type*} [Group G] {D : Subgroup G} {x y : G} (hxD : x ∈ D) (hyD : y ∈ D)
    (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hxy : x * y = y * x) (hy1 : y ≠ 1)
    (hyx : y ≠ x) (hyx2 : y ≠ x ^ 2) : ThreeRank2 ↥D := by
  have hx3' : (⟨x, hxD⟩ : ↥D) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  refine ⟨⟨x, hxD⟩, ⟨y, hyD⟩, fun h => hx1 (congrArg Subtype.val h), hx3',
    Subtype.ext (by simpa using hy3), Subtype.ext hxy, ?_⟩
  intro hmem
  obtain ⟨n, hn⟩ := exists_npow_of_mem_zpowers_of_cube hx3' hmem
  have hn' : x ^ n = y := by simpa using congrArg Subtype.val hn
  have h3 : x ^ n = x ^ (n % 3) := pow_eq_pow_mod n hx3
  have hlt : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hr : n % 3
  · exact hy1 (by rw [← hn', h3]; simp)
  · exact hyx (by rw [← hn', h3]; simp)
  · exact hyx2 (by rw [← hn', h3])

theorem threeRank2_derived (K : Type) [Field K] [CharP K 2] :
    ThreeRank2 ↥⁅cayleyGroup K, cayleyGroup K⁆ := by
  have hx : (aK (K := K) : quasithinZorn K ≃ₗ[K] quasithinZorn K) ∈ ⁅cayleyGroup K, cayleyGroup K⁆ :=
    aK_mem
  have hy : (yK (K := K) : quasithinZorn K ≃ₗ[K] quasithinZorn K) ∈ ⁅cayleyGroup K, cayleyGroup K⁆ :=
    yK_mem
  refine threeRank2_sub hx hy ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun h => aK_ne_one (Subtype.ext h)
  · simpa using congrArg Subtype.val (aK_pow3 (K := K))
  · simpa using congrArg Subtype.val (yK_pow3 (K := K))
  · exact congrArg Subtype.val (aK_comm (K := K))
  · exact fun h => yK_ne_one (Subtype.ext h)
  · exact fun h => yK_ne_aK (Subtype.ext h)
  · exact fun h => yK_ne_aK2 (Subtype.ext (by simpa using h))

theorem threeRank2_g2
    (K : Type) [Field K] [CharP K 2] : ThreeRank2 ↥(quasithinG2 K) := by
  rw [CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup]
  exact (threeRank2_derived K).of_le (commutator_le_self_aux _)

theorem threeRank2_g2_derived (K : Type) [Field K] [CharP K 2] :
    ThreeRank2 ↥⁅quasithinG2 K, quasithinG2 K⁆ := by
  rw [CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup]
  exact threeRank2_derived K

theorem b58Inputs : B58Inputs where
  g2 := fun K _ _ hc => by
    have := hc
    exact threeRank2_g2 K
  g2d := fun K _ _ hK => by
    have := charP_two_of_card_pow (n := 1) (by simpa using hK)
    exact threeRank2_g2_derived K
  ext := fun d hd => extSq_faithful hd

theorem asB58 :
    AsB58 := asB58_of_inputs b58Inputs

end FFC

end CFSG.Quasithin
