module

public import CFSG.RankThree.GF2n.Smith81.S81NMask
public import CFSG.RankThree.GF2n.Smith81.S81NComm
public import CFSG.RankThree.GF2n.Smith81.S81NUG
public import CFSG.RankThree.GF2n.Smith81.S81NModelDef


public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open scoped commutatorElement
open exteriorPower

variable {K : Type*} [Field K]

section Model2

@[expose] def vA (K : Type*) [Field K] : Cube K := ub K 0 3 4 + ub K 1 2 4

@[expose] def vB (K : Type*) [Field K] : Cube K := ub K 0 3 5 + ub K 1 2 5

@[expose] def kerG2 (K : Type*) [Field K] : Fin 12 → Cube K :=
  ![ub K 0 1 2, ub K 0 1 4, ub K 0 1 5, ub K 0 2 3, ub K 0 2 4, ub K 0 2 5, ub K 0 4 5,
    ub K 2 3 4, ub K 2 3 5, ub K 2 4 5, vA K, vB K]

@[expose] def ranG2 (K : Type*) [Field K] : Fin 8 → Cube K :=
  ![ub K 0 1 2, ub K 0 2 3, ub K 0 2 4, ub K 0 2 5, ub K 0 4 5, ub K 2 4 5, vA K, vB K]

@[expose] def ranPre2 (K : Type*) [Field K] : Fin 8 → Cube K :=
  ![ub K 0 1 3, ub K 1 2 3, ub K 0 3 4, ub K 0 3 5, ub K 1 4 5, ub K 3 4 5,
    ub K 0 3 4 + ub K 1 3 4, ub K 0 3 5 + ub K 1 3 5]

@[expose] def kerP2 : Fin 12 → ℕ := ![7, 19, 35, 13, 21, 37, 49, 28, 44, 52, 25, 41]

@[expose] def ranP2 : Fin 8 → ℕ := ![7, 13, 21, 37, 49, 52, 25, 41]

@[expose] def pA (K : Type*) [Field K] : Cube K :=
  ub K 0 1 4 + ub K 0 3 4 + ub K 1 2 4 + ub K 2 3 4

@[expose] def pB (K : Type*) [Field K] : Cube K :=
  ub K 0 1 5 + ub K 0 3 5 + ub K 1 2 5 + ub K 2 3 5

def pos2 (i j : Fin 6) : Prop := lev2 i < lev2 j

instance (i j : Fin 6) : Decidable (pos2 i j) :=
  inferInstanceAs (Decidable (lev2 i < lev2 j))

variable [CharP K 2]

theorem F2_kerG (i : Fin 12) : (rho K (tInv2 K) - 1) (kerG2 K i) = 0 := by
  rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  apply cfm_ext3
  intro m hm hc
  rw [rho_tInv2, Module.End.mul_apply, cfm_rho_X01 _ _ hm]
  rcases exists_mask3 hm hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  fin_cases i <;>
  simp (config := {decide := true}) [kerG2, vA, vB, cfm_ub_mask, cfm_rho_X23, cfm_add,
    CharTwo.add_self_eq_zero, -Representation.exteriorPower_apply]

theorem F2_ranPre (i : Fin 8) : (rho K (tInv2 K) - 1) (ranPre2 K i) = ranG2 K i := by
  rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_iff_eq_add]
  apply cfm_ext3
  intro m hm hc
  rw [rho_tInv2, Module.End.mul_apply, cfm_rho_X01 _ _ hm, cfm_add]
  rcases exists_mask3 hm hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  fin_cases i <;>
  simp (config := {decide := true}) [ranPre2, ranG2, vA, vB, cfm_ub_mask, cfm_rho_X23, cfm_add,
    CharTwo.add_self_eq_zero, -Representation.exteriorPower_apply]

theorem kerG2_pivots : ∀ i j, cfm K (kerG2 K i) (kerP2 j) = if i = j then (1 : K) else 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [kerG2, kerP2, vA, vB, cfm_ub_mask, cfm_add]

theorem ranG2_pivots : ∀ i j, cfm K (ranG2 K i) (ranP2 j) = if i = j then (1 : K) else 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [ranG2, ranP2, vA, vB, cfm_ub_mask, cfm_add]

theorem kerP2_card : ∀ j, (mset (kerP2 j)).card = 3 := by
  intro j; fin_cases j <;> decide

theorem ranP2_card : ∀ j, (mset (ranP2 j)).card = 3 := by
  intro j; fin_cases j <;> decide

theorem ker_range_eq2 :
    LinearMap.ker (rho K (tInv2 K) - 1) = Submodule.span K (Set.range (kerG2 K)) ∧
      LinearMap.range (rho K (tInv2 K) - 1) = Submodule.span K (Set.range (ranG2 K)) :=
  ker_range_eq_of_gens (a := 12) (b := 8) (by norm_num) _ (kerG2 K) (ranG2 K) F2_kerG
    (fun i => ⟨ranPre2 K i, F2_ranPre i⟩)
    (linearIndependent_of_pivots_mask _ kerP2 kerP2_card kerG2_pivots)
    (linearIndependent_of_pivots_mask _ ranP2 ranP2_card ranG2_pivots)

private theorem cube_add_self_eq_zero (x : Cube K) : x + x = 0 := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  rw [← two_smul K x, h2, zero_smul]

private theorem ι3_e_eq_ub {a b c : Fin 6} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i j k : Fin 6) (hij : i < j) (hjk : j < k)
    (hI : ({i, j, k} : Finset (Fin 6)) = {a, b, c}) :
    ιMulti K 3 ![e K a, e K b, e K c] = ub K i j k hij hjk :=
  ι3_e_eq_cubeBasis hab hac hbc (tripleSet i j k hij.ne (hij.trans hjk).ne hjk.ne) hI

private theorem ι_014 : ιMulti K 3 ![e K 0, e K 1, e K 4] = ub K 0 1 4 :=
  ι3_e_eq_ub (by decide) (by decide) (by decide) 0 1 4 (by decide) (by decide) (by decide)

private theorem ι_034 : ιMulti K 3 ![e K 0, e K 3, e K 4] = ub K 0 3 4 :=
  ι3_e_eq_ub (by decide) (by decide) (by decide) 0 3 4 (by decide) (by decide) (by decide)

private theorem ι_124 : ιMulti K 3 ![e K 2, e K 1, e K 4] = ub K 1 2 4 :=
  ι3_e_eq_ub (by decide) (by decide) (by decide) 1 2 4 (by decide) (by decide) (by decide)

private theorem ι_234 : ιMulti K 3 ![e K 2, e K 3, e K 4] = ub K 2 3 4 :=
  ι3_e_eq_ub (by decide) (by decide) (by decide) 2 3 4 (by decide) (by decide) (by decide)

private theorem ι_015 : ιMulti K 3 ![e K 0, e K 1, e K 5] = ub K 0 1 5 :=
  ι3_e_eq_ub (by decide) (by decide) (by decide) 0 1 5 (by decide) (by decide) (by decide)

private theorem ι_035 : ιMulti K 3 ![e K 0, e K 3, e K 5] = ub K 0 3 5 :=
  ι3_e_eq_ub (by decide) (by decide) (by decide) 0 3 5 (by decide) (by decide) (by decide)

private theorem ι_125 : ιMulti K 3 ![e K 2, e K 1, e K 5] = ub K 1 2 5 :=
  ι3_e_eq_ub (by decide) (by decide) (by decide) 1 2 5 (by decide) (by decide) (by decide)

private theorem ι_235 : ιMulti K 3 ![e K 2, e K 3, e K 5] = ub K 2 3 5 :=
  ι3_e_eq_ub (by decide) (by decide) (by decide) 2 3 5 (by decide) (by decide) (by decide)

private theorem ι_024 : ιMulti K 3 ![e K 0, e K 2, e K 4] = ub K 0 2 4 :=
  ι3_e_eq_ub (by decide) (by decide) (by decide) 0 2 4 (by decide) (by decide) (by decide)

private theorem ι_025 : ιMulti K 3 ![e K 0, e K 2, e K 5] = ub K 0 2 5 :=
  ι3_e_eq_ub (by decide) (by decide) (by decide) 0 2 5 (by decide) (by decide) (by decide)

theorem pA_eq : pA K = ιMulti K 3 ![e K 0 + e K 2, e K 1 + e K 3, e K 4] := by
  unfold pA
  rw [ι3_add_fst, ι3_add_snd, ι3_add_snd, ι_014, ι_034, ι_124, ι_234]
  abel

theorem pB_eq : pB K = ιMulti K 3 ![e K 0 + e K 2, e K 1 + e K 3, e K 5] := by
  unfold pB
  rw [ι3_add_fst, ι3_add_snd, ι3_add_snd, ι_015, ι_035, ι_125, ι_235]
  abel

theorem isPure_pA : IsPure K (pA K) := ⟨_, pA_eq⟩

theorem isPure_pB : IsPure K (pB K) := ⟨_, pB_eq⟩

theorem vA_eq : vA K = pA K + ub K 0 1 4 + ub K 2 3 4 := by
  have key : pA K + ub K 0 1 4 + ub K 2 3 4 =
      (ub K 0 1 4 + ub K 0 1 4) + (ub K 2 3 4 + ub K 2 3 4) + vA K := by
    unfold pA vA; abel
  rw [key]
  simp only [cube_add_self_eq_zero, zero_add]

theorem vB_eq : vB K = pB K + ub K 0 1 5 + ub K 2 3 5 := by
  have key : pB K + ub K 0 1 5 + ub K 2 3 5 =
      (ub K 0 1 5 + ub K 0 1 5) + (ub K 2 3 5 + ub K 2 3 5) + vB K := by
    unfold pB vB; abel
  rw [key]
  simp only [cube_add_self_eq_zero, zero_add]

def InC2 (ξ : Cube K) : Prop :=
  cfm K ξ 11 = 0 ∧ cfm K ξ 14 = 0 ∧ cfm K ξ 26 = 0 ∧ cfm K ξ 42 = 0 ∧ cfm K ξ 50 = 0 ∧
    cfm K ξ 56 = 0 ∧ cfm K ξ 22 = cfm K ξ 25 ∧ cfm K ξ 38 = cfm K ξ 41

def InR2 (η : Cube K) : Prop :=
  cfm K η 11 = 0 ∧ cfm K η 14 = 0 ∧ cfm K η 19 = 0 ∧ cfm K η 26 = 0 ∧ cfm K η 28 = 0 ∧
    cfm K η 35 = 0 ∧ cfm K η 42 = 0 ∧ cfm K η 44 = 0 ∧ cfm K η 50 = 0 ∧ cfm K η 56 = 0 ∧
    cfm K η 22 = cfm K η 25 ∧ cfm K η 38 = cfm K η 41

theorem InC2_of_mem_ker {ξ : Cube K} (h : ξ ∈ LinearMap.ker (rho K (tInv2 K) - 1)) : InC2 ξ := by
  rw [(ker_range_eq2 (K := K)).1] at h
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    fin_cases k <;> simp (config := {decide := true}) [InC2, kerG2, vA, vB, cfm_ub_mask, cfm_add]
  | zero => simp [InC2, cfm_zero]
  | add x y _ _ hx hy =>
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hx
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := hy
    simp [InC2, cfm_add, a1, a2, a3, a4, a5, a6, a7, a8, b1, b2, b3, b4, b5, b6, b7, b8]
  | smul c x _ hx =>
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hx
    simp [InC2, cfm_smul, a1, a2, a3, a4, a5, a6, a7, a8]

theorem mem_range_of_InR2 {η : Cube K} (h : InR2 η) :
    η ∈ LinearMap.range (rho K (tInv2 K) - 1) := by
  rw [(ker_range_eq2 (K := K)).2]
  apply mem_span_of_recon (ranG2 K) ranP2
  apply cfm_ext3
  intro m hm hc
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  rcases exists_mask3 hm hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) [ranG2, ranP2, vA, vB, cfm_ub_mask, cfm_zero, cfm_add,
    cfm_smul, Fin.sum_univ_succ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

theorem model2_hUC {u : GL (Fin 6) K} (hu : u ∈ Uset2 K) :
    ∀ ξ ∈ LinearMap.ker (rho K (tInv2 K) - 1),
      rho K u ξ - ξ ∈ LinearMap.range (rho K (tInv2 K) - 1) := by
  obtain ⟨i, j, hij, c, hlev, rfl⟩ := hu
  intro ξ hξ
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := InC2_of_mem_ker hξ
  refine mem_range_of_InR2 ?_
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd hlev (by decide)
    | simp (config := {decide := true}) [InR2, cfm_sub, cfm_rho_transv,
        -Representation.exteriorPower_apply, h1, h2, h3, h4, h5, h6, h7, h8]

theorem model2_hUfix :
    ∀ ξ ∈ LinearMap.ker (rho K (tInv2 K) - 1), (∀ u ∈ Uset2 K, rho K u ξ = ξ) →
      ξ ∈ LinearMap.range (rho K (tInv2 K) - 1) := by
  intro ξ _ hfix
  have hz : ∀ (i j : Fin 6) (hij : i ≠ j), pos2 i j → rho K (transvGL K i j hij 1) ξ = ξ :=
    fun i j hij hp => hfix _ ⟨i, j, hij, 1, hp, rfl⟩
  have z : ∀ m : ℕ, m < 64 →
      (∃ i j : Fin 6, i ≠ j ∧ pos2 i j ∧ m.testBit j.val = true ∧ m.testBit i.val = false) →
        cfm K ξ m = 0 :=
    fun m hm hmv => cfm_zero_of_fixed pos2 hz m hm hmv
  refine mem_range_of_InR2 ⟨z 11 (by norm_num) (by decide), z 14 (by norm_num) (by decide),
    z 19 (by norm_num) (by decide), z 26 (by norm_num) (by decide),
    z 28 (by norm_num) (by decide), z 35 (by norm_num) (by decide),
    z 42 (by norm_num) (by decide), z 44 (by norm_num) (by decide),
    z 50 (by norm_num) (by decide), z 56 (by norm_num) (by decide), ?_, ?_⟩
  · rw [z 22 (by norm_num) (by decide), z 25 (by norm_num) (by decide)]
  · rw [z 38 (by norm_num) (by decide), z 41 (by norm_num) (by decide)]

theorem model2_P3 :
    ∃ U : Set (GL (Fin 6) K), (∀ u ∈ U, (u : Matrix (Fin 6) (Fin 6) K).det = 1) ∧
      (∀ u ∈ U, u * tInv2 K = tInv2 K * u) ∧
      (∀ u ∈ U, ∀ ξ ∈ LinearMap.ker (rho K (tInv2 K) - 1),
        rho K u ξ - ξ ∈ LinearMap.range (rho K (tInv2 K) - 1)) ∧
      (∀ ξ ∈ LinearMap.ker (rho K (tInv2 K) - 1), (∀ u ∈ U, rho K u ξ = ξ) →
        ξ ∈ LinearMap.range (rho K (tInv2 K) - 1)) :=
  ⟨Uset2 K, fun u hu => (Uset2_det_commute hu).1, fun u hu => (Uset2_det_commute hu).2,
    fun u hu => model2_hUC hu, model2_hUfix⟩

theorem model2_P1 :
    LinearMap.ker (rho K (tInv2 K) - 1) ≤
      Submodule.span K {ξ | ξ ∈ LinearMap.ker (rho K (tInv2 K) - 1) ∧ IsPure K ξ} := by
  have hS : ∀ ξ : Cube K, ξ ∈ LinearMap.ker (rho K (tInv2 K) - 1) → IsPure K ξ →
      ξ ∈ Submodule.span K {ξ | ξ ∈ LinearMap.ker (rho K (tInv2 K) - 1) ∧ IsPure K ξ} :=
    fun ξ h1 h2 => Submodule.subset_span ⟨h1, h2⟩
  have hk : ∀ i : Fin 12, kerG2 K i ∈ LinearMap.ker (rho K (tInv2 K) - 1) :=
    fun i => LinearMap.mem_ker.mpr (F2_kerG i)
  have hvA : vA K ∈ LinearMap.ker (rho K (tInv2 K) - 1) := hk 10
  have hvB : vB K ∈ LinearMap.ker (rho K (tInv2 K) - 1) := hk 11
  have hu014 : ub K 0 1 4 ∈ LinearMap.ker (rho K (tInv2 K) - 1) := hk 1
  have hu234 : ub K 2 3 4 ∈ LinearMap.ker (rho K (tInv2 K) - 1) := hk 7
  have hu015 : ub K 0 1 5 ∈ LinearMap.ker (rho K (tInv2 K) - 1) := hk 2
  have hu235 : ub K 2 3 5 ∈ LinearMap.ker (rho K (tInv2 K) - 1) := hk 8
  have hpA : pA K ∈ LinearMap.ker (rho K (tInv2 K) - 1) := by
    have e : pA K = vA K - ub K 0 1 4 - ub K 2 3 4 := by rw [vA_eq]; abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ hvA hu014) hu234
  have hpB : pB K ∈ LinearMap.ker (rho K (tInv2 K) - 1) := by
    have e : pB K = vB K - ub K 0 1 5 - ub K 2 3 5 := by rw [vB_eq]; abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ hvB hu015) hu235
  have hA : vA K ∈ Submodule.span K
      {ξ | ξ ∈ LinearMap.ker (rho K (tInv2 K) - 1) ∧ IsPure K ξ} := by
    rw [vA_eq]
    exact Submodule.add_mem _ (Submodule.add_mem _ (hS _ hpA isPure_pA)
      (hS _ hu014 (isPure_cubeBasis _))) (hS _ hu234 (isPure_cubeBasis _))
  have hB : vB K ∈ Submodule.span K
      {ξ | ξ ∈ LinearMap.ker (rho K (tInv2 K) - 1) ∧ IsPure K ξ} := by
    rw [vB_eq]
    exact Submodule.add_mem _ (Submodule.add_mem _ (hS _ hpB isPure_pB)
      (hS _ hu015 (isPure_cubeBasis _))) (hS _ hu235 (isPure_cubeBasis _))
  refine (ker_range_eq2 (K := K)).1.le.trans (Submodule.span_le.mpr ?_)
  rintro _ ⟨i, rfl⟩
  fin_cases i
  all_goals first
    | exact hS _ (hk _) (isPure_cubeBasis _)
    | exact hA
    | exact hB

private theorem beta_u034_u124 : beta K (ub K 0 3 4) (ub K 1 2 4) = 0 :=
  beta_cubeBasis_of_not_disjoint (K := K)
    (I := tripleSet 0 3 4 (by decide) (by decide) (by decide))
    (J := tripleSet 1 2 4 (by decide) (by decide) (by decide)) (by decide)

private theorem beta_u035_u125 : beta K (ub K 0 3 5) (ub K 1 2 5) = 0 :=
  beta_cubeBasis_of_not_disjoint (K := K)
    (I := tripleSet 0 3 5 (by decide) (by decide) (by decide))
    (J := tripleSet 1 2 5 (by decide) (by decide) (by decide)) (by decide)

theorem model2_QfR :
    LinearMap.range (rho K (tInv2 K) - 1) ≤
      Submodule.span K {ξ | ξ ∈ LinearMap.range (rho K (tInv2 K) - 1) ∧
        ∃ p₁ p₂ : Cube K, IsPure K p₁ ∧ IsPure K p₂ ∧ beta K p₁ p₂ = 0 ∧ ξ = p₁ + p₂} := by
  have hr := (ker_range_eq2 (K := K)).2
  have hmem : ∀ j : Fin 8, ranG2 K j ∈ LinearMap.range (rho K (tInv2 K) - 1) := fun j => by
    rw [hr]; exact Submodule.subset_span ⟨j, rfl⟩
  refine hr.le.trans (Submodule.span_mono ?_)
  rintro _ ⟨i, rfl⟩
  refine ⟨hmem i, ?_⟩
  fin_cases i
  · exact ⟨ub K 0 1 2, 0, isPure_cubeBasis _, isPure_zero, map_zero _, (add_zero _).symm⟩
  · exact ⟨ub K 0 2 3, 0, isPure_cubeBasis _, isPure_zero, map_zero _, (add_zero _).symm⟩
  · exact ⟨ub K 0 2 4, 0, isPure_cubeBasis _, isPure_zero, map_zero _, (add_zero _).symm⟩
  · exact ⟨ub K 0 2 5, 0, isPure_cubeBasis _, isPure_zero, map_zero _, (add_zero _).symm⟩
  · exact ⟨ub K 0 4 5, 0, isPure_cubeBasis _, isPure_zero, map_zero _, (add_zero _).symm⟩
  · exact ⟨ub K 2 4 5, 0, isPure_cubeBasis _, isPure_zero, map_zero _, (add_zero _).symm⟩
  · exact ⟨ub K 0 3 4, ub K 1 2 4, isPure_cubeBasis _, isPure_cubeBasis _, beta_u034_u124, rfl⟩
  · exact ⟨ub K 0 3 5, ub K 1 2 5, isPure_cubeBasis _, isPure_cubeBasis _, beta_u035_u125, rfl⟩

theorem model2_P2 [Finite K] (h4 : 4 ≤ Nat.card K) :
    ∃ P : Set (GL (Fin 6) K),
      (∀ u ∈ P, ∃ a b : GL (Fin 6) K, (a : Matrix (Fin 6) (Fin 6) K).det = 1 ∧
        (b : Matrix (Fin 6) (Fin 6) K).det = 1 ∧ a * tInv2 K = tInv2 K * a ∧
        b * tInv2 K = tInv2 K * b ∧ u = ⁅a, b⁆) ∧
      ∀ S : AddSubgroup (Cube K), S ≠ ⊥ → (∀ s ∈ S, s ∈ LinearMap.range (rho K (tInv2 K) - 1)) →
        (∀ u ∈ P, ∀ s ∈ S, rho K u s ∈ S) → ∃ p ∈ S, p ≠ 0 ∧ IsPure K p := by
  refine ⟨Uset2 K, fun u hu => Uset2_comm (by omega) hu, ?_⟩
  intro S hS _ hSinv
  obtain ⟨s, hsS, hs0, hsfix⟩ := exists_fixed_vec_of_gens (K := K) lev2 (by decide) pos2
    (fun i j h => h) S hS (fun i j hij c hP s hs => hSinv _ ⟨i, j, hij, c, hP, rfl⟩ s hs)
  have hz : ∀ (i j : Fin 6) (hij : i ≠ j), pos2 i j → rho K (transvGL K i j hij 1) s = s :=
    fun i j hij hp => hsfix i j hij 1 hp
  obtain ⟨c1, c2, hs_eq⟩ : ∃ c1 c2 : K, s = c1 • ub K 0 2 4 + c2 • ub K 0 2 5 := by
    refine ⟨cfm K s 21, cfm K s 37, ?_⟩
    apply cfm_ext3
    intro m hm hc
    rcases exists_mask3 hm hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | (simp (config := {decide := true}) [cfm_add, cfm_smul, cfm_ub_mask]; done)
    | (rw [cfm_zero_of_fixed pos2 hz _ hm (by decide)]
       simp (config := {decide := true}) [cfm_add, cfm_smul, cfm_ub_mask])
  refine ⟨s, hsS, hs0, ?_⟩
  rw [hs_eq]
  refine ⟨![e K 0, e K 2, c1 • e K 4 + c2 • e K 5], ?_⟩
  rw [ι3_add_thd, ι3_smul_thd, ι3_smul_thd, ι_024, ι_025]

theorem involModel12_t2 [Finite K] (h4 : 4 ≤ Nat.card K) : InvolModel12 K (tInv2 K) where
  P1 := model2_P1
  QfR := model2_QfR
  P3 := model2_P3
  P2 := model2_P2 h4

end Model2

end CFSG.RankThree.GF2n.Smith81.A5Cube
