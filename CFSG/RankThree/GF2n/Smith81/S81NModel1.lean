module

public import CFSG.RankThree.GF2n.Smith81.S81NMask
public import CFSG.RankThree.GF2n.Smith81.S81NComm
public import CFSG.RankThree.GF2n.Smith81.S81NUG
public import CFSG.RankThree.GF2n.Smith81.S81NModelDef


public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open scoped commutatorElement

variable {K : Type*} [Field K]

section Model1

@[expose] def kerG1 (K : Type*) [Field K] : Fin 14 → Cube K :=
  ![ub K 0 1 2, ub K 0 1 3, ub K 0 1 4, ub K 0 1 5, ub K 0 2 3, ub K 0 2 4, ub K 0 2 5,
    ub K 0 3 4, ub K 0 3 5, ub K 0 4 5, ub K 2 3 4, ub K 2 3 5, ub K 2 4 5, ub K 3 4 5]

@[expose] def ranG1 (K : Type*) [Field K] : Fin 6 → Cube K :=
  ![ub K 0 2 3, ub K 0 2 4, ub K 0 2 5, ub K 0 3 4, ub K 0 3 5, ub K 0 4 5]

@[expose] def ranPre1 (K : Type*) [Field K] : Fin 6 → Cube K :=
  ![ub K 1 2 3, ub K 1 2 4, ub K 1 2 5, ub K 1 3 4, ub K 1 3 5, ub K 1 4 5]

@[expose] def kerP1 : Fin 14 → ℕ := ![7, 11, 19, 35, 13, 21, 37, 25, 41, 49, 28, 44, 52, 56]

@[expose] def ranP1 : Fin 6 → ℕ := ![13, 21, 37, 25, 41, 49]

variable [CharP K 2]

theorem F1_kerG (i : Fin 14) : (rho K (tInv1 K) - 1) (kerG1 K i) = 0 := by
  rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  apply cfm_ext
  intro m hm
  rw [rho_tInv1, cfm_rho_X01 _ _ hm]
  fin_cases i <;> interval_cases m <;> simp (config := {decide := true}) [kerG1, cfm_ub]

theorem F1_ranPre (i : Fin 6) : (rho K (tInv1 K) - 1) (ranPre1 K i) = ranG1 K i := by
  rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_iff_eq_add]
  apply cfm_ext
  intro m hm
  rw [rho_tInv1, cfm_rho_X01 _ _ hm, cfm_add]
  fin_cases i <;> interval_cases m <;> simp (config := {decide := true}) [ranPre1, ranG1, cfm_ub]

theorem kerG1_pivots : ∀ i j, cfm K (kerG1 K i) (kerP1 j) = if i = j then (1 : K) else 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp (config := {decide := true}) [kerG1, kerP1, cfm_ub]

theorem ranG1_pivots : ∀ i j, cfm K (ranG1 K i) (ranP1 j) = if i = j then (1 : K) else 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp (config := {decide := true}) [ranG1, ranP1, cfm_ub]

theorem kerP1_card : ∀ j, (mset (kerP1 j)).card = 3 := by
  intro j; fin_cases j <;> decide

theorem ranP1_card : ∀ j, (mset (ranP1 j)).card = 3 := by
  intro j; fin_cases j <;> decide

theorem ker_range_eq1 :
    LinearMap.ker (rho K (tInv1 K) - 1) = Submodule.span K (Set.range (kerG1 K)) ∧
      LinearMap.range (rho K (tInv1 K) - 1) = Submodule.span K (Set.range (ranG1 K)) :=
  ker_range_eq_of_gens (a := 14) (b := 6) (by norm_num) _ (kerG1 K) (ranG1 K) F1_kerG
    (fun i => ⟨ranPre1 K i, F1_ranPre i⟩)
    (linearIndependent_of_pivots_mask _ kerP1 kerP1_card kerG1_pivots)
    (linearIndependent_of_pivots_mask _ ranP1 ranP1_card ranG1_pivots)

theorem isPure_ub (a b d : Fin 6) (hab : a < b) (hbd : b < d) : IsPure K (ub K a b d hab hbd) :=
  isPure_cubeBasis _

theorem model1_P1 :
    LinearMap.ker (rho K (tInv1 K) - 1) ≤
      Submodule.span K {ξ | ξ ∈ LinearMap.ker (rho K (tInv1 K) - 1) ∧ IsPure K ξ} := by
  refine (ker_range_eq1 (K := K)).1.le.trans (Submodule.span_mono ?_)
  rintro _ ⟨i, rfl⟩
  refine ⟨LinearMap.mem_ker.mpr (F1_kerG i), ?_⟩
  fin_cases i <;> exact isPure_cubeBasis _

theorem model1_QfR :
    LinearMap.range (rho K (tInv1 K) - 1) ≤
      Submodule.span K {ξ | ξ ∈ LinearMap.range (rho K (tInv1 K) - 1) ∧
        ∃ p₁ p₂ : Cube K, IsPure K p₁ ∧ IsPure K p₂ ∧ beta K p₁ p₂ = 0 ∧ ξ = p₁ + p₂} := by
  have hr := (ker_range_eq1 (K := K)).2
  refine hr.le.trans (Submodule.span_mono ?_)
  rintro _ ⟨i, rfl⟩
  refine ⟨hr.symm ▸ (Submodule.subset_span ⟨i, rfl⟩ : ranG1 K i ∈ Submodule.span K (Set.range (ranG1 K))), ranG1 K i, 0, ?_, isPure_zero, map_zero _, (add_zero _).symm⟩
  fin_cases i <;> exact isPure_cubeBasis _

def pos1 (i j : Fin 6) : Prop := (i = 0 ∧ 1 ≤ j.val) ∨ (j = 1 ∧ 2 ≤ i.val)

instance (i j : Fin 6) : Decidable (pos1 i j) :=
  inferInstanceAs (Decidable ((i = 0 ∧ 1 ≤ j.val) ∨ (j = 1 ∧ 2 ≤ i.val)))

def InC1 (ξ : Cube K) : Prop :=
  cfm K ξ 14 = 0 ∧ cfm K ξ 22 = 0 ∧ cfm K ξ 38 = 0 ∧ cfm K ξ 26 = 0 ∧ cfm K ξ 42 = 0 ∧
    cfm K ξ 50 = 0

def InR1 (η : Cube K) : Prop :=
  cfm K η 7 = 0 ∧ cfm K η 11 = 0 ∧ cfm K η 19 = 0 ∧ cfm K η 35 = 0 ∧ cfm K η 14 = 0 ∧
    cfm K η 22 = 0 ∧ cfm K η 38 = 0 ∧ cfm K η 26 = 0 ∧ cfm K η 42 = 0 ∧ cfm K η 50 = 0 ∧
    cfm K η 28 = 0 ∧ cfm K η 44 = 0 ∧ cfm K η 52 = 0 ∧ cfm K η 56 = 0

theorem InC1_of_mem_ker {ξ : Cube K} (h : ξ ∈ LinearMap.ker (rho K (tInv1 K) - 1)) : InC1 ξ := by
  rw [(ker_range_eq1 (K := K)).1] at h
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    fin_cases k <;> simp (config := {decide := true}) [InC1, kerG1, cfm_ub_mask]
  | zero => simp [InC1, cfm_zero]
  | add x y _ _ hx hy =>
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hx
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hy
    simp [InC1, cfm_add, a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6]
  | smul c x _ hx =>
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hx
    simp [InC1, cfm_smul, a1, a2, a3, a4, a5, a6]

theorem mem_range_of_InR1 {η : Cube K} (h : InR1 η) : η ∈ LinearMap.range (rho K (tInv1 K) - 1) := by
  rw [(ker_range_eq1 (K := K)).2]
  apply mem_span_of_recon (ranG1 K) ranP1
  apply cfm_ext3
  intro m hm hc
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  rcases exists_mask3 hm hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) [ranG1, ranP1, cfm_ub_mask, cfm_zero, cfm_add, cfm_smul, Fin.sum_univ_succ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]

theorem model1_hUC {u : GL (Fin 6) K} (hu : u ∈ Uset1 K) :
    ∀ ξ ∈ LinearMap.ker (rho K (tInv1 K) - 1),
      rho K u ξ - ξ ∈ LinearMap.range (rho K (tInv1 K) - 1) := by
  obtain ⟨i, j, hij, c, hpos, rfl⟩ := hu
  intro ξ hξ
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := InC1_of_mem_ker hξ
  refine mem_range_of_InR1 ?_
  have hp : pos1 i j := hpos
  unfold pos1 at hp
  fin_cases i <;> fin_cases j <;> simp at hp <;>
    simp (config := {decide := true}) [InR1, cfm_sub, cfm_rho_transv, -Representation.exteriorPower_apply, h1, h2, h3, h4, h5, h6]

theorem model1_hUfix :
    ∀ ξ ∈ LinearMap.ker (rho K (tInv1 K) - 1), (∀ u ∈ Uset1 K, rho K u ξ = ξ) →
      ξ ∈ LinearMap.range (rho K (tInv1 K) - 1) := by
  intro ξ _ hfix
  have hz : ∀ (i j : Fin 6) (hij : i ≠ j), pos1 i j →
      rho K (transvGL K i j hij 1) ξ = ξ := fun i j hij hp => hfix _ ⟨i, j, hij, 1, hp, rfl⟩
  refine mem_range_of_InR1 ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact cfm_zero_of_fixed pos1 hz _ (by norm_num) (by decide)

theorem model1_P3 :
    ∃ U : Set (GL (Fin 6) K), (∀ u ∈ U, (u : Matrix (Fin 6) (Fin 6) K).det = 1) ∧
      (∀ u ∈ U, u * tInv1 K = tInv1 K * u) ∧
      (∀ u ∈ U, ∀ ξ ∈ LinearMap.ker (rho K (tInv1 K) - 1),
        rho K u ξ - ξ ∈ LinearMap.range (rho K (tInv1 K) - 1)) ∧
      (∀ ξ ∈ LinearMap.ker (rho K (tInv1 K) - 1), (∀ u ∈ U, rho K u ξ = ξ) →
        ξ ∈ LinearMap.range (rho K (tInv1 K) - 1)) :=
  ⟨Uset1 K, fun u hu => (Uset1_det_commute hu).1, fun u hu => (Uset1_det_commute hu).2,
    fun u hu => model1_hUC hu, model1_hUfix⟩

theorem model1_P2 [Finite K] (h4 : 4 ≤ Nat.card K) :
    ∃ P : Set (GL (Fin 6) K),
      (∀ u ∈ P, ∃ a b : GL (Fin 6) K, (a : Matrix (Fin 6) (Fin 6) K).det = 1 ∧
        (b : Matrix (Fin 6) (Fin 6) K).det = 1 ∧ a * tInv1 K = tInv1 K * a ∧
        b * tInv1 K = tInv1 K * b ∧ u = ⁅a, b⁆) ∧
      ∀ S : AddSubgroup (Cube K), S ≠ ⊥ → (∀ s ∈ S, s ∈ LinearMap.range (rho K (tInv1 K) - 1)) →
        (∀ u ∈ P, ∀ s ∈ S, rho K u s ∈ S) → ∃ p ∈ S, p ≠ 0 ∧ IsPure K p := by
  refine ⟨Pset1 K, fun u hu => Pset1_comm (by omega) hu, ?_⟩
  intro S hS hSR hSinv
  obtain ⟨s, hsS, hs0, hsfix⟩ := exists_fixed_vec_of_gens (K := K) ![0, 0, 0, 1, 2, 3]
    (by decide) (fun i j => 2 ≤ i.val ∧ i.val < j.val) (by decide) S hS
    (fun i j hij c hP s hs => hSinv _ ⟨i, j, hij, c, hP.1, hP.2, rfl⟩ s hs)
  have hr := (ker_range_eq1 (K := K)).2
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hr ▸ hSR s hsS)
  have hz : ∀ (i j : Fin 6) (hij : i ≠ j), (2 ≤ i.val ∧ i.val < j.val) →
      rho K (transvGL K i j hij 1) s = s := fun i j hij hp => hsfix i j hij 1 hp
  have hs_eq : s = cfm K s 13 • ub K 0 2 3 := by
    apply cfm_ext3
    intro m hm hc'
    rcases exists_mask3 hm hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | (rw [cfm_zero_of_fixed (fun i j => 2 ≤ i.val ∧ i.val < j.val) hz _ hm (by decide)]
       simp [cfm_smul, cfm_ub_mask]; done)
    | (simp [cfm_smul, cfm_ub_mask]; done)
    | (rw [← hc]; simp [ranG1, cfm_add, cfm_smul, cfm_ub_mask, Fin.sum_univ_succ, cfm_zero]; done)
  refine ⟨s, hsS, hs0, ?_⟩
  rw [hs_eq]
  exact (isPure_ub 0 2 3 _ _).smul _

theorem involModel12_t1 [Finite K] (h4 : 4 ≤ Nat.card K) : InvolModel12 K (tInv1 K) where
  P1 := model1_P1
  QfR := model1_QfR
  P3 := model1_P3
  P2 := model1_P2 h4

end Model1

end CFSG.RankThree.GF2n.Smith81.A5Cube
