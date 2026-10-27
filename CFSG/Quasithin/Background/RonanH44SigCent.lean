module

public import CFSG.Quasithin.Background.RonanH44Sig
public import CFSG.Quasithin.Background.HFL3PRank

public section

namespace CFSG.Quasithin.RonanH44

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

private theorem sigCent_single_ne_zero (i : Fin 3) : (Pi.single i (1 : K) : Fin 3 → K) ≠ 0 := by
  intro h
  have := congrFun h i
  simp at this

private theorem sigCent_single_01 (i : Fin 3) :
    ∀ a : Fin 3, (Pi.single i (1 : K) : Fin 3 → K) a = 0 ∨
      (Pi.single i (1 : K) : Fin 3 → K) a = 1 := by
  intro a
  by_cases h : a = i <;> simp [Pi.single_apply, h]

private theorem sigCent_sum_single_01 {i j : Fin 3} (hij : i ≠ j) :
    ∀ a : Fin 3, (Pi.single i (1 : K) + Pi.single j (1 : K) : Fin 3 → K) a = 0 ∨
      (Pi.single i (1 : K) + Pi.single j (1 : K) : Fin 3 → K) a = 1 := by
  intro a
  by_cases hi : a = i
  · right
    simp [Pi.single_apply, hi, hij]
  · by_cases hj : a = j
    · right
      simp [Pi.single_apply, hj, hi, Ne.symm hij]
    · left
      simp [Pi.single_apply, hi, hj]

private theorem sigCent_pt_mem_fixV (hK : Nat.card K = (2 ^ n) ^ 2) {v : Fin 3 → K}
    (hv : ∀ a, v a = 0 ∨ v a = 1) : pt hK v ∈ fixV (Subgroup.zpowers (sig n K)) := by
  rw [mem_fixV_sig hK]
  intro i j
  rw [mat_pt, rk1_apply]
  rcases hv i with hi | hi <;> rcases hv j with hj | hj <;> simp [hi, hj]

private theorem sigCent_comp_eq (τ : K ≃+* K) {v : Fin 3 → K}
    (hv : ∀ a, v a = 0 ∨ v a = 1) : (fun a => τ (v a)) = v := by
  funext a
  rcases hv a with h | h <;> simp [h]

private theorem sigCent_exists_scalar (hK : Nat.card K = (2 ^ n) ^ 2)
    {A : Matrix (Fin 3) (Fin 3) K}
    (h1 : ∀ i : Fin 3, pt hK (A *ᵥ Pi.single i 1) = pt hK (Pi.single i 1))
    (h2 : ∀ i j : Fin 3, i ≠ j →
      pt hK (A *ᵥ (Pi.single i 1 + Pi.single j 1)) = pt hK (Pi.single i 1 + Pi.single j 1)) :
    ∃ d : K, d * bar n d = 1 ∧ A = d • 1 := by
  have hcol : ∀ i : Fin 3, ∃ μ : K, A *ᵥ Pi.single i 1 = μ • Pi.single i 1 ∧
      μ * bar n μ = 1 := by
    intro i
    have hr : rk1 n (A *ᵥ Pi.single i 1) = rk1 n (Pi.single i 1) := by
      rw [← mat_pt hK, ← mat_pt hK, h1 i]
    obtain ⟨μ, hμ⟩ := eq_smul_of_rk1_eq (sigCent_single_ne_zero i) hr
    refine ⟨μ, hμ, norm_eq_one_of_pt hK (sigCent_single_ne_zero i) ?_⟩
    rw [← hμ]
    exact h1 i
  choose μ hμ hμn using hcol
  have hpair : ∀ i j : Fin 3, i ≠ j → μ i * bar n (μ j) = 1 := by
    intro i j hij
    have hr : rk1 n (A *ᵥ (Pi.single i 1 + Pi.single j 1)) =
        rk1 n (Pi.single i 1 + Pi.single j 1) := by
      rw [← mat_pt hK, ← mat_pt hK, h2 i j hij]
    rw [Matrix.mulVec_add, hμ i, hμ j] at hr
    have h := congrFun (congrFun hr i) j
    simpa [rk1_apply, Pi.single_apply, hij, Ne.symm hij] using h
  have hμeq : ∀ i j : Fin 3, i ≠ j → μ j = μ i := by
    intro i j hij
    have hμi0 : μ i ≠ 0 := by
      intro h0
      have h := hμn i
      rw [h0, zero_mul] at h
      exact zero_ne_one h
    have hb : bar n (μ j) = bar n (μ i) := by
      apply mul_left_cancel₀ hμi0
      rw [hpair i j hij, hμn i]
    have h := congrArg (bar n) hb
    rwa [bar_bar hK, bar_bar hK] at h
  have hμ0 : ∀ i : Fin 3, μ i = μ 0 := by
    intro i
    by_cases h : i = 0
    · rw [h]
    · exact hμeq 0 i (Ne.symm h)
  have hcolA : ∀ i k : Fin 3, (A *ᵥ Pi.single i 1) k = A k i := fun i k => by
    rw [Matrix.mulVec_single_one]
    rfl
  refine ⟨μ 0, hμn 0, ?_⟩
  ext k i
  have h := congrFun (hμ i) k
  rw [hcolA i k, hμ0 i, Pi.smul_apply, smul_eq_mul] at h
  rw [h]
  simp [Pi.single_apply, Matrix.one_apply]

private theorem sigCent_exists_F_decomp (hK : Nat.card K = (2 ^ n) ^ 2) {ω : K}
    (hbω : bar n ω = 1 + ω) (y : K) :
    ∃ u v : K, bar n u = u ∧ bar n v = v ∧ y = u + v * ω := by
  obtain ⟨v, hv⟩ : ∃ v : K, v = y + bar n y := ⟨_, rfl⟩
  have hbv : bar n v = v := by
    rw [hv, map_add, bar_bar hK, add_comm]
  refine ⟨y + v * ω, v, ?_, hbv, ?_⟩
  · rw [map_add, map_mul, hbv, hbω]
    linear_combination hv + bar n y * (CharTwo.two_eq_zero (R := K))
  · linear_combination (-(v * ω)) * (CharTwo.two_eq_zero (R := K))

private theorem sigCent_eq_one_or_eq_bar (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {τ : K ≃+* K} (hτ : ∀ c : K, bar n c = c → τ c = c) : τ = 1 ∨ τ = bar n := by
  obtain ⟨ω, hω⟩ := exists_trace_one hn hK
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hbω : bar n ω = 1 + ω := by linear_combination hω - ω * h2
  have ha : bar n (ω * bar n ω) = ω * bar n ω := by
    rw [map_mul, bar_bar hK, mul_comm]
  have hpoly : ω ^ 2 + ω + ω * bar n ω = 0 := by
    rw [hbω]
    linear_combination (ω ^ 2 + ω) * h2
  have hs : τ ω ^ 2 + τ ω + ω * bar n ω = 0 := by
    have h := congrArg τ hpoly
    rw [map_add, map_add, map_pow, map_zero, hτ _ ha] at h
    exact h
  have hroot : (τ ω - ω) * (τ ω - (1 + ω)) = 0 := by
    linear_combination hs - hpoly + (-(τ ω) - ω * τ ω + ω + ω ^ 2) * h2
  have hτω : τ ω = ω ∨ τ ω = bar n ω := by
    rcases mul_eq_zero.mp hroot with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (by rw [hbω]; exact sub_eq_zero.mp h)
  rcases hτω with hs1 | hs2
  · left
    refine RingEquiv.ext fun y => ?_
    obtain ⟨u, v, hu, hv, rfl⟩ := sigCent_exists_F_decomp hK hbω y
    simp only [map_add, map_mul, hτ u hu, hτ v hv, hs1]
    rfl
  · right
    refine RingEquiv.ext fun y => ?_
    obtain ⟨u, v, hu, hv, rfl⟩ := sigCent_exists_F_decomp hK hbω y
    simp only [map_add, map_mul, hτ u hu, hτ v hv, hs2, hu, hv]

theorem eq_one_or_eq_sig_of_fix (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {x : MulAut (HMod n K)} (hx : x ∈ norm hK)
    (hfix : ∀ v ∈ fixV (Subgroup.zpowers (sig n K)), x v = v) : x = 1 ∨ x = sig n K := by
  obtain ⟨A, τ, rfl⟩ := exists_eq_rhoT_mul_fldAut hn hK hx
  have h1 : ∀ i : Fin 3, pt hK ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single i 1) =
      pt hK (Pi.single i 1) := by
    intro i
    have h := hfix _ (sigCent_pt_mem_fixV hK (sigCent_single_01 i))
    rw [rhoT_fldAut_pt, sigCent_comp_eq τ (sigCent_single_01 i)] at h
    exact h
  have h2 : ∀ i j : Fin 3, i ≠ j →
      pt hK ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single i 1 + Pi.single j 1)) =
        pt hK (Pi.single i 1 + Pi.single j 1) := by
    intro i j hij
    have h := hfix _ (sigCent_pt_mem_fixV hK (sigCent_sum_single_01 hij))
    rw [rhoT_fldAut_pt, sigCent_comp_eq τ (sigCent_sum_single_01 hij)] at h
    exact h
  obtain ⟨d, hd, hA⟩ := sigCent_exists_scalar hK h1 h2
  have hrhoT : rhoT hK A = 1 := rhoT_eq_one_of_smul hK hA hd
  have hfix' : ∀ v ∈ fixV (Subgroup.zpowers (sig n K)), fldAut τ v = v := by
    intro v hv
    have h := hfix v hv
    rwa [hrhoT, one_mul] at h
  have hτF : ∀ c : K, bar n c = c → τ c = c := by
    intro c hc
    have hM : (conjM n (Matrix.single (0 : Fin 3) (0 : Fin 3) c))ᵀ =
        Matrix.single (0 : Fin 3) (0 : Fin 3) c := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [conjM, Matrix.single_apply, hc]
    have hmem : mkH (Matrix.single (0 : Fin 3) (0 : Fin 3) c) hM ∈
        fixV (Subgroup.zpowers (sig n K)) := by
      rw [mem_fixV_sig hK]
      intro i j
      rw [mat_mkH]
      fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply, hc]
    have h := congrArg mat (hfix' _ hmem)
    rw [mat_fldAut, mat_mkH] at h
    have h00 := congrFun (congrFun h 0) 0
    simpa using h00
  rw [hrhoT, one_mul]
  rcases sigCent_eq_one_or_eq_bar hn hK hτF with rfl | rfl
  · left
    exact fldAut_one
  · right
    rfl

end CFSG.Quasithin.RonanH44
