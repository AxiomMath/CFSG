module

public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertKac

public section

namespace CFSG.StandardType.StepTwoToralCert

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem tcAlcAux_complete (θ : List ℕ) (hθ : ∀ t ∈ θ, 0 < t) (b : ℕ) (μ : List ℕ)
    (hlen : μ.length = θ.length) (hsum : (List.zipWith (· * ·) θ μ).sum ≤ b) :
    μ ∈ tcAlcAux θ b := by
  induction θ generalizing b μ with
  | nil =>
    cases μ with
    | nil => simp [tcAlcAux]
    | cons _ _ => simp at hlen
  | cons t ts ih =>
    cases μ with
    | nil => simp at hlen
    | cons v μ' =>
      have ht : 0 < t := hθ t List.mem_cons_self
      have hts : ∀ s ∈ ts, 0 < s := fun s hs => hθ s (List.mem_cons_of_mem _ hs)
      simp only [List.zipWith_cons_cons, List.sum_cons] at hsum
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [tcAlcAux, List.mem_flatMap]
      refine ⟨v, ?_, List.mem_map.2 ⟨μ', ih hts (b - t * v) μ' hlen ?_, rfl⟩⟩
      · rw [List.mem_range, Nat.lt_succ_iff, Nat.le_div_iff_mul_le ht, Nat.mul_comm]
        omega
      · omega

theorem tcA_zipWith_ofFn_sum {n : ℕ} (a b : Fin n → ℕ) :
    (List.zipWith (· * ·) (List.ofFn a) (List.ofFn b)).sum = ∑ i, a i * b i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.zipWith_cons_cons, List.sum_cons, ih,
      Fin.sum_univ_succ]

theorem tcA_theta_toList (τ : Tag) :
    (tcTheta τ).toList.map Int.toNat =
      List.ofFn fun i : Fin τ.rank => (tcEnt (tcTheta τ) i).toNat := by
  cases τ <;> rfl

theorem mem_tcAlcove {τ : Tag} {p : ℕ} {μ : Fin τ.rank → ℤ} (hμ : (kacOf τ).IsNormal p μ) :
    Array.ofFn μ ∈ tcAlcove τ p := by
  obtain ⟨hnn, hdot⟩ := hμ
  have hμ' : ∀ i, (((μ i).toNat : ℕ) : ℤ) = μ i := fun i => Int.toNat_of_nonneg (hnn i)
  refine List.mem_map.2 ⟨List.ofFn fun i => (μ i).toNat, ?_, ?_⟩
  · rw [tcA_theta_toList]
    refine tcAlcAux_complete _ ?_ p _ (by simp) ?_
    · intro t ht
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ht
      exact Int.lt_toNat.2 (tcTheta_pos τ i)
    · rw [tcA_zipWith_ofFn_sum]
      have h1 : ((∑ i : Fin τ.rank, (tcEnt (tcTheta τ) i).toNat * (μ i).toNat : ℕ) : ℤ)
          ≤ p := by
        push_cast
        calc ∑ i : Fin τ.rank, ((tcEnt (tcTheta τ) i).toNat : ℤ) * ((μ i).toNat : ℤ)
            = ∑ i : Fin τ.rank, (kacOf τ).θ i * μ i := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Int.toNat_of_nonneg (tcTheta_pos τ i).le, hμ', kacOf_θ_apply]
          _ ≤ p := hdot
      exact_mod_cast h1
  · simp [List.map_ofFn, Function.comp_def, hμ']

end CFSG.StandardType.StepTwoToralCert
