module

public import CFSG.Quasithin.Vol2.Ch10SecQ34MJ

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

open CFSG.Quasithin Matrix

variable {K : Type} [Field K] [CharP K 2] (a : ℕ)

theorem eq_smul_of_comm_twist [Finite K] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a))
    (f : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K)
    (hherm : ∀ X, IsHerm a X → IsHerm a (f X))
    (hadd : ∀ X Y, IsHerm a X → IsHerm a Y → f (X + Y) = f X + f Y)
    (hU : ∀ t X, IsHerm a X → f (tw a (um t) X) = tw a (um t) (f X))
    (hW : ∀ X, IsHerm a X → f (tw a wm X) = tw a wm (f X)) :
    ∃ μ : K, μ ^ 2 ^ a = μ ∧ ∀ X, IsHerm a X → f X = μ • X := by
  obtain ⟨t₁, ht₁⟩ := exists_trace_eq_one a ha hK
  have h2 : (2 ^ a : ℕ) ≠ 0 := by positivity
  have he11 : ∀ c : K, c ^ 2 ^ a = c → IsHerm a (e11 c) := fun c hc => by
    rw [isHerm_iff]
    simp [e11, hc, zero_pow h2]
  have he22 : ∀ c : K, c ^ 2 ^ a = c → IsHerm a (e22 c) := fun c hc => by
    rw [isHerm_iff]
    simp [e22, hc, zero_pow h2]
  have hom : ∀ t : K, IsHerm a (om a t) := fun t => by
    rw [isHerm_iff]
    simp [om, frob_frob a hK, zero_pow h2]
  set ψ : K → K := fun c => f (e11 c) 0 0 with hψ
  have hA : ∀ c, c ^ 2 ^ a = c → f (e11 c) = e11 (ψ c) := fun c hc =>
    eq_e11_of_fixed a ha hK (hherm _ (he11 c hc)) fun t => by
      rw [← hU t _ (he11 c hc), tw_u_e11]
  have hψq : ∀ c, c ^ 2 ^ a = c → ψ c ^ 2 ^ a = ψ c := fun c hc =>
    ((isHerm_iff a _).mp (hherm _ (he11 c hc))).1
  have hA22 : ∀ c, c ^ 2 ^ a = c → f (e22 c) = e22 (ψ c) := by
    intro c hc
    rw [← tw_w_e11, hW _ (he11 c hc), hA c hc, tw_w_e11]
  have hB : ∀ c r, c ^ 2 ^ a = c → r ^ 2 ^ a = r → f (e11 (c * r)) = e11 (ψ c * r) := by
    intro c r hc hr
    set t := r * t₁ with ht
    have htr : t + t ^ 2 ^ a = r := by rw [ht, frob_mul, hr, ← mul_add, ht₁, mul_one]
    have hT : IsHerm a (tw a (um t) (e22 c)) := isHerm_tw a hK _ (he22 c hc)
    have hA' : IsHerm a (tw a (um t) (e22 c) + e22 c) := isHerm_add a hT (he22 c hc)
    have hfA : f (tw a (um t) (e22 c) + e22 c) = tw a (um t) (e22 (ψ c)) + e22 (ψ c) := by
      rw [hadd _ _ hT (he22 c hc), hU t _ (he22 c hc), hA22 c hc]
    have key : e11 (c * r) = tw a (um 1) (tw a (um t) (e22 c) + e22 c) +
        (tw a (um t) (e22 c) + e22 c) := by
      rw [tw_u_e22, tw_u_aux, htr]
    rw [key, hadd _ _ (isHerm_tw a hK _ hA') hA', hU 1 _ hA', hfA, tw_u_e22, tw_u_aux, htr]
  set μ := ψ 1 with hμ
  have hμq : μ ^ 2 ^ a = μ := hψq 1 (one_pow _)
  have hE11 : ∀ r, r ^ 2 ^ a = r → f (e11 r) = e11 (μ * r) := by
    intro r hr
    have := hB 1 r (one_pow _) hr
    rwa [one_mul] at this
  have hE22 : ∀ r, r ^ 2 ^ a = r → f (e22 r) = e22 (μ * r) := by
    intro r hr
    rw [← tw_w_e11, hW _ (he11 r hr), hE11 r hr, tw_w_e11]
  have hO : ∀ t : K, f (om a t) = μ • om a t := by
    intro t
    have hn : (t * t ^ 2 ^ a) ^ 2 ^ a = t * t ^ 2 ^ a := by
      rw [frob_mul, frob_frob a hK, mul_comm]
    have hsplit : tw a (um t) (e22 1) + e22 1 = e11 (t * t ^ 2 ^ a) + om a t := by
      rw [tw_u_e22]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [e11, om]
    have h1 := hadd (tw a (um t) (e22 1)) (e22 1) (isHerm_tw a hK (um t) (he22 1 (one_pow _)))
      (he22 1 (one_pow _))
    rw [hsplit, hadd _ _ (he11 _ hn) (hom t), hE11 _ hn, hU t _ (he22 1 (one_pow _)),
      hE22 1 (one_pow _), mul_one, tw_u_e22] at h1
    calc f (om a t) = (e11 (μ * (t * t ^ 2 ^ a)) + f (om a t)) - e11 (μ * (t * t ^ 2 ^ a)) := by
          abel
      _ = !![t * μ * t ^ 2 ^ a, t * μ; μ * t ^ 2 ^ a, 0] - e11 (μ * (t * t ^ 2 ^ a)) := by
          rw [h1]
      _ = μ • om a t := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [e11, om] <;> ring
  refine ⟨μ, hμq, fun X hX => ?_⟩
  have hX' := (isHerm_iff a X).mp hX
  have hdec : X = e11 (X 0 0) + e22 (X 1 1) + om a (X 0 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e11, e22, om, hX'.2.2.1]
  rw [hdec, hadd _ _ (isHerm_add a (he11 _ hX'.1) (he22 _ hX'.2.1)) (hom _),
    hadd _ _ (he11 _ hX'.1) (he22 _ hX'.2.1), hE11 _ hX'.1, hE22 _ hX'.2.1, hO]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e11, e22, om]

end CFSG.Quasithin.Vol2.Ch10.SecB.C10P34
