module

public import CFSG.Sporadic.Recognition.JankoWongPresInputs
public import Mathlib

public section

namespace CFSG.Sporadic.Recognition.JankoWong

variable {G : Type*} [Group G]

@[expose] def jwConj (x y : G) : G := y⁻¹ * x * y

@[expose] def jwComm (x y : G) : G := x⁻¹ * y⁻¹ * x * y

structure JWElements (G : Type*) [Group G] where
  a₁ : G
  σ₁ : G
  u : G
  v : G
  v₁ : G
  φ₁ : G

namespace JWElements

variable (e : JWElements G)

abbrev b₁ : G := jwConj e.a₁ e.σ₁

abbrev a₂ : G := jwConj e.a₁ e.u

abbrev σ₂ : G := jwConj e.σ₁ e.u

abbrev b₂ : G := jwConj e.a₂ e.σ₂

abbrev z : G := e.a₁ ^ 2

abbrev φ₂ : G := jwConj e.φ₁ e.v

abbrev φ₃ : G := jwConj e.φ₁ e.a₂

abbrev φ₄ : G := jwConj e.φ₂ e.a₂

@[expose] def gen : Fin 6 → G := ![e.a₁, e.σ₁, e.u, e.v, e.φ₁, e.v₁]

@[expose] def gens : Set G := {e.a₁, e.σ₁, e.u, e.v, e.v₁, e.φ₁}

theorem range_gen : Set.range e.gen = e.gens := by
  ext x
  simp only [Set.mem_range, gens, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [gen]
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨5, rfl⟩, ⟨4, rfl⟩]

end JWElements

structure JWRelations (ι : ℤˣ) (e : JWElements G) : Prop where
  sigma1_cube : e.σ₁ ^ 3 = 1
  b1_sq : e.b₁ ^ 2 = e.z
  a1_by_v : jwConj e.a₁ e.v = e.a₁⁻¹
  b1_by_sigma1 : jwConj e.b₁ e.σ₁ = e.a₁ * e.b₁
  a2_sq : e.a₂ ^ 2 = e.z
  a2_by_v : jwConj e.a₂ e.v = e.a₂⁻¹
  sigma2_by_v : jwConj e.σ₂ e.v = e.σ₂⁻¹
  a1_a2_comm : jwComm e.a₁ e.a₂ = 1
  a1_sigma2_comm : jwComm e.a₁ e.σ₂ = 1
  sigma1_sigma2_comm : jwComm e.σ₁ e.σ₂ = 1
  v_sq : e.v ^ 2 = e.z
  u_sq : e.u ^ 2 = 1
  v_by_u : jwConj e.v e.u = e.v⁻¹
  v1_a2_cube : (e.v₁ * e.a₂) ^ 3 = 1
  v1_u_sq : (e.v₁ * e.u) ^ 2 = e.v
  phi1_by_z : jwConj e.φ₁ e.z = e.φ₁⁻¹
  phi1_by_u : jwConj e.φ₁ e.u = e.φ₁
  phi3_by_sigma2 : jwConj e.φ₃ e.σ₂ = e.φ₁⁻¹ * e.φ₃ * e.σ₁
  phi1_by_phi3 : jwConj e.φ₁ e.φ₃ = e.φ₁ * e.σ₁⁻¹
  phi1_phi4_comm : jwComm e.φ₁ e.φ₄ = 1
  u_z_phi3_cube : (e.u * e.z * e.φ₃) ^ 3 = 1
  u_v_phi3_phi4_cube : (e.u * e.v * e.φ₃⁻¹ * e.φ₄) ^ 3 = 1
  phi3_by_v1 : jwConj e.φ₃ e.v₁ =
    e.σ₁ ^ (-(ι : ℤ)) * e.φ₁⁻¹ * e.φ₃ ^ (-(ι : ℤ)) * e.φ₄ ^ (-(ι : ℤ))

namespace JWElements

variable (e : JWElements G)

@[expose] def eval (w : JWWord) : G :=
  (w.map fun l => if l.2 then e.gen l.1 else (e.gen l.1)⁻¹).prod

theorem eval_nil : e.eval [] = 1 := rfl

theorem eval_append (w₁ w₂ : JWWord) : e.eval (w₁ ++ w₂) = e.eval w₁ * e.eval w₂ := by
  simp [eval]

theorem eval_inv (w : JWWord) : e.eval (jwWInv w) = (e.eval w)⁻¹ := by
  induction w with
  | nil => simp [jwWInv, eval]
  | cons l w ih =>
    have h : jwWInv (l :: w) = jwWInv w ++ [(l.1, !l.2)] := by simp [jwWInv]
    rw [h, eval_append, ih]
    obtain ⟨i, b⟩ := l
    cases b <;> simp [eval]

theorem eval_wg (i : Fin 6) : e.eval (jwWg i) = e.gen i := by simp [eval, jwWg]

theorem eval_conj (x y : JWWord) : e.eval (jwWConj x y) = jwConj (e.eval x) (e.eval y) := by
  simp [jwWConj, jwConj, eval_append, eval_inv, mul_assoc]

theorem eval_comm (x y : JWWord) : e.eval (jwWComm x y) = jwComm (e.eval x) (e.eval y) := by
  simp [jwWComm, jwComm, eval_append, eval_inv, mul_assoc]

theorem eval_pow (w : JWWord) (n : ℕ) : e.eval (jwWPow w n) = (e.eval w) ^ n := by
  induction n with
  | zero => simp [jwWPow, eval]
  | succ n ih => rw [jwWPow, eval_append, ih, pow_succ']

theorem eval_wA1 : e.eval jwWA1 = e.a₁ := eval_wg e 0

theorem eval_wS1 : e.eval jwWS1 = e.σ₁ := eval_wg e 1

theorem eval_wU : e.eval jwWU = e.u := eval_wg e 2

theorem eval_wV : e.eval jwWV = e.v := eval_wg e 3

theorem eval_wF1 : e.eval jwWF1 = e.φ₁ := eval_wg e 4

theorem eval_wV1 : e.eval jwWV1 = e.v₁ := eval_wg e 5

theorem eval_wB1 : e.eval jwWB1 = e.b₁ := by
  simp only [jwWB1, eval_conj, eval_wA1, eval_wS1]

theorem eval_wA2 : e.eval jwWA2 = e.a₂ := by
  simp only [jwWA2, eval_conj, eval_wA1, eval_wU]

theorem eval_wS2 : e.eval jwWS2 = e.σ₂ := by
  simp only [jwWS2, eval_conj, eval_wS1, eval_wU]

theorem eval_wZ : e.eval jwWZ = e.z := by
  simp only [jwWZ, eval_pow, eval_wA1]

theorem eval_wF2 : e.eval jwWF2 = e.φ₂ := by
  simp only [jwWF2, eval_conj, eval_wF1, eval_wV]

theorem eval_wF3 : e.eval jwWF3 = e.φ₃ := by
  simp only [jwWF3, eval_conj, eval_wF1, eval_wA2]

theorem eval_wF4 : e.eval jwWF4 = e.φ₄ := by
  simp only [jwWF4, eval_conj, eval_wF2, eval_wA2]

theorem lift_mk (w : JWWord) : FreeGroup.lift e.gen (FreeGroup.mk w) = e.eval w := by
  rw [FreeGroup.lift_mk]
  simp [eval]

end JWElements

local syntax (name := jwNorm) "jw_norm" (Lean.Parser.Tactic.location)? : tactic

local macro_rules
  | `(tactic| jw_norm $[$loc]?) =>
    `(tactic| simp only [JWElements.eval_pow, JWElements.eval_conj, JWElements.eval_comm,
      JWElements.eval_inv, JWElements.eval_append, JWElements.eval_nil, JWElements.eval_wA1,
      JWElements.eval_wS1, JWElements.eval_wU, JWElements.eval_wV, JWElements.eval_wF1,
      JWElements.eval_wV1, JWElements.eval_wB1, JWElements.eval_wA2, JWElements.eval_wS2,
      JWElements.eval_wZ, JWElements.eval_wF2, JWElements.eval_wF3, JWElements.eval_wF4] $[$loc]?)

theorem JWRelations.eval_pairs {ι : ℤˣ} {e : JWElements G} (h : JWRelations ι e) :
    ∀ p ∈ jwPairs (decide (ι = -1)), e.eval p.1 = e.eval p.2 := by
  have hlast := h.phi3_by_v1
  rcases Int.units_eq_one_or ι with rfl | rfl
  · have hneg : decide ((1 : ℤˣ) = -1) = false := by decide
    rw [hneg]
    intro p hp
    simp only [jwPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · jw_norm; exact h.sigma1_cube
    · jw_norm; exact h.b1_sq
    · jw_norm; exact h.a1_by_v
    · jw_norm; exact h.b1_by_sigma1
    · jw_norm; exact h.a2_sq
    · jw_norm; exact h.a2_by_v
    · jw_norm; exact h.sigma2_by_v
    · jw_norm; exact h.a1_a2_comm
    · jw_norm; exact h.a1_sigma2_comm
    · jw_norm; exact h.sigma1_sigma2_comm
    · jw_norm; exact h.v_sq
    · jw_norm; exact h.u_sq
    · jw_norm; exact h.v_by_u
    · jw_norm; exact h.v1_a2_cube
    · jw_norm; exact h.v1_u_sq
    · jw_norm; exact h.phi1_by_z
    · jw_norm; exact h.phi1_by_u
    · jw_norm; exact h.phi3_by_sigma2
    · jw_norm; exact h.phi1_by_phi3
    · jw_norm; exact h.phi1_phi4_comm
    · jw_norm; exact h.u_z_phi3_cube
    · jw_norm; exact h.u_v_phi3_phi4_cube
    · simp only [Bool.false_eq_true, ↓reduceIte]
      jw_norm
      simpa only [Units.val_one, neg_zero, zpow_neg_one] using hlast
  · have hneg : decide ((-1 : ℤˣ) = -1) = true := by decide
    rw [hneg]
    intro p hp
    simp only [jwPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · jw_norm; exact h.sigma1_cube
    · jw_norm; exact h.b1_sq
    · jw_norm; exact h.a1_by_v
    · jw_norm; exact h.b1_by_sigma1
    · jw_norm; exact h.a2_sq
    · jw_norm; exact h.a2_by_v
    · jw_norm; exact h.sigma2_by_v
    · jw_norm; exact h.a1_a2_comm
    · jw_norm; exact h.a1_sigma2_comm
    · jw_norm; exact h.sigma1_sigma2_comm
    · jw_norm; exact h.v_sq
    · jw_norm; exact h.u_sq
    · jw_norm; exact h.v_by_u
    · jw_norm; exact h.v1_a2_cube
    · jw_norm; exact h.v1_u_sq
    · jw_norm; exact h.phi1_by_z
    · jw_norm; exact h.phi1_by_u
    · jw_norm; exact h.phi3_by_sigma2
    · jw_norm; exact h.phi1_by_phi3
    · jw_norm; exact h.phi1_phi4_comm
    · jw_norm; exact h.u_z_phi3_cube
    · jw_norm; exact h.u_v_phi3_phi4_cube
    · simp only [↓reduceIte]
      jw_norm
      simpa only [Units.val_neg, Units.val_one, neg_neg, zpow_one] using hlast


theorem JWRelations.of_pairs {ι : ℤˣ} {e : JWElements G}
    (h : ∀ p ∈ jwPairs (decide (ι = -1)), e.eval p.1 = e.eval p.2) : JWRelations ι e := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · have := h _ (show (jwWPow jwWS1 3, ([] : JWWord)) ∈
        jwPairs (decide (ι = -1)) by simp [jwPairs])
    dsimp only at this
    jw_norm at this; exact this
  · have := h _ (show (jwWPow jwWB1 2, jwWZ) ∈
        jwPairs (decide (ι = -1)) by simp [jwPairs])
    dsimp only at this
    jw_norm at this; exact this
  · have := h _ (show (jwWConj jwWA1 jwWV, jwWInv jwWA1) ∈
        jwPairs (decide (ι = -1)) by simp [jwPairs])
    dsimp only at this
    jw_norm at this; exact this
  · have := h _ (show (jwWConj jwWB1 jwWS1, jwWA1 ++ jwWB1) ∈
        jwPairs (decide (ι = -1)) by simp [jwPairs])
    dsimp only at this
    jw_norm at this; exact this
  · have := h _ (show (jwWPow jwWA2 2, jwWZ) ∈
        jwPairs (decide (ι = -1)) by simp [jwPairs])
    dsimp only at this
    jw_norm at this; exact this
  · have := h _ (show (jwWConj jwWA2 jwWV, jwWInv jwWA2) ∈
        jwPairs (decide (ι = -1)) by simp [jwPairs])
    dsimp only at this
    jw_norm at this; exact this
  · have := h _ (show (jwWConj jwWS2 jwWV, jwWInv jwWS2) ∈
        jwPairs (decide (ι = -1)) by simp [jwPairs])
    dsimp only at this
    jw_norm at this; exact this
  · have := h _ (show (jwWComm jwWA1 jwWA2, ([] : JWWord)) ∈
        jwPairs (decide (ι = -1)) by simp [jwPairs])
    dsimp only at this
    jw_norm at this; exact this
  · have := h _ (show (jwWComm jwWA1 jwWS2, ([] : JWWord)) ∈
        jwPairs (decide (ι = -1)) by simp [jwPairs])
    dsimp only at this
    jw_norm at this; exact this
  · have := h _ (show (jwWComm jwWS1 jwWS2, ([] : JWWord)) ∈
        jwPairs (decide (ι = -1)) by simp [jwPairs])
    dsimp only at this
    jw_norm at this; exact this
  · have := h _ (show (jwWPow jwWV 2, jwWZ) ∈
        jwPairs (decide (ι = -1)) by simp [jwPairs])
    dsimp only at this
    jw_norm at this; exact this
  · have := h _ (show (jwWPow jwWU 2, ([] : JWWord)) ∈
        jwPairs (decide (ι = -1)) by simp [jwPairs])
    dsimp only at this
    jw_norm at this; exact this
  · have := h _ (show (jwWConj jwWV jwWU, jwWInv jwWV) ∈
        jwPairs (decide (ι = -1)) by simp [jwPairs])
    dsimp only at this
    jw_norm at this; exact this
  · have := h _ (show (jwWPow (jwWV1 ++ jwWA2) 3, ([] : JWWord)) ∈
        jwPairs (decide (ι = -1)) by simp [jwPairs])
    dsimp only at this
    jw_norm at this; exact this
  · have := h _ (show (jwWPow (jwWV1 ++ jwWU) 2, jwWV) ∈
        jwPairs (decide (ι = -1)) by simp [jwPairs])
    dsimp only at this
    jw_norm at this; exact this
  · have := h _ (show (jwWConj jwWF1 jwWZ, jwWInv jwWF1) ∈
        jwPairs (decide (ι = -1)) by simp [jwPairs])
    dsimp only at this
    jw_norm at this; exact this
  · have := h _ (show (jwWConj jwWF1 jwWU, jwWF1) ∈
        jwPairs (decide (ι = -1)) by simp [jwPairs])
    dsimp only at this
    jw_norm at this; exact this
  · have := h _ (show (jwWConj jwWF3 jwWS2, jwWInv jwWF1 ++ jwWF3 ++ jwWS1) ∈
        jwPairs (decide (ι = -1)) by simp [jwPairs])
    dsimp only at this
    jw_norm at this; exact this
  · have := h _ (show (jwWConj jwWF1 jwWF3, jwWF1 ++ jwWInv jwWS1) ∈
        jwPairs (decide (ι = -1)) by simp [jwPairs])
    dsimp only at this
    jw_norm at this; exact this
  · have := h _ (show (jwWComm jwWF1 jwWF4, ([] : JWWord)) ∈
        jwPairs (decide (ι = -1)) by simp [jwPairs])
    dsimp only at this
    jw_norm at this; exact this
  · have := h _ (show (jwWPow (jwWU ++ jwWZ ++ jwWF3) 3, ([] : JWWord)) ∈
        jwPairs (decide (ι = -1)) by simp [jwPairs])
    dsimp only at this
    jw_norm at this; exact this
  · have := h _ (show (jwWPow (jwWU ++ jwWV ++ jwWInv jwWF3 ++ jwWF4) 3, ([] : JWWord)) ∈
        jwPairs (decide (ι = -1)) by simp [jwPairs])
    dsimp only at this
    jw_norm at this; exact this
  · rcases Int.units_eq_one_or ι with rfl | rfl
    · have hneg : decide ((1 : ℤˣ) = -1) = false := by decide
      have := h (jwWConj jwWF3 jwWV1,
          jwWInv jwWS1 ++ jwWInv jwWF1 ++ jwWInv jwWF3 ++ jwWInv jwWF4)
        (by rw [hneg]; simp [jwPairs])
      dsimp only at this
      jw_norm at this
      simpa only [Units.val_one, neg_zero, zpow_neg_one] using this
    · have hneg : decide ((-1 : ℤˣ) = -1) = true := by decide
      have := h (jwWConj jwWF3 jwWV1, jwWS1 ++ jwWInv jwWF1 ++ jwWF3 ++ jwWF4)
        (by rw [hneg]; simp [jwPairs])
      dsimp only at this
      jw_norm at this
      simpa only [Units.val_neg, Units.val_one, neg_neg, zpow_one] using this


end CFSG.Sporadic.Recognition.JankoWong
