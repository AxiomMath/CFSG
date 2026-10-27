module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
public import Mathlib.Tactic.Module
public import Mathlib.Combinatorics.SimpleGraph.Hasse

public section
namespace CFSG.StandardType.OrthF3
open TauCeti
@[expose] def ggOrthAdjFork (k : ℕ) (i j : Fin k) : Prop :=
  (i.val + 1 = j.val ∧ j.val + 2 < k) ∨ (j.val + 1 = i.val ∧ i.val + 2 < k) ∨
    (i.val + 3 = k ∧ (j.val + 2 = k ∨ j.val + 1 = k)) ∨ (j.val + 3 = k ∧ (i.val + 2 = k ∨ i.val + 1 = k))
@[expose] def ggOrthAdjPathIso (i j : Fin 5) : Prop := i.val < 4 ∧ j.val < 4 ∧ (i.val + 1 = j.val ∨ j.val + 1 = i.val)
private lemma ct_tya_refl_self {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) {u : V} (hu : Q u ≠ 0) :
    u - (QuadraticMap.polar Q u u / Q u) • u = -u := by
  rw [QuadraticMap.polar_self]
  rw [show (2 • Q u : ZMod 3) = (2 : ZMod 3) * Q u by simp]
  rw [mul_div_cancel_right₀ _ hu]
  module
private lemma ct_tya_refl_eq_of_smul {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) {u v w : V} (hu : Q u ≠ 0) {c : ZMod 3} (hc : c ≠ 0)
    (hvu : v = c • u) :
    w - (QuadraticMap.polar Q u w / Q u) • u
      = w - (QuadraticMap.polar Q v w / Q v) • v := by
  have hu0 : u ≠ 0 := fun h => hu (by simp [h])
  subst hvu
  rw [QuadraticMap.map_smul, QuadraticMap.polar_smul_left, smul_smul]
  congr 1
  rw [smul_left_inj hu0]
  field_simp [hc, hu]
  ring
private lemma ct_tya_comm_of_polar_zero {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) {g h : V ≃ₗ[ZMod 3] V} {u v : V}
    (hg : ∀ w, g w = w - (QuadraticMap.polar Q u w / Q u) • u)
    (hh : ∀ w, h w = w - (QuadraticMap.polar Q v w / Q v) • v)
    (h0 : QuadraticMap.polar Q u v = 0) : g * h = h * g := by
  ext w
  change g (h w) = h (g w)
  rw [hg (h w), hh (g w), hh w, hg w]
  simp [h0, QuadraticMap.polar_comm, sub_eq_add_neg,
    add_assoc, add_comm, add_left_comm]
private lemma ct_tya_pair_linearIndependent {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) {u v : V} (hu : Q u ≠ 0) (hv : Q v ≠ 0)
    (hnot : ∀ c : ZMod 3, v ≠ c • u) : LinearIndependent (ZMod 3) ![u, v] := by
  rw [linearIndependent_fin2]
  change v ≠ 0 ∧ ∀ c : ZMod 3, c • v ≠ u
  constructor
  · intro hv0
    exact hv (by simp [hv0])
  · intro c hc
    have hc0 : c ≠ 0 := by
      intro h0
      apply hu
      rw [← hc, h0, zero_smul, map_zero]
    exact hnot c⁻¹ (by
      calc
        v = c⁻¹ • (c • v) := by rw [inv_smul_smul₀ hc0]
        _ = c⁻¹ • u := by rw [hc])
private lemma ct_tya_coeff_u (A B C : ZMod 3) (hB : B ≠ 0) (hC : C ≠ 0) :
    ((A / B * (A / C) - 1) ^ 2 - A / B * (A / C)) * (A / B * (A / C) - 1) +
        -(A / B) * (A / B * (A / C) - 1 - 1) * (A / C) =
      (A / B * (A / C) - 1) ^ 3 -
        A / B * (A / C) * (2 * (A / B * (A / C) - 1) - 1) := by
  revert A B C
  decide +kernel
private lemma ct_tya_coeff_v (A B C : ZMod 3) (hB : B ≠ 0) (hC : C ≠ 0) :
    ((A / B * (A / C) - 1) ^ 2 - A / B * (A / C)) * (-(A / B)) +
        (-(A / B)) * (A / B * (A / C) - 1 - 1) * (-1) =
      -(A / B) * ((A / B * (A / C)) ^ 2 - A / B * (A / C)) := by
  revert A B C
  decide +kernel
private def ct_tya_sgn (x : Fin 2) : ZMod 3 := if x = 0 then 1 else -1
private lemma ct_tya_two_nsmul_eq_neg (x : ZMod 3) : (2 : ℕ) • x = -x := by
  revert x
  decide +kernel
private lemma ct_tya_sgn_sq (x : Fin 2) : ct_tya_sgn x ^ 2 = 1 := by
  fin_cases x <;> decide
private lemma ct_tya_eq_pm_one (x : ZMod 3) (hx : x ≠ 0) (hx2 : x ^ 2 = 1) :
    x = 1 ∨ x = -1 := by
  revert x
  decide +kernel
private lemma ct_tya_sgn_of_ne_zero (x : ZMod 3) (hx : x ≠ 0) :
    ct_tya_sgn (if x = 1 then (0 : Fin 2) else 1) = x := by
  revert x
  decide +kernel
private lemma ct_tya_sgn_of_pm (x : ZMod 3) (hx : x = 1 ∨ x = -1) :
    ct_tya_sgn (if x = 1 then (0 : Fin 2) else 1) = x := by
  rcases hx with rfl | rfl <;> decide
private lemma ct_tya_edge_norm_aux (qi qj b : ZMod 3) (hi : qi ≠ 0) (hj : qj ≠ 0)
    (hb : b ^ 2 = qi * qj) (hne : b ≠ 0) : qi = qj := by
  revert qi qj b
  decide +kernel
private lemma ct_tya_norm_eq_of_edge {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) {k : ℕ} {v : Fin k → V} {i j : Fin k}
    (hQ : ∀ i, Q (v i) ≠ 0)
    (hb : QuadraticMap.polar Q (v i) (v j) ^ 2 = Q (v i) * Q (v j))
    (hne : QuadraticMap.polar Q (v i) (v j) ≠ 0) : Q (v i) = Q (v j) :=
  ct_tya_edge_norm_aux _ _ _ (hQ i) (hQ j) hb hne
private lemma ct_tya_sgn_edge_of {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) {k : ℕ} {v : Fin k → V} {i j : Fin k} {c : Fin 2}
    (hqi : ct_tya_sgn c = Q (v i)) (hqj : ct_tya_sgn c = Q (v j))
    (hb : QuadraticMap.polar Q (v i) (v j) ^ 2 = Q (v i) * Q (v j))
    (hne : QuadraticMap.polar Q (v i) (v j) ≠ 0) :
    ct_tya_sgn (if QuadraticMap.polar Q (v i) (v j) = 1 then (0 : Fin 2) else 1) =
      QuadraticMap.polar Q (v i) (v j) := by
  apply ct_tya_sgn_of_pm
  apply ct_tya_eq_pm_one
  · exact hne
  · rw [hb, ← hqi, ← hqj]
    simpa [pow_two] using ct_tya_sgn_sq c
private lemma ct_tya_polar_comm_sgn {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) {k : ℕ} {v : Fin k → V} {i j : Fin k} {s : Fin 2}
    (h : QuadraticMap.polar Q (v i) (v j) = ct_tya_sgn s) :
    QuadraticMap.polar Q (v j) (v i) = ct_tya_sgn s :=
  (QuadraticMap.polar_comm Q (v j) (v i)).trans h
private lemma ct_tya_diag_sgn {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) {k : ℕ} {v : Fin k → V} {i : Fin k} {c : ZMod 3}
    (hq : c = Q (v i)) : QuadraticMap.polar Q (v i) (v i) = -c := by
  rw [QuadraticMap.polar_self, ← hq]
  exact ct_tya_two_nsmul_eq_neg c
private lemma ct_tya_path4_decide (c : Fin 2) (s : Fin 3 → Fin 2) (a : Fin 4 → ZMod 3)
    (h : ∀ j, ∑ i, a i * (![![ -ct_tya_sgn c, ct_tya_sgn (s 0), 0, 0],
      ![ct_tya_sgn (s 0), -ct_tya_sgn c, ct_tya_sgn (s 1), 0],
      ![0, ct_tya_sgn (s 1), -ct_tya_sgn c, ct_tya_sgn (s 2)],
      ![0, 0, ct_tya_sgn (s 2), -ct_tya_sgn c]] i j) = 0) : a = 0 := by
  revert c s a
  decide +kernel
private lemma ct_tya_fork4_decide (c : Fin 2) (s : Fin 3 → Fin 2) (a : Fin 4 → ZMod 3)
    (h : ∀ j, ∑ i, a i * (![![ -ct_tya_sgn c, ct_tya_sgn (s 0), 0, 0],
      ![ct_tya_sgn (s 0), -ct_tya_sgn c, ct_tya_sgn (s 1), ct_tya_sgn (s 2)],
      ![0, ct_tya_sgn (s 1), -ct_tya_sgn c, 0],
      ![0, ct_tya_sgn (s 2), 0, -ct_tya_sgn c]] i j) = 0) : a = 0 := by
  revert c s a
  decide +kernel
private lemma ct_tya_fork5_decide (c : Fin 2) (s : Fin 4 → Fin 2) (a : Fin 5 → ZMod 3)
    (h : ∀ j, ∑ i, a i * (![![ -ct_tya_sgn c, ct_tya_sgn (s 0), 0, 0, 0],
      ![ct_tya_sgn (s 0), -ct_tya_sgn c, ct_tya_sgn (s 1), 0, 0],
      ![0, ct_tya_sgn (s 1), -ct_tya_sgn c, ct_tya_sgn (s 2), ct_tya_sgn (s 3)],
      ![0, 0, ct_tya_sgn (s 2), -ct_tya_sgn c, 0],
      ![0, 0, ct_tya_sgn (s 3), 0, -ct_tya_sgn c]] i j) = 0) : a = 0 := by
  revert c s a
  decide +kernel
private lemma ct_tya_pathIso_decide (c d : Fin 2) (s : Fin 3 → Fin 2) (a : Fin 5 → ZMod 3)
    (h : ∀ j, ∑ i, a i * (![![ -ct_tya_sgn c, ct_tya_sgn (s 0), 0, 0, 0],
      ![ct_tya_sgn (s 0), -ct_tya_sgn c, ct_tya_sgn (s 1), 0, 0],
      ![0, ct_tya_sgn (s 1), -ct_tya_sgn c, ct_tya_sgn (s 2), 0],
      ![0, 0, ct_tya_sgn (s 2), -ct_tya_sgn c, 0],
      ![0, 0, 0, 0, -ct_tya_sgn d]] i j) = 0) : a = 0 := by
  revert c d s a
  decide +kernel
private lemma ct_tya_gram_independent {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) {k : ℕ} (v : Fin k → V)
    (hcoeff : ∀ a : Fin k → ZMod 3,
      (∀ j, ∑ i, a i • QuadraticMap.polar Q (v i) (v j) = 0) → a = 0) :
    LinearIndependent (ZMod 3) v ∧
      ∀ u ∈ Submodule.span (ZMod 3) (Set.range v),
        (∀ i, QuadraticMap.polar Q (v i) u = 0) → u = 0 := by
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro a hrel j
    refine congrFun (hcoeff a ?_) j
    intro j
    have := congrArg (fun x => QuadraticMap.polar Q (v j) x) hrel
    simp only [← QuadraticMap.polarBilin_apply_apply, map_sum, smul_eq_mul] at this ⊢
    simpa [QuadraticMap.polar_comm] using this
  · intro u hu horth
    rw [Submodule.mem_span_range_iff_exists_fun] at hu
    obtain ⟨a, ha⟩ := hu
    have hzero : a = 0 := hcoeff a (by
      intro j
      have := horth j
      rw [← ha] at this
      simp only [← QuadraticMap.polarBilin_apply_apply, map_sum, smul_eq_mul] at this ⊢
      simpa [QuadraticMap.polar_comm] using this)
    rw [← ha, hzero]
    simp
theorem ggOrthGram_relations {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (Q : QuadraticForm (ZMod 3) V)
    {g h : V ≃ₗ[ZMod 3] V} {u v : V} (hu : Q u ≠ 0) (hv : Q v ≠ 0)
    (hg : ∀ w, g w = w - (QuadraticMap.polar Q u w / Q u) • u)
    (hh : ∀ w, h w = w - (QuadraticMap.polar Q v w / Q v) • v) :
    (g ≠ h → (g * h = h * g ↔ QuadraticMap.polar Q u v = 0)) ∧
      ((g * h) ^ 3 = 1 → g * h ≠ h * g → QuadraticMap.polar Q u v ^ 2 = Q u * Q v) := by
  constructor
  · intro hne
    constructor
    · intro hcomm
      by_contra ha
      have hgu : g u = -u := by
        rw [hg u]
        exact ct_tya_refl_self Q hu
      have hgv : g v = v - (QuadraticMap.polar Q u v / Q u) • u := by
        rw [hg v]
      have hhu : h u = u - (QuadraticMap.polar Q u v / Q v) • v := by
        rw [hh u, QuadraticMap.polar_comm]
      have hcommu : g (h u) = h (g u) := by
        have := congrArg (fun e : V ≃ₗ[ZMod 3] V => e u) hcomm
        simpa using this
      rw [hhu, hgu, map_neg, hhu] at hcommu
      rw [map_sub, map_smul, hgu, hgv] at hcommu
      have hsmul : (QuadraticMap.polar Q u v / Q v) • (v - (QuadraticMap.polar Q u v / Q u) • u)
          = (QuadraticMap.polar Q u v / Q v) • v
            - ((QuadraticMap.polar Q u v / Q v) * (QuadraticMap.polar Q u v / Q u)) • u := by
        rw [smul_sub, smul_smul]
      rw [hsmul] at hcommu
      have h1 : -((QuadraticMap.polar Q u v / Q v) • v)
          + ((QuadraticMap.polar Q u v / Q v) * (QuadraticMap.polar Q u v / Q u)) • u
          = (QuadraticMap.polar Q u v / Q v) • v := by
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hcommu
      let A : V := (QuadraticMap.polar Q u v / Q v) • v
      let B : V := ((QuadraticMap.polar Q u v / Q v) * (QuadraticMap.polar Q u v / Q u)) • u
      have h2 : B = A + A := by
        calc
          B = (-A + B) + A := by abel
          _ = A + A := by rw [h1]
      have h2' : B = (2 * (QuadraticMap.polar Q u v / Q v)) • v := by
        rw [h2]
        dsimp [A]
        module
      have hcoef : (2 * (QuadraticMap.polar Q u v / Q v)) ≠ 0 := by
        exact mul_ne_zero (by decide) (div_ne_zero ha hv)
      have hv_eq : v = ((2 * (QuadraticMap.polar Q u v / Q v))⁻¹
          * ((QuadraticMap.polar Q u v / Q v) * (QuadraticMap.polar Q u v / Q u))) • u := by
        calc
          v = (2 * (QuadraticMap.polar Q u v / Q v))⁻¹
                • ((2 * (QuadraticMap.polar Q u v / Q v)) • v) := by
              rw [inv_smul_smul₀ hcoef]
          _ = (2 * (QuadraticMap.polar Q u v / Q v))⁻¹
                • (((QuadraticMap.polar Q u v / Q v)
                    * (QuadraticMap.polar Q u v / Q u)) • u) := by
              rw [← h2']
          _ = ((2 * (QuadraticMap.polar Q u v / Q v))⁻¹
                * ((QuadraticMap.polar Q u v / Q v)
                    * (QuadraticMap.polar Q u v / Q u))) • u := by
              rw [smul_smul]
      have hc : ((2 * (QuadraticMap.polar Q u v / Q v))⁻¹
          * ((QuadraticMap.polar Q u v / Q v) * (QuadraticMap.polar Q u v / Q u))) ≠ 0 := by
        exact mul_ne_zero (inv_ne_zero hcoef) (mul_ne_zero (div_ne_zero ha hv) (div_ne_zero ha hu))
      apply hne
      ext w
      rw [hg w, hh w]
      exact ct_tya_refl_eq_of_smul Q hu hc hv_eq
    · intro h0
      exact ct_tya_comm_of_polar_zero Q hg hh h0
  · intro hcube hnc
    have hB : QuadraticMap.polar Q u v ≠ 0 := by
      intro h0
      exact hnc (ct_tya_comm_of_polar_zero Q hg hh h0)
    have hnot : ∀ c : ZMod 3, v ≠ c • u := by
      intro c hc
      have hc0 : c ≠ 0 := by
        intro h0
        apply hv
        rw [hc, h0, zero_smul, map_zero]
      have hgh : g = h := by
        ext w
        rw [hg w, hh w]
        exact ct_tya_refl_eq_of_smul Q hu hc0 hc
      exact hnc (by rw [hgh])
    have hli : LinearIndependent (ZMod 3) ![u, v] :=
      ct_tya_pair_linearIndependent Q hu hv hnot
    let a : ZMod 3 := QuadraticMap.polar Q u v
    let s : ZMod 3 := (a / Q v) * (a / Q u)
    let l : ZMod 3 := s - 1
    let m : ZMod 3 := -(a / Q v)
    let n : ZMod 3 := a / Q u
    let T : V ≃ₗ[ZMod 3] V := g * h
    have hgu : g u = -u := by
      rw [hg u]
      exact ct_tya_refl_self Q hu
    have hgv : g v = v - (a / Q u) • u := by
      dsimp [a]
      rw [hg v]
    have hhu : h u = u - (a / Q v) • v := by
      dsimp [a]
      rw [hh u, QuadraticMap.polar_comm]
    have hTu : T u = l • u + m • v := by
      change g (h u) = l • u + m • v
      rw [hhu, map_sub, map_smul, hgu, hgv]
      dsimp [l, s, m, a]
      module
    have hhv : h v = -v := by
      rw [hh v]
      exact ct_tya_refl_self Q hv
    have hTv : T v = n • u - v := by
      change g (h v) = n • u - v
      rw [hhv, map_neg, hgv]
      dsimp [n, a]
      module
    have hT2u : T (T u) = (l ^ 2 - s) • u + (m * (l - 1)) • v := by
      rw [hTu, map_add, map_smul, map_smul, hTu, hTv]
      dsimp [l, s, m, n, a]
      module
    have hT3u : T (T (T u)) = (l ^ 3 - s * (2 * l - 1)) • u
        + (m * (s ^ 2 - s)) • v := by
      rw [hT2u, map_add, map_smul, map_smul, hTu, hTv]
      match_scalars <;> dsimp [l, s, m, n, a]
      · exact ct_tya_coeff_u (QuadraticMap.polar Q u v) (Q v) (Q u) hv hu
      · exact ct_tya_coeff_v (QuadraticMap.polar Q u v) (Q v) (Q u) hv hu
    have hfixU : T (T (T u)) = u := by
      have h := congrArg (fun e : V ≃ₗ[ZMod 3] V => e u) hcube
      simpa [T, pow_three, mul_assoc] using h
    rw [hT3u] at hfixU
    have hcoef := hli.eq_of_pair (s' := 1) (t' := 0) (by simpa using hfixU)
    have hC : l ^ 3 - s * (2 * l - 1) = 1 := hcoef.1
    have hD : m * (s ^ 2 - s) = 0 := hcoef.2
    have hm : m ≠ 0 := by
      dsimp [m]
      exact neg_ne_zero.mpr (div_ne_zero hB hv)
    have hs0 : s ^ 2 - s = 0 := by
      rcases mul_eq_zero.mp hD with hm0 | hs0
      · exact absurd hm0 hm
      · exact hs0
    have hs : s = 0 ∨ s = 1 := by
      have hprod : s * (s - 1) = 0 := by
        calc
          s * (s - 1) = s ^ 2 - s := by ring
          _ = 0 := hs0
      rcases mul_eq_zero.mp hprod with hs00 | hs01
      · exact Or.inl hs00
      · exact Or.inr (sub_eq_zero.mp hs01)
    have hs1 : s = 1 := by
      rcases hs with hs00 | hs01
      · exfalso
        have h0 : ((0 : ZMod 3) - 1) ^ 3 = 1 := by simpa [hs00, l] using hC
        exact absurd h0 (by decide)
      · exact hs01
    have hsq : a ^ 2 = Q u * Q v := by
      have h := hs1
      dsimp [s] at h
      have hmul := congrArg (fun x : ZMod 3 => x * (Q u * Q v)) h
      field_simp [hu, hv] at hmul
      simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hmul
    dsimp [a] at hsq
    exact hsq
theorem ggOrthGram_path_four {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (Q : QuadraticForm (ZMod 3) V) (v : Fin 4 → V)
    (hQ : ∀ i, Q (v i) ≠ 0)
    (h2 : ∀ i j, i ≠ j → ¬ (SimpleGraph.pathGraph 4).Adj i j → QuadraticMap.polar Q (v i) (v j) = 0)
    (h3 : ∀ i j, i ≠ j → (SimpleGraph.pathGraph 4).Adj i j → QuadraticMap.polar Q (v i) (v j) ^ 2 = Q (v i) * Q (v j) ∧ QuadraticMap.polar Q (v i) (v j) ≠ 0) :
    LinearIndependent (ZMod 3) v ∧ ∀ u ∈ Submodule.span (ZMod 3) (Set.range v), (∀ i, QuadraticMap.polar Q (v i) u = 0) → u = 0 := by
  refine ct_tya_gram_independent Q v ?_
  intro a hsys
  let c : Fin 2 := if Q (v 0) = 1 then 0 else 1
  let s0 : Fin 2 := if QuadraticMap.polar Q (v 0) (v 1) = 1 then 0 else 1
  let s1 : Fin 2 := if QuadraticMap.polar Q (v 1) (v 2) = 1 then 0 else 1
  let s2 : Fin 2 := if QuadraticMap.polar Q (v 2) (v 3) = 1 then 0 else 1
  let s : Fin 3 → Fin 2 := ![s0, s1, s2]
  have hc : ct_tya_sgn c = Q (v 0) := by
    dsimp [c]
    exact ct_tya_sgn_of_ne_zero _ (hQ 0)
  have h01 : Q (v 0) = Q (v 1) :=
    ct_tya_norm_eq_of_edge Q hQ (h3 0 1 (by decide) (by simp [SimpleGraph.pathGraph_adj])).1 (h3 0 1 (by decide) (by simp [SimpleGraph.pathGraph_adj])).2
  have h12 : Q (v 1) = Q (v 2) :=
    ct_tya_norm_eq_of_edge Q hQ (h3 1 2 (by decide) (by simp [SimpleGraph.pathGraph_adj])).1 (h3 1 2 (by decide) (by simp [SimpleGraph.pathGraph_adj])).2
  have h23 : Q (v 2) = Q (v 3) :=
    ct_tya_norm_eq_of_edge Q hQ (h3 2 3 (by decide) (by simp [SimpleGraph.pathGraph_adj])).1 (h3 2 3 (by decide) (by simp [SimpleGraph.pathGraph_adj])).2
  have hq : ∀ i, ct_tya_sgn c = Q (v i) := by
    intro i
    fin_cases i <;> simp [hc, h01, h12, h23]
  have hs0 : ct_tya_sgn (s 0) = QuadraticMap.polar Q (v 0) (v 1) := by
    dsimp [s, s0]
    exact ct_tya_sgn_edge_of Q (hq 0) (hq 1) (h3 0 1 (by decide) (by simp [SimpleGraph.pathGraph_adj])).1 (h3 0 1 (by decide) (by simp [SimpleGraph.pathGraph_adj])).2
  have hs1 : ct_tya_sgn (s 1) = QuadraticMap.polar Q (v 1) (v 2) := by
    dsimp [s, s1]
    exact ct_tya_sgn_edge_of Q (hq 1) (hq 2) (h3 1 2 (by decide) (by simp [SimpleGraph.pathGraph_adj])).1 (h3 1 2 (by decide) (by simp [SimpleGraph.pathGraph_adj])).2
  have hs2 : ct_tya_sgn (s 2) = QuadraticMap.polar Q (v 2) (v 3) := by
    dsimp [s, s2]
    exact ct_tya_sgn_edge_of Q (hq 2) (hq 3) (h3 2 3 (by decide) (by simp [SimpleGraph.pathGraph_adj])).1 (h3 2 3 (by decide) (by simp [SimpleGraph.pathGraph_adj])).2
  let M : Fin 4 → Fin 4 → ZMod 3 :=
    ![![ -ct_tya_sgn c, ct_tya_sgn (s 0), 0, 0],
      ![ct_tya_sgn (s 0), -ct_tya_sgn c, ct_tya_sgn (s 1), 0],
      ![0, ct_tya_sgn (s 1), -ct_tya_sgn c, ct_tya_sgn (s 2)],
      ![0, 0, ct_tya_sgn (s 2), -ct_tya_sgn c]]
  have hs0' : QuadraticMap.polar Q (v 1) (v 0) = ct_tya_sgn (s 0) :=
    ct_tya_polar_comm_sgn Q hs0.symm
  have hs1' : QuadraticMap.polar Q (v 2) (v 1) = ct_tya_sgn (s 1) :=
    ct_tya_polar_comm_sgn Q hs1.symm
  have hs2' : QuadraticMap.polar Q (v 3) (v 2) = ct_tya_sgn (s 2) :=
    ct_tya_polar_comm_sgn Q hs2.symm
  have hdiag : ∀ i, QuadraticMap.polar Q (v i) (v i) = -ct_tya_sgn c :=
    fun i => ct_tya_diag_sgn Q (hq i)
  have hM : ∀ i j : Fin 4, QuadraticMap.polar Q (v i) (v j) = M i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [M, hdiag 0, hdiag 1, hdiag 2, hdiag 3,
        hq 0, hs0, hs0', hs1, hs1', hs2, hs2', h2, SimpleGraph.pathGraph_adj]
  have hsys' : ∀ j, ∑ i, a i * M i j = 0 := by
    intro j
    have := hsys j
    simpa [hM, smul_eq_mul] using this
  exact ct_tya_path4_decide c s a hsys'
theorem ggOrthGram_fork_four {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (Q : QuadraticForm (ZMod 3) V) (v : Fin 4 → V)
    (hQ : ∀ i, Q (v i) ≠ 0)
    (h2 : ∀ i j, i ≠ j → ¬ ggOrthAdjFork 4 i j → QuadraticMap.polar Q (v i) (v j) = 0)
    (h3 : ∀ i j, i ≠ j → ggOrthAdjFork 4 i j → QuadraticMap.polar Q (v i) (v j) ^ 2 = Q (v i) * Q (v j) ∧ QuadraticMap.polar Q (v i) (v j) ≠ 0) :
    LinearIndependent (ZMod 3) v ∧ ∀ u ∈ Submodule.span (ZMod 3) (Set.range v), (∀ i, QuadraticMap.polar Q (v i) u = 0) → u = 0 := by
  refine ct_tya_gram_independent Q v ?_
  intro a hsys
  let c : Fin 2 := if Q (v 0) = 1 then 0 else 1
  let s0 : Fin 2 := if QuadraticMap.polar Q (v 0) (v 1) = 1 then 0 else 1
  let s1 : Fin 2 := if QuadraticMap.polar Q (v 1) (v 2) = 1 then 0 else 1
  let s2 : Fin 2 := if QuadraticMap.polar Q (v 1) (v 3) = 1 then 0 else 1
  let s : Fin 3 → Fin 2 := ![s0, s1, s2]
  have hc : ct_tya_sgn c = Q (v 0) := by
    dsimp [c]
    exact ct_tya_sgn_of_ne_zero _ (hQ 0)
  have h01 : Q (v 0) = Q (v 1) :=
    ct_tya_norm_eq_of_edge Q hQ (h3 0 1 (by decide) (by simp [ggOrthAdjFork])).1 (h3 0 1 (by decide) (by simp [ggOrthAdjFork])).2
  have h12 : Q (v 1) = Q (v 2) :=
    ct_tya_norm_eq_of_edge Q hQ (h3 1 2 (by decide) (by simp [ggOrthAdjFork])).1 (h3 1 2 (by decide) (by simp [ggOrthAdjFork])).2
  have h13 : Q (v 1) = Q (v 3) :=
    ct_tya_norm_eq_of_edge Q hQ (h3 1 3 (by decide) (by simp [ggOrthAdjFork])).1 (h3 1 3 (by decide) (by simp [ggOrthAdjFork])).2
  have h23 : Q (v 2) = Q (v 3) := h12.symm.trans h13
  have hq : ∀ i, ct_tya_sgn c = Q (v i) := by
    intro i
    fin_cases i <;> simp [hc, h01, h12, h23]
  have hs0 : ct_tya_sgn (s 0) = QuadraticMap.polar Q (v 0) (v 1) := by
    dsimp [s, s0]
    exact ct_tya_sgn_edge_of Q (hq 0) (hq 1) (h3 0 1 (by decide) (by simp [ggOrthAdjFork])).1 (h3 0 1 (by decide) (by simp [ggOrthAdjFork])).2
  have hs1 : ct_tya_sgn (s 1) = QuadraticMap.polar Q (v 1) (v 2) := by
    dsimp [s, s1]
    exact ct_tya_sgn_edge_of Q (hq 1) (hq 2) (h3 1 2 (by decide) (by simp [ggOrthAdjFork])).1 (h3 1 2 (by decide) (by simp [ggOrthAdjFork])).2
  have hs2 : ct_tya_sgn (s 2) = QuadraticMap.polar Q (v 1) (v 3) := by
    dsimp [s, s2]
    exact ct_tya_sgn_edge_of Q (hq 1) (hq 3) (h3 1 3 (by decide) (by simp [ggOrthAdjFork])).1 (h3 1 3 (by decide) (by simp [ggOrthAdjFork])).2
  have hs0' : QuadraticMap.polar Q (v 1) (v 0) = ct_tya_sgn (s 0) :=
    ct_tya_polar_comm_sgn Q hs0.symm
  have hs1' : QuadraticMap.polar Q (v 2) (v 1) = ct_tya_sgn (s 1) :=
    ct_tya_polar_comm_sgn Q hs1.symm
  have hs2' : QuadraticMap.polar Q (v 3) (v 1) = ct_tya_sgn (s 2) :=
    ct_tya_polar_comm_sgn Q hs2.symm
  have hdiag : ∀ i, QuadraticMap.polar Q (v i) (v i) = -ct_tya_sgn c :=
    fun i => ct_tya_diag_sgn Q (hq i)
  let M : Fin 4 → Fin 4 → ZMod 3 :=
    ![![ -ct_tya_sgn c, ct_tya_sgn (s 0), 0, 0],
      ![ct_tya_sgn (s 0), -ct_tya_sgn c, ct_tya_sgn (s 1), ct_tya_sgn (s 2)],
      ![0, ct_tya_sgn (s 1), -ct_tya_sgn c, 0],
      ![0, ct_tya_sgn (s 2), 0, -ct_tya_sgn c]]
  have hM : ∀ i j : Fin 4, QuadraticMap.polar Q (v i) (v j) = M i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [M, hdiag 0, hdiag 1, hdiag 2, hdiag 3,
        hq 0, hs0, hs0', hs1, hs1', hs2, hs2', h2, ggOrthAdjFork]
  have hsys' : ∀ j, ∑ i, a i * M i j = 0 := by
    intro j
    have := hsys j
    simpa [hM, smul_eq_mul] using this
  exact ct_tya_fork4_decide c s a hsys'
theorem ggOrthGram_fork_five {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (Q : QuadraticForm (ZMod 3) V) (v : Fin 5 → V)
    (hQ : ∀ i, Q (v i) ≠ 0)
    (h2 : ∀ i j, i ≠ j → ¬ ggOrthAdjFork 5 i j → QuadraticMap.polar Q (v i) (v j) = 0)
    (h3 : ∀ i j, i ≠ j → ggOrthAdjFork 5 i j → QuadraticMap.polar Q (v i) (v j) ^ 2 = Q (v i) * Q (v j) ∧ QuadraticMap.polar Q (v i) (v j) ≠ 0) :
    LinearIndependent (ZMod 3) v ∧ ∀ u ∈ Submodule.span (ZMod 3) (Set.range v), (∀ i, QuadraticMap.polar Q (v i) u = 0) → u = 0 := by
  refine ct_tya_gram_independent Q v ?_
  intro a hsys
  let c : Fin 2 := if Q (v 0) = 1 then 0 else 1
  let s0 : Fin 2 := if QuadraticMap.polar Q (v 0) (v 1) = 1 then 0 else 1
  let s1 : Fin 2 := if QuadraticMap.polar Q (v 1) (v 2) = 1 then 0 else 1
  let s2 : Fin 2 := if QuadraticMap.polar Q (v 2) (v 3) = 1 then 0 else 1
  let s3 : Fin 2 := if QuadraticMap.polar Q (v 2) (v 4) = 1 then 0 else 1
  let s : Fin 4 → Fin 2 := ![s0, s1, s2, s3]
  have hc : ct_tya_sgn c = Q (v 0) := by
    dsimp [c]
    exact ct_tya_sgn_of_ne_zero _ (hQ 0)
  have h01 : Q (v 0) = Q (v 1) :=
    ct_tya_norm_eq_of_edge Q hQ (h3 0 1 (by decide) (by simp [ggOrthAdjFork])).1 (h3 0 1 (by decide) (by simp [ggOrthAdjFork])).2
  have h12 : Q (v 1) = Q (v 2) :=
    ct_tya_norm_eq_of_edge Q hQ (h3 1 2 (by decide) (by simp [ggOrthAdjFork])).1 (h3 1 2 (by decide) (by simp [ggOrthAdjFork])).2
  have h23 : Q (v 2) = Q (v 3) :=
    ct_tya_norm_eq_of_edge Q hQ (h3 2 3 (by decide) (by simp [ggOrthAdjFork])).1 (h3 2 3 (by decide) (by simp [ggOrthAdjFork])).2
  have h24 : Q (v 2) = Q (v 4) :=
    ct_tya_norm_eq_of_edge Q hQ (h3 2 4 (by decide) (by simp [ggOrthAdjFork])).1 (h3 2 4 (by decide) (by simp [ggOrthAdjFork])).2
  have h34 : Q (v 3) = Q (v 4) := h23.symm.trans h24
  have hq : ∀ i, ct_tya_sgn c = Q (v i) := by
    intro i
    fin_cases i <;> simp [hc, h01, h12, h23, h34]
  have hs0 : ct_tya_sgn (s 0) = QuadraticMap.polar Q (v 0) (v 1) := by
    dsimp [s, s0]
    exact ct_tya_sgn_edge_of Q (hq 0) (hq 1) (h3 0 1 (by decide) (by simp [ggOrthAdjFork])).1 (h3 0 1 (by decide) (by simp [ggOrthAdjFork])).2
  have hs1 : ct_tya_sgn (s 1) = QuadraticMap.polar Q (v 1) (v 2) := by
    dsimp [s, s1]
    exact ct_tya_sgn_edge_of Q (hq 1) (hq 2) (h3 1 2 (by decide) (by simp [ggOrthAdjFork])).1 (h3 1 2 (by decide) (by simp [ggOrthAdjFork])).2
  have hs2 : ct_tya_sgn (s 2) = QuadraticMap.polar Q (v 2) (v 3) := by
    dsimp [s, s2]
    exact ct_tya_sgn_edge_of Q (hq 2) (hq 3) (h3 2 3 (by decide) (by simp [ggOrthAdjFork])).1 (h3 2 3 (by decide) (by simp [ggOrthAdjFork])).2
  have hs3 : ct_tya_sgn (s 3) = QuadraticMap.polar Q (v 2) (v 4) := by
    dsimp [s, s3]
    exact ct_tya_sgn_edge_of Q (hq 2) (hq 4) (h3 2 4 (by decide) (by simp [ggOrthAdjFork])).1 (h3 2 4 (by decide) (by simp [ggOrthAdjFork])).2
  have hs0' : QuadraticMap.polar Q (v 1) (v 0) = ct_tya_sgn (s 0) :=
    ct_tya_polar_comm_sgn Q hs0.symm
  have hs1' : QuadraticMap.polar Q (v 2) (v 1) = ct_tya_sgn (s 1) :=
    ct_tya_polar_comm_sgn Q hs1.symm
  have hs2' : QuadraticMap.polar Q (v 3) (v 2) = ct_tya_sgn (s 2) :=
    ct_tya_polar_comm_sgn Q hs2.symm
  have hs3' : QuadraticMap.polar Q (v 4) (v 2) = ct_tya_sgn (s 3) :=
    ct_tya_polar_comm_sgn Q hs3.symm
  have hdiag : ∀ i, QuadraticMap.polar Q (v i) (v i) = -ct_tya_sgn c :=
    fun i => ct_tya_diag_sgn Q (hq i)
  let M : Fin 5 → Fin 5 → ZMod 3 :=
    ![![ -ct_tya_sgn c, ct_tya_sgn (s 0), 0, 0, 0],
      ![ct_tya_sgn (s 0), -ct_tya_sgn c, ct_tya_sgn (s 1), 0, 0],
      ![0, ct_tya_sgn (s 1), -ct_tya_sgn c, ct_tya_sgn (s 2), ct_tya_sgn (s 3)],
      ![0, 0, ct_tya_sgn (s 2), -ct_tya_sgn c, 0],
      ![0, 0, ct_tya_sgn (s 3), 0, -ct_tya_sgn c]]
  have hM : ∀ i j : Fin 5, QuadraticMap.polar Q (v i) (v j) = M i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [M, hdiag 0, hdiag 1, hdiag 2, hdiag 3, hdiag 4,
        hq 0, hs0, hs0', hs1, hs1', hs2, hs2', hs3, hs3', h2, ggOrthAdjFork]
  have hsys' : ∀ j, ∑ i, a i * M i j = 0 := by
    intro j
    have := hsys j
    simpa [hM, smul_eq_mul] using this
  exact ct_tya_fork5_decide c s a hsys'
theorem ggOrthGram_path_iso {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (Q : QuadraticForm (ZMod 3) V) (v : Fin 5 → V)
    (hQ : ∀ i, Q (v i) ≠ 0)
    (h2 : ∀ i j, i ≠ j → ¬ ggOrthAdjPathIso i j → QuadraticMap.polar Q (v i) (v j) = 0)
    (h3 : ∀ i j, i ≠ j → ggOrthAdjPathIso i j → QuadraticMap.polar Q (v i) (v j) ^ 2 = Q (v i) * Q (v j) ∧ QuadraticMap.polar Q (v i) (v j) ≠ 0) :
    LinearIndependent (ZMod 3) v ∧ ∀ u ∈ Submodule.span (ZMod 3) (Set.range v), (∀ i, QuadraticMap.polar Q (v i) u = 0) → u = 0 := by
  refine ct_tya_gram_independent Q v ?_
  intro a hsys
  let c : Fin 2 := if Q (v 0) = 1 then 0 else 1
  let d : Fin 2 := if Q (v 4) = 1 then 0 else 1
  let s0 : Fin 2 := if QuadraticMap.polar Q (v 0) (v 1) = 1 then 0 else 1
  let s1 : Fin 2 := if QuadraticMap.polar Q (v 1) (v 2) = 1 then 0 else 1
  let s2 : Fin 2 := if QuadraticMap.polar Q (v 2) (v 3) = 1 then 0 else 1
  let s : Fin 3 → Fin 2 := ![s0, s1, s2]
  have hc : ct_tya_sgn c = Q (v 0) := by
    dsimp [c]
    exact ct_tya_sgn_of_ne_zero _ (hQ 0)
  have hd : ct_tya_sgn d = Q (v 4) := by
    dsimp [d]
    exact ct_tya_sgn_of_ne_zero _ (hQ 4)
  have h01 : Q (v 0) = Q (v 1) :=
    ct_tya_norm_eq_of_edge Q hQ (h3 0 1 (by decide) (by simp [ggOrthAdjPathIso])).1 (h3 0 1 (by decide) (by simp [ggOrthAdjPathIso])).2
  have h12 : Q (v 1) = Q (v 2) :=
    ct_tya_norm_eq_of_edge Q hQ (h3 1 2 (by decide) (by simp [ggOrthAdjPathIso])).1 (h3 1 2 (by decide) (by simp [ggOrthAdjPathIso])).2
  have h23 : Q (v 2) = Q (v 3) :=
    ct_tya_norm_eq_of_edge Q hQ (h3 2 3 (by decide) (by simp [ggOrthAdjPathIso])).1 (h3 2 3 (by decide) (by simp [ggOrthAdjPathIso])).2
  have hq : ∀ i, (if i = 4 then ct_tya_sgn d else ct_tya_sgn c) = Q (v i) := by
    intro i
    fin_cases i <;> simp [hc, hd, h01, h12, h23]
  have hs0 : ct_tya_sgn (s 0) = QuadraticMap.polar Q (v 0) (v 1) := by
    dsimp [s, s0]
    exact ct_tya_sgn_edge_of Q (hq 0) (hq 1) (h3 0 1 (by decide) (by simp [ggOrthAdjPathIso])).1 (h3 0 1 (by decide) (by simp [ggOrthAdjPathIso])).2
  have hs1 : ct_tya_sgn (s 1) = QuadraticMap.polar Q (v 1) (v 2) := by
    dsimp [s, s1]
    exact ct_tya_sgn_edge_of Q (hq 1) (hq 2) (h3 1 2 (by decide) (by simp [ggOrthAdjPathIso])).1 (h3 1 2 (by decide) (by simp [ggOrthAdjPathIso])).2
  have hs2 : ct_tya_sgn (s 2) = QuadraticMap.polar Q (v 2) (v 3) := by
    dsimp [s, s2]
    exact ct_tya_sgn_edge_of Q (hq 2) (hq 3) (h3 2 3 (by decide) (by simp [ggOrthAdjPathIso])).1 (h3 2 3 (by decide) (by simp [ggOrthAdjPathIso])).2
  have hs0' : QuadraticMap.polar Q (v 1) (v 0) = ct_tya_sgn (s 0) :=
    ct_tya_polar_comm_sgn Q hs0.symm
  have hs1' : QuadraticMap.polar Q (v 2) (v 1) = ct_tya_sgn (s 1) :=
    ct_tya_polar_comm_sgn Q hs1.symm
  have hs2' : QuadraticMap.polar Q (v 3) (v 2) = ct_tya_sgn (s 2) :=
    ct_tya_polar_comm_sgn Q hs2.symm
  have hdiag : ∀ i, QuadraticMap.polar Q (v i) (v i) = -(if i = 4 then ct_tya_sgn d else ct_tya_sgn c) :=
    fun i => ct_tya_diag_sgn Q (hq i)
  let M : Fin 5 → Fin 5 → ZMod 3 :=
    ![![ -ct_tya_sgn c, ct_tya_sgn (s 0), 0, 0, 0],
      ![ct_tya_sgn (s 0), -ct_tya_sgn c, ct_tya_sgn (s 1), 0, 0],
      ![0, ct_tya_sgn (s 1), -ct_tya_sgn c, ct_tya_sgn (s 2), 0],
      ![0, 0, ct_tya_sgn (s 2), -ct_tya_sgn c, 0],
      ![0, 0, 0, 0, -ct_tya_sgn d]]
  have hM : ∀ i j : Fin 5, QuadraticMap.polar Q (v i) (v j) = M i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [M, hdiag 0, hdiag 1, hdiag 2, hdiag 3, hdiag 4,
        hs0, hs0', hs1, hs1', hs2, hs2', h2, ggOrthAdjPathIso]
  have hsys' : ∀ j, ∑ i, a i * M i j = 0 := by
    intro j
    have := hsys j
    simpa [hM, smul_eq_mul] using this
  exact ct_tya_pathIso_decide c d s a hsys'
end CFSG.StandardType.OrthF3
end
