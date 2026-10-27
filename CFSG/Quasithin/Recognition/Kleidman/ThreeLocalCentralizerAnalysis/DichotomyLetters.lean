module

public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.RelatorCases
public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.Presentation

public section

namespace CFSG.Quasithin.Kleidman.ThreeLocal

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

@[expose] def wWord : List (Fin 7 × Bool) :=
  [(5, true), (6, true), (5, false), (6, false), (3, true)]

@[expose] def gWord : List (Fin 7 × Bool) := [(5, true), (6, true)]

@[expose] def powWord (u : List (Fin 7 × Bool)) (n : ℕ) : List (Fin 7 × Bool) :=
  (List.replicate n u).flatten

@[expose] def yInvPow (k : ℕ) : List (Fin 7 × Bool) := List.replicate k (0, false)

@[expose] def wRelator (o k : ℕ) : List (Fin 7 × Bool) := powWord wWord o ++ yInvPow k

@[expose] def gRelator (o k : ℕ) : List (Fin 7 × Bool) := powWord gWord (2 * o) ++ yInvPow k

@[expose] def dichotomyRelators : List (List (Fin 7 × Bool)) :=
  ([3, 4, 5].flatMap fun o => [0, 1, 2].map fun k => wRelator o k) ++
    ([3, 4].flatMap fun o => [0, 1, 2].map fun k => gRelator o k)

section Facts

variable {G : Type*} [Group G]

theorem lift_mk_prod (g : Fin 7 → G) (r : List (Fin 7 × Bool)) :
    FreeGroup.lift g (FreeGroup.mk r) = (r.map fun x => if x.2 then g x.1 else (g x.1)⁻¹).prod := by
  induction r with
  | nil => simp
  | cons x r ih =>
    have e1 : x :: r = [x] ++ r := rfl
    rw [e1, ← FreeGroup.mul_mk, map_mul, ih]
    obtain ⟨i, s⟩ := x
    cases s
    · have : FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ := rfl
      simp [this]
    · have : FreeGroup.mk [(i, true)] = FreeGroup.of i := rfl
      simp [this]

theorem lift_powWord (g : Fin 7 → G) (u : List (Fin 7 × Bool)) (n : ℕ) :
    FreeGroup.lift g (FreeGroup.mk (powWord u n)) =
      (FreeGroup.lift g (FreeGroup.mk u)) ^ n := by
  rw [lift_mk_prod, lift_mk_prod, powWord, List.map_flatten, List.prod_flatten]
  simp [List.map_map, Function.comp_def, List.map_const', List.prod_replicate]

theorem lift_yInvPow (g : Fin 7 → G) (k : ℕ) :
    FreeGroup.lift g (FreeGroup.mk (yInvPow k)) = ((g 0)⁻¹) ^ k := by
  rw [lift_mk_prod, yInvPow]
  simp [List.map_replicate, List.prod_replicate]

theorem lift_append (g : Fin 7 → G) (r s : List (Fin 7 × Bool)) :
    FreeGroup.lift g (FreeGroup.mk (r ++ s)) =
      FreeGroup.lift g (FreeGroup.mk r) * FreeGroup.lift g (FreeGroup.mk s) := by
  rw [← map_mul, FreeGroup.mul_mk]

theorem lift_wWord (g : Fin 7 → G) :
    FreeGroup.lift g (FreeGroup.mk wWord) = g 5 * g 6 * (g 5)⁻¹ * (g 6)⁻¹ * g 3 := by
  rw [lift_mk_prod]
  simp [wWord, mul_assoc]

theorem lift_gWord (g : Fin 7 → G) :
    FreeGroup.lift g (FreeGroup.mk gWord) = g 5 * g 6 := by
  rw [lift_mk_prod]
  simp [gWord]

theorem lift_wRelator (g : Fin 7 → G) (o k : ℕ) :
    FreeGroup.lift g (FreeGroup.mk (wRelator o k)) =
      (g 5 * g 6 * (g 5)⁻¹ * (g 6)⁻¹ * g 3) ^ o * ((g 0)⁻¹) ^ k := by
  rw [wRelator, lift_append, lift_powWord, lift_wWord, lift_yInvPow]

theorem lift_gRelator (g : Fin 7 → G) (o k : ℕ) :
    FreeGroup.lift g (FreeGroup.mk (gRelator o k)) =
      ((g 5 * g 6) ^ 2) ^ o * ((g 0)⁻¹) ^ k := by
  rw [gRelator, lift_append, lift_powWord, lift_gWord, lift_yInvPow, ← pow_mul]

theorem rel_apply' {g : Fin 7 → G}
    (hrel : ∀ r ∈ j3WordsRest, FreeGroup.lift g (FreeGroup.mk r) = 1)
    {r : List (Fin 7 × Bool)} (hr : r ∈ j3WordsRest) :
    (r.map fun x => if x.2 then g x.1 else (g x.1)⁻¹).prod = 1 := by
  rw [← lift_mk_prod]
  exact hrel r hr

theorem comm_of_rel' {y e : G} (he : e * e = 1) (h : y * e * y⁻¹ * e = 1) : e * y = y * e := by
  have h1 : y * e * y⁻¹ = e := by
    have := eq_inv_of_mul_eq_one_left h
    rw [this, inv_eq_of_mul_eq_one_right he]
  calc e * y = (y * e * y⁻¹) * y := by rw [h1]
    _ = y * e := by group

theorem relFacts3 {g : Fin 7 → G}
    (hrel : ∀ r ∈ j3WordsRest, FreeGroup.lift g (FreeGroup.mk r) = 1) :
    g 3 * g 3 = 1 ∧ g 5 * g 5 = 1 ∧ g 5 * g 0 * g 5 = (g 0)⁻¹ ∧ g 3 * g 0 = g 0 * g 3 ∧
      g 6 * g 0 = g 0 * g 6 := by
  have he3 : g 3 * g 3 = 1 := by
    have h := rel_apply' hrel (r := [(3, true), (3, true)]) (by simp [j3WordsRest])
    simpa using h
  have he2 : g 2 * g 2 = 1 := by
    have h := rel_apply' hrel (r := [(2, true), (2, true)]) (by simp [j3WordsRest])
    simpa using h
  have hal : g 5 * g 5 = 1 := by
    have h := rel_apply' hrel (r := [(5, true), (5, true)]) (by simp [j3WordsRest])
    simpa using h
  refine ⟨he3, hal, ?_, ?_, ?_⟩
  · have h := rel_apply' hrel (r := [(0, false), (5, true), (0, false), (5, true)])
      (by simp [j3WordsRest])
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
    simp only [Bool.false_eq_true, ↓reduceIte, mul_one] at h
    have h1 : g 5 * (g 0)⁻¹ * g 5 = g 0 := by
      calc g 5 * (g 0)⁻¹ * g 5 = g 0 * ((g 0)⁻¹ * (g 5 * ((g 0)⁻¹ * g 5))) := by group
        _ = g 0 := by rw [h]; simp
    calc g 5 * g 0 * g 5 = (g 5)⁻¹ * g 0 * (g 5)⁻¹ := by
          rw [inv_eq_of_mul_eq_one_right hal]
      _ = (g 5 * (g 0)⁻¹ * g 5)⁻¹ := by group
      _ = (g 0)⁻¹ := by rw [h1]
  · have h := rel_apply' hrel (r := [(0, true), (3, true), (0, false), (3, true)])
      (by simp [j3WordsRest])
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
    simp only [Bool.false_eq_true, ↓reduceIte, ↓reduceIte, mul_one, mul_assoc] at h
    exact comm_of_rel' he3 (by simpa [mul_assoc] using h)
  · have h19 := rel_apply' hrel (r := [(6, true), (0, true), (6, true), (2, true)])
      (by simp [j3WordsRest])
    have h20 := rel_apply' hrel (r := [(6, false), (6, false), (0, false), (2, true)])
      (by simp [j3WordsRest])
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h19 h20
    simp only [Bool.false_eq_true, ↓reduceIte, mul_one] at h19 h20
    have hB : (g 0)⁻¹ * g 2 = g 6 * g 6 := by
      have h1 := inv_mul_eq_iff_eq_mul.mp h20
      have h2 := inv_mul_eq_iff_eq_mul.mp (show (g 6)⁻¹ * ((g 0)⁻¹ * g 2) = g 6 * 1 from by
        simpa using h1)
      simpa using h2
    have hA : g 6 * g 0 * g 6 = g 2 := by
      have := eq_inv_of_mul_eq_one_left (show g 6 * g 0 * g 6 * g 2 = 1 by
        simpa [mul_assoc] using h19)
      rw [this, inv_eq_of_mul_eq_one_right he2]
    have hC : g 6 * g 0 * g 6 = g 0 * g 6 * g 6 := by
      calc g 6 * g 0 * g 6 = g 2 := hA
        _ = g 0 * ((g 0)⁻¹ * g 2) := by group
        _ = g 0 * (g 6 * g 6) := by rw [hB]
        _ = g 0 * g 6 * g 6 := by simp only [mul_assoc]
    exact mul_right_cancel hC

theorem w_g_facts {g : Fin 7 → G}
    (hrel : ∀ r ∈ j3WordsRest, FreeGroup.lift g (FreeGroup.mk r) = 1) :
    (g 5 * g 6 * (g 5)⁻¹ * (g 6)⁻¹ * g 3) * g 0 = g 0 * (g 5 * g 6 * (g 5)⁻¹ * (g 6)⁻¹ * g 3) ∧
      (g 5 * g 6) * g 0 * (g 5 * g 6)⁻¹ = (g 0)⁻¹ := by
  obtain ⟨he3, he5, h5, h3, h6⟩ := relFacts3 hrel
  have c3 : g 3 * g 0 * (g 3)⁻¹ = g 0 := by rw [h3]; group
  have c6 : g 6 * g 0 * (g 6)⁻¹ = g 0 := by rw [h6]; group
  have c6' : (g 6)⁻¹ * g 0 * g 6 = g 0 := by
    have : g 6 * g 0 = g 0 * g 6 := h6
    calc (g 6)⁻¹ * g 0 * g 6 = (g 6)⁻¹ * (g 0 * g 6) := by group
      _ = (g 6)⁻¹ * (g 6 * g 0) := by rw [this]
      _ = g 0 := by group
  have i5 : (g 5)⁻¹ = g 5 := inv_eq_of_mul_eq_one_right he5
  have c5 : g 5 * g 0 * (g 5)⁻¹ = (g 0)⁻¹ := by rw [i5]; exact h5
  have c5' : (g 5)⁻¹ * g 0 * g 5 = (g 0)⁻¹ := by rw [i5]; exact h5
  have c5i : g 5 * (g 0)⁻¹ * (g 5)⁻¹ = g 0 := by
    have := congrArg (·⁻¹) c5
    simpa [mul_assoc] using this
  have c6i : g 6 * (g 0)⁻¹ * (g 6)⁻¹ = (g 0)⁻¹ := by
    have := congrArg (·⁻¹) c6
    simpa [mul_assoc] using this
  have hw : (g 5 * g 6 * (g 5)⁻¹ * (g 6)⁻¹ * g 3) * g 0 * (g 5 * g 6 * (g 5)⁻¹ * (g 6)⁻¹ * g 3)⁻¹
      = g 0 := by
    calc (g 5 * g 6 * (g 5)⁻¹ * (g 6)⁻¹ * g 3) * g 0 *
          (g 5 * g 6 * (g 5)⁻¹ * (g 6)⁻¹ * g 3)⁻¹
        = g 5 * (g 6 * ((g 5)⁻¹ * ((g 6)⁻¹ * (g 3 * g 0 * (g 3)⁻¹) * g 6) * g 5) *
            (g 6)⁻¹) * (g 5)⁻¹ := by group
      _ = g 0 := by
        rw [c3, c6', c5', c6i, c5i]
  refine ⟨?_, ?_⟩
  · have := hw
    calc (g 5 * g 6 * (g 5)⁻¹ * (g 6)⁻¹ * g 3) * g 0
        = (g 5 * g 6 * (g 5)⁻¹ * (g 6)⁻¹ * g 3) * g 0 *
            (g 5 * g 6 * (g 5)⁻¹ * (g 6)⁻¹ * g 3)⁻¹ * (g 5 * g 6 * (g 5)⁻¹ * (g 6)⁻¹ * g 3) := by
          group
      _ = g 0 * (g 5 * g 6 * (g 5)⁻¹ * (g 6)⁻¹ * g 3) := by rw [hw]
  · calc (g 5 * g 6) * g 0 * (g 5 * g 6)⁻¹ = g 5 * (g 6 * g 0 * (g 6)⁻¹) * (g 5)⁻¹ := by group
      _ = (g 0)⁻¹ := by rw [c6, c5]

end Facts

variable {G : Type} [Group G] [Finite G]

theorem _root_.CFSG.Quasithin.IsTypeH2.exists_dichotomy_relator
    {z : G} (h : IsTypeH2 G z) (hone : involutionClassCount G = 1) {e : Fin 7 → G}
    (hrel : ∀ r ∈ j3WordsRest, FreeGroup.lift e (FreeGroup.mk r) = 1)
    (hy : e 0 ∈ Subgroup.centralizer ({z} : Set G)) (hy3 : orderOf (e 0) = 3) :
    (∃ o ∈ ({3, 4, 5} : Finset ℕ), ∃ k ∈ ({0, 1, 2} : Finset ℕ),
        FreeGroup.lift e (FreeGroup.mk (wRelator o k)) = 1) ∨
      (∃ o ∈ ({3, 4} : Finset ℕ), ∃ k ∈ ({0, 1, 2} : Finset ℕ),
        FreeGroup.lift e (FreeGroup.mk (gRelator o k)) = 1) := by
  obtain ⟨hwc, hgi⟩ := w_g_facts hrel
  have hw : (e 5 * e 6 * (e 5)⁻¹ * (e 6)⁻¹ * e 3) ∈ CK (e 0) := by
    rw [CK, Subgroup.mem_centralizer_singleton_iff]
    exact hwc
  rcases h.relator_cases hone hy hy3 hw hgi with ⟨o, ho, k, hk, hok⟩ | ⟨o, ho, k, hk, hok⟩
  · refine Or.inl ⟨o, ho, k, hk, ?_⟩
    rw [lift_wRelator, hok, inv_pow, mul_inv_cancel]
  · refine Or.inr ⟨o, ho, k, hk, ?_⟩
    rw [lift_gRelator, hok, inv_pow, mul_inv_cancel]

theorem _root_.CFSG.Quasithin.IsTypeH2.exists_mem_dichotomyRelators
    {z : G} (h : IsTypeH2 G z) (hone : involutionClassCount G = 1) {e : Fin 7 → G}
    (hrel : ∀ r ∈ j3WordsRest, FreeGroup.lift e (FreeGroup.mk r) = 1)
    (hy : e 0 ∈ Subgroup.centralizer ({z} : Set G)) (hy3 : orderOf (e 0) = 3) :
    ∃ r ∈ dichotomyRelators, FreeGroup.lift e (FreeGroup.mk r) = 1 := by
  rcases h.exists_dichotomy_relator hone hrel hy hy3 with ⟨o, ho, k, hk, hr⟩ | ⟨o, ho, k, hk, hr⟩
  · refine ⟨wRelator o k, ?_, hr⟩
    simp only [dichotomyRelators, List.mem_append, List.mem_flatMap, List.mem_map]
    refine Or.inl ⟨o, ?_, k, ?_, rfl⟩ <;> simp_all
  · refine ⟨gRelator o k, ?_, hr⟩
    simp only [dichotomyRelators, List.mem_append, List.mem_flatMap, List.mem_map]
    refine Or.inr ⟨o, ?_, k, ?_, rfl⟩ <;> simp_all

end CFSG.Quasithin.Kleidman.ThreeLocal
