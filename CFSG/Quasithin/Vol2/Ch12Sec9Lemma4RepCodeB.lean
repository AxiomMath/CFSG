module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4RepCode
public import Mathlib.Tactic.FinCases

public section

namespace CFSG.Quasithin.H13.GL42

variable {G : Type} [Group G]

theorem evalWord_eq (y₁ y₂ : Code) (w : List (Fin 5)) :
    evalWord y₁ y₂ w = w.foldl (fun g l => g.comp (letter y₁ y₂ l)) idC := rfl

theorem false_of_good {z a p d : G} (hF : Frame z a p d) {T : Subgroup G}
    (hT : ¬ 2 ∣ T.index)
    (hTc : ∀ t ∈ T, HasCode z a p d t idC ∨ HasCode z a p d t tau1 ∨ HasCode z a p d t tau2 ∨
      HasCode z a p d t tau12)
    {y₁ y₂ : G} {c₁ : Fin 16} {q : Fin 16 × Fin 16} {d₂ d₃ : Fin 16}
    (h₁ : c₁ ∈ c1s) (h₂ : q ∈ omegas) (h₃ : d₂ ∈ d2s) (h₄ : d₃ ∈ d3s)
    (hy₁ : HasCode z a p d y₁ (y1Code c₁ q.1 q.2)) (hy₂ : HasCode z a p d y₂ (y2Code d₂ d₃)) :
    False := by
  classical
  set Y₁ := y1Code c₁ q.1 q.2
  set Y₂ := y2Code d₂ d₃
  set P1 := ∃ t ∈ T, HasCode z a p d t tau1
  set P2 := ∃ t ∈ T, HasCode z a p d t tau2
  set P12 := ∃ t ∈ T, HasCode z a p d t tau12
  set S : Bool × Bool × Bool := (decide P1, decide P2, decide P12) with hSdef
  have hS : S ∈ fiveS := by
    by_cases e1 : P1 <;> by_cases e2 : P2 <;> by_cases e12 : P12 <;>
      simp only [hSdef, e1, e2, e12, decide_true, decide_false] <;> try decide
    · exact absurd (by
        obtain ⟨t, ht, htc⟩ := e1
        obtain ⟨t', ht', htc'⟩ := e2
        exact ⟨t * t', T.mul_mem ht ht', tau1_comp_tau2 ▸ htc.mul hF htc'⟩) e12
    · exact absurd (by
        obtain ⟨t, ht, htc⟩ := e1
        obtain ⟨t', ht', htc'⟩ := e12
        exact ⟨t * t', T.mul_mem ht ht', tau1_comp_tau12 ▸ htc.mul hF htc'⟩) e2
    · exact absurd (by
        obtain ⟨t, ht, htc⟩ := e2
        obtain ⟨t', ht', htc'⟩ := e12
        exact ⟨t * t', T.mul_mem ht ht', tau2_comp_tau12 ▸ htc.mul hF htc'⟩) e1
  have hrep : ∀ s ∈ sList S, ∃ t : G, HasCode z a p d t s := by
    intro s hs
    simp only [sList, hSdef, List.mem_cons, List.mem_append] at hs
    rcases hs with rfl | ((hs | hs) | hs)
    · exact ⟨1, hasCode_one z a p d⟩
    · by_cases e : P1
      · obtain ⟨t, -, ht⟩ := e
        simp only [List.mem_ite_nil_right, List.mem_singleton] at hs
        exact ⟨t, hs.2 ▸ ht⟩
      · simp [e] at hs
    · by_cases e : P2
      · obtain ⟨t, -, ht⟩ := e
        simp only [List.mem_ite_nil_right, List.mem_singleton] at hs
        exact ⟨t, hs.2 ▸ ht⟩
      · simp [e] at hs
    · by_cases e : P12
      · obtain ⟨t, -, ht⟩ := e
        simp only [List.mem_ite_nil_right, List.mem_singleton] at hs
        exact ⟨t, hs.2 ▸ ht⟩
      · simp [e] at hs
  let letterG : Fin 5 → G := fun l =>
    if l = 3 then y₁ else if l = 4 then y₂ else
      if h : ∃ t : G, HasCode z a p d t (letter Y₁ Y₂ l) then h.choose else 1
  have hletter : ∀ l, allowed S l = true → HasCode z a p d (letterG l) (letter Y₁ Y₂ l) := by
    intro l hl
    fin_cases l
    · have hm : tau1 ∈ sList S := by
        simp only [allowed, hSdef] at hl
        simp [sList, hSdef, hl]
      obtain ⟨t, ht⟩ := hrep _ hm
      have h : ∃ t : G, HasCode z a p d t (letter Y₁ Y₂ 0) := ⟨t, ht⟩
      simp only [letterG]
      simpa [h] using h.choose_spec
    · have hm : tau2 ∈ sList S := by
        simp only [allowed, hSdef] at hl
        simp [sList, hSdef, hl]
      obtain ⟨t, ht⟩ := hrep _ hm
      have h : ∃ t : G, HasCode z a p d t (letter Y₁ Y₂ 1) := ⟨t, ht⟩
      simp only [letterG]
      simpa [h] using h.choose_spec
    · have hm : tau12 ∈ sList S := by
        simp only [allowed, hSdef] at hl
        simp [sList, hSdef, hl]
      obtain ⟨t, ht⟩ := hrep _ hm
      have h : ∃ t : G, HasCode z a p d t (letter Y₁ Y₂ 2) := ⟨t, ht⟩
      simp only [letterG]
      simpa [h] using h.choose_spec
    · simpa [letterG, letter] using hy₁
    · simpa [letterG, letter] using hy₂
  obtain ⟨w, hw⟩ := exists_good h₁ h₂ h₃ h₄ hS
  simp only [good, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hw
  obtain ⟨⟨⟨hwl, hgS⟩, hg2S⟩, hgN⟩ := hw
  set ev := evalWord Y₁ Y₂ w with hev
  have hfold : ∀ (u : List (Fin 5)) (x : G) (c : Code), HasCode z a p d x c →
      (∀ l ∈ u, allowed S l = true) →
      HasCode z a p d (x * (u.map letterG).prod)
        (u.foldl (fun g l => g.comp (letter Y₁ Y₂ l)) c) := by
    intro u
    induction u with
    | nil => intro x c hx _; simpa using hx
    | cons l u ih =>
      intro x c hx hu
      have := ih (x * letterG l) (c.comp (letter Y₁ Y₂ l))
        (hx.mul hF (hletter l (hu l (by simp)))) (fun l' hl' => hu l' (by simp [hl']))
      simpa [mul_assoc] using this
  set g := (w.map letterG).prod
  have hg : HasCode z a p d g ev := by
    simpa [hev, evalWord_eq] using hfold w 1 idC (hasCode_one z a p d) hwl
  let Q : Subgroup G :=
    { carrier := {x | ∃ s ∈ sList S, HasCode z a p d x s}
      one_mem' := ⟨idC, by simp [sList], hasCode_one z a p d⟩
      mul_mem' := by
        rintro x y ⟨s, hs, hx⟩ ⟨s', hs', hy⟩
        exact ⟨s.comp s', sList_comp_mem S hS s hs s' hs', hx.mul hF hy⟩
      inv_mem' := by
        rintro x ⟨s, hs, hx⟩
        exact ⟨s, hs, hx.inv hF (sList_comp_self S hS s hs)⟩ }
  have hmem : ∀ c : Code, memS S c = true → ∃ s ∈ sList S, s = c := fun c hc => by
    simpa [memS] using hc
  have hTQ : T ≤ Q := by
    intro t ht
    rcases hTc t ht with h | h | h | h
    · exact ⟨idC, by simp [sList], h⟩
    · exact ⟨tau1, by simp [sList, hSdef, show P1 from ⟨t, ht, h⟩], h⟩
    · exact ⟨tau2, by simp [sList, hSdef, show P2 from ⟨t, ht, h⟩], h⟩
    · exact ⟨tau12, by simp [sList, hSdef, show P12 from ⟨t, ht, h⟩], h⟩
  have hgQ : g ∉ Q := by
    rintro ⟨s, hs, hgs⟩
    have hs' : ev ∈ sList S := hgs.unique hF hg ▸ hs
    have : memS S ev = true := by
      simp only [memS, List.any_eq_true, decide_eq_true_eq]
      exact ⟨ev, hs', rfl⟩
    rw [this] at hgS
    exact Bool.noConfusion hgS
  have hg2 : g * g ∈ Q := by
    obtain ⟨s, hs, e⟩ := hmem _ hg2S
    exact ⟨s, hs, e ▸ hg.mul hF hg⟩
  have hgnorm : ∀ x ∈ Q, g * x * g⁻¹ ∈ Q := by
    rintro x ⟨s, hs, hx⟩
    obtain ⟨s', hs', e⟩ := by simpa using hgN s hs
    obtain ⟨t', ht'⟩ := hrep s' hs'
    have hgx := hg.mul hF hx
    have ht'g := ht'.mul hF hg
    have key : ∀ (i : Fin 16) (b : G), coord z a p d i = b →
        g * x * g⁻¹ * b * (g * x * g⁻¹)⁻¹ = t' * b * t'⁻¹ := by
      intro i b hb
      obtain ⟨m, hm⟩ := hg.exists_preimage hF i
      rw [hb] at hm
      calc g * x * g⁻¹ * b * (g * x * g⁻¹)⁻¹ = g * x * (g⁻¹ * b * g) * (g * x)⁻¹ := by group
        _ = g * x * coord z a p d m * (g * x)⁻¹ := by rw [← hm]; group
        _ = coord z a p d ((ev.comp s).app m) := hgx.conj hF m
        _ = coord z a p d ((s'.comp ev).app m) := by rw [e]
        _ = t' * g * coord z a p d m * (t' * g)⁻¹ := (ht'g.conj hF m).symm
        _ = t' * b * t'⁻¹ := by rw [← hm]; group
    obtain ⟨k0, k1, k2, k3⟩ := ht'
    refine ⟨s', hs', ?_, ?_, ?_, ?_⟩
    · rw [key 1 z (coord_one_eq z a p d), k0]
    · rw [key 2 a (coord_two_eq z a p d), k1]
    · rw [key 4 p (coord_four_eq z a p d), k2]
    · rw [key 8 d (coord_eight_eq z a p d), k3]
  exact false_of_index_two hT hTQ hgQ hg2 hgnorm

end CFSG.Quasithin.H13.GL42
