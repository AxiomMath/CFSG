module

public import CFSG.YGroups.MarkedWalks
public import CFSG.Monster.B.GSide.HomotopyLocal
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Monster.Tri

open SimpleGraph CFSG.Monster.B.Recog CFSG.Monster.B.GSide CFSG.YGroups

variable {V : Type*} {G : SimpleGraph V}

theorem exists_append_length_eq {u v : V} (p : G.Walk u v) (m : ℕ) (hm : m ≤ p.length) :
    ∃ (w : V) (p₁ : G.Walk u w) (p₂ : G.Walk w v), p₁.length = m ∧ p = p₁.append p₂ := by
  induction m generalizing u with
  | zero => exact ⟨u, .nil, p, rfl, rfl⟩
  | succ m ih =>
    cases p with
    | nil => simp at hm
    | cons h p =>
      simp only [Walk.length_cons] at hm
      obtain ⟨w, p₁, p₂, h₁, h₂⟩ := ih p (by omega)
      exact ⟨w, .cons h p₁, p₂, by simp [h₁], by simp [h₂]⟩

theorem homotopic_nil_of_shorten (Φ : Set V) (k : ℕ)
    (hs : ∀ {u v : V} (p : G.Walk u v), p.length = k + 1 → (∀ x ∈ p.support, x ∈ Φ) →
      ∃ q : G.Walk u v, q.length ≤ k ∧ (∀ x ∈ q.support, x ∈ Φ) ∧ Homotopic p q)
    (hk : ∀ {u : V} (c : G.Walk u u), c.length ≤ k → (∀ x ∈ c.support, x ∈ Φ) →
      Homotopic c .nil) :
    ∀ {u : V} (c : G.Walk u u), (∀ x ∈ c.support, x ∈ Φ) → Homotopic c .nil := by
  suffices key : ∀ (n : ℕ) {u v : V} (p : G.Walk u v), p.length = n →
      (∀ x ∈ p.support, x ∈ Φ) →
      ∃ q : G.Walk u v, q.length ≤ k ∧ (∀ x ∈ q.support, x ∈ Φ) ∧ Homotopic p q by
    intro u c hc
    obtain ⟨q, hq, hqΦ, hpq⟩ := key _ c rfl hc
    exact hpq.trans (hk q hq hqΦ)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u v p hp hpΦ
    by_cases hn : n ≤ k
    · exact ⟨p, hp ▸ hn, hpΦ, Homotopic.refl _⟩
    · obtain ⟨w, p₁, p₂, h₁, h₂⟩ := exists_append_length_eq p (k + 1) (by omega)
      subst h₂
      have hΦ₁ : ∀ x ∈ p₁.support, x ∈ Φ := fun x hx =>
        hpΦ x ((Walk.mem_support_append_iff _ _).2 (Or.inl hx))
      have hΦ₂ : ∀ x ∈ p₂.support, x ∈ Φ := fun x hx =>
        hpΦ x ((Walk.mem_support_append_iff _ _).2 (Or.inr hx))
      obtain ⟨q₁, hq₁, hqΦ₁, hh₁⟩ := hs p₁ h₁ hΦ₁
      have hlen : (q₁.append p₂).length < n := by
        rw [Walk.length_append]
        rw [Walk.length_append] at hp
        omega
      have hΦq : ∀ x ∈ (q₁.append p₂).support, x ∈ Φ := fun x hx => by
        rcases (Walk.mem_support_append_iff _ _).1 hx with hx | hx
        · exact hqΦ₁ x hx
        · exact hΦ₂ x hx
      obtain ⟨q, hq, hqΦ, hh⟩ := ih _ hlen (q₁.append p₂) rfl hΦq
      exact ⟨q, hq, hqΦ, (hh₁.append_right p₂).trans hh⟩

theorem triangulable_of_short4
    (hs : ∀ {u v : V} (p : G.Walk u v), p.length = 4 →
      ∃ q : G.Walk u v, q.length ≤ 3 ∧ Homotopic p q) : Triangulable G := fun _ c =>
  homotopic_nil_of_shorten Set.univ 3
    (fun p hp _ => by
      obtain ⟨q, hq, hpq⟩ := hs p hp
      exact ⟨q, hq, fun _ _ => Set.mem_univ _, hpq⟩)
    (fun c hc _ => homotopic_nil_of_length_le_three c hc) c fun _ _ => Set.mem_univ _

private theorem isCycle_cons_of_isPath {u w : V} (h : G.Adj u w) (t : G.Walk w u)
    (ht : t.IsPath) (hlen : 2 ≤ t.length) : (Walk.cons h t).IsCycle := by
  rw [Walk.cons_isCycle_iff]
  refine ⟨ht, ?_⟩
  cases t with
  | nil => simp at hlen
  | @cons _ x _ h' t' =>
    rw [Walk.cons_isPath_iff] at ht
    obtain ⟨ht', hw⟩ := ht
    have hxu : x ≠ u := by
      cases t' with
      | nil => simp at hlen
      | cons h'' t'' =>
        rw [Walk.cons_isPath_iff] at ht'
        exact fun hxu => ht'.2 (hxu ▸ t''.end_mem_support)
    rw [Walk.edges_cons, List.mem_cons, not_or]
    refine ⟨fun he => ?_, fun he => hw (t'.snd_mem_support_of_mem_edges he)⟩
    rcases Sym2.eq_iff.1 he with ⟨h₁, -⟩ | ⟨h₁, -⟩
    · exact h.ne h₁
    · exact hxu h₁.symm

theorem homotopic_bypass_supp [DecidableEq V] (Φ : Set V) {L : ℕ}
    (hcyc : ∀ (x : V) (c : G.Walk x x), c.IsCycle → c.length ≤ L →
      (∀ y ∈ c.support, y ∈ Φ) → Homotopic c .nil)
    {u v : V} (p : G.Walk u v) (hp : p.length ≤ L) (hpΦ : ∀ x ∈ p.support, x ∈ Φ) :
    Homotopic p p.bypass := by
  induction p with
  | nil => exact Homotopic.refl _
  | @cons u w v h p ih =>
    rw [Walk.length_cons] at hp
    have hpΦ' : ∀ x ∈ p.support, x ∈ Φ := fun x hx => hpΦ x (by simp [hx])
    have ih' := ih (by omega) hpΦ'
    simp only [Walk.bypass]
    split_ifs with hs
    · have htpath : (p.bypass.takeUntil u hs).IsPath := p.bypass_isPath.takeUntil hs
      have htlen : (p.bypass.takeUntil u hs).length ≤ p.length :=
        (p.bypass.length_takeUntil_le_length hs).trans p.length_bypass_le_length
      have htΦ : ∀ x ∈ (p.bypass.takeUntil u hs).support, x ∈ Φ := fun x hx =>
        hpΦ' x (p.support_bypass_subset_support
          (p.bypass.support_takeUntil_subset_support hs hx))
      have hc : Homotopic (Walk.cons h (p.bypass.takeUntil u hs)) .nil := by
        rcases Nat.lt_or_ge (p.bypass.takeUntil u hs).length 2 with hlt | hge
        · exact homotopic_nil_of_length_le_three _ (by rw [Walk.length_cons]; omega)
        · refine hcyc _ _ (isCycle_cons_of_isPath h _ htpath hge)
            (by rw [Walk.length_cons]; omega) fun x hx => ?_
          rw [Walk.support_cons, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hpΦ _ (by simp)
          · exact htΦ x hx
      have h₂ := hc.append_right (p.bypass.dropUntil u hs)
      rw [Walk.cons_append, Walk.take_spec, Walk.nil_append] at h₂
      exact (ih'.cons h).trans h₂
    · exact ih'.cons h

theorem homotopic_nil_of_forall_isCycle_supp (Φ : Set V) {L : ℕ}
    (hcyc : ∀ (x : V) (c : G.Walk x x), c.IsCycle → c.length ≤ L →
      (∀ y ∈ c.support, y ∈ Φ) → Homotopic c .nil)
    {u : V} (p : G.Walk u u) (hp : p.length ≤ L) (hpΦ : ∀ x ∈ p.support, x ∈ Φ) :
    Homotopic p .nil := by
  classical
  have h := homotopic_bypass_supp Φ hcyc p hp hpΦ
  rwa [Walk.eq_nil_iff_nil.2 (Walk.isPath_iff_nil.1 p.bypass_isPath)] at h

theorem homotopic_of_length_add_le {L : ℕ}
    (h : ∀ (u : V) (c : G.Walk u u), c.length ≤ L → Homotopic c .nil) {u v : V}
    (p q : G.Walk u v) (hpq : p.length + q.length ≤ L) : Homotopic p q :=
  homotopic_iff_append_reverse_nil.2 (h _ _ (by simpa using hpq))

theorem pentagon_parity (a b c d e : Prop)
    (h : ¬(a ∧ d) ∧ ¬(b ∧ e) ∧ ¬(c ∧ a) ∧ ¬(d ∧ b) ∧ ¬(e ∧ c)) :
    (¬a ∧ ¬d) ∨ (¬b ∧ ¬e) ∨ (¬c ∧ ¬a) ∨ (¬d ∧ ¬b) ∨ (¬e ∧ ¬c) := by
  tauto

theorem homotopic_nil_pent_rotate {x₀ x₁ x₂ x₃ x₄ : V} (h₀₁ : G.Adj x₀ x₁) (h₁₂ : G.Adj x₁ x₂)
    (h₂₃ : G.Adj x₂ x₃) (h₃₄ : G.Adj x₃ x₄) (h₄₀ : G.Adj x₄ x₀)
    (h : Homotopic (.cons h₁₂ (.cons h₂₃ (.cons h₃₄ (.cons h₄₀ (.cons h₀₁ .nil)))) :
      G.Walk x₁ x₁) .nil) :
    Homotopic (.cons h₀₁ (.cons h₁₂ (.cons h₂₃ (.cons h₃₄ (.cons h₄₀ .nil)))) : G.Walk x₀ x₀)
      .nil := by
  have := (homotopic_nil_append_comm (.cons h₀₁ .nil : G.Walk x₀ x₁)
    (.cons h₁₂ (.cons h₂₃ (.cons h₃₄ (.cons h₄₀ .nil))))).2
  simp only [Walk.cons_append, Walk.nil_append] at this
  exact this h

end CFSG.Monster.Tri
