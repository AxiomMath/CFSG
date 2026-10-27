module

public import CFSG.Monster.Tri.ASegInvolutions

public section

namespace CFSG.Monster.Tri

open SimpleGraph CFSG.Monster.B.Recog CFSG.Monster.B.GSide CFSG.YGroups

variable {V I : Type*} {Γ : SimpleGraph V}

abbrev walk4 {x₀ x₁ x₂ x₃ x₄ : V} (h₀₁ : Γ.Adj x₀ x₁) (h₁₂ : Γ.Adj x₁ x₂) (h₂₃ : Γ.Adj x₂ x₃)
    (h₃₄ : Γ.Adj x₃ x₄) : Γ.Walk x₀ x₄ :=
  .cons h₀₁ (.cons h₁₂ (.cons h₂₃ (.cons h₃₄ .nil)))

theorem short4_of_close
    (h5 : ∀ (u : V) (c : Γ.Walk u u), c.length ≤ 5 → Homotopic c .nil)
    {x₀ x₁ x₂ x₃ x₄ : V} (h₀₁ : Γ.Adj x₀ x₁) (h₁₂ : Γ.Adj x₁ x₂) (h₂₃ : Γ.Adj x₂ x₃)
    (h₃₄ : Γ.Adj x₃ x₄)
    (hc : (x₀ = x₂ ∨ Γ.Adj x₀ x₂) ∨ (x₁ = x₃ ∨ Γ.Adj x₁ x₃) ∨ (x₂ = x₄ ∨ Γ.Adj x₂ x₄) ∨
      (x₀ = x₃ ∨ Γ.Adj x₀ x₃) ∨ (x₁ = x₄ ∨ Γ.Adj x₁ x₄) ∨ (x₀ = x₄ ∨ Γ.Adj x₀ x₄)) :
    ∃ q : Γ.Walk x₀ x₄, q.length ≤ 3 ∧ Homotopic (walk4 h₀₁ h₁₂ h₂₃ h₃₄) q := by
  rcases hc with hc | hc | hc | hc | hc | hc
  · obtain ⟨s, hs⟩ := exists_spoke hc
    have e : Homotopic (.cons h₀₁ (.cons h₁₂ .nil) : Γ.Walk x₀ x₂) s :=
      homotopic_of_length_add_le h5 _ _ (by simp; omega)
    refine ⟨s.append (.cons h₂₃ (.cons h₃₄ .nil)), by simp; omega, ?_⟩
    simpa using e.append_right (.cons h₂₃ (.cons h₃₄ .nil))
  · obtain ⟨s, hs⟩ := exists_spoke hc
    have e : Homotopic (.cons h₁₂ (.cons h₂₃ .nil) : Γ.Walk x₁ x₃) s :=
      homotopic_of_length_add_le h5 _ _ (by simp; omega)
    refine ⟨.cons h₀₁ (s.append (.cons h₃₄ .nil)), by simp; omega, ?_⟩
    simpa using (e.append_right (.cons h₃₄ .nil)).cons h₀₁
  · obtain ⟨s, hs⟩ := exists_spoke hc
    have e : Homotopic (.cons h₂₃ (.cons h₃₄ .nil) : Γ.Walk x₂ x₄) s :=
      homotopic_of_length_add_le h5 _ _ (by simp; omega)
    exact ⟨.cons h₀₁ (.cons h₁₂ s), by simp; omega, (e.cons h₁₂).cons h₀₁⟩
  · obtain ⟨s, hs⟩ := exists_spoke hc
    have e : Homotopic (.cons h₀₁ (.cons h₁₂ (.cons h₂₃ .nil)) : Γ.Walk x₀ x₃) s :=
      homotopic_of_length_add_le h5 _ _ (by simp; omega)
    refine ⟨s.append (.cons h₃₄ .nil), by simp; omega, ?_⟩
    simpa using e.append_right (.cons h₃₄ .nil)
  · obtain ⟨s, hs⟩ := exists_spoke hc
    have e : Homotopic (.cons h₁₂ (.cons h₂₃ (.cons h₃₄ .nil)) : Γ.Walk x₁ x₄) s :=
      homotopic_of_length_add_le h5 _ _ (by simp; omega)
    exact ⟨.cons h₀₁ s, by simp; omega, e.cons h₀₁⟩
  · obtain ⟨s, hs⟩ := exists_spoke hc
    exact ⟨s, hs.trans (by norm_num), homotopic_of_length_add_le h5 _ _ (by simp; omega)⟩

variable (A : CommStruct Γ I)

theorem exists_cen_of_walk_le_two {x y : V} (q : Γ.Walk x y) (hq : q.length ≤ 2) :
    ∃ b, A.cen (A.ι x) b ∧ A.cen (A.ι y) b := by
  cases q with
  | nil => exact ⟨x, A.cen_refl x, A.cen_refl x⟩
  | cons h q =>
    cases q with
    | nil => exact ⟨_, A.cen_refl _, A.cen_of_adj _ _ h.symm⟩
    | cons h' q =>
      cases q with
      | nil => exact ⟨_, A.cen_of_adj _ _ h, A.cen_of_adj _ _ h'.symm⟩
      | cons _ _ => simp at hq

section Case1

variable (H : ASegHyp0 A)

include H

theorem short4_case1 {x₀ x₁ x₂ x₃ x₄ : V} (h₀₁ : Γ.Adj x₀ x₁) (h₁₂ : Γ.Adj x₁ x₂)
    (h₂₃ : Γ.Adj x₂ x₃) (h₃₄ : Γ.Adj x₃ x₄) {b : V} (hb₀ : A.cen (A.ι x₀) b)
    (hb₃ : A.cen (A.ι x₃) b) :
    ∃ q : Γ.Walk x₀ x₄, q.length ≤ 3 ∧ Homotopic (walk4 h₀₁ h₁₂ h₂₃ h₃₄) q := by
  have key : ∀ (y w : V), (y = w ∨ Γ.Adj y w) → A.cen (A.ι y) b →
      ∃ z ∈ closedNbhd Γ b, z = w ∨ Γ.Adj z w := by
    intro y w hy hyb
    rcases H.h814 b w ⟨y, hy, A.cen_symm _ _ hyb⟩ with hbw | hbw | ⟨t, hbt, htw⟩
    · exact ⟨b, Or.inl rfl, Or.inl hbw⟩
    · exact ⟨b, Or.inl rfl, Or.inr hbw⟩
    · exact ⟨t, Or.inr hbt.symm, Or.inr htw⟩
  refine homotopic_short_of_cone (fun _ c hc => homotopic_nil_of_length_le_five A H c hc) b
    (walk4 h₀₁ h₁₂ h₂₃ h₃₄) ?_ ?_
  · intro w hw
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact key _ _ (Or.inl rfl) hb₀
    · exact key _ _ (Or.inr h₀₁) hb₀
    · exact key _ _ (Or.inr h₂₃.symm) hb₃
    · exact key _ _ (Or.inl rfl) hb₃
    · exact key _ _ (Or.inr h₃₄) hb₃
  · intro z hz
    rcases H.h814 x₀ z ⟨b, hz.imp Eq.symm SimpleGraph.Adj.symm, hb₀⟩ with h | h | ⟨t, h₁, h₂⟩
    · subst h
      exact ⟨.nil, by simp⟩
    · exact ⟨.cons h .nil, by simp⟩
    · exact ⟨.cons h₁ (.cons h₂ .nil), by simp⟩

end Case1

section Case2

variable (H : ASegHyp A)

include H

theorem short4_case2 {x₀ x₁ x₂ x₃ x₄ : V} (h₀₁ : Γ.Adj x₀ x₁) (h₁₂ : Γ.Adj x₁ x₂)
    (h₂₃ : Γ.Adj x₂ x₃) (h₃₄ : Γ.Adj x₃ x₄) (hn : ¬(x₀ = x₂ ∨ Γ.Adj x₀ x₂))
    (hno : ¬∃ b, A.cen (A.ι x₀) b ∧ A.cen (A.ι x₃) b) :
    ∃ q : Γ.Walk x₀ x₄, q.length ≤ 3 ∧ Homotopic (walk4 h₀₁ h₁₂ h₂₃ h₃₄) q := by
  have h5 : ∀ (u : V) (c : Γ.Walk u u), c.length ≤ 5 → Homotopic c .nil :=
    fun _ c hc => homotopic_nil_of_length_le_five A H.toASegHyp0 c hc
  push Not at hn
  obtain ⟨i, hi₀, hi₂, hi₃⟩ := H.h83_2 x₀ x₂ x₃ (dist_eq_two_of_adj_adj hn.1 hn.2 h₀₁ h₁₂) h₂₃
  have hiZ : i ∈ A.Z := by
    rcases A.inv_cases i with ⟨b, rfl⟩ | hZ
    · exact absurd ⟨b, A.cen_symm _ _ hi₀, A.cen_symm _ _ hi₃⟩ hno
    · exact hZ
  have h3 : A.three x₀ x₃ :=
    (H.h813_1 i hiZ x₀ x₃ hi₀ hi₃).resolve_left fun ⟨b, _, hb₀, hb₃⟩ => hno ⟨b, hb₀, hb₃⟩
  have key : ∀ s : Γ.Walk x₀ x₃, s.length = 3 →
      Homotopic s (.cons h₀₁ (.cons h₁₂ (.cons h₂₃ .nil))) := fun s hs =>
    H.h3C x₀ x₃ h3 hno s _ hs rfl
  by_cases hcl : x₀ = x₄ ∨ Γ.Adj x₀ x₄
  · exact short4_of_close h5 h₀₁ h₁₂ h₂₃ h₃₄ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hcl)))))
  by_cases hcn : ∃ c, Γ.Adj x₀ c ∧ Γ.Adj c x₄
  ·
    obtain ⟨c, hc₀, hc₄⟩ := hcn
    refine ⟨.cons hc₀ (.cons hc₄ .nil), by simp, ?_⟩
    have e := (key (.cons hc₀ (.cons hc₄ (.cons h₃₄.symm .nil))) rfl).symm.append_right
      (.cons h₃₄ .nil)
    exact e.trans (((homotopic_cons_cons_nil h₃₄.symm).cons hc₄).cons hc₀)
  by_cases hb : ∃ b, A.cen (A.ι x₀) b ∧ A.cen (A.ι x₄) b
  ·
    obtain ⟨b, hb₀, hb₄⟩ := hb
    obtain ⟨w₄, hw₄b, hw₄x⟩ : ∃ w₄, (w₄ = b ∨ Γ.Adj w₄ b) ∧ (w₄ = x₄ ∨ Γ.Adj w₄ x₄) := by
      rcases H.h814 b x₄ ⟨x₄, Or.inl rfl, A.cen_symm _ _ hb₄⟩ with h | h | ⟨t, hbt, htx⟩
      · exact ⟨b, Or.inl rfl, Or.inl h⟩
      · exact ⟨b, Or.inl rfl, Or.inr h⟩
      · exact ⟨t, Or.inr hbt.symm, Or.inr htx⟩
    obtain ⟨w, hxw, hww₄, hw₄x'⟩ : ∃ w, Γ.Adj x₀ w ∧ Γ.Adj w w₄ ∧ Γ.Adj w₄ x₄ := by
      rcases H.h814 x₀ w₄ ⟨b, hw₄b.imp Eq.symm SimpleGraph.Adj.symm, hb₀⟩ with
        h | h | ⟨w, h₁, h₂⟩
      · rcases hw₄x with h' | h'
        · exact absurd (Or.inl (h.trans h')) hcl
        · exact absurd (Or.inr (by rw [h]; exact h')) hcl
      · rcases hw₄x with h' | h'
        · exact absurd (Or.inr (by rw [← h']; exact h)) hcl
        · exact absurd ⟨w₄, h, h'⟩ hcn
      · rcases hw₄x with h' | h'
        · exact absurd ⟨w, h₁, by rw [← h']; exact h₂⟩ hcn
        · exact ⟨w, h₁, h₂, h'⟩
    obtain ⟨q, hq, hhq⟩ := short4_case1 A H.toASegHyp0 hxw hww₄ hw₄x' h₃₄.symm hb₀ hb₄
    have hq3 : q.length = 3 := by
      by_contra hne
      exact hno (exists_cen_of_walk_le_two A q (by omega))
    have e := ((hhq.trans (key q hq3)).symm).append_right (.cons h₃₄ .nil)
    refine ⟨.cons hxw (.cons hww₄ (.cons hw₄x' .nil)), by simp, ?_⟩
    exact e.trans ((((homotopic_cons_cons_nil h₃₄.symm).cons hw₄x').cons hww₄).cons hxw)
  ·
    obtain ⟨c, hxc, hcm⟩ := H.hS4 x₀ x₃ x₄ h3 h₃₄ hcl hcn hb
    obtain ⟨hm₃, hm₄⟩ := A.adj_mid x₃ x₄ h₃₄
    refine ⟨.cons hxc (.cons hcm (.cons hm₄.symm .nil)), by simp, ?_⟩
    have e := (key (.cons hxc (.cons hcm (.cons hm₃.symm .nil))) rfl).symm.append_right
      (.cons h₃₄ .nil)
    have t : Homotopic (.cons hm₃.symm (.cons h₃₄ .nil) : Γ.Walk (A.mid x₃ x₄) x₄)
        (.cons hm₄.symm .nil) :=
      homotopic_of_length_add_le h5 _ _ (by simp)
    exact e.trans ((t.cons hcm).cons hxc)

theorem short4_of_hyp {u v : V} (p : Γ.Walk u v) (hp : p.length = 4) :
    ∃ q : Γ.Walk u v, q.length ≤ 3 ∧ Homotopic p q := by
  obtain ⟨x₁, x₂, x₃, h₀₁, h₁₂, h₂₃, h₃₄, rfl⟩ := exists_walk_four p hp
  by_cases hc : (u = x₂ ∨ Γ.Adj u x₂) ∨ (x₁ = x₃ ∨ Γ.Adj x₁ x₃) ∨ (x₂ = v ∨ Γ.Adj x₂ v) ∨
      (u = x₃ ∨ Γ.Adj u x₃) ∨ (x₁ = v ∨ Γ.Adj x₁ v) ∨ (u = v ∨ Γ.Adj u v)
  · exact short4_of_close (fun _ c hc => homotopic_nil_of_length_le_five A H.toASegHyp0 c hc)
      h₀₁ h₁₂ h₂₃ h₃₄ hc
  · by_cases hb : ∃ b, A.cen (A.ι u) b ∧ A.cen (A.ι x₃) b
    · obtain ⟨b, hb₀, hb₃⟩ := hb
      exact short4_case1 A H.toASegHyp0 h₀₁ h₁₂ h₂₃ h₃₄ hb₀ hb₃
    · exact short4_case2 A H h₀₁ h₁₂ h₂₃ h₃₄ (fun h => hc (Or.inl h)) hb

end Case2

end CFSG.Monster.Tri
