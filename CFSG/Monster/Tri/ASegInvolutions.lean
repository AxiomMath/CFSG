module

public import CFSG.Monster.Tri.ASegBase
public import CFSG.Monster.B.GSide.HomotopyCycles
public import CFSG.Monster.Tri.ConeCover

public section

namespace CFSG.Monster.Tri

open SimpleGraph CFSG.Monster.B.Recog CFSG.Monster.B.GSide CFSG.YGroups

variable {V I : Type*} {Γ : SimpleGraph V} (A : CommStruct Γ I) (H : ASegHyp0 A)

include H

theorem inducedNull_cen_vertex (x : V) : InducedNull Γ {y | A.cen (A.ι x) y} :=
  inducedNull_of_cone_cover x (fun a ha b hb hab => H.h85 x a b ha hb hab) H.h88

omit H in
theorem dist_eq_two_of_not_cen {x y w : V} (hn : ¬A.cen (A.ι x) y) (h₁ : Γ.Adj x w)
    (h₂ : Γ.Adj w y) : Γ.dist x y = 2 :=
  dist_eq_two_of_adj_adj (fun h => hn (by subst h; exact A.cen_refl _))
    (fun h => hn (A.cen_of_adj x y h)) h₁ h₂

theorem exists_walk_cen (i : I) {x y w : V} (hx : A.cen i x) (hy : A.cen i y)
    (hn : ¬A.cen (A.ι x) y) (h₁ : Γ.Adj x w) (h₂ : Γ.Adj w y) :
    ∃ a : Γ.Walk x y, a.length ≤ 2 ∧ ∀ u ∈ a.support, A.cen i u := by
  obtain ⟨v, hv, hvx, hvy⟩ := H.h810 i x y hx hy (dist_eq_two_of_not_cen A hn h₁ h₂) hn
  exact ⟨.cons hvx.symm (.cons hvy .nil), by simp, by simp [hx, hv, hy]⟩

theorem pent_null_of_walks {v x₀ x₁ x₂ x₃ x₄ : V} (h₀₁ : Γ.Adj x₀ x₁) (h₁₂ : Γ.Adj x₁ x₂)
    (h₂₃ : Γ.Adj x₂ x₃) (h₃₄ : Γ.Adj x₃ x₄) (h₄₀ : Γ.Adj x₄ x₀)
    (ha : ∃ a : Γ.Walk x₀ x₂, a.length ≤ 2 ∧ ∀ w ∈ a.support, A.cen (A.ι v) w)
    (hb : ∃ b : Γ.Walk x₃ x₀, b.length ≤ 2 ∧ ∀ w ∈ b.support, A.cen (A.ι v) w) :
    Homotopic (.cons h₀₁ (.cons h₁₂ (.cons h₂₃ (.cons h₃₄ (.cons h₄₀ .nil)))) : Γ.Walk x₀ x₀)
      .nil := by
  obtain ⟨a, ha, haΦ⟩ := ha
  obtain ⟨b, hb, hbΦ⟩ := hb
  exact homotopic_pentagon_nil_of_inner_cycle h₀₁ h₁₂ h₂₃ h₃₄ h₄₀ a ha haΦ b hb hbΦ
    (inducedNull_cen_vertex A H v) H.h88

theorem pent_null_of_all_cen {v x₀ x₁ x₂ x₃ x₄ : V} (h₀₁ : Γ.Adj x₀ x₁) (h₁₂ : Γ.Adj x₁ x₂)
    (h₂₃ : Γ.Adj x₂ x₃) (h₃₄ : Γ.Adj x₃ x₄) (h₄₀ : Γ.Adj x₄ x₀) (c₀ : A.cen (A.ι v) x₀)
    (c₁ : A.cen (A.ι v) x₁) (c₂ : A.cen (A.ι v) x₂) (c₃ : A.cen (A.ι v) x₃)
    (c₄ : A.cen (A.ι v) x₄) :
    Homotopic (.cons h₀₁ (.cons h₁₂ (.cons h₂₃ (.cons h₃₄ (.cons h₄₀ .nil)))) : Γ.Walk x₀ x₀)
      .nil := by
  refine inducedNull_cen_vertex A H v _ _ fun w hw => ?_
  simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem pent_null_qs {z : I} (hz : z ∈ A.Z) {x₀ x₁ x₂ x₃ x₄ : V} (h₀₁ : Γ.Adj x₀ x₁)
    (h₁₂ : Γ.Adj x₁ x₂) (h₂₃ : Γ.Adj x₂ x₃) (h₃₄ : Γ.Adj x₃ x₄) (h₄₀ : Γ.Adj x₄ x₀)
    (hq₀ : x₀ ∈ A.Qs z) (hq₂ : x₂ ∈ A.Qs z) (hq₃ : x₃ ∈ A.Qs z) :
    Homotopic (.cons h₀₁ (.cons h₁₂ (.cons h₂₃ (.cons h₃₄ (.cons h₄₀ .nil)))) : Γ.Walk x₀ x₀)
      .nil := by
  by_cases h₂ : A.cen (A.ι x₀) x₂
  · by_cases h₃ : A.cen (A.ι x₀) x₃
    ·
      exact pent_null_of_all_cen A H h₀₁ h₁₂ h₂₃ h₃₄ h₄₀ (A.cen_refl x₀)
        (A.cen_of_adj x₀ x₁ h₀₁) h₂ h₃ (A.cen_of_adj x₀ x₄ h₄₀.symm)
    ·
      refine pent_null_of_walks A H (v := x₂) h₀₁ h₁₂ h₂₃ h₃₄ h₄₀
        ⟨.cons h₀₁ (.cons h₁₂ .nil), by simp, ?_⟩ ?_
      · simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
          or_false]
        rintro w (rfl | rfl | rfl)
        · exact A.cen_symm _ _ h₂
        · exact A.cen_of_adj x₂ _ h₁₂.symm
        · exact A.cen_refl _
      · obtain ⟨b, hb, hbΦ⟩ := exists_walk_cen A H (A.ι x₂) (x := x₀) (y := x₃) (w := x₄)
          (A.cen_symm _ _ h₂) (A.cen_of_adj x₂ x₃ h₂₃) h₃ h₄₀.symm h₃₄.symm
        exact ⟨b.reverse, by simpa using hb, by simpa using hbΦ⟩
  · by_cases h₃ : A.cen (A.ι x₀) x₃
    ·
      refine pent_null_of_walks A H (v := x₃) h₀₁ h₁₂ h₂₃ h₃₄ h₄₀ ?_
        ⟨.cons h₃₄ (.cons h₄₀ .nil), by simp, ?_⟩
      · obtain ⟨a, ha, haΦ⟩ := exists_walk_cen A H (A.ι x₃) (x := x₀) (y := x₂) (w := x₁)
          (A.cen_symm _ _ h₃) (A.cen_of_adj x₃ x₂ h₂₃.symm) h₂ h₀₁ h₁₂
        exact ⟨a, ha, haΦ⟩
      · simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
          or_false]
        rintro w (rfl | rfl | rfl)
        · exact A.cen_refl _
        · exact A.cen_of_adj x₃ _ h₃₄
        · exact A.cen_symm _ _ h₃
    ·
      have hm : A.cen (A.ι x₀) (A.mid x₂ x₃) := by
        rcases H.h87_3 z hz x₂ hq₂ x₃ hq₃ x₀ hq₀ h₂₃ with h | h | h
        · exact absurd h h₂
        · exact absurd h h₃
        · exact h
      obtain ⟨hm₂, hm₃⟩ := A.adj_mid x₂ x₃ h₂₃
      refine pent_null_of_walks A H (v := A.mid x₂ x₃) h₀₁ h₁₂ h₂₃ h₃₄ h₄₀ ?_ ?_
      · obtain ⟨a, ha, haΦ⟩ := exists_walk_cen A H (A.ι (A.mid x₂ x₃)) (x := x₀) (y := x₂)
          (w := x₁) (A.cen_symm _ _ hm) (A.cen_of_adj _ x₂ hm₂.symm) h₂ h₀₁ h₁₂
        exact ⟨a, ha, haΦ⟩
      · obtain ⟨b, hb, hbΦ⟩ := exists_walk_cen A H (A.ι (A.mid x₂ x₃)) (x := x₀) (y := x₃)
          (w := x₄) (A.cen_symm _ _ hm) (A.cen_of_adj _ x₃ hm₃.symm) h₃ h₄₀.symm h₃₄.symm
        exact ⟨b.reverse, by simpa using hb, by simpa using hbΦ⟩

theorem inducedNull_qs {z : I} (hz : z ∈ A.Z) : InducedNull Γ (A.Qs z) := by
  refine inducedNull_of_pentagons (H.h87_1 z hz) H.h88 ?_
  intro u c hc hlen hΦ
  obtain ⟨x₁, x₂, x₃, x₄, h₀₁, h₁₂, h₂₃, h₃₄, h₄₀, rfl⟩ := exists_closed_walk_five c hlen
  exact pent_null_qs A H hz h₀₁ h₁₂ h₂₃ h₃₄ h₄₀ (hΦ u (by simp)) (hΦ x₂ (by simp))
    (hΦ x₃ (by simp))

theorem inducedNull_cen_Z {z : I} (hz : z ∈ A.Z) : InducedNull Γ {y | A.cen z y} := by
  refine inducedNull_of_diamTwo (Φ := A.Qs z) (H.h87_1 z hz) (fun a ha b hb hab => ?_) H.h88
    (inducedNull_qs A H hz)
  by_cases ha' : a ∈ A.Qs z
  · exact ⟨a, ha', Or.inl rfl, Or.inr hab⟩
  · by_cases hb' : b ∈ A.Qs z
    · exact ⟨b, hb', Or.inr hab.symm, Or.inl rfl⟩
    · obtain ⟨w, hw, hwa, hwb⟩ := H.h89 z hz a b ha hb ha' hb' hab
      exact ⟨w, hw, Or.inr hwa, Or.inr hwb⟩

theorem inducedNull_cen (i : I) : InducedNull Γ {y | A.cen i y} := by
  rcases A.inv_cases i with ⟨x, rfl⟩ | hz
  · exact inducedNull_cen_vertex A H x
  · exact inducedNull_cen_Z A H hz

theorem pent_null_good {x₀ x₁ x₂ x₃ x₄ : V} (h₀₁ : Γ.Adj x₀ x₁) (h₁₂ : Γ.Adj x₁ x₂)
    (h₂₃ : Γ.Adj x₂ x₃) (h₃₄ : Γ.Adj x₃ x₄) (h₄₀ : Γ.Adj x₄ x₀) (hn₂ : ¬A.cen (A.ι x₀) x₂)
    (hn₃ : ¬A.cen (A.ι x₀) x₃) :
    Homotopic (.cons h₀₁ (.cons h₁₂ (.cons h₂₃ (.cons h₃₄ (.cons h₄₀ .nil)))) : Γ.Walk x₀ x₀)
      .nil := by
  obtain ⟨i, hi₀, hi₂, hi₃⟩ := H.h83_2 x₀ x₂ x₃ (dist_eq_two_of_not_cen A hn₂ h₀₁ h₁₂) h₂₃
  obtain ⟨a, ha, haΦ⟩ := exists_walk_cen A H i hi₀ hi₂ hn₂ h₀₁ h₁₂
  obtain ⟨b, hb, hbΦ⟩ := exists_walk_cen A H i hi₀ hi₃ hn₃ h₄₀.symm h₃₄.symm
  exact homotopic_pentagon_nil_of_inner_cycle (Φ := {y | A.cen i y}) h₀₁ h₁₂ h₂₃ h₃₄ h₄₀ a ha
    haΦ b.reverse (by simpa using hb) (by simpa using hbΦ) (inducedNull_cen A H i) H.h88

theorem pent_null {x₀ x₁ x₂ x₃ x₄ : V} (h₀₁ : Γ.Adj x₀ x₁) (h₁₂ : Γ.Adj x₁ x₂)
    (h₂₃ : Γ.Adj x₂ x₃) (h₃₄ : Γ.Adj x₃ x₄) (h₄₀ : Γ.Adj x₄ x₀) :
    Homotopic (.cons h₀₁ (.cons h₁₂ (.cons h₂₃ (.cons h₃₄ (.cons h₄₀ .nil)))) : Γ.Walk x₀ x₀)
      .nil := by
  have s02 := A.cen_symm x₀ x₂
  have s20 := A.cen_symm x₂ x₀
  have s13 := A.cen_symm x₁ x₃
  have s31 := A.cen_symm x₃ x₁
  have s24 := A.cen_symm x₂ x₄
  have s42 := A.cen_symm x₄ x₂
  have s03 := A.cen_symm x₀ x₃
  have s30 := A.cen_symm x₃ x₀
  have s14 := A.cen_symm x₁ x₄
  have s41 := A.cen_symm x₄ x₁
  by_cases v0 : A.cen (A.ι x₀) x₂ ∧ A.cen (A.ι x₀) x₃
  · exact pent_null_of_all_cen A H h₀₁ h₁₂ h₂₃ h₃₄ h₄₀ (A.cen_refl x₀) (A.cen_of_adj x₀ x₁ h₀₁)
      v0.1 v0.2 (A.cen_of_adj x₀ x₄ h₄₀.symm)
  by_cases v1 : A.cen (A.ι x₁) x₃ ∧ A.cen (A.ι x₁) x₄
  · refine homotopic_nil_pent_rotate h₀₁ h₁₂ h₂₃ h₃₄ h₄₀ ?_
    exact pent_null_of_all_cen A H h₁₂ h₂₃ h₃₄ h₄₀ h₀₁ (A.cen_refl x₁)
      (A.cen_of_adj x₁ x₂ h₁₂) v1.1 v1.2 (A.cen_of_adj x₁ x₀ h₀₁.symm)
  by_cases v2 : A.cen (A.ι x₂) x₄ ∧ A.cen (A.ι x₂) x₀
  · refine homotopic_nil_pent_rotate h₀₁ h₁₂ h₂₃ h₃₄ h₄₀ (homotopic_nil_pent_rotate h₁₂ h₂₃
      h₃₄ h₄₀ h₀₁ ?_)
    exact pent_null_of_all_cen A H h₂₃ h₃₄ h₄₀ h₀₁ h₁₂ (A.cen_refl x₂) (A.cen_of_adj x₂ x₃ h₂₃)
      v2.1 v2.2 (A.cen_of_adj x₂ x₁ h₁₂.symm)
  by_cases v3 : A.cen (A.ι x₀) x₃ ∧ A.cen (A.ι x₁) x₃
  · refine homotopic_nil_pent_rotate h₀₁ h₁₂ h₂₃ h₃₄ h₄₀ (homotopic_nil_pent_rotate h₁₂ h₂₃
      h₃₄ h₄₀ h₀₁ (homotopic_nil_pent_rotate h₂₃ h₃₄ h₄₀ h₀₁ h₁₂ ?_))
    exact pent_null_of_all_cen A H h₃₄ h₄₀ h₀₁ h₁₂ h₂₃ (A.cen_refl x₃) (A.cen_of_adj x₃ x₄ h₃₄)
      (s03 v3.1) (s13 v3.2) (A.cen_of_adj x₃ x₂ h₂₃.symm)
  by_cases v4 : A.cen (A.ι x₁) x₄ ∧ A.cen (A.ι x₂) x₄
  · refine homotopic_nil_pent_rotate h₀₁ h₁₂ h₂₃ h₃₄ h₄₀ (homotopic_nil_pent_rotate h₁₂ h₂₃
      h₃₄ h₄₀ h₀₁ (homotopic_nil_pent_rotate h₂₃ h₃₄ h₄₀ h₀₁ h₁₂ (homotopic_nil_pent_rotate
        h₃₄ h₄₀ h₀₁ h₁₂ h₂₃ ?_)))
    exact pent_null_of_all_cen A H h₄₀ h₀₁ h₁₂ h₂₃ h₃₄ (A.cen_refl x₄) (A.cen_of_adj x₄ x₀ h₄₀)
      (s14 v4.1) (s24 v4.2) (A.cen_of_adj x₄ x₃ h₃₄.symm)
  rcases pentagon_parity (A.cen (A.ι x₀) x₂) (A.cen (A.ι x₁) x₃) (A.cen (A.ι x₂) x₄)
    (A.cen (A.ι x₀) x₃) (A.cen (A.ι x₁) x₄) ⟨v0, v1, fun h => v2 ⟨h.1, s02 h.2⟩, v3,
      fun h => v4 ⟨h.1, h.2⟩⟩ with g | g | g | g | g
  · exact pent_null_good A H h₀₁ h₁₂ h₂₃ h₃₄ h₄₀ g.1 g.2
  · refine homotopic_nil_pent_rotate h₀₁ h₁₂ h₂₃ h₃₄ h₄₀ ?_
    exact pent_null_good A H h₁₂ h₂₃ h₃₄ h₄₀ h₀₁ g.1 g.2
  · refine homotopic_nil_pent_rotate h₀₁ h₁₂ h₂₃ h₃₄ h₄₀ (homotopic_nil_pent_rotate h₁₂ h₂₃
      h₃₄ h₄₀ h₀₁ ?_)
    exact pent_null_good A H h₂₃ h₃₄ h₄₀ h₀₁ h₁₂ g.1 fun h => g.2 (s20 h)
  · refine homotopic_nil_pent_rotate h₀₁ h₁₂ h₂₃ h₃₄ h₄₀ (homotopic_nil_pent_rotate h₁₂ h₂₃
      h₃₄ h₄₀ h₀₁ (homotopic_nil_pent_rotate h₂₃ h₃₄ h₄₀ h₀₁ h₁₂ ?_))
    exact pent_null_good A H h₃₄ h₄₀ h₀₁ h₁₂ h₂₃ (fun h => g.1 (s30 h)) fun h => g.2 (s31 h)
  · refine homotopic_nil_pent_rotate h₀₁ h₁₂ h₂₃ h₃₄ h₄₀ (homotopic_nil_pent_rotate h₁₂ h₂₃
      h₃₄ h₄₀ h₀₁ (homotopic_nil_pent_rotate h₂₃ h₃₄ h₄₀ h₀₁ h₁₂ (homotopic_nil_pent_rotate
        h₃₄ h₄₀ h₀₁ h₁₂ h₂₃ ?_)))
    exact pent_null_good A H h₄₀ h₀₁ h₁₂ h₂₃ h₃₄ (fun h => g.1 (s41 h)) fun h => g.2 (s42 h)

theorem homotopic_nil_of_length_le_five {u : V} (c : Γ.Walk u u) (hc : c.length ≤ 5) :
    Homotopic c .nil := by
  classical
  refine homotopic_nil_of_forall_isCycle (L := 5) (fun x c hcyc hlen => ?_) c hc
  rcases Nat.lt_or_ge c.length 5 with hlt | hge
  · exact H.h88 x c (by omega)
  · obtain ⟨x₁, x₂, x₃, x₄, h₀₁, h₁₂, h₂₃, h₃₄, h₄₀, rfl⟩ := exists_closed_walk_five c (by omega)
    exact pent_null A H h₀₁ h₁₂ h₂₃ h₃₄ h₄₀

end CFSG.Monster.Tri
