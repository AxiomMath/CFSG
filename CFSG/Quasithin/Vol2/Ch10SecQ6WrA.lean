module

public import CFSG.Quasithin.Vol2.Ch10SecQ6WrPM

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open Equiv

@[expose] def HypFix (V : AddSubgroup PMod) (A : Subgroup SymFiveWrTwo) : Prop :=
  ∃ B : Subgroup SymFiveWrTwo, B ≤ A ∧ (∃ x ∈ A, x ∉ B ∧ ∀ g ∈ A, g ∈ B ∨ g * x ∈ B) ∧
    ∃ m ∈ V, (∀ b ∈ B, gP b m = m) ∧ ∃ a ∈ A, gP a m ≠ m

theorem left_mul_base {g : SymFiveWrTwo} (hg : g.right = 1) (h : SymFiveWrTwo)
    (q : Multiplicative (ZMod 2)) : (g * h).left q = g.left q * h.left q := by
  rw [left_mul_apply, hg, one_inv_mul]

theorem right_mul (g h : SymFiveWrTwo) : (g * h).right = g.right * h.right := rfl

@[expose] def projSub (A : Subgroup SymFiveWrTwo) (q : Multiplicative (ZMod 2)) :
    Subgroup (Perm (Fin 5)) where
  carrier := {σ | ∃ g ∈ A, g.right = 1 ∧ g.left q = σ}
  one_mem' := ⟨1, A.one_mem, rfl, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨g, hg, hgr, rfl⟩ ⟨h, hh, hhr, rfl⟩
    exact ⟨g * h, A.mul_mem hg hh, by rw [right_mul, hgr, hhr, one_mul], left_mul_base hgr h q⟩
  inv_mem' := by
    rintro _ ⟨g, hg, hgr, rfl⟩
    exact ⟨g⁻¹, A.inv_mem hg, inv_right_base hgr, inv_left_base hgr q⟩

theorem projSub_comm {A : Subgroup SymFiveWrTwo} (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (q : Multiplicative (ZMod 2)) : ∀ σ ∈ projSub A q, ∀ τ ∈ projSub A q, σ * τ = τ * σ := by
  rintro _ ⟨g, hg, hgr, rfl⟩ _ ⟨h, hh, hhr, rfl⟩
  rw [← left_mul_base hgr, ← left_mul_base hhr, hc g hg h hh]

theorem projSub_sq {A : Subgroup SymFiveWrTwo} (h2 : ∀ a ∈ A, a * a = 1)
    (q : Multiplicative (ZMod 2)) : ∀ σ ∈ projSub A q, σ * σ = 1 := by
  rintro _ ⟨g, hg, hgr, rfl⟩
  rw [← left_mul_base hgr, h2 g hg]
  rfl

theorem hypFix_of_conj {V : AddSubgroup PMod} (hV : ∀ g : SymFiveWrTwo, ∀ v ∈ V, gP g v ∈ V)
    {A : Subgroup SymFiveWrTwo} (c : SymFiveWrTwo)
    (h : HypFix V (A.map (MulAut.conj c).toMonoidHom)) : HypFix V A := by
  obtain ⟨B', hB'A, ⟨x', hx'A, hx'B, hcov⟩, m', hm'V, hfix, a', ha'A, ha'⟩ := h
  obtain ⟨x, hxA, rfl⟩ := hx'A
  obtain ⟨a, haA, rfl⟩ := ha'A
  refine ⟨B'.comap (MulAut.conj c).toMonoidHom, fun b hb => ?_, ⟨x, hxA, hx'B, fun g hg => ?_⟩,
    gP c⁻¹ m', hV _ _ hm'V, fun b hb => ?_, a, haA, fun h' => ha' ?_⟩
  · obtain ⟨g, hg, hgb⟩ := hB'A hb
    exact (MulAut.conj c).injective hgb ▸ hg
  · rcases hcov _ ⟨g, hg, rfl⟩ with h1 | h1
    · exact Or.inl h1
    · right
      change MulAut.conj c (g * x) ∈ B'
      rwa [map_mul]
  · have h1 : gP (c * b * c⁻¹) m' = m' := hfix _ hb
    rw [← gP_mul, show b * c⁻¹ = c⁻¹ * (c * b * c⁻¹) by group, gP_mul, h1]
  · change gP (c * a * c⁻¹) m' = m'
    rw [gP_mul, gP_mul, h', ← gP_mul, mul_inv_cancel, gP_one]

theorem tens_ne_left {u u' v : Fin 5 → ZMod 2} (hv : v ≠ 0) (hu : u' ≠ u) :
    tens u' v ≠ tens u v := by
  intro h
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv (funext hc)
  have hj1 : v j = 1 := by
    revert hj
    generalize v j = y
    revert y
    decide
  apply hu
  funext i
  have := congrFun (congrFun h i) j
  simp only [tens, hj1, mul_one] at this
  exact this

theorem tens_ne_right {u v v' : Fin 5 → ZMod 2} (hu : u ≠ 0) (hv : v' ≠ v) :
    tens u v' ≠ tens u v := by
  intro h
  apply tens_ne_left hu hv
  funext i j
  have := congrFun (congrFun h j) i
  simp only [tens] at this ⊢
  rw [mul_comm, this, mul_comm]

theorem zmod_two_mul_self (x : ZMod 2) : x * x = x := by
  revert x
  decide

theorem eq_of_tens_diag {u w : Fin 5 → ZMod 2} (h : tens w w = tens u u) : w = u := by
  funext i
  have := congrFun (congrFun h i) i
  simp only [tens, zmod_two_mul_self] at this
  exact this

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD
