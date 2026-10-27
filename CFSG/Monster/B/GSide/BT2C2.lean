module

public import CFSG.Monster.B.GSide.BT2Reduce

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open SimpleGraph CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.E6.StdF4

theorem orbM_two_two_pos : ∀ l : Fin 5, l ≠ 0 → 0 < orbM 2 l 2 := by decide

theorem triType_cv0_eq_orbK
    (M : RootModel cv0) (a b : cgraph.neighborSet cv0) :
    triType cv0 a b = orbK (relIdx (M.iv a) (M.iv b)) :=
  (M.triType_eq_orbSize a b).trans (orbSize_inl_eq _ _)

theorem adj_and_not_isType1782_of_relIdx
    (M : RootModel cv0) {a b : cgraph.neighborSet cv0}
    (h : relIdx (M.iv a) (M.iv b) = 2) :
    cgraph.Adj (a : CVert) b ∧ ¬ IsType1782 cv0 a b := by
  have hne : a ≠ b := fun e => by
    rw [e, (relIdx_eq_zero_iff _ _).2 rfl] at h
    exact absurd h (by decide)
  have hc := ((isNbr_iff _ _).1 (Or.inr h)).2
  refine ⟨(M.adj_iff a b hne).2 hc, fun h' => ?_⟩
  have e := h'.2
  rw [triType_cv0_eq_orbK M, h] at e
  exact absurd e (by decide)

theorem bt2C2 :
    BT2C2 := by
  intro p q p' q' hp _ _ _ hp' _ _ _
  obtain ⟨M, -⟩ := exists_rootModel cv0
  by_cases hpp : p = p'
  · subst hpp
    exact Relation.ReflTransGen.refl
  · set x : Pts := M.iv ⟨p, hp⟩ with hx
    set x' : Pts := M.iv ⟨p', hp'⟩ with hx'
    have hxx : x ≠ x' := fun h => hpp (congrArg Subtype.val (M.iv.injective h))
    have hl : relIdx x x' ≠ 0 := fun h => hxx ((relIdx_eq_zero_iff x x').1 h)
    have hpos := orbM_two_two_pos _ hl
    rw [← card_filter_relIdx x x' 2 2] at hpos
    obtain ⟨z, hz⟩ := Finset.card_pos.1 hpos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    set b : cgraph.neighborSet cv0 := M.iv.symm z with hb
    have hzb : M.iv b = z := M.iv.apply_symm_apply z
    have h₁ := adj_and_not_isType1782_of_relIdx M (a := ⟨p, hp⟩) (b := b)
      (by rw [hzb]; exact hz.1)
    have h₂ := adj_and_not_isType1782_of_relIdx M (a := ⟨p', hp'⟩) (b := b)
      (by rw [hzb, relIdx_comm]; exact hz.2)
    exact Relation.ReflTransGen.single ⟨b, hp, h₁.1, b.2.symm, h₁.2, hp', h₂.1, h₂.2⟩

end CFSG.Monster.B.GSide
