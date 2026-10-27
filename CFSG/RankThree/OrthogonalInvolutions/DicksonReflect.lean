module

public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.ClassicalGroups.Orthogonal.Derived

public section

namespace CFSG.RankThree.OrthogonalInvolutions

open CFSG.ClassicalGroups.Orthogonal

theorem prod_reflect_mem_omegaGroup
    {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (l : List V)
    (hl : ∀ a ∈ l, Q a ≠ 0) (hev : Even l.length) :
    (l.map (reflect Q)).prod ∈ omegaGroup Q hQ := by
  have hmemO : ∀ l : List V, (l.map (reflect Q)).prod ∈
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.map_cons, List.prod_cons]
      exact mul_mem (reflect_mem_orthogonalGroup Q a) ih
  have key : ∀ l : List V, (∀ a ∈ l, Q a ≠ 0) →
      (Module.finrank K (commSpace ((l.map (reflect Q)).prod)) : ZMod 2) = (l.length : ZMod 2) := by
    intro l
    induction l with
    | nil =>
      intro _
      rw [List.map_nil, List.prod_nil]
      exact natCast_finrank_commSpace_one
    | cons a l ih =>
      intro hl
      have ha : Q a ≠ 0 := hl a (by simp)
      have hl' : ∀ x ∈ l, Q x ≠ 0 := fun x hx => hl x (by simp [hx])
      rw [List.map_cons, List.prod_cons]
      have hmul := natCast_finrank_commSpace_mul hQ
        (reflect_mem_orthogonalGroup Q a) (hmemO l)
      rw [hmul, ih hl']
      have h1 : Module.finrank K (commSpace (reflect Q a)) = 1 := by
        letI : Invertible (Q a) := invertibleOfNonzero ha
        rw [reflect_eq_reflection]
        exact finrank_commSpace_reflection hQ a
      rw [h1, List.length_cons]
      push_cast
      ring
  rw [mem_omegaGroup]
  refine ⟨hmemO l, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff_even, key l hl]
  exact ZMod.natCast_eq_zero_iff_even.mpr hev

end CFSG.RankThree.OrthogonalInvolutions
