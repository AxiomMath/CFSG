module

public import CFSG.Quasithin.Background.P4InspOrthBasic
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace G11

namespace P4InspOrth

open CFSG.ClassicalGroups.Orthogonal CFSG.GroupTheory.WeirSylow
open CFSG.LieType.Universal.Spin (quadPlus quadMinus)

section Simple

theorem p4insporth_orthogonalGroup_eq {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V) :
    TauCeti.QuadraticMap.orthogonalGroup Q = orthSub ⇑Q := by
  ext g
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  exact Iff.rfl

theorem p4insporth_nonempty_proj_equiv {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Nontrivial V] (Q : QuadraticForm (ZMod 2) V) :
    Nonempty (ProjElementary Q ≃* ↥(elementaryGroup Q)) := by
  have hZ : (scalars (ZMod 2) V).subgroupOf (elementaryGroup Q) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_subgroupOf, mem_scalars] at hg
    obtain ⟨c, hc⟩ := hg
    rw [Subgroup.mem_bot]
    have hc1 : c = 1 := by
      by_contra hne
      have hc0 : c = 0 := by
        have : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide
        exact this c hne
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      apply hv
      apply (g : V ≃ₗ[ZMod 2] V).injective
      rw [map_zero]
      have := hc v
      rw [hc0, zero_smul] at this
      exact this
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    have := hc v
    rw [hc1, one_smul] at this
    exact this
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot⟩

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] {f : LinearMap.BilinForm (ZMod 2) U}
  {q : U → ZMod 2}

theorem p4insporth_simple_plus [Finite U] (hf : IsSymplectic f)
    (hq : ∀ x y, q (x + y) = q x + q y + f x y) {n : ℕ} (hn : 3 ≤ n)
    (hdim : Module.finrank (ZMod 2) U = 2 * n) (hplus : IsPlusType (p4insporth_quad hq)) :
    IsSimpleGroup ↥⁅orthSub q, orthSub q⁆ := by
  obtain ⟨e⟩ := nonempty_isometry_quadPlus (p4insporth_nondegenerate_quad hf hq) hdim hplus
  refine p4insporth_isSimpleGroup_commutator_of_iso (q' := ⇑(quadPlus n (ZMod 2)))
    e.toLinearEquiv (fun x => ?_) ?_
  · have := e.map_app x
    rwa [p4insporth_quad_apply] at this
  · have hU : Nontrivial U := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
    have : Nontrivial (Fin n ⊕ Fin n → ZMod 2) := e.toLinearEquiv.symm.nontrivial
    obtain ⟨φ⟩ := p4insporth_nonempty_proj_equiv (quadPlus n (ZMod 2))
    have hs := isSimpleGroup_projElementary_quadPlus (K := ZMod 2) hn
    rw [← p4insporth_orthogonalGroup_eq, commutator_orthogonalGroup_quadPlus hn]
    exact φ.symm.isSimpleGroup

theorem p4insporth_simple_minus [Finite U] (hf : IsSymplectic f)
    (hq : ∀ x y, q (x + y) = q x + q y + f x y) {n : ℕ} (hn : 4 ≤ n)
    (hdim : Module.finrank (ZMod 2) U = 2 * n) (hminus : ¬ IsPlusType (p4insporth_quad hq)) :
    IsSimpleGroup ↥⁅orthSub q, orthSub q⁆ := by
  have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
  obtain ⟨e⟩ := nonempty_isometry_of_not_isPlusType (p4insporth_nondegenerate_quad hf hq)
    (by omega) hdim hminus hirr
  refine p4insporth_isSimpleGroup_commutator_of_iso (q' := ⇑(quadMinus n (ZMod 2) 1 1))
    e.toLinearEquiv (fun x => ?_) ?_
  · have := e.map_app x
    rwa [p4insporth_quad_apply] at this
  · have hU : Nontrivial U := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
    have : Nontrivial (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ZMod 2) :=
      e.toLinearEquiv.symm.nontrivial
    obtain ⟨φ⟩ := p4insporth_nonempty_proj_equiv (quadMinus n (ZMod 2) 1 1)
    have hs := isSimpleGroup_projElementary_quadMinus (K := ZMod 2) hn hirr
    rw [← p4insporth_orthogonalGroup_eq, commutator_orthogonalGroup_quadMinus hn hirr]
    exact φ.symm.isSimpleGroup

end Simple

end P4InspOrth

end G11

end CFSG.Quasithin
