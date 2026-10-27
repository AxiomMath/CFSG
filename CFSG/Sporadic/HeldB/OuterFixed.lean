module

public import CFSG.Sporadic.HeldB.OuterFixedCore
public import CFSG.Sporadic.HeldB.AutModel
public import CFSG.Sporadic.HeldB.OuterCentQS

public noncomputable section

namespace CFSG.Sporadic.HeldB

open CFSG.ComponentClassification.FixedCommutingProduct

theorem heOuterC_pComponent_quasisimple :
    ∀ L : Subgroup (heP ⊓ Subgroup.centralizer {heAutU} : Subgroup (Equiv.Perm (Fin 8330))),
      CFSG.IsPComponent 2 L → CFSG.IsQuasisimple L := by
  obtain ⟨hD, hq, hidx⟩ := ctbh_outer_centralizer_derived_quasisimple
  have hDC : heOuterD ≤ heOuterC := by
    rw [hD]
    exact Subgroup.commutator_le_self _
  exact pComponent_quasisimple_of_mulEquiv (MulEquiv.subgroupCongr heOuterC_eq.symm) 2
    Nat.prime_two (pComponent_quasisimple_of_relIndex_two hDC hq hidx 2 Nat.prime_two)

theorem outer_fixed_pComponent_quasisimple
    {S : Type*} [Group S] (e : S ≃* heP)
    (α : MulAut S) (hα : orderOf α = 2) (hinn : α ∉ (MulAut.conj : S →* MulAut S).range)
    (L : Subgroup (fixedSubgroup α)) (hL : CFSG.IsPComponent 2 L) : CFSG.IsQuasisimple L :=
  outer_fixed_pComponent_quasisimple_of ctbh_full_automorphism_permutation_model.1
    (fun _ hx hxP hx2 => exists_conj_heAutU hx hxP hx2) heOuterC_pComponent_quasisimple e α hα
    hinn L hL

theorem ctbh_outer_involution_fixed_p_components
    {S : Type*} [Group S]
    (hS : Nonempty (S ≃* heP) ∨ Nonempty (S ≃* Blueprint.NativeSporadic.He)) (α : MulAut S)
    (hα : orderOf α = 2) (hinn : α ∉ (MulAut.conj : S →* MulAut S).range)
    (L : Subgroup (fixedSubgroup α)) (hL : CFSG.IsPComponent 2 L) : CFSG.IsQuasisimple L := by
  rcases hS with h | h
  · exact outer_fixed_pComponent_quasisimple h.some α hα hinn L hL
  · exact outer_fixed_pComponent_quasisimple (h.some.trans heEquivP) α hα hinn L hL

end CFSG.Sporadic.HeldB
