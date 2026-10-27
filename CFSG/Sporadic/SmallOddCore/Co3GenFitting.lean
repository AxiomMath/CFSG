module

public import CFSG.Sporadic.SmallOddCore.Co3Aut
public import CFSG.Sporadic.SmallOddCore.Co3Odd
public import CFSG.Sporadic.SmallOddCore.Assembly
public import CFSG.GroupTheory.LocalCores.Components

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.Blueprint

theorem co3_exists_not_comm_z : ∃ g ∈ co3P, g * co3Z ≠ co3Z * g := by
  by_contra h
  push Not at h
  have hle : co3P ≤ co3P ⊓ centralizer ({co3Z} : Set (Equiv.Perm (Fin 276))) :=
    le_inf le_rfl fun g hg => mem_centralizer_singleton_iff.mpr (h g hg)
  have := Subgroup.card_le_of_le hle
  rw [← co3M_eq_centralizer, card_co3M, card_co3P] at this
  norm_num at this

theorem co3P_not_comm : ∃ a b : co3P, a * b ≠ b * a := by
  obtain ⟨g, hg, hgz⟩ := co3_exists_not_comm_z
  refine ⟨⟨g, hg⟩, co3ZP, fun h => hgz ?_⟩
  have := congrArg Subtype.val h
  rwa [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mk, co3ZP_coe] at this

theorem co3_autModel [IsSimpleGroup co3P] : AutModel co3P co3P where
  le := le_rfl
  conj_mem x hx p hp := co3P.mul_mem (co3P.mul_mem hx hp) (co3P.inv_mem hx)
  surj α := by
    obtain ⟨p, rfl⟩ := co3P_allInner α
    refine ⟨p, p.2, fun q => ?_⟩
    rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  inj x hx hc := by
    have hcen : center co3P = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center co3P) with h | h
      · exact h
      · obtain ⟨a, b, hab⟩ := co3P_not_comm
        exact absurd (mem_center_iff.mp (h ▸ mem_top b) a) hab
    have hx1 : (⟨x, hx⟩ : co3P) ∈ center co3P := by
      rw [mem_center_iff]
      intro p
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mk]
      exact (hc p p.2).symm
    rw [hcen, mem_bot] at hx1
    have := congrArg Subtype.val hx1
    rwa [Subgroup.coe_mk, Subgroup.coe_one] at this

theorem ctuc_co3_generalized_fitting_centralizers_odd_core_trivial {X : Type*} [Group X]
    [Finite X] (hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (hJ : Nonempty (CFSG.generalizedFitting X ≃* NativeSporadic.Co3)) :
    CFSG.generalizedFitting X = ⊤ ∧
      ∀ u : X, orderOf u = 2 → CFSG.oddCore ↥(centralizer ({u} : Set X)) = ⊥ := by
  have : (CFSG.generalizedFitting X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  obtain ⟨ψ⟩ := hJ
  set θ : CFSG.generalizedFitting X ≃* co3P := ψ.trans co3PermEquiv
  have : IsSimpleGroup co3P := θ.symm.isSimpleGroup
  have hnab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := co3P_not_comm
    refine ⟨θ.symm a, θ.symm b, fun h => hab ?_⟩
    have := congrArg θ h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this
  have hC := centralizer_generalizedFitting_eq_bot hF hnab
  have h := co3_autModel
  refine ⟨?_, fun u hu => oddCore_centralizer_eq_bot h (by omega)
    ctuc_co3_involution_centralizers_odd_core_trivial _ θ hC u hu⟩
  have hinj := h.embed_injective _ θ hC
  have hrange : (h.embed _ θ).range ≤ co3P := by
    rintro _ ⟨x, rfl⟩
    exact h.embed_mem _ θ x
  have hX : Nat.card X ≤ Nat.card (CFSG.generalizedFitting X) := by
    rw [Nat.card_congr θ.toEquiv, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Subgroup.card_le_of_le hrange
  exact Subgroup.eq_top_of_card_eq _ (le_antisymm (Subgroup.card_le_card_group _) hX)

end CFSG.Sporadic.SmallOddCore
