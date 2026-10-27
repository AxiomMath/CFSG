module

public import CFSG.RankThree.PartTwo.Sec8.Hering611KFInvolFinal
import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreExcOut
import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.LieModelOrders

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem center_eq_bot_of_sp62 {Kb : Type} [Group Kb] (hK : StatedClassicalModel Kb .PSp 3 2 1) :
    Subgroup.center Kb = ⊥ := by
  have hsimple : IsSimpleGroup Kb := Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hK
  have hcard : Nat.card Kb = 1451520 :=
    Blueprint.LieModel.card_psp_three_two (Or.inl ⟨by decide, hK⟩)
  rcases (Subgroup.center Kb).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hcomm : ∀ x y : Kb, x * y = y * x := fun x y =>
      Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y) x
    let _ : CommGroup Kb := { ‹Group Kb› with mul_comm := hcomm }
    have hfin : Finite Kb := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    have hp := IsSimpleGroup.prime_card (α := Kb)
    rw [hcard] at hp
    exact absurd hp (by norm_num)

theorem exists_conj_eq_of_sp62 {Kb : Type} [Group Kb] (hK : StatedClassicalModel Kb .PSp 3 2 1)
    (α : MulAut Kb) : ∃ γ : Kb, α = MulAut.conj γ := by
  have hout := ComponentClassification.Foote5.card_outer_eq_one_of_psp_three_two hK
  obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.mp hout
  have h1 : (QuotientGroup.mk α : ComponentClassification.OuterAutomorphisms.Outer Kb) = 1 :=
    Subsingleton.elim _ _
  obtain ⟨γ, hγ⟩ := (QuotientGroup.eq_one_iff α).mp h1
  exact ⟨γ, hγ.symm⟩

theorem kF611Sp62Inner_holds : KF611Sp62Inner := by
  intro Kb _ _ hK α hα3
  obtain ⟨γ, rfl⟩ := exists_conj_eq_of_sp62 hK α
  refine ⟨γ, ?_, rfl⟩
  have hc : γ ^ 3 ∈ Subgroup.center Kb := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun β : MulAut Kb => β g) hα3
    simp only [← map_pow, MulAut.conj_apply, MulAut.one_apply] at h
    calc g * γ ^ 3 = (γ ^ 3 * g * (γ ^ 3)⁻¹) * γ ^ 3 := by rw [h]
      _ = γ ^ 3 * g := by group
  rw [center_eq_bot_of_sp62 hK, Subgroup.mem_bot] at hc
  exact hc

end CFSG.RankThree.PartTwo.Sec8.Hering611
