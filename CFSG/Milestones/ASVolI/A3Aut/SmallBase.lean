module

public import CFSG.Milestones.ASVolI.A3OddFacts

public section

namespace CFSG.ASVolI

theorem burnsideAut_Config_sup_ne_top {X : Type} [Group X] [Finite X] {S B : Subgroup X}
    (hc : burnsideA315x_Config X S B) [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) :
    B ⊔ S ≠ ⊤ := by
  have hnil : Group.IsNilpotent ↥B := by
    rcases hc.cases with hab | ⟨r, hr, hBr⟩
    · haveI := hab
      infer_instance
    · haveI : Fact r.Prime := ⟨hr⟩
      exact hBr.isNilpotent
  have hsolv : Group.IsSolvable ↥(B ⊔ S) := hc.sup_solvable hnil
  intro htop
  obtain ⟨a, b, hab⟩ := hnab
  rw [htop] at hsolv
  haveI := hsolv
  have : Group.IsSolvable X :=
    solvable_of_surjective (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X).toMonoidHom)
      Subgroup.topEquiv.surjective
  exact hab ((IsSimpleGroup.comm_iff_isSolvable.2 this) a b)

end CFSG.ASVolI
