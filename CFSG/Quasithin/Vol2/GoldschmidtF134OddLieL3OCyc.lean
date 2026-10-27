module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OLift
public import CFSG.LocalAnalysis.SectionRank.OddCover.CubicCyclic

public section

namespace CFSG.Quasithin.H13.NQCore.L3Odd

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

theorem isCyclic_of_isPGroup_projectiveSL {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hp3 : p ≠ 3) (hpq : ¬ p ∣ Nat.card K) (hp1 : ¬ p ∣ Nat.card K - 1)
    {P : Subgroup (projectiveSL 3 K)} (hP : IsPGroup p P) : IsCyclic P := by
  obtain ⟨Q, hQp, hQP, -⟩ := exists_lift_projectiveSL hp3 hP
  have hGL : IsCyclic (Q.map Matrix.SpecialLinearGroup.toGL) :=
    CFSG.SectionRank.OddCover.isCyclic_of_isPGroup_GL_three hpq hp1 (hQp.map _)
  have hQc : IsCyclic Q :=
    ((Q.equivMapOfInjective Matrix.SpecialLinearGroup.toGL
      Matrix.SpecialLinearGroup.toGL_injective).isCyclic).2 hGL
  have hc : IsCyclic (Q.map (proj 3 K)) :=
    isCyclic_of_surjective ((proj 3 K).subgroupMap Q)
      (MonoidHom.subgroupMap_surjective _ _)
  rwa [hQP] at hc

end CFSG.Quasithin.H13.NQCore.L3Odd
