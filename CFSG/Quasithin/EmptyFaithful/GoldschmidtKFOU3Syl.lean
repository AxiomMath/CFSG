module

public import CFSG.ClassicalInvolution.ModelFacts.OddCover.ThreeQ
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

theorem isCyclic_sylow_three_of_statedProj_su {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 1)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = (p ^ 1) ^ 2) {X : Type} [Group X]
    (e : X ≃* StatedProj (StatedSU 3 (p ^ 1) F)) (Q : Sylow 3 X) :
    IsCyclic ↥(Q : Subgroup X) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU : UnitaryFieldData p 1 F := ⟨hp, le_rfl, by rw [hF]; ring⟩
  have : CharP F p := hU.charP
  let f : StatedSU 3 (p ^ 1) F →* X :=
    e.symm.toMonoidHom.comp (QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf _))
  have hf : Function.Surjective f := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨T, rfl⟩ := Sylow.mapSurjective_surjective hf 3 Q
  have hcyc := CFSG.ClassicalInvolution.ModelFacts.OddCover.statedSU_three_isCyclic_sylow hF
    (by norm_num) (by rintro rfl; omega) (by rw [pow_one]; omega) T
  rw [Sylow.coe_mapSurjective]
  exact isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ _)

theorem mod_three_ne_one_of_noncyclic {p : ℕ} (hp : p.Prime) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (p ^ 1) ^ 2) {X : Type} [Group X]
    (e : X ≃* StatedProj (StatedSU 3 (p ^ 1) F))
    (hQ : ∃ Q : Sylow 3 X, ¬ IsCyclic ↥(Q : Subgroup X)) : p % 3 ≠ 1 := by
  intro hp3
  obtain ⟨Q, hQ⟩ := hQ
  exact hQ (isCyclic_sylow_three_of_statedProj_su hp hp3 hF e Q)

end CFSG.Quasithin.SBd19F
