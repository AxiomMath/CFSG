module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsFiveK
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.DescentLeft
public import CFSG.RankThree.PartTwo.KFacts.KS14MultCore
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXSp6TwoFactorCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Quasithin

private theorem ker_eq_bot_of_isL2_cover {E S : Type} [Group E] [Finite E] [Group S]
    (hE : Group.IsPerfect E) {j : ℕ} (hS : IsL2 S j)
    (f : E →* S) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card f.ker)) :
    f.ker = ⊥ := by
  haveI := hE
  have hPSL : IsPSL 2 2 j S := hS.statedClassicalModel (by decide)
  have hPSLq : IsPSL 2 2 j (E ⧸ f.ker) :=
    IsPSL.of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective f hf).symm hPSL
  refine CFSG.RankThree.PartTwo.KFacts.KS14.eq_bot_of_isPerfect_of_isCyclic_sylow hker ?_
  intro p hp hpker Q
  letI : Fact p.Prime := ⟨hp⟩
  exact CFSG.SectionRank.QTK.Insp443.isCyclic_sylow_of_isPSL_two_two hPSLq
    (hodd.ne_two_of_dvd_nat hpker) Q

theorem kSchurL2_holds : KSchurL2 := by
  intro X _ _ j hperf Z _ hZc hoddZ hshape
  haveI : Group.IsPerfect X := Group.IsPerfect.mk (by rw [commutator_def]; exact hperf)
  rcases hshape with hsingle | hsquare
  · have hker : (QuotientGroup.mk' Z).ker ≤ Subgroup.center X := by
      rw [QuotientGroup.ker_mk']
      exact hZc
    have hodd : Odd (Nat.card (QuotientGroup.mk' Z).ker) := by
      rw [QuotientGroup.ker_mk']
      exact hoddZ
    have hbot := ker_eq_bot_of_isL2_cover (E := X) (S := X ⧸ Z) inferInstance hsingle
      (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z) hker hodd
    rwa [QuotientGroup.ker_mk'] at hbot
  · obtain ⟨A, B, hGA, hGB, ⟨e⟩, hA, hB⟩ := hsquare
    letI : Group A := hGA
    letI : Group B := hGB
    haveI : Group.IsPerfect (X ⧸ Z) := inferInstance
    haveI : Group.IsPerfect (A × B) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    haveI : Group.IsPerfect A :=
      Group.IsPerfect.ofSurjective (f := MonoidHom.fst A B) fun a => ⟨(a, 1), rfl⟩
    haveI : Group.IsPerfect B :=
      Group.IsPerfect.ofSurjective (f := MonoidHom.snd A B) fun b => ⟨(1, b), rfl⟩
    let η : X →* A × B := e.toMonoidHom.comp (QuotientGroup.mk' Z)
    have hη : Function.Surjective η :=
      e.surjective.comp (QuotientGroup.mk'_surjective Z)
    have hkerη : η.ker = Z := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff]
      simpa using QuotientGroup.eq_one_iff (N := Z) x
    have hker : η.ker ≤ Subgroup.center X := by
      rw [hkerη]
      exact hZc
    have hodd : Odd (Nat.card η.ker) := by
      rw [hkerη]
      exact hoddZ
    have hcov₁ : ∀ E : Subgroup X, Group.IsPerfect E → ∀ f : E →* A,
        Function.Surjective f → f.ker ≤ Subgroup.center E → Odd (Nat.card f.ker) →
        f.ker = ⊥ :=
      fun E hE f hf hkerE hoddE => ker_eq_bot_of_isL2_cover hE hA f hf hkerE hoddE
    have hcov₂ : ∀ E : Subgroup X, Group.IsPerfect E → ∀ f : E →* B,
        Function.Surjective f → f.ker ≤ Subgroup.center E → Odd (Nat.card f.ker) →
        f.ker = ⊥ :=
      fun E hE f hf hkerE hoddE => ker_eq_bot_of_isL2_cover hE hB f hf hkerE hoddE
    have hbot :=
      CFSG.LocalAnalysis.ComponentInitial.SteinbergBX.TwoFactor.ker_eq_bot_of_perfect_central_prod
        η hη hker hodd hcov₁ hcov₂
    rwa [hkerη] at hbot

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
