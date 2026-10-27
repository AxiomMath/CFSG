module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KFacts
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3Torus
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3U4
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3U5Torus
import CFSG.LocalAnalysis.EvenBN.U5.Setting
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismBasic
import CFSG.Quasithin.H13.U4ParModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

open CFSG.Open Subgroup CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Syl3

theorem sylow_three_comm {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsU45 X n)
    {S : Subgroup X} (hS : IsPGroup 3 S) (hSi : ¬ 3 ∣ S.index) :
    ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases hX with ⟨hU5, rfl⟩ | ⟨hU4, hn⟩
  · obtain ⟨K, _, h, ⟨e⟩⟩ := CFSG.LocalAnalysis.EvenBN.U5.exists_hypPSU_equiv one_le_two hU5
    have : Finite (hypPSU h 2 1) := Finite.of_equiv X e.toEquiv
    obtain ⟨hp, hi, hE, _⟩ := sylow_three_hypPSU_two_one h
    obtain ⟨φ, hφ⟩ := CFSG.ProperTwoGeneratedCore.RootCenter.exists_mulEquiv_map_eq e
      (hp.toSylow hi) (hS.toSylow hSi)
    simp only [IsPGroup.toSylow_coe] at hφ
    subst hφ
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    have h := congrArg (fun t : ↥((torusPow h 2 1 3).map (hypProj h 2 1)) =>
      φ.toMonoidHom (t : hypPSU h 2 1)) (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    simpa only [Subgroup.coe_mul, map_mul] using h
  · obtain ⟨K, _, h, ⟨e⟩⟩ := CFSG.Quasithin.H13.U4Par.exists_hypSU_equiv_of_lieModel hU4
    have := CFSG.Quasithin.H13.U4Par.finite_hypSU h
    obtain ⟨hp, hi, _, _⟩ := sylow_three_hypSU_two_zero h hn
    obtain ⟨φ, hφ⟩ := CFSG.ProperTwoGeneratedCore.RootCenter.exists_mulEquiv_map_eq e.symm
      (hp.toSylow hi) (hS.toSylow hSi)
    simp only [IsPGroup.toSylow_coe] at hφ
    subst hφ
    have hcomm : IsMulCommutative
        ↥(torusPow h 2 0 (3 ^ (Nat.card Kˣ).factorization 3)) :=
      (isElemAbelian_torusPow h 2 0 _).1
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    have h := congrArg (fun t : ↥(torusPow h 2 0 (3 ^ (Nat.card Kˣ).factorization 3)) =>
      φ.toMonoidHom (t : hypSU h 2 0)) (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    simpa only [Subgroup.coe_mul, map_mul] using h

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105
