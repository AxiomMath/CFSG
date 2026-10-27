module

public import CFSG.RankThree.PartTwo.Sec15.HypR
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item136Pair

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14


variable {G : Type} [Group G] [Finite G]

theorem center_eq_bot_of_types {K : Subgroup G} {a : G} (hK : K ∈ thetaComponentsAt 3 a)
    (htypes : Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
      IsLThreePi (K ⧸ aschbacherSolvableCore 3 K) ∨
      Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* CFSG.Blueprint.NativeSporadic.M12)) :
    Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ := by
  obtain ⟨⟨-, hM22z⟩, ⟨-, hM12z⟩, ⟨-, hJ2z⟩⟩ := sporadicModels131
  have hq : IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hK
  rcases htypes with ⟨⟨φ⟩⟩ | hL3 | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact center_eq_bot_of_mulEquiv φ hJ2z
  · obtain ⟨p, e, hp, he, hcase⟩ := hL3
    rcases hcase with ⟨hq3, ⟨φ⟩⟩ | ⟨hq3, ⟨φ⟩⟩
    · exact center_eq_bot_of_mulEquiv φ (isPerfect_center_projSL p e he hq3).2
    · by_cases hq2 : 2 < p ^ e
      · exact center_eq_bot_of_mulEquiv φ (isPerfect_center_projSU p e he hq3 hq2).2
      ·
        exfalso
        have h2 : p ^ e = 2 := by
          have : 2 ≤ p ^ e := le_trans hp.out.two_le (Nat.le_self_pow (by omega) _)
          omega
        obtain ⟨rfl, rfl⟩ := eq_two_one_of_pow_eq_two hp.out h2
        have := isSolvable_projSU_two
        have hsol : Group.IsSolvable (K ⧸ aschbacherSolvableCore 3 K) :=
          Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
        have : Nontrivial (K ⧸ aschbacherSolvableCore 3 K) := by
          obtain ⟨x, y, hxy⟩ := hq.2.2
          by_contra hn
          rw [not_nontrivial_iff_subsingleton] at hn
          apply hxy
          have : Subsingleton ((K ⧸ aschbacherSolvableCore 3 K) ⧸
              Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) :=
            QuotientGroup.mk_surjective.subsingleton
          exact Subsingleton.elim _ _
        have := hq.1
        exact Group.IsPerfect.not_isSolvable _ hsol
  · exact center_eq_bot_of_mulEquiv φ isPerfect_center_alt7.2
  · exact center_eq_bot_of_mulEquiv φ hM22z
  · exact center_eq_bot_of_mulEquiv φ hM12z

theorem Sec15R.hypS {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L) : HypS A := by
  refine ⟨h.toSec13Data.mem_partTwoE, h.not_mem_partTwoT, fun a ha K hK => ?_⟩
  have hD : Sec13Data G A a K := { h.toSec13Data with zpowers_mem_omegaA := ha, mem_lA := hK }
  exact not_mem_of_center_eq_bot hD
    (center_eq_bot_of_types hD.mem_thetaComponentsAt (h.chosen136.2 a ha K hK).1)

end CFSG.RankThree.PartTwo.Sec15
