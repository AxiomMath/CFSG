module

public import CFSG.RankThree.PartTwo.Sec8.Item87Proof84
import CFSG.RankThree.PartTwo.Sec8.Item87Res2ProofLink
import CFSG.RankThree.PartTwo.KFacts.K72FieldKind
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo


@[expose] def KF84Outer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    Sec4.InducesOuterTheta a (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)))

@[expose] def KF84FieldRee : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    IsGammaTypeRee (L ⧸ aschbacherSolvableCore 3 L) n →
    KFacts.InducesStdKind (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G))) a
      .field

theorem kF84Field_of (hO : KF84Outer) (hR : KF84FieldRee) : KF84Field := by
  intro G _ _ A c L a b X n h
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  rcases Item87Res2Proof.quot_cases_of_isGammaIndex h.isGammaIndex with ⟨hRee, -⟩ | hL2
  · exact hR G A c L a b X n h hRee
  · obtain ⟨e⟩ := hL2
    exact .psl2 (GaloisField 2 (3 * n))
      ⟨e.trans (Sec4.projSLEquivPSL _), KFacts.inducesKind_field_of_pow_three _ ha3
        (hO G A c L a b X n h) _⟩

end CFSG.RankThree.PartTwo.Sec8
