module

public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.PartTwo.Sec17

@[expose] def J2NotSectionOfGLFourPrimeToThree : Prop :=
  ∀ (q : ℕ), q.Prime → 5 ≤ q → ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ q = 1) →
    Nat.card V ≤ q ^ 4 →
      ∀ (H : Type) [Group H] [Finite H] (φ : H →* MulAut V) (N : Subgroup H) [N.Normal],
        ¬ 3 ∣ Nat.card N → φ.ker ≤ N → IsEmpty ((H ⧸ N) ≃* CFSG.Blueprint.NativeSporadic.J2)

@[expose] def J2NotSectionOfGLFourTwo : Prop :=
  ∀ (q : ℕ), q.Prime → 5 ≤ q → ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ q = 1) →
    Nat.card V ≤ q ^ 4 →
      ∀ (H : Type) [Group H] [Finite H] (φ : H →* MulAut V) (N : Subgroup H) [N.Normal],
        IsPGroup 2 N → φ.ker ≤ N → IsEmpty ((H ⧸ N) ≃* CFSG.Blueprint.NativeSporadic.J2)

end CFSG.RankThree.PartTwo.Sec17
