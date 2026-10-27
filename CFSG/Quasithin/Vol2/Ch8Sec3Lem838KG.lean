module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin.H13

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def OutIsTwoGroup (K : Type) [Group K] : Prop :=
  ∀ φ : MulAut K, ∃ k : ℕ, φ ^ 2 ^ k ∈ (MulAut.conj : K →* MulAut K).range

@[expose] def KG838Out : Prop :=
  (∀ (K : Type) [Group K] [Finite K] (p : ℕ), StatedClassicalModel K .PSL 2 p 1 →
      OutIsTwoGroup K) ∧
    (∀ (K : Type) [Group K] [Finite K], StatedClassicalModel K .PSL 4 2 1 → OutIsTwoGroup K) ∧
    (∀ (K : Type) [Group K] [Finite K], StatedClassicalModel K .PSL 5 2 1 → OutIsTwoGroup K) ∧
    (∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* NativeSporadic.Carrier .He) →
      OutIsTwoGroup K)

@[expose] def KG838Par : Prop :=
  ∀ (K : Type) [Group K] [Finite K],
    (StatedClassicalModel K .PSL 4 2 1 ∨ StatedClassicalModel K .PSL 5 2 1 ∨
      Nonempty (K ≃* NativeSporadic.Carrier .He)) →
    ∀ (S : Sylow 2 K) (Y : Subgroup K), (S : Subgroup K) ≤ Subgroup.normalizer (Y : Set K) →
      ¬ 3 ∣ Nat.card Y → Y ≤ S

end CFSG.Quasithin.H13
