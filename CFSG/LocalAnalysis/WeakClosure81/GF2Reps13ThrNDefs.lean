module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

@[expose] def R4_133N : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
    ∀ (A : Subgroup (MulAut W)) (t : MulAut W), t ∈ A → t ^ 2 = 1 → t ≠ 1 →
      rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3 → pCoreOf 2 A = ⊥ → IsIndivisible A →
      ∀ p : ℕ, p.Prime → ⁅pCoreOf p A, Subgroup.zpowers t⁆ ≠ ⊥ →
        ∃ L N : Subgroup (MulAut W), L ≤ N ∧ N ≤ pCoreOf p A ∧ (N.subgroupOf A).Normal ∧
          (∀ n ∈ N, ∀ w ∈ commSub ⊤ L, n w ∈ commSub ⊤ L) ∧
          (∀ g ∈ A, (commSub ⊤ L).map g.toMonoidHom = commSub ⊤ L →
            L.map (MulAut.conj g).toMonoidHom = L) ∧
          Conc4_133 A t L

end CFSG.LocalAnalysis.WeakClosure81
