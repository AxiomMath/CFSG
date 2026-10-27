module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldLinear
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalizedStatements

public section

open CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem fieldClauses_statedPSL {T : Type} [Group T] {n ℓ f p : ℕ}
    (hm : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSL n ℓ f) (hn : 3 ≤ n)
    (hp : p.Prime) (hodd : Odd p) (hpT : ¬ p ∣ Nat.card T) (hNL : SubfieldNonLocalizedPSL) :
    FieldClauses p T := by
  obtain ⟨-, K, _, _, -, ⟨eT⟩⟩ := hm
  let e' : T ≃* LinearFlag.projectiveSL n K :=
    eT.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K))
  have hpT' : ¬ p ∣ Nat.card (LinearFlag.projectiveSL n K) := by
    rwa [← Nat.card_congr e'.toEquiv]
  exact FieldClauses.of_mulEquiv e'.symm
    (fieldClauses_projectiveSL hn hp hodd hpT' (hNL K n hn p hp hodd hpT'))

end CFSG.SignalizerFunctorTheorem.CatalogBridge
