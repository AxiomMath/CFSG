module

public import CFSG.LocalAnalysis.StandardType.GGTorusE7PlusToral

public section

namespace CFSG.StandardType.ExcPay

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType


theorem card_eq_pow_seven_of_sc_E7 {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hq : p ∣ Nat.card K + 1)
    (E : Subgroup (adjointGroup .E7 K)) (hE : IsElemAbelian p E)
    (hSC : ∀ g : adjointGroup .E7 K, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) :
    Nat.card E = p ^ 7 := by
  have hne : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨-, -, -, -, ι, -, -, -, -, -, hinj, hrange, -, -, -, -⟩ :=
    exists_e7_scalar_frame_of_sc hp hp5 hq E hE hSC
  have hcard : Nat.card E = Nat.card (Multiplicative (Fin Tag.E7.rank → ZMod p)) := by
    have h1 : Nat.card ι.range = Nat.card (Multiplicative (Fin Tag.E7.rank → ZMod p)) :=
      (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    rwa [hrange] at h1
  rw [hcard, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin,
    show Tag.E7.rank = 7 from rfl]

end CFSG.StandardType.ExcPay
