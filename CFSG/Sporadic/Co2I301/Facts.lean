module

public import CFSG.Sporadic.Co2I301.Inputs
public import CFSG.Sporadic.Co2Schreier.SixGroup

public section

namespace CFSG.Sporadic.Co2I301

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Schreier

@[expose] def RowCentFacts : Prop :=
  ∀ g ∈ co2P, Commute g (permOfArr 2300 (i301D ())) → Commute g locZ →
    (∃ i j k : ℕ, i < 3 ∧ j < 2 ∧ k < 2 ∧
      g * (permOfArr 2300 (i301D ()) ^ i * locZ ^ j * permOfArr 2300 (i301S ()) ^ k)⁻¹ ∈
        Subgroup.closure {permOfArr 2300 (i301K1 ()), permOfArr 2300 (i301K2 ())}) ∧
    (Commute g (permOfArr 2300 (i301K1 ())) → Commute g (permOfArr 2300 (i301K2 ())) →
      ∃ i j : ℕ, i < 3 ∧ j < 2 ∧ g = permOfArr 2300 (i301D ()) ^ i * locZ ^ j)

@[expose] def RowSixFacts : Prop :=
  ∀ Y : ℕ → Equiv.Perm (Fin 63), (∀ t < (hl63 ()).size, Rep 63 (hl63 ())[t]! (Y t)) →
    ∀ g ∈ Subgroup.closure {π | ∃ i < 2, sixPi i = π}, g * g = 1 → g ≠ 1 →
      ∃ t < (hl63 ()).size, ¬ Commute g (Y t * g * (Y t)⁻¹)

end CFSG.Sporadic.Co2I301

end
