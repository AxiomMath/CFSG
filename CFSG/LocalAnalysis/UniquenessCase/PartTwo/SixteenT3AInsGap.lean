module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Ctx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def S16GapA168FourThree (D : Data G) : Prop :=
  UC6S846.SigmaStd D →
  ∀ (V L : Subgroup G) (hV : IsElemAbelian 2 V), Counterex16 D ⊥ V L hV →
    ¬ Concl1613_2 D ⊥ V hV L →
    ⁅oddBar D.M ⊥ V hV, barSub ⊥ V hV (E3.wClos V D.k D.T)⁆ ≠ ⊥ →
    Case168_4At D ⊥ V hV L 3 2 →
    ¬ 3 ≤ CFSG.Open.pRank 3 (Mbar D.M ⊥ V hV) →
    3 ^ 3 ∣ Nat.card (Mbar D.M ⊥ V hV) →
    ∀ (ι : Type) [Fintype ι] (Y : ι → Subgroup (Vtil ⊥ V hV)),
      Fintype.card ι = 3 → iSupIndep Y → Function.Injective Y → ⨆ i, Y i = ⊤ →
      (∀ i, rk ↥(Y i) = dParam 3) →
      (∀ g ∈ Mbar D.M ⊥ V hV, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) →
      (∀ π : Equiv.Perm ι, ∃ g ∈ Mbar D.M ⊥ V hV,
        ∀ i, (Y i).map g.toMonoidHom = Y (π i)) →
      (∀ E : Subgroup G, E ≤ D.M → IsElemAbelian 3 E → 3 ^ 3 ≤ Nat.card E →
        (∃ b ∈ barSub ⊥ V hV E, ∃ i, (Y i).map b.toMonoidHom ≠ Y i) ∧
        ∃ w ∈ barSub ⊥ V hV (E3.wClos V D.k D.T), ∃ f ∈ barSub ⊥ V hV E,
          w * f * w⁻¹ ∉ barSub ⊥ V hV E) →
      Insp1613U D V

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
