module

public import CFSG.Quasithin.Background.Harris.L3.IdentHermEnd
public import CFSG.Quasithin.Background.Harris.L3.IdentHermGroup
public import CFSG.Quasithin.Background.Harris.L2.Natural
public import CFSG.Quasithin.Background.Harris.L3.Classify
public import CFSG.Quasithin.Background.Harris.L3.IdentNat

public section

namespace CFSG.Quasithin.G11.Harris.L3

set_option linter.unusedSectionVars false

open CFSG.Quasithin.H.L3Nine Matrix
open scoped MatrixGroups

theorem card_of_hermShape {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {F : Type} [Field F] [Finite F] [CharP F 2] {k : ℕ} (hk : 1 ≤ k)
    (hK : Nat.card F = (2 ^ k) ^ 2) (E : Multiplicative V ≃* HMod k F) :
    Nat.card V = 2 ^ (9 * k) := by
  rw [← card_HMod hk hK, ← Nat.card_congr E.toEquiv]
  exact Nat.card_congr (Multiplicative.ofAdd : V ≃ Multiplicative V)

theorem case17_holds : Case17Input := by
  intro V _ _ _ Γ A L m k hs hk π hπ hm hH
  obtain ⟨hK, ψ, hψ, E, hE⟩ := hH
  have hk1 : 1 ≤ k := by omega
  have hV := card_of_hermShape hk1 hK E
  have hdim : Module.finrank (ZMod 2) V = 9 * k := finrank_eq_of_natCard hV
  have hb := hs.bound
  refine ⟨k, ⟨hk, hdim, by omega, isSL3_or_isPSL_herm hk1 hπ hK hψ hE,
    isHermitianTensorModule_herm hπ hK hψ hE⟩, ?_,
    not_selfDual_herm hk1 hK (hermQ_radSet hK hψ hE) (radSet_subset π ψ) hV⟩
  exact CFSG.Quasithin.G11.Harris.L2.endIsField_of_natCard hs.L_irr
    (natCard_endCommutant_herm hπ hk1 hK hψ hE hs.L_irr)

theorem notSelfDual_holds : NotSelfDualInput := by
  intro V _ _ _ L f hf π hπ hirr hshape
  rcases hshape with hN | ⟨k, hH⟩
  · exact not_selfDual_natShape hN
  · obtain ⟨hK, ψ, hψ, E, hE⟩ := hH
    have hk1 : 1 ≤ k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      subst hk0
      have : 1 < Nat.card (GaloisField 2 f) := Finite.one_lt_card
      simp at hK
      omega
    exact not_selfDual_herm hk1 hK (hermQ_radSet hK hψ hE) (radSet_subset π ψ)
      (card_of_hermShape hk1 hK E)

end CFSG.Quasithin.G11.Harris.L3
