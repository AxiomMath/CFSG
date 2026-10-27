module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaPlusFourTwoNatInvIso
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaPlusFourTwoNatScalarTwisted

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H.Pair
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem exists_pair_of_sumOfNat_two {W : Type} [CommGroup W]
    {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop} {X : Subgroup (MulAut W)}
    (hsum : SumOfNat N X ⊤ ⊥ 2) :
    ∃ I : Fin 2 → Subgroup W, I 0 ⊓ I 1 = ⊥ ∧ I 0 ⊔ I 1 = ⊤ ∧ (∀ i, N X (I i) ⊥) ∧
      (∀ i, I i ⊓ (⊥ ⊔ ⨆ (j : Fin 2) (_ : j ≠ i), I j) ≤ ⊥) ∧ (⊥ ⊔ ⨆ i, I i) = ⊤ := by
  obtain ⟨I, -, hind, hsup, hN⟩ := hsum
  have hrest : ∀ i j : Fin 2, i ≠ j → (⨆ (k : Fin 2) (_ : k ≠ i), I k) = I j := by
    intro i j hij
    refine le_antisymm (iSup₂_le fun k hk => ?_) (le_iSup₂ (f := fun k (_ : k ≠ i) => I k) j
      (Ne.symm hij))
    have hkj : k = j := by omega
    rw [hkj]
  have hinf : I 0 ⊓ I 1 = ⊥ := by
    have h0 := hind 0
    rw [hrest 0 1 (by decide), bot_sup_eq] at h0
    exact le_bot_iff.1 h0
  have hsup' : I 0 ⊔ I 1 = ⊤ := by
    have hall : (⨆ i, I i) = I 0 ⊔ I 1 := by
      refine le_antisymm (iSup_le fun i => ?_) (sup_le (le_iSup I 0) (le_iSup I 1))
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    have h := hsup
    rw [hall, bot_sup_eq] at h
    exact h
  exact ⟨I, hinf, hsup', hN, hind, hsup⟩

theorem sumOfNatIsoMod_of_pair {W : Type} [CommGroup W]
    {X : Subgroup (MulAut W)} {I : Fin 2 → Subgroup W}
    (hIind : ∀ i, I i ⊓ (⊥ ⊔ ⨆ (j : Fin 2) (_ : j ≠ i), I j) ≤ ⊥)
    (hIsup : (⊥ ⊔ ⨆ i, I i) = ⊤)
    (hIN : ∀ i, NatOmegaPlus X (I i) ⊥ 4 2)
    (hiso : IsoMod X (I 0) (I 1)) :
    SumOfNatIsoMod (fun H U Z => NatOmegaPlus H U Z 4 2) X ⊤ ⊥ 2 := by
  refine ⟨I, fun _ => bot_le, hIind, hIsup, hIN, fun i j => ?_⟩
  fin_cases i <;> fin_cases j
  · exact ⟨MulEquiv.refl _, fun _ _ _ _ => rfl⟩
  · exact hiso
  · have hinv : IsInv X (I 0) := by
      obtain ⟨-, K, hF, hFin, -, π, hRV⟩ := hIN 0
      exact fun x hx => hRV.2.2.2.1 ⟨x, hx⟩
    exact IsoMod.symm hinv hiso
  · exact ⟨MulEquiv.refl _, fun _ _ _ _ => rfl⟩

theorem k_OmegaPlusFour_twoNat_inv_holds : K_OmegaPlusFour_twoNat_inv := by
  intro W _ _ hW X H hXH hHN hX hsum w hwH hw1 hw2 hm
  obtain ⟨I, hIbot, hItop, hIN, hIind, hIsup⟩ := exists_pair_of_sumOfNat_two hsum
  by_cases hiso : IsoMod X (I 0) (I 1)
  · have hsumIso : SumOfNatIsoMod (fun H U Z => NatOmegaPlus H U Z 4 2) X ⊤ ⊥ 2 :=
      sumOfNatIsoMod_of_pair hIind hIsup hIN hiso
    exact k_OmegaPlusFour_twoNat_inv_of_isoMod hW hXH hHN hX hsumIso hwH hw1 hw2 hm
  · exact (false_of_involution_of_not_isoMod hIbot hItop hIN hiso (hHN hwH) hw2 hm).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
