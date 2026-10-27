module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamSModelSix
public import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield

public section

namespace CFSG.Quasithin.F6.GoldAmS

theorem isSp42_S6 : IsSp42 S6 := by
  have : CharP (ZMod 2) 2 := ZMod.charP 2
  have hk : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  obtain ⟨e6⟩ := CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm hk
  have hbij : Function.Bijective
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 (ZMod 2)) :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
  exact ⟨ZMod 2, inferInstance, inferInstance, by rw [Nat.card_eq_fintype_card, hk],
    ⟨e6.symm.trans (MulEquiv.ofBijective _ hbij)⟩⟩

theorem exists_model_Sp42 : ∃ (W : Type) (_ : Group W) (_ : Finite W) (K₁ K₂ : Subgroup W),
    IsSp42 W ∧ IsTwoLocalAmalgam K₁ K₂ ∧ Nonempty (TypeBData K₁ K₂) :=
  ⟨S6, inferInstance, inferInstance, S6G1, S6G2, isSp42_S6, isTwoLocalAmalgam_S6, ⟨typeB_S6⟩⟩

end CFSG.Quasithin.F6.GoldAmS
