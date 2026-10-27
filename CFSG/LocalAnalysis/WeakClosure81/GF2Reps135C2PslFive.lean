module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslRep
public import CFSG.LieType.SpecialLinear.BinaryDescent.ExteriorTwist
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix
open CFSG.LieType.SpecialLinear
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem w135c2_psl_five {W : Type} [CommGroup W] [Finite W] [Module (ZMod 2) (Additive W)]
    {L : Subgroup (MulAut W)} {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = 2) (φ : SpecialLinearGroup (Fin 5) K →* ↥L)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 5) K))
    {j r : ℕ} (hj : j = 2 ∨ j = 3) (β : Additive W ≃+ (Set.powersetCard (Fin 5) j → K))
    (hβ : ∀ g w, β (pslRep φ g w) = extTwist 5 j r K g *ᵥ β w) : Chev2Item3 W L := by
  have hcenter : Subgroup.center (SpecialLinearGroup (Fin 5) K) = ⊥ :=
    center_specialLinear_eq_bot_of_card_two hK
  have hkerbot : φ.ker = ⊥ := le_bot_iff.mp (hker.trans (le_of_eq hcenter))
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hkerbot
  let e : SpecialLinearGroup (Fin 5) K ≃* ↥L := MulEquiv.ofBijective φ ⟨hinj, hφ⟩
  have hK' : Nat.card K = 2 := by rw [Nat.card_eq_fintype_card, hK]
  have hSLn : IsSLn ↥L 5 1 :=
    ⟨K, inferInstance, inferInstance, by rw [hK']; norm_num,
      ⟨e.symm.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 5 K)⟩⟩
  have hcardW : Nat.card W = 2 ^ 10 := by
    calc Nat.card W = Nat.card (Additive W) := (Nat.card_congr Additive.toMul).symm
      _ = Nat.card (Set.powersetCard (Fin 5) j → K) := Nat.card_congr β.toEquiv
      _ = Nat.card K ^ Nat.card (Set.powersetCard (Fin 5) j) := Nat.card_fun
      _ = 2 ^ 10 := by
            rw [hK', Set.powersetCard.card, Nat.card_fin]
            rcases hj with h | h <;> rw [h] <;> decide
  exact Or.inr (Or.inl ⟨hSLn, hcardW⟩)

end CFSG.LocalAnalysis.WeakClosure81
