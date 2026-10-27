module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6SplitRootGen
public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6SplitCoverComm
public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6Label
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLTransfer
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three
public import CFSG.LocalAnalysis.StandardType.GGTableBExcCoverRows

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three
  E6ThreeModel


theorem e6ThreeStrong_holds_E {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K - 1) :
    GGE6ThreeStrongSCr (adjointGroup .E6 K) ((hatAut .E6 K).range : Set _) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := Fintype.ofFinite K
  obtain ⟨n, -, hKcard⟩ := FiniteField.card K 2
  have hn : 1 ≤ (n : ℕ) := n.pos
  have hK : Nat.card K = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hKcard]
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) (p := 3) h3
  have hζ : ζ ^ 3 = 1 := hζo ▸ pow_orderOf_eq_one ζ
  exact strongSCr_of_good ggAbelianLift (eFrame K ζ hζ) (eFrame_good hζo hζ)
    (rGen_eFrame hζo hζ) (coverOdd_E (n : ℕ) hn hK) _ rfl (coverCommSCr_E6 h3)

theorem ggTorusGenTableB_E6_three {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K - 1) :
    GGTorusGenTableB 3 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) := by
  have hRk := ggTorusGenTableBRk_of_e6StrongSCr (e6ThreeStrong_holds_E h3)
  have hfull : GGTorusGenTableB 3 (adjointGroup .E6 K)
      ((hatAut .E6 K).range : Set _) :=
    ggTorusGenTableB_of_rk (r := 6) Nat.prime_three (by norm_num)
      (by simpa using TableBExc.ggTorusLift_adjoint_E6_three h3) hRk
  exact ggTorusGenTableB_of_mulEquiv (TableBExc.recipeEquiv .E6 K)
    (fun φ hφ => (recipeID_iff_hatAut φ).1 hφ) hfull

theorem largeEvenLabelAll_torusGenTableB_E6_three {lab : LargeEvenLabel}
    (hrow : GGL48TBE6Row 3 lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableB 3 R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hdvd⟩ := hrow
  dsimp only at ht
  subst ht
  intro Q hQ
  exact recipeChevalley_and (P := fun R _ I _ => GGTorusGenTableB 3 R I)
    (fun K _ _ hK => by
      have : CharP K 2 := charP_two_of_card hK
      exact ggTorusGenTableB_E6_three (by rw [hK]; exact hdvd)) hQ

end CFSG.StandardType
