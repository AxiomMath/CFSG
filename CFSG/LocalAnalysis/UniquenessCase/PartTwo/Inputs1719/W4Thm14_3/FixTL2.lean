module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.FixTBorel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.Quasithin.JonesParshall
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups

theorem exists_borelMoves_of_isL2 (hExt : K14_3Ext) {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} {n : ℕ} (hL : IsL2 ↥L n) (hn : 3 ≤ n)
    {J : Subgroup W} (hJ : J ∈ irrSet L) (hJC : J ⊓ fixV L ≠ ⊥) :
    ∃ S₀ : Subgroup (MulAut W), IsSylowIn 2 S₀ L ∧ BorelMoves L S₀ := by
  obtain ⟨K, hKf, hKfin, hKcard, hR⟩ := hExt W hW L n hL hn J hJ hJC
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by rw [← Nat.card_eq_fintype_card, hKcard])
  have h8 : 8 ≤ Nat.card K := by
    rw [hKcard]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hcard : Nat.card ↥L = Nat.card SL(2, K) := by
    obtain ⟨-, F, hFf, hFfin, hFcard, ⟨eF⟩⟩ :=
      CFSG.Blueprint.LieModel.statedClassicalModel hL (t := .PSL) (n := 2) (p := 2) (f := n)
        (by decide)
    letI : Field F := hFf
    letI : Finite F := hFfin
    haveI : Fintype F := Fintype.ofFinite F
    haveI : CharP F 2 :=
      charP_of_card_eq_prime_pow (p := 2) (f := n)
        (by rw [← Nat.card_eq_fintype_card, hFcard])
    have hcardF : Nat.card ↥L = Nat.card SL(2, F) := by
      rw [Nat.card_congr eF.toEquiv]
      rw [← Nat.card_congr
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).toEquiv]
      exact Nat.card_congr (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := F)).toEquiv
    rw [hcardF, CFSG.GorensteinWalter.sl2_card_formula F,
      CFSG.GorensteinWalter.sl2_card_formula K, hFcard, hKcard]
  obtain ⟨π, hπ⟩ := hR
  exact borelMoves_of_realizesVia (J₀ := J ⊓ fixV L) hW h8 π hπ inf_le_right hcard

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3
