module

public import CFSG.LocalAnalysis.StandardType.GGL45E67RankLift
public import CFSG.LocalAnalysis.StandardType.GGL45E67RankChev
public import CFSG.LocalAnalysis.StandardType.GGL45E67RankTwE6
public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
public import CFSG.LocalAnalysis.StandardType.GGL45FamCover
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGL45E67Rank (p : ℕ) (lab : LargeEvenLabel) : LargeEvenRawCont :=
  fun R _ I F => ∀ (K : Type) [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R),
    commutator K = ⊤ → ∀ (ψ : MulAut K) (E : Subgroup (MulAut K)),
      GGL45TorusKGHyp p lab I F θ ψ E →
        p ^ 4 ≤ Nat.card E ∧ (lab.tag = .E7 → p ^ 6 ≤ Nat.card E)

private theorem ggL45E67RankOn_E6
    {l n : ℕ} :
    LargeEvenLabelAll ⟨.E6, l, n⟩ (GGL45E67Rank 3 ⟨.E6, l, n⟩) := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  refine recipeChevalley_and (P := GGL45E67Rank 3 ⟨.E6, l, n⟩) (fun K _ _ hK => ?_) hQ
  intro K' _ _ θ hθ ψ E hyp
  have : CharP K 2 := charP_two_of_card hK
  have hconf : ∀ f ∈ LargeEvenChevFieldImage (LargeEvenCartanE 6) K
      (LargeEvenChevH (LargeEvenCartanE 6) K false), orderOf f = 3 → GGL45E67Config f 4 :=
    fun f hf _ => ggL45E67Config_chevFieldImage (τ := CFSG.Blueprint.Chevalley.Tag.E6) (r := 4)
      (fun σ => ggL45E67Config_entrywise_E6 (K := K) σ) f hf
  refine ⟨three_pow_le_card_of_ggL45E67Config ⟨.E6, l, n⟩ θ ψ E hyp hconf, ?_⟩
  simp

private theorem ggL45E67RankOn_twE6
    {l n : ℕ} (hn : 1 ≤ n) :
    LargeEvenLabelAll ⟨.twE6, l, n⟩ (GGL45E67Rank 3 ⟨.twE6, l, n⟩) := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  refine recipeTwisted_and (P := GGL45E67Rank 3 ⟨.twE6, l, n⟩) (fun K _ _ hK => ?_) hQ
  intro K' _ _ θ hθ ψ E hyp
  have hK' : Nat.card K = 2 ^ (n * 2) := by
    rw [pow_mul]
    exact hK
  have : CharP K 2 := charP_two_of_card hK'
  have hconf : ∀ f ∈ LargeEvenChevFieldImage (LargeEvenCartanE 6) K
      (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n),
      orderOf f = 3 → GGL45E67Config f 4 :=
    ggL45E67Config_twE6Recipe (n := n) hn hK
  refine ⟨three_pow_le_card_of_ggL45E67Config ⟨.twE6, l, n⟩ θ ψ E hyp hconf, ?_⟩
  simp

private theorem ggL45E67RankOn_E7
    {l n : ℕ} :
    LargeEvenLabelAll ⟨.E7, l, n⟩ (GGL45E67Rank 3 ⟨.E7, l, n⟩) := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  refine recipeChevalley_and (P := GGL45E67Rank 3 ⟨.E7, l, n⟩) (fun K _ _ hK => ?_) hQ
  intro K' _ _ θ hθ ψ E hyp
  have : CharP K 2 := charP_two_of_card hK
  have hconf : ∀ f ∈ LargeEvenChevFieldImage (LargeEvenCartanE 7) K
      (LargeEvenChevH (LargeEvenCartanE 7) K false), orderOf f = 3 → GGL45E67Config f 6 :=
    fun f hf _ => ggL45E67Config_chevFieldImage (τ := CFSG.Blueprint.Chevalley.Tag.E7) (r := 6)
      (fun σ => ggL45E67Config_entrywise_of_frame (TableBExcTwo.frameE7) (K := K) σ) f hf
  have h6 := three_pow_le_card_of_ggL45E67Config ⟨.E7, l, n⟩ θ ψ E hyp hconf
  exact ⟨le_trans (by norm_num) h6, fun _ => h6⟩

theorem ggL45E67RankOn_holds :
    GGL45NtOn GGL45FamE67 GGL45E67Rank := by
  intro p hp hp2 lab hlab hKG hS
  obtain ⟨rfl, hS⟩ := hS
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  rcases hS with ht | ht | ht <;> dsimp only at ht <;> subst ht
  · exact ggL45E67RankOn_E6
  · exact ggL45E67RankOn_twE6 hn
  · exact ggL45E67RankOn_E7

end CFSG.StandardType
