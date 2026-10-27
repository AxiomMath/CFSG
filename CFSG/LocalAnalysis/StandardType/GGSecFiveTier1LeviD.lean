module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatLeviDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1System
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Weyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1PresDLevi

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld

section LeviD

variable {G : Type} [Group G] [Finite G]

theorem ggSecFiveLeviD_of_tier1 (hT : GGSecFiveTier1Input) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hsplit : GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) {n : ℕ} (hn : 4 ≤ n)
    (e' : Fin n ≃ ι) (hM : M = (ggCoxeterMatrixD n).reindex e') :
    GGLeviPresented (L ⊔ ⨆ K ∈ 𝒦, K)
      (fun i : ι => ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) := by
  have hsl : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 :=
    GGIsWeylMatrixAD.le_three (Or.inr ⟨n, e', hn, hM⟩)
  have hlabel2 : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      M.M (e' i) (e' j) = 2 := by
    intro i j hij h1 h2
    rw [hM, coxeterMatrix_reindex_apply_equiv]
    exact ggCoxeterMatrixD_eq_two hn i j hij h1 h2
  have hlabel3 : ∀ i j : Fin n, edgeD n i j → M.M (e' i) (e' j) = 3 := by
    intro i j h
    rw [hM, coxeterMatrix_reindex_apply_equiv]
    exact ggCoxeterMatrixD_eq_three hn i j h
  obtain ⟨f, U, hq, hgen, hcomm, hpair, hmap⟩ := tier1_system hT hcfg hsplit hpres hsl e'
    (fun i j : Fin n => i ≠ j ∧ ¬ edgeD n i j ∧ ¬ edgeD n j i) (fun i j : Fin n => edgeD n i j)
    (fun i j hij => ⟨hij.1, hlabel2 i j hij.1 hij.2.1 hij.2.2⟩) hlabel3
  obtain ⟨ψ, hψ, σ, -, hlevi⟩ := ggPresentsG0_typeD_of_system_levi hn hq
    (fun i j hij h1 h2 => hcomm i j ⟨hij, h1, h2⟩) hpair hgen
  refine ⟨.POmegaPlus, n, f, ψ, by simp, by simp only [bnRank]; omega, hψ, σ.trans e', ?_⟩
  intro k
  exact (hlevi k).trans (hmap (σ k))

end LeviD

end CFSG.StandardType

end
