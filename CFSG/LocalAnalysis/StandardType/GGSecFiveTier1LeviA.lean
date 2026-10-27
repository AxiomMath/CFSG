module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatLeviDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1System
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Weyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1PresALevi

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.WeakCT

section LeviA

variable {G : Type} [Group G] [Finite G]

theorem ggSecFiveLeviA_of_tier1 (hT : GGSecFiveTier1Input) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hsplit : GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) {n : ℕ} (hn : 3 ≤ n)
    (e' : Fin n ≃ ι) (hM : M = (CoxeterMatrix.A n).reindex e') :
    GGLeviPresented (L ⊔ ⨆ K ∈ 𝒦, K)
      (fun i : ι => ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) := by
  have hsl : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 :=
    GGIsWeylMatrixAD.le_three (Or.inl ⟨n, e', hn, hM⟩)
  have hlabel2 : ∀ i j : Fin n, (i : ℕ) + 1 < j → M.M (e' i) (e' j) = 2 := by
    intro i j hij
    rw [hM, coxeterMatrix_reindex_apply_equiv]
    exact coxeterMatrixA_eq_two n i j hij
  have hlabel3 : ∀ i j : Fin n, (j : ℕ) = i + 1 → M.M (e' i) (e' j) = 3 := by
    intro i j hij
    rw [hM, coxeterMatrix_reindex_apply_equiv]
    exact coxeterMatrixA_eq_three n i j hij
  obtain ⟨f, U, hq, hgen, hcomm, hpair, hmap⟩ := tier1_system hT hcfg hsplit hpres hsl e'
    (fun i j : Fin n => (i : ℕ) + 1 < j) (fun i j : Fin n => (j : ℕ) = i + 1)
    (fun i j hij => ⟨fun h => by subst h; omega, hlabel2 i j hij⟩) hlabel3
  obtain ⟨ψ, hψ, σ, -, hlevi⟩ := ggPresentsG0_typeA_of_system_levi hn hq hcomm hpair hgen
  exact ⟨.PSL, n + 1, f, ψ, by simp, by simp only [bnRank]; omega, hψ, σ.trans e',
    fun k => (hlevi k).trans (hmap (σ k))⟩

end LeviA

end CFSG.StandardType

end
