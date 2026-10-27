module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatLeviDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1System
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1WeylE
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1PresE67
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1PresE8

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld

section LeviE

variable {G : Type} [Group G] [Finite G]

theorem ggSecFiveLeviE6_of_tier1 (hT : GGSecFiveTier1Input) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hsplit : GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (e' : Fin 6 ≃ ι) (hM : M = CoxeterMatrix.E₆.reindex e') :
    GGLeviPresented (L ⊔ ⨆ K ∈ 𝒦, K)
      (fun i : ι => ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) := by
  have hWeyl : GGIsWeylMatrixE M := Or.inl ⟨e', hM⟩
  have hsl : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := GGIsWeylMatrixE.le_three hWeyl
  have hlabel2 : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i →
      M.M (e' i) (e' j) = 2 := by
    intro i j hij h1 h2
    rw [hM, coxeterMatrix_reindex_apply_equiv]
    exact coxeterMatrixE6_eq_two i j hij h1 h2
  have hlabel3 : ∀ i j : Fin 6, edgeE 6 i j → M.M (e' i) (e' j) = 3 := by
    intro i j h
    rw [hM, coxeterMatrix_reindex_apply_equiv]
    exact coxeterMatrixE6_eq_three i j h
  obtain ⟨f, U, hq, hgen, hcomm, hpair, hmap⟩ := tier1_system hT hcfg hsplit hpres hsl e'
    (fun i j : Fin 6 => i ≠ j ∧ ¬ edgeE 6 i j ∧ ¬ edgeE 6 j i) (fun i j : Fin 6 => edgeE 6 i j)
    (fun i j hij => ⟨hij.1, hlabel2 i j hij.1 hij.2.1 hij.2.2⟩) hlabel3
  obtain ⟨ψ, hψ, σ, -, hlevi⟩ := ggPresentsG0_typeE6_of_system_levi hq
    (fun i j hij h1 h2 => hcomm i j ⟨hij, h1, h2⟩) hpair hgen
  exact ⟨.E6, 0, f, ψ, by simp, by simp [bnRank], hψ, σ.trans e',
    fun k => (hlevi k).trans (hmap (σ k))⟩

theorem ggSecFiveLeviE7_of_tier1 (hT : GGSecFiveTier1Input) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hsplit : GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (e' : Fin 7 ≃ ι) (hM : M = CoxeterMatrix.E₇.reindex e') :
    GGLeviPresented (L ⊔ ⨆ K ∈ 𝒦, K)
      (fun i : ι => ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) := by
  have hWeyl : GGIsWeylMatrixE M := Or.inr (Or.inl ⟨e', hM⟩)
  have hsl : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := GGIsWeylMatrixE.le_three hWeyl
  have hlabel2 : ∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i →
      M.M (e' i) (e' j) = 2 := by
    intro i j hij h1 h2
    rw [hM, coxeterMatrix_reindex_apply_equiv]
    exact coxeterMatrixE7_eq_two i j hij h1 h2
  have hlabel3 : ∀ i j : Fin 7, edgeE 7 i j → M.M (e' i) (e' j) = 3 := by
    intro i j h
    rw [hM, coxeterMatrix_reindex_apply_equiv]
    exact coxeterMatrixE7_eq_three i j h
  obtain ⟨f, U, hq, hgen, hcomm, hpair, hmap⟩ := tier1_system hT hcfg hsplit hpres hsl e'
    (fun i j : Fin 7 => i ≠ j ∧ ¬ edgeE 7 i j ∧ ¬ edgeE 7 j i) (fun i j : Fin 7 => edgeE 7 i j)
    (fun i j hij => ⟨hij.1, hlabel2 i j hij.1 hij.2.1 hij.2.2⟩) hlabel3
  obtain ⟨ψ, hψ, σ, -, hlevi⟩ := ggPresentsG0_typeE7_of_system_levi hq
    (fun i j hij h1 h2 => hcomm i j ⟨hij, h1, h2⟩) hpair hgen
  exact ⟨.E7, 0, f, ψ, by simp, by simp [bnRank], hψ, σ.trans e',
    fun k => (hlevi k).trans (hmap (σ k))⟩

theorem ggSecFiveLeviE8_of_tier1 (hT : GGSecFiveTier1Input) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hsplit : GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (e' : Fin 8 ≃ ι) (hM : M = CoxeterMatrix.E₈.reindex e') :
    GGLeviPresented (L ⊔ ⨆ K ∈ 𝒦, K)
      (fun i : ι => ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) := by
  have hWeyl : GGIsWeylMatrixE M := Or.inr (Or.inr ⟨e', hM⟩)
  have hsl : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := GGIsWeylMatrixE.le_three hWeyl
  have hlabel2 : ∀ i j : Fin 8, i ≠ j → ¬ edgeE 8 i j → ¬ edgeE 8 j i →
      M.M (e' i) (e' j) = 2 := by
    intro i j hij h1 h2
    rw [hM, coxeterMatrix_reindex_apply_equiv]
    exact coxeterMatrixE8_eq_two i j hij h1 h2
  have hlabel3 : ∀ i j : Fin 8, edgeE 8 i j → M.M (e' i) (e' j) = 3 := by
    intro i j h
    rw [hM, coxeterMatrix_reindex_apply_equiv]
    exact coxeterMatrixE8_eq_three i j h
  obtain ⟨f, U, hq, hgen, hcomm, hpair, hmap⟩ := tier1_system hT hcfg hsplit hpres hsl e'
    (fun i j : Fin 8 => i ≠ j ∧ ¬ edgeE 8 i j ∧ ¬ edgeE 8 j i) (fun i j : Fin 8 => edgeE 8 i j)
    (fun i j hij => ⟨hij.1, hlabel2 i j hij.1 hij.2.1 hij.2.2⟩) hlabel3
  obtain ⟨ψ, hψ, σ, -, hlevi⟩ := ggPresentsG0_typeE8_of_system_levi hq
    (fun i j hij h1 h2 => hcomm i j ⟨hij, h1, h2⟩) hpair hgen
  exact ⟨.E8, 0, f, ψ, by simp, by simp [bnRank], hψ, σ.trans e',
    fun k => (hlevi k).trans (hmap (σ k))⟩

end LeviE

end CFSG.StandardType

end
