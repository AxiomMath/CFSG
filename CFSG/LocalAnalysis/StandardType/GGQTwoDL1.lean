module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDInputs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1Odd
public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1Seed
public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1Transfer
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly

section Odd


theorem qtwoDL1_rankOne_of_odd (ha₀ : GGLNoncyclicInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) {m : ℕ} {e' : Fin m ≃ ι}
    (hM : M = (ggCoxeterMatrixD m).reindex e')
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer (Bs : Set G))))
    {X : Subgroup G} (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X)
    {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs) (hrC : r ∈ ggCoxRefl M e) :
    ggRankOne Bs r = ggRankOneIn X Bs r ∧ Nat.card ↥(ggRankOne Bs r) = 6 := by
  obtain ⟨hroute, -, -, hpres, r₀, hr₀A, hr₀C, hr₀6⟩ := hcfg
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hroute
  have h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := by
    intro i j hij
    have hne : e'.symm i ≠ e'.symm j := fun h => hij (e'.symm.injective h)
    have h23 := CFSG.ClassicalInvolution.PhanDn.QTwo.ggCoxeterMatrixD_two_or_three _ _ hne
    rw [hM, CoxeterMatrix.reindex_apply]
    omega
  have hseed : ggRankOne Bs r₀ = ggRankOneIn L Bs r₀ :=
    qtwoDL1_seed ha₀ hroute hodd hr₀A (ggCoxRefl_isReflection hpres.2 hr₀C) hr₀6
  have h6 : Nat.card ↥(ggRankOne Bs r₀) = 6 := by rw [hseed]; exact hr₀6
  have hXN : Bs ≤ Subgroup.normalizer (X : Set G) := by
    rcases hX with rfl | ⟨y, hy⟩
    · exact GGDichotomy.le_normalizer_of_innerDiagOn hroute.1.2.2.1.1
    · exact GGDichotomy.le_normalizer_of_innerDiagOn (hroute.1.2.2.1.2 y X hy)
  exact qtwoDL1_transfer hp hp2 (ggRouteCfg_isElemAbelian hroute) hpres h3 hr₀C h6 hXN hrA hrC

@[expose] def GGQTwoDL1InvFixInputOn (R : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
      ∀ (m : ℕ) (e' : Fin m ≃ ι), R m → M = (ggCoxeterMatrixD m).reindex e' →
        B = Bs → QTwoDL1InvFix p B Bs x L D J

@[expose] def GGQTwoDL1InvFixInput : Prop :=
  GGQTwoDL1InvFixInputOn fun m => 7 ≤ m

theorem qtwoDL1_odd_of_cfg {R : ℕ → Prop} (ha₀ : GGLNoncyclicInput) (hL : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (hfix : GGQTwoDL1InvFixInputOn R) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) {m : ℕ} {e' : Fin m ≃ ι} (hm : R m)
    (hM : M = (ggCoxeterMatrixD m).reindex e') :
    Odd (Nat.card ↥(Subgroup.centralizer (Bs : Set G))) := by
  have hroute := hcfg.1
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hroute.1.1.1 hroute.1.1.2.2
  by_cases hB : B = Bs
  · exact qtwoDL1_odd_centralizer_of_invFix ha₀ hL hroute hpJ
      (hfix G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM hB)
  · exact qtwoDL1_odd_centralizer_of_ne hroute hB

theorem ggQTwoL1Input_of_invFix {R : ℕ → Prop} (ha₀ : GGLNoncyclicInput) (hL : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (hfix : GGQTwoDL1InvFixInputOn R) : GGQTwoL1InputOn R := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM X hX r hrA hrC
  exact qtwoDL1_rankOne_of_odd ha₀ hcfg hM (qtwoDL1_odd_of_cfg ha₀ hL hP hfix hcfg hm hM) hX hrA
    hrC

end Odd

end CFSG.StandardType.QTwo

end
