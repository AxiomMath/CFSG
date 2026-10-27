module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDShared
public import CFSG.LocalAnalysis.StandardType.GGOrthFrameCore
import CFSG.LocalAnalysis.StandardType.GGQTwoChartTwoThreeOdd
import CFSG.LocalAnalysis.StandardType.GGQTwoSixGensWindows
import CFSG.LocalAnalysis.StandardType.GGLinearFusionSLCent

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan

@[expose] def QTwoDL1OrthPair : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs X : Subgroup G)
    (Φ : OrthTorus.OrthFrameCore p Bs X), Nat.card Φ.F = 2 → Subgroup.center ↥X = ⊥ →
      ∀ r ∈ ggAutomizer X Bs, GGIsReflection p r → ∀ r' ∈ ggAutomizer X Bs, GGIsReflection p r' →
        r * r' ≠ r' * r →
          ∃ W : Subgroup G, W ≤ X ⊓ Subgroup.centralizer
              ((ggHyperplane Bs r ⊓ ggHyperplane Bs r' : Subgroup G) : Set G) ∧
            UnitaryBlockStandardPair (GaloisField 2 2) 2 1 W (ggRankOneIn X Bs r)
              (ggRankOneIn X Bs r') ∧ Nat.card ↥W = 216

theorem qtwoDL1_local_orth (hW : QTwoDL1OrthPair) {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs X : Subgroup G} (Φ : OrthTorus.OrthFrameCore p Bs X) (hF : Nat.card Φ.F = 2)
    (hZ : Subgroup.center ↥X = ⊥) {r r' : MulAut ↥Bs} (hrX : r ∈ ggAutomizer X Bs)
    (hr'X : r' ∈ ggAutomizer X Bs) (hr : GGIsReflection p r) (hr' : GGIsReflection p r')
    (hne : r * r' ≠ r' * r) :
    216 ≤ Nat.card ↥(ggRankTwoIn X Bs r r') := by
  obtain ⟨W, hWle, hpair, hWcard⟩ := hW G p Bs X Φ hF hZ r hrX hr r' hr'X hr' hne
  obtain ⟨θ, c, hrange, _hker, _hrest⟩ := hpair
  have htop : ggOTwoPrime (⊤ : Subgroup (Su (GaloisField 2 2) 2 1 3)) = ⊤ := by
    have hsu : CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary.coordBlockSU
        (GaloisField 2 2) 2 1 (Finset.univ : Finset (Fin 3)) = ⊤ :=
      SixPoint.qTwoSixWin_coordBlockSU_univ 3
    have h := qTwoChartTwoThree_oTwoPrime_coordBlockSU (F0 := GaloisField 2 2) (m := 3)
      natCard_galoisField_two_two (J := Finset.univ) (by simp) (by simp)
    rw [hsu] at h
    exact h
  have hWsub : W ≤ ggOTwoPrime (X ⊓ Subgroup.centralizer
      ((ggHyperplane Bs r ⊓ ggHyperplane Bs r' : Subgroup G) : Set G)) := by
    calc W = θ.range := hrange.symm
      _ = (⊤ : Subgroup (Su (GaloisField 2 2) 2 1 3)).map θ := by
        rw [Subgroup.map_top]
      _ = (ggOTwoPrime (⊤ : Subgroup (Su (GaloisField 2 2) 2 1 3))).map θ := by
        rw [htop]
      _ ≤ ggOTwoPrime ((⊤ : Subgroup (Su (GaloisField 2 2) 2 1 3)).map θ) :=
        LinFusion.map_ggOTwoPrime_le θ ⊤
      _ = ggOTwoPrime W := by rw [Subgroup.map_top, hrange]
      _ ≤ ggOTwoPrime (X ⊓ Subgroup.centralizer
          ((ggHyperplane Bs r ⊓ ggHyperplane Bs r' : Subgroup G) : Set G)) :=
        LinFusion.ggOTwoPrime_mono hWle
  calc 216 = Nat.card ↥W := hWcard.symm
    _ ≤ Nat.card ↥(ggOTwoPrime (X ⊓ Subgroup.centralizer
        ((ggHyperplane Bs r ⊓ ggHyperplane Bs r' : Subgroup G) : Set G))) :=
      Subgroup.card_le_of_le hWsub
    _ = Nat.card ↥(ggRankTwoIn X Bs r r') := rfl

end CFSG.StandardType.QTwo

end
