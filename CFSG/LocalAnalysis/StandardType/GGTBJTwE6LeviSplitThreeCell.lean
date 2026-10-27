module

public import CFSG.LocalAnalysis.StandardType.GGTBJF4LeviFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJETypeCells
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6SplitFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6LeviSplitClass
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6LeviSplitThreeFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6LeviSplitThree
public import CFSG.LocalAnalysis.StandardType.GGTwE6SplitRootGenRoot

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem twE6Split_leviFrame_three
    {K : Type} [Field K] [Finite K] (σ : K →+* K) {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ n) (h3 : 3 ∣ 2 ^ n - 1)
    {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) (hζσ : σ (ζ : K) = ζ) :
    GGF4LeviFrame 3 (ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ).range := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨nk, wt, hnk, hwn, hwt⟩ := twE6Split_frame_three σ hn hK hσ h3 hζo hζ hζσ
  exact ⟨K, inferInstance, ζ, hζ, ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ, nk, _, wt, hζo,
    TwE6SplitRootGen.twE6SplitFrameHom_injective_of_orderOf σ hζo hζ hζσ, rfl, hnk, hwn, hwt,
    fun t ht Y hY => twE6Split_classFacts σ hn hK hσ (by norm_num) h3 hζo hζ hζσ t ht hY⟩

theorem ggTwE6Split_leviModel_K_three
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.twE6, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.twE6, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (h3 : 3 ∣ 2 ^ n - 1) :
    GGF4LeviModel 3 Bs K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hN, F, hF, hFfin, σ, hcard, hσ, ζ, hζ, hζσ, e, hZ, hζo, hA⟩ :=
    ggTwE6Split_model_K_three hRig hH hΛ hK h3
  have hn2 : 2 ≤ n := by
    have h1n : 1 ≤ n := hΛ.1
    by_contra h
    have hn1 : n = 1 := by omega
    rw [hn1] at h3
    omega
  have hZR : Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 F σ) = ⊥ := by
    have h1 : (Subgroup.center ↥K).map (e : ↥K →* ↥(graphFixedRootGroup TwistTag.E6 F σ)) =
        Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 F σ) := Subgroup.map_center_eq e
    rw [← h1, hZ, Subgroup.map_bot]
  exact ⟨hN, ↥(graphFixedRootGroup TwistTag.E6 F σ), inferInstance, hZR, e, _, hA,
    twE6Split_leviFrame_three σ hn2 hcard hσ h3 hζo hζ hζσ⟩

theorem ggTBJTwE6LeviK_minus_three
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hJK : J ≤ K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.twE6, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.twE6, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (h3 : 3 ∣ 2 ^ n - 1) :
    GGResSideDatum 3 Bs K J ∨ GGResLeviSideDatumLE3 3 Bs K J :=
  ggTBJF4LeviK_of_model hH hJK (ggTwE6Split_leviModel_K_three hRig hH hΛ hK h3)

end CFSG.StandardType

end
