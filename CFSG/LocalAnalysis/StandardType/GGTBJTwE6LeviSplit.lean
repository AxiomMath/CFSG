module

public import CFSG.LocalAnalysis.StandardType.GGTBJF4LeviFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJETypeCells
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6LeviSplitClass
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6LeviSplitThreeFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6LeviSplitModel
public import CFSG.LocalAnalysis.StandardType.GGTwE6SplitRootGenRoot

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem twE6Split_leviFrame
    {K : Type} [Field K] [Finite K] (σ : K →+* K) {n p : ℕ} [Fact p.Prime] [NeZero p]
    (hn : 2 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1)
    {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) (hζσ : σ (ζ : K) = ζ) :
    GGF4LeviFrame p (ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ).range := by
  obtain ⟨nk, wt, hnk, hwn, hwt⟩ := twE6Split_frame σ hn hK hσ hp2 hpn hζo hζ hζσ
  exact ⟨K, inferInstance, ζ, hζ, ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ, nk, _, wt, hζo,
    TwE6SplitRootGen.twE6SplitFrameHom_injective_of_orderOf σ hζo hζ hζσ, rfl, hnk, hwn, hwt,
    fun t ht Y hY => twE6Split_classFacts σ hn hK hσ hp2 hpn hζo hζ hζσ t ht hY⟩

theorem ggTwE6Split_leviModel_K
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.twE6, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.twE6, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n - 1) (hZ : Subgroup.center ↥K = ⊥) :
    GGF4LeviModel p Bs K := by
  obtain ⟨hN, F, hF, hFfin, σ, hcard, hσ, ζ, hζ, hζσ, e, hζo, hA⟩ :=
    ggTwE6Split_model_K hRig hH hΛ hK hp5 hpn hZ
  have hn2 : 2 ≤ n := by
    have h1n : 1 ≤ n := hΛ.1
    by_contra h
    have hn1 : n = 1 := by omega
    rw [hn1] at hpn
    have h1 : p ∣ 1 := by simpa using hpn
    exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp h1)
  have hZR : Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 F σ) = ⊥ := by
    have h1 : (Subgroup.center ↥K).map (e : ↥K →* ↥(graphFixedRootGroup TwistTag.E6 F σ)) =
        Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 F σ) := Subgroup.map_center_eq e
    rw [← h1, hZ, Subgroup.map_bot]
  exact ⟨hN, ↥(graphFixedRootGroup TwistTag.E6 F σ), inferInstance, hZR, e, _, hA,
    twE6Split_leviFrame σ hn2 hcard hσ (by omega) hpn hζo hζ hζσ⟩

theorem ggTBJTwE6LeviK_minus_ge5
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hJK : J ≤ K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.twE6, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.twE6, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n - 1) (hZ : Subgroup.center ↥K = ⊥) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J :=
  ggTBJF4LeviK_of_model hH hJK (ggTwE6Split_leviModel_K hRig hH hΛ hK hp5 hpn hZ)

end CFSG.StandardType

end
