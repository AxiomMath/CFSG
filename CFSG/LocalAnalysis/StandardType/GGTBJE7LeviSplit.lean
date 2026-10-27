module

public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviSplit
public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviEnnola
public import CFSG.LocalAnalysis.StandardType.GGTBTorE7
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeE7
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplit
public import CFSG.LocalAnalysis.StandardType.GGMaxRankJModel
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.E7Arith
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE7
public import CFSG.LocalAnalysis.StandardType.GGTBJE7LeviCore
public import CFSG.LocalAnalysis.StandardType.GGTBJE7Levi
public import CFSG.LocalAnalysis.StandardType.GGTBJE7LeviSplitModel
public import CFSG.LocalAnalysis.StandardType.GGTBJE7LeviSplitComp

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem e7SplitFrameCore
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {n : ℕ} (hq : Nat.card K = 2 ^ n) (hpn : p ∣ 2 ^ n - 1) :
    GGE7LeviFrame p (TableBExc.torusPow .E7 K p) := by
  have hp : p.Prime := Fact.out
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have hpK : p ∣ Nat.card K - 1 := by rw [hq]; exact hpn
  have hK4 : 4 ≤ Nat.card K := by
    have hle := Nat.le_of_dvd (by omega) hpK
    have h2 := hp.two_le
    omega
  obtain ⟨ζ, hζ, ι₀, nk, hζo, hι, hrange, hιι₀, hsimple, -, wt, hwn, hwt⟩ :=
    e7Split_frame (K := K) hp2 hpK
  refine ⟨K, inferInstance, ζ, hζ, ι₀, nk, _, wt, hζo, hι, hrange, hsimple, hwn, hwt,
    fun t _ Y hY => ?_⟩
  obtain ⟨i, hi, hcent⟩ := e7Split_class hK4 hιι₀ hY
  exact ⟨i, hcent, fun _ _ _ _ => e7Split_lower hιι₀ i hi⟩

theorem ggE7Split_leviModel_L
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E7, 0, n⟩ : LargeEvenLabel))
    (hL : GGHasLabel (⟨.E7, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    (hpn : p ∣ 2 ^ n - 1) :
    GGE7LeviModel p Bs L := by
  obtain ⟨hN, Fq, _, _, _, hFqcard, e, hA⟩ := ggE7Split_model_L hRig hH hΛ hL hpn
  exact ⟨hN, Fq, inferInstance, inferInstance, inferInstance, e, _, hA,
    e7SplitFrameCore (ne_two_of_dvd_two_pow_sub_one hΛ.1 hpn) hFqcard hpn⟩

theorem ggE7Split_leviModel_K
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E7, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.E7, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hpn : p ∣ 2 ^ n - 1) :
    GGE7LeviModel p Bs K := by
  obtain ⟨hN, Fq, _, _, _, hFqcard, e, hA⟩ := ggE7Split_model_K hRig hH hΛ hK hpn
  exact ⟨hN, Fq, inferInstance, inferInstance, inferInstance, e, _, hA,
    e7SplitFrameCore (ne_two_of_dvd_two_pow_sub_one hΛ.1 hpn) hFqcard hpn⟩

end CFSG.StandardType

end
