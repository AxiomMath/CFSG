module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6LeviIso
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6LeviFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6EnnModel
public import CFSG.LocalAnalysis.StandardType.GGTBJETypeCells

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem tw5_two_le {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n + 1) :
    2 ≤ n := by
  by_contra h
  have hn : n = 0 ∨ n = 1 := by omega
  rcases hn with rfl | rfl
  · have h2 : p ∣ 2 := by simpa using hpn
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  · have h3 : p ∣ 3 := by simpa using hpn
    have := Nat.le_of_dvd (by norm_num) h3
    omega

theorem ggTBJTwE6LeviL_ge5
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.twE6, 0, n⟩ : LargeEvenLabel))
    (hL : GGHasLabel (⟨.twE6, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n + 1) (h3 : ¬ 3 ∣ 2 ^ n + 1) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hn2 : 2 ≤ n := tw5_two_le hp hp5 hpn
  refine ggTBJE6LeviL_of_cellFn hH fun hBs hSC hJX hyBs hJg hgX hcomp bX hbX1 hbXc hcardJ => ?_
  obtain ⟨hN, F, _, _, σ, hcard, hσ, e, E, hZ, hE, hcardE, hsc, hA⟩ :=
    ggTwE6Enn_model_L hRig hH hΛ hL hp5 hpn h3
  exact ggTBJE6Levi_of_isoFrame hp2 hp3 hBs hSC hJX hyBs hJg hgX hcomp hN hZ e hA
    (ggTwE6_leviFrame hn2 hcard hp5 hpn hσ E hE hcardE hsc) bX hbX1 hbXc hcardJ

theorem ggTBJTwE6LeviK_ge5
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hJK : J ≤ K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.twE6, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.twE6, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n + 1) (h3 : ¬ 3 ∣ 2 ^ n + 1) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hn2 : 2 ≤ n := tw5_two_le hp hp5 hpn
  refine ggTBJE6LeviK_of_cellFn hH hJK fun hBs hSC hJK' hxBs hJg hgX hcomp bX hbX1 hbXc hcardJ => ?_
  obtain ⟨hN, F, _, _, σ, hcard, hσ, e, E, hZ, hE, hcardE, hsc, hA⟩ :=
    ggTwE6Enn_model_K hRig hH hΛ hK hp5 hpn h3
  exact ggTBJE6Levi_of_isoFrame hp2 hp3 hBs hSC hJK' hxBs hJg hgX hcomp hN hZ e hA
    (ggTwE6_leviFrame hn2 hcard hp5 hpn hσ E hE hcardE hsc) bX hbX1 hbXc hcardJ

end CFSG.StandardType

end
