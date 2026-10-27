module

public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviEnnola
public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviSplitModel
public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviSplitComp

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

theorem e8Split_leviFrame
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {n : ℕ} (hq : Nat.card K = 2 ^ n) (hpn : p ∣ 2 ^ n - 1) :
    GGE8LeviFrame p (TableBExc.torusPow .E8 K p) := by
  have hp : p.Prime := Fact.out
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have hpK : p ∣ Nat.card K - 1 := by rw [hq]; exact hpn
  have hK4 : 4 ≤ Nat.card K := by
    have hle := Nat.le_of_dvd (by omega) hpK
    have := hp.two_le
    omega
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h0
    · rw [hq, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h0
  have hΛA : LargeEvenInLambda2 (⟨.A, 8, n⟩ : LargeEvenLabel) := ⟨hn, by norm_num, by norm_num⟩
  obtain ⟨ζ, hζ, ι₀, nk, hζo, hι, hrange, hιι₀, hsimple, -, wt, hwn, hwt⟩ :=
    e8Split_frame (K := K) hp2 hpK
  refine ⟨K, inferInstance, ζ, hζ, ι₀, nk, _, wt, hζo, hι, hrange, hsimple, hwn, hwt,
    fun t _ Y hY => ?_⟩
  obtain ⟨i, hi, hcent⟩ := e8Split_class hK4 hιι₀ hY
  exact ⟨i, hcent, fun _ _ _ _ => e8Split_lower hιι₀ i hi,
    fun _ _ hΨ => ⟨⟨.A, 8, n⟩, hΛA, Or.inl rfl, rfl, e8Split_a8 hq i hi hΨ⟩⟩

theorem ggE8Split_leviModel_L
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E8, 0, n⟩ : LargeEvenLabel))
    (hL : GGHasLabel (⟨.E8, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    (hpn : p ∣ 2 ^ n - 1) :
    GGE8LeviModel p Bs L := by
  obtain ⟨hN, Fq, _, _, _, hFqcard, e, hA⟩ := ggE8Split_model_L hRig hH hΛ hL hpn
  exact ⟨hN, Fq, inferInstance, inferInstance, inferInstance, e, _, hA,
    e8Split_leviFrame (ne_two_of_dvd_two_pow_sub_one hΛ.1 hpn) hFqcard hpn⟩

theorem ggE8Split_leviModel_K
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E8, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.E8, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hpn : p ∣ 2 ^ n - 1) :
    GGE8LeviModel p Bs K := by
  obtain ⟨hN, Fq, _, _, _, hFqcard, e, hA⟩ := ggE8Split_model_K hRig hH hΛ hK hpn
  exact ⟨hN, Fq, inferInstance, inferInstance, inferInstance, e, _, hA,
    e8Split_leviFrame (ne_two_of_dvd_two_pow_sub_one hΛ.1 hpn) hFqcard hpn⟩

theorem ggTBJE8LeviL_minus
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E8, 0, n⟩ : LargeEvenLabel))
    (hL : GGHasLabel (⟨.E8, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    (hpn : p ∣ 2 ^ n - 1) {labJ : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hJlab : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hnA8 : ¬ ((labJ.tag = .A ∨ labJ.tag = .twA) ∧ labJ.rank = 8)) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J :=
  ggTBJE8LeviL_of_frame hRig hH (ggE8Split_leviModel_L hRig hH hΛ hL hpn) hΛJ hJlab hnA8

theorem ggTBJE8LeviK_minus
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hJK : J ≤ K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E8, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.E8, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hpn : p ∣ 2 ^ n - 1) {labJ : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hJlab : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hnA8 : ¬ ((labJ.tag = .A ∨ labJ.tag = .twA) ∧ labJ.rank = 8)) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J :=
  ggTBJE8LeviK_of_frame hRig hH hJK (ggE8Split_leviModel_K hRig hH hΛ hK hpn) hΛJ hJlab hnA8

theorem ggTBJE8LeviL_holds
    (hRig : GGLabelRigidInput) : GGTBJE8LeviL := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ hH _ _ _ _ hΛ hL hpn _ hΛJ hJlab _ hnA8
  rcases hpn with hpn | hpn
  · exact ggTBJE8LeviL_minus hRig hH hΛ hL hpn hΛJ hJlab hnA8
  · exact ggTBJE8LeviL_plus hRig hH hΛ hL hpn hΛJ hJlab hnA8

theorem ggTBJE8LeviK_holds
    (hRig : GGLabelRigidInput) : GGTBJE8LeviK := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ hH hJK _ _ _ _ hΛ hK hpn _ hΛJ hJlab _ hnA8
  rcases hpn with hpn | hpn
  · exact ggTBJE8LeviK_minus hRig hH hJK hΛ hK hpn hΛJ hJlab hnA8
  · exact ggTBJE8LeviK_plus hRig hH hJK hΛ hK hpn hΛJ hJlab hnA8

end CFSG.StandardType
