module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeKLie
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeU52Models
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.Census.Witness46

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models

theorem inner_of_U52 {G : Type} [Group G] {X : Subgroup G} (hX : LieModel X .PSU 5 2 1) {b : G}
    (hb : b ∈ normalizer (X : Set G)) (hb3 : b ^ 3 = 1) :
    ∃ k ∈ X, ∀ y ∈ X, b * y * b⁻¹ = k * y * k⁻¹ := by
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := lieModel_PSU_five hX
  have h3 : conjAut X hb ^ 3 = 1 := by
    ext t
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply]
    show b * (b * (b * (t : G) * b⁻¹) * b⁻¹) * b⁻¹ = t
    have : b * (b * (b * (t : G) * b⁻¹) * b⁻¹) * b⁻¹ = (b * b * b) * t * (b * b * b)⁻¹ := by
      group
    rw [this, show b * b * b = b ^ 3 by rw [pow_succ, pow_succ, pow_one], hb3]; group
  obtain ⟨r, hr⟩ := outThree_of_equiv e (u52OrderThreeAutInner K hF hfin hK) _ h3
  refine ⟨r, r.2, fun y hy => ?_⟩
  have := congrArg Subtype.val (DFunLike.congr_fun hr ⟨y, hy⟩)
  simpa [conjAut, MulAut.conj_apply] using this

theorem center_trivial_of_U52 {G : Type} [Group G] {X : Subgroup G} (hX : LieModel X .PSU 5 2 1) :
    ∀ k ∈ X, (∀ y ∈ X, k * y = y * k) → k = 1 := by
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := lieModel_PSU_five hX
  intro k hk hc
  haveI := hfin
  have hZ := u52_center K hK
  have hmem : e ⟨k, hk⟩ ∈ center (StatedProj (StatedSU 5 (2 ^ 1) K)) := by
    rw [mem_center_iff]
    intro m
    obtain ⟨y, rfl⟩ := e.surjective m
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (hc y y.2).symm)
  rw [hZ, mem_bot, map_eq_one_iff _ e.injective] at hmem
  exact congrArg Subtype.val hmem

theorem o1pp_B_eq_of_model {G : Type} [Group G]
    [Finite G] {B X T : Subgroup G} (hX : LieModel X .PSU 5 2 1)
    (hBab : IsElemAbelian 3 B) (hBX : B ≤ normalizer (X : Set G)) (hT : T ≠ ⊥)
    (hT2 : IsPGroup 2 T) (hBT : B ≤ normalizer (T : Set G)) (hXT : X ≤ normalizer (T : Set G))
    (hrank : twoLocalPrimeRank 3 G ≤ 6) (hcard : Nat.card B = 3 ^ 6) :
    B = (B ⊓ X) ⊔ (B ⊓ centralizer (X : Set G)) :=
  decomp_eq (center_trivial_of_U52 hX) (fun b hb => inner_of_U52 hX (hBX hb) (hBab.2 b hb))
    hBab hT hT2 hBT hXT hrank hcard

theorem bstar_eq_of_normalizes {G : Type} [Group G] [Finite G] {B Bs U : Subgroup G}
    (hBmax : CFSG.Assembly.LargeEvenIsBmax 3 B) (hBs : CFSG.StandardType.GGBstar 3 B Bs)
    (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hBsU : Bs ≤ normalizer (U : Set G)) :
    Bs = B ∧ (Nat.card Bs = 3 ^ 6 → twoLocalPrimeRank 3 G = 6) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hBB, hBsab, -, -⟩ := hBs
  have hB : Nat.card B = 3 ^ twoLocalPrimeRank 3 G := hBmax.2.1
  have h3 : IsPGroup 3 Bs := fun g => ⟨1, by
    rw [pow_one]; exact Subtype.ext (by simpa using hBsab.2 _ g.2)⟩
  obtain ⟨k, hk⟩ := h3.exists_card_eq
  have hkm := le_twoLocalPrimeRank (by norm_num) U Bs hU hU2 hBsU hBsab hk
  have hEq : Bs = B := (Subgroup.eq_of_le_of_card_ge hBB (by
    rw [hk, hB]; exact Nat.pow_le_pow_right (by norm_num) hkm)).symm
  refine ⟨hEq, fun h6 => ?_⟩
  rw [hEq, hB] at h6
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h6

end CFSG.GGQ2Prime
