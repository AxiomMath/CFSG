module

import CFSG.RankThree.PartTwo.Source.GammaTwoSubgroups
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartTwo.Late.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

theorem map_perfectResidual_le {X Y : Type*} [Group X] [Group Y] (f : X →* Y) :
    (perfectResidual X).map f ≤ perfectResidual Y := by
  rw [perfectResidual, perfectResidual]
  refine le_iInf fun n => ?_
  exact (Subgroup.map_mono (iInf_le _ n)).trans (map_derivedSeries_le_derivedSeries f n)

theorem exists_map_conj_eq_of_isSylowOf {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B B' N : Subgroup G} (hB : CFSG.ABGLocalTools.IsSylowOf p B N)
    (hB' : CFSG.ABGLocalTools.IsSylowOf p B' N) :
    ∃ n ∈ N, B' = B.map (MulAut.conj n).toMonoidHom := by
  obtain ⟨Q, rfl⟩ := hB
  obtain ⟨Q', rfl⟩ := hB'
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N Q Q'
  refine ⟨n, n.2, ?_⟩
  rw [← hn]
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    rw [Sylow.coe_subgroup_smul] at hy
    obtain ⟨z, hz, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hy
    refine ⟨(z : G), ⟨_, hz, rfl⟩, ?_⟩
    change (n : G) * (z : G) * (n : G)⁻¹ = ((MulAut.conj n • z : N) : G)
    rw [MulAut.smul_def, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨MulAut.conj n • y, ?_, ?_⟩
    · rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hy
    · change ((MulAut.conj n • y : N) : G) = (n : G) * (y : G) * (n : G)⁻¹
      rw [MulAut.smul_def, MulAut.conj_apply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]

theorem exists_mul_of_isSylowOf {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B N K : Subgroup G} (hB : CFSG.ABGLocalTools.IsSylowOf p B N)
    (hK : K ≤ Subgroup.normalizer (N : Set G)) {k : G} (hk : k ∈ K) :
    ∃ n ∈ N, ∃ m ∈ Subgroup.normalizer (B : Set G), k = n * m := by
  have hkN : k ∈ Subgroup.normalizer (N : Set G) := hK hk
  have hle : B.map (MulAut.conj k).toMonoidHom ≤ N := by
    rintro _ ⟨b, hb, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hkN b).mp (hB.le hb)
  have hB' : CFSG.ABGLocalTools.IsSylowOf p (B.map (MulAut.conj k).toMonoidHom) N := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj k).injective]
    exact hB.card_eq
  obtain ⟨n, hn, hnk⟩ := exists_map_conj_eq_of_isSylowOf hB hB'
  refine ⟨n, hn, n⁻¹ * k, ?_, by group⟩
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ b, b ∈ B ↔ k * b * k⁻¹ ∈ B.map (MulAut.conj n).toMonoidHom := by
    intro b
    rw [← hnk]
    constructor
    · intro hb
      exact ⟨b, hb, rfl⟩
    · rintro ⟨b', hb', hbb'⟩
      have h2 : k * b' * k⁻¹ = k * b * k⁻¹ := hbb'
      rwa [mul_left_cancel (mul_right_cancel h2)] at hb'
  intro b
  rw [key b]
  constructor
  · rintro ⟨b', hb', hbb'⟩
    have h1 : n * b' * n⁻¹ = k * b * k⁻¹ := hbb'
    have : n⁻¹ * k * b * (n⁻¹ * k)⁻¹ = b' := by
      calc n⁻¹ * k * b * (n⁻¹ * k)⁻¹ = n⁻¹ * (k * b * k⁻¹) * n := by group
        _ = n⁻¹ * (n * b' * n⁻¹) * n := by rw [h1]
        _ = b' := by group
    rw [this]
    exact hb'
  · intro hb
    refine ⟨_, hb, ?_⟩
    change n * (n⁻¹ * k * b * (n⁻¹ * k)⁻¹) * n⁻¹ = k * b * k⁻¹
    group

theorem le_sup_normalizer_of_isSylowOf {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B N K : Subgroup G} (hB : CFSG.ABGLocalTools.IsSylowOf p B N)
    (hK : K ≤ Subgroup.normalizer (N : Set G)) : K ≤ N ⊔ Subgroup.normalizer (B : Set G) := by
  intro k hk
  obtain ⟨n, hn, m, hm, rfl⟩ := exists_mul_of_isSylowOf hB hK hk
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hm)

theorem pCore_quotient_pCore_eq_bot {X : Type*} [Group X] [Finite X] (p : ℕ) [Fact p.Prime] :
    CFSG.pCore p (X ⧸ CFSG.pCore p X) = ⊥ := by
  set N : Subgroup X := CFSG.pCore p X with hN
  set K : Subgroup X := (CFSG.pCore p (X ⧸ N)).comap (QuotientGroup.mk' N) with hK
  have hKn : K.Normal := (CFSG.pCore_normal (p := p) (G := X ⧸ N)).comap _
  have hKp : IsPGroup p K := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha⟩ := CFSG.pCore_isPGroup (p := p) (G := X ⧸ N) ⟨_, hx⟩
    have hxa : x ^ (p ^ a) ∈ N := by
      have h1 := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one, QuotientGroup.mk'_apply] at h1
      rw [← QuotientGroup.mk_pow] at h1
      exact (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨b, hb⟩ := CFSG.pCore_isPGroup (p := p) (G := X) ⟨_, hxa⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have h2 := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2 ⊢
    rw [pow_add, pow_mul, h2]
  have hle : K ≤ N := le_sSup ⟨hKn, hKp⟩
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have hx : x ∈ K := hy
  exact (QuotientGroup.eq_one_iff x).mpr (hle hx)

variable {G : Type} [Group G] [Finite G]

theorem le_of_le_normalizer_of_isPGroup_two {A M R : Subgroup G} (h : Sec18Std G A M)
    (hR : IsPGroup 2 R) (hAR : A ≤ Subgroup.normalizer (R : Set G)) : R ≤ M := by
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  refine (Source.le_aschCore_of_le_normalizer hA.1 hA.2 hR hAR).trans ?_
  rw [aschCore_eq_gamma_of_mem_partTwoE h.mem_partTwoE]
  exact h.mem_scriptM.2

theorem pCoreOf_le_pCoreOf_inf {A M X : Subgroup G} (h : Sec18Std G A M) (hAX : A ≤ X) :
    CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 (X ⊓ M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hXN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hRM := le_of_le_normalizer_of_isPGroup_two h hR (hAX.trans hXN)
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 X) hRM) (inf_le_left.trans hXN) hR

end CFSG.RankThree.PartTwo.Sec18
