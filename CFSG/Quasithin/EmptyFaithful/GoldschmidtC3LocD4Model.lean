module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtC3LocD4Fac
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieD4
public import CFSG.LieType.Chevalley.GraphTwistedOuterTwoPart

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique.Setup.X6
open CFSG.QuasithinUnique.Vol2Native.L239.Lie (ParabolicFacts)
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4

namespace GoldC3

section Model


theorem hasBorelData_model {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hK : Nat.card K = (2 ^ 1) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ 1)) :
    HasBorelData ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  classical
  have hK3 : Nat.card K = 2 ^ (3 * 1) := by rw [hK, ← pow_mul, mul_comm]
  have hK8 : Nat.card K = 8 := by rw [hK]; norm_num
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hσ3 : σ.toRingHom ^ 3 = 1 := by
    refine RingHom.ext fun c => ?_
    have hc : c ^ ((2 ^ 1) ^ 3) = c := by
      have : Fintype K := Fintype.ofFinite K
      rw [← hK, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card c
    change σ (σ (σ c)) = c
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
    convert hc using 2
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  obtain ⟨hU, hcov, h₀, h₁, hgen, hi₀, hi₁⟩ := triality_named_covers (f := 1) le_rfl σ hK hσ
  have hinv := invariant_of_unequal_covers hcov (by rw [hi₀, hi₁]; norm_num)
  have hP₁C : P1 σ ≤ C := graphFixedParabolic_le _ _ _ _
  have hQ₁C : Q1 σ ≤ C := graphFixedParabolicRadical_le_graphFixedRootGroup _ _ _ _
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ C :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  have hBnorm := (fixed_Borel_self_normalizers TwistTag.D4 K σ w₀ hw₀).2.2.2.2.2.2.1
  have hnorm : Subgroup.normalizer
      (((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf C : Subgroup _) : Set _) =
      (graphFixedRootBorel TwistTag.D4 K σ.toRingHom).subgroupOf C := by
    rw [normalizer_subgroupOf_eq' hUC, hBnorm]
  have hcov₁ := (hcov ((P1 σ).subgroupOf C)).2 (Or.inr rfl)
  refine ⟨(P1 σ).subgroupOf C, (Q1 σ).subgroupOf C, hcov₁, ?_, ?_, ?_, ?_,
    fun α hα => (hinv α hα).2⟩
  · rw [hi₁]
    norm_num
  · rw [hnorm, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (graphFixedRootBorel_le TwistTag.D4 K σ.toRingHom)).toEquiv]
    exact not_three_dvd_card_graphFixedRootBorel_d4 hK8 σ
  · refine GoldCMax.isMaxSubgroupIn_d4_of_borel K σ ?_ ?_ h₁
    · rw [← hnorm]
      exact hcov₁.le
    · rw [← hnorm]
      exact hcov₁.lt.ne'
  · refine ParabolicFacts.of_map C.subtype C.subtype_injective ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hP₁C, Subgroup.map_subgroupOf_eq_of_le hQ₁C]
    exact parabolicFacts_a1 σ hσ3

theorem odd_card_outer_of_is3D4 {Y : Type} [Group Y] [Finite Y]
    (h : ChevalleyExceptionalModel Y .trialityD4 2 1) :
    Odd (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y)) := by
  have h2 := (graph_twisted_exceptional_model_outer_two_part_bound Y .trialityD4 2 1 3 h
    (Or.inr ⟨rfl, rfl⟩)).2.1 rfl
  have h1 : ordProj[2] 1 = 1 := by simp
  rw [h1] at h2
  have hne : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y) ≠ 0 :=
    Nat.card_pos.ne'
  have hcop := Nat.coprime_ordCompl Nat.prime_two hne
  rw [h2, Nat.div_one] at hcop
  exact Nat.coprime_two_left.mp hcop

theorem exists_conj_of_odd_outer {Γ : Type} [Group Γ]
    (hodd : Odd (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Γ)))
    (α : MulAut Γ) {a : ℕ} (hα : α ^ 2 ^ a = 1) : ∃ g : Γ, ∀ x, α x = g * x * g⁻¹ := by
  have hP : IsPGroup 2 (Subgroup.zpowers α) := by
    rintro ⟨g, i, rfl⟩
    refine ⟨a, Subtype.ext ?_⟩
    change (α ^ i) ^ 2 ^ a = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hα, one_zpow]
  obtain ⟨j, hj⟩ := A38c8.le_inner_of_isPGroup_two_odd hodd _ hP (Subgroup.mem_zpowers α)
  exact ⟨j, fun x => by rw [← hj]; simp [MulAut.conj_apply]⟩

theorem threeCLocConcl_3d4 {G : Type} [Group G] [Finite G] {L S : Subgroup G}
    (hL : Is3D4 2 1 ↥L) (hS2 : IsPGroup 2 S) (hSN : S ≤ Subgroup.normalizer (L : Set G))
    (hSyl : IsSylowTwoOf (S ⊓ L) L) : ThreeCLocConcl G L S := by
  obtain ⟨-, K, hFld, hFin, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_triality_model hL
  obtain ⟨hUsyl, -⟩ := triality_named_covers (f := 1) le_rfl σ hK hσ
  have hBorel := (hasBorelData_model σ hK hσ).map e.symm
  have hsyl : IsSylowTwoOf (((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map e.symm.toMonoidHom) ⊤ := by
    refine isSylowTwoOf_iff_isSylowOf.2 ?_
    have := isSylowOf_map_injective (p := 2) e.symm.toMonoidHom e.symm.injective
      (isSylowTwoOf_iff_isSylowOf.1 hUsyl)
    rwa [Subgroup.map_top_of_surjective _ e.symm.surjective] at this
  have hout : ∀ α : MulAut ↥L, (∃ a : ℕ, α ^ 2 ^ a = 1) → ∃ g : ↥L, ∀ x, α x = g * x * g⁻¹ :=
    fun α ⟨_, ha⟩ => exists_conj_of_odd_outer (odd_card_outer_of_is3D4 hL) α ha
  have hZ : ∀ g : ↥L, (∀ x : ↥L, x * g = g * x) → g = 1 := by
    intro g hg
    have hc : e g ∈ Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h2 := congrArg e (hg (e.symm y))
      simpa only [map_mul, MulEquiv.apply_symm_apply] using h2
    rw [exceptional_fixed_center_trivial _ _ σ, Subgroup.mem_bot] at hc
    exact e.injective (hc.trans (map_one e).symm)
  obtain ⟨P, hP⟩ := c3Facts_of_borelData hsyl hBorel (cent9Data_of_trialityD4 hL) hout hZ
  exact threeCLocConcl_of_hasC3Data (MulEquiv.refl ↥L) hsyl ⟨P, hP⟩ hS2 hSN hSyl

end Model

end GoldC3

end CFSG.Quasithin
