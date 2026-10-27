module

public import CFSG.Quasithin.EmptyFaithful.S151CLG2Map
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieD4
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsG24Good
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParL3

public section

namespace CFSG.Quasithin.CLG2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
open CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.L239
open CFSG.QuasithinUnique.Vol2Native.L239.Lie CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
open CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

theorem two_le_of_four_le_pow_two {m : ℕ} (h : 4 ≤ 2 ^ m) : 2 ≤ m := by
  by_contra hm
  have : m ≤ 1 := by omega
  have : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
  omega

section D4


theorem rank2Levi_fixed {t : TwistTag} {K : Type} [Field K] [Finite K] [CharP K 2]
    (σ : K ≃+* K) (a : Fin t.foldedTag.rank)
    (hU : IsPGroup 2 ↥(graphFixedPosUnipotent t K σ.toRingHom))
    (h4 : 4 ≤ Nat.card ↥(orbitField t K σ.toRingHom a)) :
    Rk2.Rank2Levi ((graphFixedParabolic t K σ.toRingHom {a}).subgroupOf
      (graphFixedRootGroup t K σ.toRingHom)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Nat.card ↥(orbitField t K σ.toRingHom a) = 2 ^ m := by
    have : Fintype ↥(orbitField t K σ.toRingHom a) := Fintype.ofFinite _
    obtain ⟨n, -, hn⟩ := FiniteField.card ↥(orbitField t K σ.toRingHom a) 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card]; exact hn⟩
  have hm2 : 2 ≤ m := two_le_of_four_le_pow_two (hm ▸ h4)
  obtain ⟨g, hg, hker⟩ := exists_levi_hom_fixed σ a hU (exists_finset_card_four h4)
  exact ⟨↥(orbitField t K σ.toRingHom a), inferInstance, inferInstance, inferInstance, m, hm, hm2,
    g, hg, hker⟩

theorem rankTwoPar_model_d4 {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 2 ≤ f) (σ : K ≃+* K)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    RankTwoPar ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      (fun j => (graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j}).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  classical
  have hf1 : 1 ≤ f := by omega
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hσ3 : σ.toRingHom ^ 3 = 1 := by
    refine RingHom.ext fun c => ?_
    have hc : c ^ ((2 ^ f) ^ 3) = c := by
      have : Fintype K := Fintype.ofFinite K
      rw [← hK, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card c
    change σ (σ (σ c)) = c
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
    convert hc using 2
    ring
  have hq4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ 2 ^ f := hq4
      _ = (2 ^ f) ^ 1 := (pow_one _).symm
      _ ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  obtain ⟨-, hcov, h₀, h₁, hgen, hi₀, hi₁⟩ := triality_named_covers hf1 σ hK hσ
  have hne : (2 ^ f) ^ 3 + 1 ≠ 2 ^ f + 1 := by
    intro h
    have h1 : (2 ^ f) ^ 3 = 2 ^ f := Nat.add_right_cancel h
    have h2 : 2 ^ f < (2 ^ f) ^ 3 := by
      calc 2 ^ f = (2 ^ f) ^ 1 := (pow_one _).symm
        _ < (2 ^ f) ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  have hinv := invariant_of_unequal_covers hcov (by rw [hi₀, hi₁]; exact hne)
  obtain ⟨σ', hσ', -, hcard', -, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two hf1 K hK
  have hσσ' : σ = σ' := RingEquiv.ext fun c => (hσ c).trans (hσ' c).symm
  have hcard : ∀ a, Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom a) =
      (2 ^ f) ^ (TwistTag.D4.orbit a).card := by
    rw [hσσ']
    exact hcard'
  have hU := isPGroup_posUnipotent σ hσ3
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  have hP₀C : P0 σ ≤ C := graphFixedParabolic_le _ _ _ _
  have hP₁C : P1 σ ≤ C := graphFixedParabolic_le _ _ _ _
  have hQ₀C : Q0 σ ≤ C := graphFixedParabolicRadical_le_graphFixedRootGroup _ _ _ _
  have hQ₁C : Q1 σ ≤ C := graphFixedParabolicRadical_le_graphFixedRootGroup _ _ _ _
  have hF₀ : ParabolicFacts ((P0 σ).subgroupOf C) ((Q0 σ).subgroupOf C) := by
    refine ParabolicFacts.of_map C.subtype C.subtype_injective ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hP₀C, Subgroup.map_subgroupOf_eq_of_le hQ₀C]
    exact parabolicFacts_a0 σ hσ3 hK4
  have hF₁ : ParabolicFacts ((P1 σ).subgroupOf C) ((Q1 σ).subgroupOf C) := by
    refine ParabolicFacts.of_map C.subtype C.subtype_injective ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hP₁C, Subgroup.map_subgroupOf_eq_of_le hQ₁C]
    exact parabolicFacts_a1 σ hσ3
  have hN₀ := ((hcov _).2 (Or.inl rfl)).le
  have hN₁ := ((hcov _).2 (Or.inr rfl)).le
  have hbig : ∀ k : ℕ, 1 ≤ k → 4 ≤ (2 ^ f) ^ k := fun k hk =>
    calc 4 ≤ 2 ^ f := hq4
      _ = (2 ^ f) ^ 1 := (pow_one _).symm
      _ ≤ (2 ^ f) ^ k := Nat.pow_le_pow_right (by omega) hk
  have hl₀ : Rk2.Rank2Levi
      ((graphFixedParabolic TwistTag.D4 K σ.toRingHom {fa0}).subgroupOf C) := by
    refine rank2Levi_fixed σ fa0 hU ?_
    have h3 : (TwistTag.D4.orbit fa0).card = 3 := card_orbit_D4.1
    rw [hcard, h3]
    exact hbig 3 (by norm_num)
  have hl₁ : Rk2.Rank2Levi
      ((graphFixedParabolic TwistTag.D4 K σ.toRingHom {fa1}).subgroupOf C) := by
    refine rank2Levi_fixed σ fa1 hU ?_
    have h1 : (TwistTag.D4.orbit fa1).card = 1 := card_orbit_D4.2
    rw [hcard, h1]
    exact hbig 1 le_rfl
  have hj : ∀ j : Fin 2, d4Index j = fa0 ∨ d4Index j = fa1 := fun j =>
    foldedRank_D4_cases (d4Index j)
  refine ⟨⟨triality_residualOvergroupsAt σ, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j
    rcases hj j with h | h <;> rw [h]
    · exact hN₀
    · exact hN₁
  · intro j
    rcases hj j with h | h <;> rw [h]
    · exact hl₀
    · exact hl₁
  · intro j
    rcases hj j with h | h <;> rw [h]
    · exact Rk2.charTwo_perfectCore hF₀.charTwo
    · exact Rk2.charTwo_perfectCore hF₁.charTwo
  · intro α hα j
    rcases hj j with h | h <;> rw [h]
    · exact (hinv α hα).1
    · exact (hinv α hα).2
  · intro j
    rcases hj j with h | h <;> rw [h]
    · exact hF₀.goodLocal
    · exact hF₁.goodLocal

theorem rankTwoPar_d4 {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : 2 ≤ n) (hY : Is3D4 2 n Y)
    {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) : ∃ P : Fin 2 → Subgroup Y, RankTwoPar Y U P := by
  obtain ⟨hf, K, hF, hFin, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_triality_model hY
  have hU₀ := (triality_named_covers hf σ hK hσ).1
  exact RankTwoPar.exists_of_equiv e (rankTwoPar_model_d4 hn σ hK hσ) hU₀ hU

end D4

end CFSG.Quasithin.CLG2
