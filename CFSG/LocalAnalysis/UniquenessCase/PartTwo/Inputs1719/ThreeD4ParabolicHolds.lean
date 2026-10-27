module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4ParabolicsGen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieD4
public import CFSG.Quasithin.EmptyFaithful.S151CLG2F4Step
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder
public import CFSG.Quasithin.Background.RonanF918Four

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Quasithin
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.QuasithinUnique.Setup.X6
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
open CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.CLG2
open CFSG.LieType.Chevalley
open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

theorem isPGroup_graphFixedPosUnipotent_D4
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f) {σ : K →+* K}
    (hK : Nat.card K = (2 ^ f) ^ 3) :
    IsPGroup 2 ↥(graphFixedPosUnipotent TwistTag.D4 K σ) := by
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK3
  exact (CFSG.LieType.Chevalley.isPGroup_posUnipotent (K := K) 2 TwistTag.D4.tag).to_le
    (inf_le_left : graphFixedPosUnipotent TwistTag.D4 K σ ≤ posUnipotent TwistTag.D4.tag K)

theorem invariant_P0_P1_of_mapS
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f) (σ : K ≃+* K)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {X : Type} [Group X] [Finite X] {S : Subgroup X}
    (φ : X ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hS : S.map φ.toMonoidHom =
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    {α : MulAut X} (hα : S.map α.toMonoidHom = S) :
    IsPGroup 2 ↥(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) ∧
    (((graphFixedParabolic TwistTag.D4 K σ.toRingHom {fa0}).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.symm.toMonoidHom).map
        α.toMonoidHom =
      ((graphFixedParabolic TwistTag.D4 K σ.toRingHom {fa0}).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.symm.toMonoidHom ∧
    (((graphFixedParabolic TwistTag.D4 K σ.toRingHom {fa1}).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.symm.toMonoidHom).map
        α.toMonoidHom =
      ((graphFixedParabolic TwistTag.D4 K σ.toRingHom {fa1}).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.symm.toMonoidHom := by
  have hU := isPGroup_graphFixedPosUnipotent_D4 (f := f) (σ := σ.toRingHom) hf hK
  obtain ⟨-, hcov, -, -, -, hi₀, hi₁⟩ := triality_named_covers hf σ hK hσ
  have hne : (2 ^ f) ^ 3 + 1 ≠ 2 ^ f + 1 := by
    intro hc
    have h1 : (2 ^ f) ^ 3 = 2 ^ f := Nat.add_right_cancel hc
    have h2 : 2 ^ f < (2 ^ f) ^ 3 := by
      have h1 : 1 < 2 ^ f := by
        calc 1 < 2 ^ 1 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      calc 2 ^ f = (2 ^ f) ^ 1 := (pow_one _).symm
        _ < (2 ^ f) ^ 3 := Nat.pow_lt_pow_right h1 (by norm_num)
    omega
  have hinv := invariant_of_unequal_covers hcov (by rw [hi₀, hi₁]; exact hne)
  set α' : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    φ.symm.trans (α.trans φ) with hα'def
  have hα' : ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map α'.toMonoidHom =
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    have h1 := map_comm_equiv φ α' S
    rw [hS] at h1
    have h2 : φ.trans (α'.trans φ.symm) = α := by
      rw [hα'def]
      ext x
      change φ.symm (φ (α (φ.symm (φ x)))) = α x
      rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    rw [h2, hα, hS] at h1
    exact h1
  have hmap : ∀ P : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      (P.map φ.symm.toMonoidHom).map α.toMonoidHom =
        (P.map (φ.symm.trans (α.trans φ)).toMonoidHom).map φ.symm.toMonoidHom :=
    fun P => map_comm_equiv φ.symm α P
  refine ⟨hU, ?_, ?_⟩
  · rw [hmap, ← hα'def, (hinv α' hα').1]
  · rw [hmap, ← hα'def, (hinv α' hα').2]

theorem k_3D4ParabolicGen_holds :
    K_3D4ParabolicGen := by
  intro X _ _ n hn hX S hS
  classical
  have hCE : ChevalleyExceptionalModel X .trialityD4 2 n :=
    CFSG.Blueprint.LieModel.chevalleyExceptionalModel hX (by decide)
  obtain ⟨K, hF, hFin, σ, φ, hK, hσ, hUφ, hres, -⟩ :=
    even_rank_two_residual_triality hCE hS
  let Q : Fin TwistTag.D4.foldedTag.rank → Subgroup X := fun a =>
    ((graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.symm.toMonoidHom
  have hresQ : ResidualOvergroupsAt X S (fun j => Q (d4Index j)) := hres
  have hK3 : Nat.card K = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK3
  have hU := isPGroup_graphFixedPosUnipotent_D4 (f := n) (by omega) (σ := σ.toRingHom) hK
  have hj : ∀ j : Fin 2, d4Index j = fa0 ∨ d4Index j = fa1 := fun j =>
    foldedRank_D4_cases (d4Index j)
  have hcard₀ : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom fa0) = 2 ^ (3 * n) := by
    rw [card_orbitField_D4_orientation (r := 1) Nat.prime_two (by omega) hK (Or.inl rfl)
      (by simpa using hσ) fa0, orbit_card_fa0]
    rw [← pow_mul]
    congr 1
    ring
  have hcard₁ : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom fa1) = 2 ^ n := by
    rw [card_orbitField_D4_orientation (r := 1) Nat.prime_two (by omega) hK (Or.inl rfl)
      (by simpa using hσ) fa1, orbit_card_fa1, pow_one]
  have h4₀ : ∃ s : Finset ↥(orbitField TwistTag.D4 K σ.toRingHom fa0), s.card = 4 :=
    exists_finset_card_four (by rw [hcard₀]; exact four_le_pow_two (by omega))
  have h4₁ : ∃ s : Finset ↥(orbitField TwistTag.D4 K σ.toRingHom fa1), s.card = 4 :=
    exists_finset_card_four (by rw [hcard₁]; exact four_le_pow_two (by omega))
  obtain ⟨ψ₀, hψ₀, hk₀⟩ := exists_levi_hom_fixed σ fa0 hU h4₀
  obtain ⟨ψ₁, hψ₁, hk₁⟩ := exists_levi_hom_fixed σ fa1 hU h4₁
  obtain ⟨g₀, hg₀, hgk₀⟩ := exists_hom_perfectCore_map φ.symm ⟨ψ₀, hψ₀, hk₀⟩
  obtain ⟨g₁, hg₁, hgk₁⟩ := exists_hom_perfectCore_map φ.symm ⟨ψ₁, hψ₁, hk₁⟩
  have hlevi₀ : Rk2.Rank2Levi (Q fa0) :=
    ⟨↥(orbitField TwistTag.D4 K σ.toRingHom fa0), inferInstance, inferInstance,
      inferInstance, 3 * n, hcard₀, by omega, g₀, hg₀, hgk₀⟩
  have hlevi₁ : Rk2.Rank2Levi (Q fa1) :=
    ⟨↥(orbitField TwistTag.D4 K σ.toRingHom fa1), inferInstance, inferInstance,
      inferInstance, n, hcard₁, by omega, g₁, hg₁, hgk₁⟩
  have hL2₀ : IsL2 (Bar2 (perfectCore (Q fa0))) (3 * n) :=
    CFSG.Quasithin.RonanF918.lieModel_of_isPSL
      (sl2_quotient hcard₀ (by omega) g₀ hg₀ hgk₀).1
  have hL2₁ : IsL2 (Bar2 (perfectCore (Q fa1))) n :=
    CFSG.Quasithin.RonanF918.lieModel_of_isPSL
      (sl2_quotient hcard₁ (by omega) g₁ hg₁ hgk₁).1
  have hns : ∀ j : Fin 2, ¬ Group.IsSolvable ↥(perfectCore (Q (d4Index j))) := by
    intro j
    rcases hj j with h | h
    · rw [h]
      exact not_isSolvable_perfectCore_of_levi (Or.inl hlevi₀)
    · rw [h]
      exact not_isSolvable_perfectCore_of_levi (Or.inl hlevi₁)
  have hgen : perfectCore (Q (d4Index 0)) ⊔ perfectCore (Q (d4Index 1)) ⊔ S = ⊤ :=
    sup_perfectCore_eq_top_of_res (P := fun j => Q (d4Index j)) (U := S) hresQ hns
  have hgenQ : perfectCore (Q fa0) ⊔ perfectCore (Q fa1) ⊔ S = ⊤ := by
    have h := hgen
    rcases hj 0 with h0 | h0 <;> rcases hj 1 with h1 | h1
    · exact absurd (d4Index_injective (h0.trans h1.symm)) (by decide)
    · simpa [h0, h1] using h
    · rw [h0, h1, sup_comm (perfectCore (Q fa1)) (perfectCore (Q fa0))] at h
      exact h
    · exact absurd (d4Index_injective (h0.trans h1.symm)) (by decide)
  refine ⟨perfectCore (Q fa0), perfectCore (Q fa1), perfectCore_perfect (Q fa0),
    perfectCore_perfect (Q fa1), hL2₀, hL2₁, hgenQ, ?_⟩
  intro α hα
  obtain ⟨-, hinv₀, hinv₁⟩ :=
    invariant_P0_P1_of_mapS (f := n) (by omega) σ hK hσ φ hUφ hα
  refine ⟨?_, ?_⟩
  · rw [CFSG.Quasithin.map_perfectCore α.toMonoidHom (Q fa0), hinv₀]
  · rw [CFSG.Quasithin.map_perfectCore α.toMonoidHom (Q fa1), hinv₁]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end