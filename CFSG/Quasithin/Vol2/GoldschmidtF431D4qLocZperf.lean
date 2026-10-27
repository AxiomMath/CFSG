module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocCenter
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocWeyl
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModD4
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModD4Perf
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4Cell
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocAut
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocRep
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructSyl

public section

namespace CFSG.Quasithin.H13.F431.D4q.Loc

open scoped commutatorElement
open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Quasithin
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4

set_option linter.unusedSectionVars false

section Scalar

variable {K : Type} [Field K]

theorem inv_conj_d4x₆ {g : ModGL TwistTag.D4.tag K} {μ : K} (hμ : μ ≠ 0)
    (hg : ∀ c : K, g * d4x₆ K c * g⁻¹ = d4x₆ K (μ * c)) (c : K) :
    g⁻¹ * d4x₆ K c * g = d4x₆ K (μ⁻¹ * c) := by
  have h := hg (μ⁻¹ * c)
  rw [← mul_assoc, mul_inv_cancel₀ hμ, one_mul] at h
  calc g⁻¹ * d4x₆ K c * g = g⁻¹ * (g * d4x₆ K (μ⁻¹ * c) * g⁻¹) * g := by rw [h]
    _ = d4x₆ K (μ⁻¹ * c) := by group

@[expose] def scalX6 : Subgroup (ModGL TwistTag.D4.tag K) where
  carrier := {g | ∃ μ : K, μ ≠ 0 ∧ ∀ c : K, g * d4x₆ K c * g⁻¹ = d4x₆ K (μ * c)}
  one_mem' := ⟨1, one_ne_zero, fun c => by simp⟩
  mul_mem' := by
    rintro g h ⟨μ, hμ, hg⟩ ⟨ν, hν, hh⟩
    refine ⟨μ * ν, mul_ne_zero hμ hν, fun c => ?_⟩
    calc g * h * d4x₆ K c * (g * h)⁻¹ = g * (h * d4x₆ K c * h⁻¹) * g⁻¹ := by group
      _ = d4x₆ K (μ * ν * c) := by rw [hh, hg, mul_assoc]
  inv_mem' := by
    rintro g ⟨μ, hμ, hg⟩
    exact ⟨μ⁻¹, inv_ne_zero hμ, fun c => by rw [inv_inv]; exact inv_conj_d4x₆ hμ hg c⟩

theorem commutator_scalX6_commute {g h : ModGL TwistTag.D4.tag K} (hg : g ∈ scalX6)
    (hh : h ∈ scalX6) (c : K) : ⁅g, h⁆ * d4x₆ K c = d4x₆ K c * ⁅g, h⁆ := by
  obtain ⟨μ, hμ, hg⟩ := hg
  obtain ⟨ν, hν, hh⟩ := hh
  have key : ⁅g, h⁆ * d4x₆ K c * ⁅g, h⁆⁻¹ = d4x₆ K c := by
    have e : ⁅g, h⁆ * d4x₆ K c * ⁅g, h⁆⁻¹ =
        g * (h * (g⁻¹ * (h⁻¹ * d4x₆ K c * h) * g) * h⁻¹) * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, inv_conj_d4x₆ hν hh, inv_conj_d4x₆ hμ hg, hh, hg]
    congr 1
    field_simp
  calc ⁅g, h⁆ * d4x₆ K c = (⁅g, h⁆ * d4x₆ K c * ⁅g, h⁆⁻¹) * ⁅g, h⁆ := by group
    _ = d4x₆ K c * ⁅g, h⁆ := by rw [key]

end Scalar

section Perfect

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem P0_le_scalX6 : P0 σ ≤ scalX6 := by
  refine sup_le (fun b hb => borel_conj_d4x₆ σ hσ hb) ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨_, rfl, rfl⟩
  refine ⟨1, one_ne_zero, fun c => ?_⟩
  set n := canonicalRep (coxeterSystem TwistTag.D4.tag) K
    (TwistTag.D4.orbitReflection ⟨0, by decide⟩) with hn
  have h : d4x₆ K c * n = n * d4x₆ K c :=
    d4Mr_commute_d4x₆ σ (canonicalRep_orbitReflection_mem_d4 σ ⟨0, by decide⟩) c
  show n * d4x₆ K c * n⁻¹ = d4x₆ K (1 * c)
  rw [one_mul, ← h, mul_inv_cancel_right]

include hσ in
theorem perfectCore_P0_commute_d4x₆ {g : ModGL TwistTag.D4.tag K} (hg : g ∈ perfectCore (P0 σ))
    (c : K) : g * d4x₆ K c = d4x₆ K c * g := by
  have h1 : perfectCore (P0 σ) ≤ ⁅P0 σ, P0 σ⁆ := perfectCore_le_derivedSeriesOf (P0 σ) 1
  have h2 := Subgroup.commutator_mono (P0_le_scalX6 σ hσ) (P0_le_scalX6 σ hσ)
  have h3 : ⁅(scalX6 : Subgroup (ModGL TwistTag.D4.tag K)), scalX6⁆ ≤
      Subgroup.centralizer {d4x₆ K c} :=
    Subgroup.commutator_le.2 fun g hg h hh => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact commutator_scalX6_commute hg hh c
  exact Subgroup.mem_centralizer_singleton_iff.mp (h3 (h2 (h1 hg)))

end Perfect

section Zperf

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
  (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem d4x₆_mem_centerOf_perfectCore_Pst0 (hK4 : 4 ≤ Nat.card K) {w : Cm σ} {f : K}
    (hf : σ f = f) (hw : (w : ModGL TwistTag.D4.tag K) = d4x₆ K f) :
    w ∈ centerOf (perfectCore (Pst0 σ)) := by
  have hP0C : P0 σ ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedParabolic_le _ _ _ _
  refine ⟨?_, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
  · refine (CFSG.Quasithin.H13.Sec53F.TriD4.mem_perfectCore_subgroupOf hP0C w).2
      (CFSG.Quasithin.H13.Sec53F.TriD4.posUnipotent_le_perfectCore_P0 σ
        (toRingHom_pow_three_d4 σ hσ) hK4 ?_)
    rw [hw, d4x₆_eq_d4v σ]
    exact d4v_mem_graphFixedPosUnipotent σ hσ (map_zero σ) (map_zero σ) hf
  · have hg' := (CFSG.Quasithin.H13.Sec53F.TriD4.mem_perfectCore_subgroupOf hP0C g).1 hg
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hw]
    exact perfectCore_P0_commute_d4x₆ σ hσ hg' f

include hσ in
theorem zC_mem_centerOf {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3) :
    zC σ ∈ centerOf (perfectCore (Pst0 σ)) := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_left (Nat.le_self_pow (by omega) 2) 3
  exact d4x₆_mem_centerOf_perfectCore_Pst0 σ hσ hK4 (map_one σ) rfl

end Zperf

end CFSG.Quasithin.H13.F431.D4q.Loc
