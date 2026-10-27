module

public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.Quasithin.Vol2.Ch9Sec3FactsF112PfA
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModD4
import CFSG.Quasithin.Vol2.GoldschmidtF431D4qModel
public import CFSG.Quasithin.H13.NQCatD4Irred
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ResidualTriality
public import CFSG.Quasithin.Vol2.Ch9Sec3FactsF112
import CFSG.Quasithin.Background.F3
import CFSG.Quasithin.Recognition.F4Moufang
import CFSG.Quasithin.Recognition.F4Thirtyone

public section

namespace CFSG.Quasithin.F112R

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
  CFSG.Quasithin.H13.Sec53F.TriD4 CFSG.Quasithin.H13.Ch9.F112Pf

section


section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem genComm_d4Q0 (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)
    (hK4 : 4 ≤ Nat.card K) : GenComm (perfectCore (P0 σ)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hF := parabolicFacts_a0 σ hσ3 hK4
  have hQ0pc : Q0 σ ≤ perfectCore (P0 σ) := Q0_le_perfectCore σ hσ3 hK4
  have hnorm : perfectCore (P0 σ) ≤
      Subgroup.normalizer (Q0 σ : Set (ModGL TwistTag.D4.tag K)) :=
    (perfectCore_le (P0 σ)).trans hF.normalizes
  have hQ0le : Q0 σ ≤ pCoreOf 2 (perfectCore (P0 σ)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQ0pc hnorm hF.pGroup
  have hne : pCoreOf 2 (perfectCore (P0 σ)) ≠ ⊥ := by
    intro hbot
    obtain ⟨x, hx, y, hy, hxy⟩ := hF.nonabelian
    have hx1 : x = 1 := by
      have : x ∈ (⊥ : Subgroup (ModGL TwistTag.D4.tag K)) := by
        rw [← hbot]
        exact hQ0le hx
      simpa using this
    have hy1 : y = 1 := by
      have : y ∈ (⊥ : Subgroup (ModGL TwistTag.D4.tag K)) := by
        rw [← hbot]
        exact hQ0le hy
      simpa using this
    exact hxy (by rw [hx1, hy1])
  have hpc := CFSG.Quasithin.H13.NQCat.D4Irred.pCoreOf_eq_of_parabolicFacts hF hne
  unfold GenComm
  rw [hpc]
  exact generation_a0 σ hσ3 (isPGroup_posUnipotent σ hσ3) hK4

private theorem genComm_d4Q1 (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)
    (hk4 : 4 ≤ Nat.card ↥(trialityFixedField K σ.toRingHom)) :
    GenComm (perfectCore (P1 σ)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hF := parabolicFacts_a1 σ hσ3
  have hQ1pc : Q1 σ ≤ perfectCore (P1 σ) := Q1_le_perfectCore σ hσ3 hk4
  have hnorm : perfectCore (P1 σ) ≤
      Subgroup.normalizer (Q1 σ : Set (ModGL TwistTag.D4.tag K)) :=
    (perfectCore_le (P1 σ)).trans hF.normalizes
  have hQ1le : Q1 σ ≤ pCoreOf 2 (perfectCore (P1 σ)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQ1pc hnorm hF.pGroup
  have hne : pCoreOf 2 (perfectCore (P1 σ)) ≠ ⊥ := by
    intro hbot
    obtain ⟨x, hx, y, hy, hxy⟩ := hF.nonabelian
    have hx1 : x = 1 := by
      have : x ∈ (⊥ : Subgroup (ModGL TwistTag.D4.tag K)) := by
        rw [← hbot]
        exact hQ1le hx
      simpa using this
    have hy1 : y = 1 := by
      have : y ∈ (⊥ : Subgroup (ModGL TwistTag.D4.tag K)) := by
        rw [← hbot]
        exact hQ1le hy
      simpa using this
    exact hxy (by rw [hx1, hy1])
  have hpc := CFSG.Quasithin.H13.NQCat.D4Irred.pCoreOf_eq_of_parabolicFacts hF hne
  unfold GenComm
  rw [hpc]
  exact generation_a1 σ hσ3 (isPGroup_posUnipotent σ hσ3) hk4

private theorem genComm_d4 (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)
    (hK4 : 4 ≤ Nat.card K)
    (hk4 : 4 ≤ Nat.card ↥(trialityFixedField K σ.toRingHom)) (j : Fin 2) :
    GenComm (perfectCore
      (graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j})) := by
  have hj : d4Index j = fa0 ∨ d4Index j = fa1 := by
    have h2 : ∀ a : Fin TwistTag.D4.foldedTag.rank, a = fa0 ∨ a = fa1 := by decide
    exact h2 _
  rcases hj with h | h
  · rw [h]
    exact genComm_d4Q0 σ hσ3 hK4
  · rw [h]
    exact genComm_d4Q1 σ hσ3 hk4

end Model

theorem hasModelFacts_d4 (f : ℕ) (hf : 2 ≤ f) :
    HasModelFacts (IsLieOverTwo .trialityD4 0 f) := by
  intro Y _ hY
  have hX : ChevalleyExceptionalModel Y .trialityD4 2 f :=
    CFSG.Blueprint.LieModel.chevalleyExceptionalModel hY (by decide)
  have hfin : Finite Y := (CFSG.Quasithin.H13.F431.D4q.Hex.f431ModelFacts_d4 f Y hY).1
  refine ⟨hfin, fun T hT => ?_⟩
  haveI : Finite Y := hfin
  obtain ⟨K, _, _, σ, φ, hK, hσq, hUmap, hres, -⟩ :=
    CFSG.QuasithinUnique.Setup.X6.even_rank_two_residual_triality hX hT
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK3
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hσ3 : σ.toRingHom ^ 3 = 1 := by
    ext c
    simp only [RingHom.coe_pow, Function.iterate_succ, Function.comp_apply,
      Function.iterate_zero, id_eq, RingHom.one_def, RingHom.id_apply]
    exact CFSG.LieType.Chevalley.ringEquiv_cube_apply_eq hK hσq c
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    exact hq4.trans (Nat.le_self_pow (by norm_num) _)
  have hk4 : 4 ≤ Nat.card ↥(trialityFixedField K σ.toRingHom) := by
    obtain ⟨-, -, -, -, -, k, hk, hcard, -⟩ :=
      CFSG.LieType.Chevalley.finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two
        (by omega : 1 ≤ f) K hK
    have hkeq : trialityFixedField K σ.toRingHom = k := by
      apply SetLike.ext'
      rw [hk]
      ext c
      simp [CFSG.LieType.Chevalley.mem_trialityFixedField, hσq]
    rw [hkeq, hcard]
    exact hq4
  refine ⟨_, hres, fun j => ?_⟩
  have hPC : graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j} ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedParabolic_le _ _ _ _
  have hT' : T = ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.symm.toMonoidHom := by
    rw [← hUmap, Subgroup.map_map]
    have e : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id Y := by
      ext x
      exact φ.symm_apply_apply x
    rw [e, Subgroup.map_id]
  constructor
  · rw [hT', ← map_perfectCore]
    apply Subgroup.map_mono
    intro x hx
    rw [mem_perfectCore_subgroupOf hPC]
    have hj : d4Index j = fa0 ∨ d4Index j = fa1 := by
      have h2 : ∀ a : Fin TwistTag.D4.foldedTag.rank, a = fa0 ∨ a = fa1 := by decide
      exact h2 _
    rcases hj with h | h
    · rw [h]
      exact posUnipotent_le_perfectCore_P0 σ hσ3 hK4 (Subgroup.mem_subgroupOf.1 hx)
    · rw [h]
      exact posUnipotent_le_perfectCore_P1 σ hσ3 hk4 (Subgroup.mem_subgroupOf.1 hx)
  · rw [← map_perfectCore, genComm_map_iff φ.symm.injective,
      ← genComm_map_iff (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective,
      map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hPC]
    exact genComm_d4 σ hσ3 hK4 hk4 j

end

end CFSG.Quasithin.F112R
