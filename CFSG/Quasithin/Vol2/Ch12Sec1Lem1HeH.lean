module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1HeE
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListG2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListD4

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.QuasithinUnique.Setup.X6
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

namespace Sec1211He

variable {X : Type} [Group X] [Finite X] {m : ℕ}

theorem leviTarget_of_leviData {S : Type} [Group S] {P : Subgroup S} (h : LeviData P) :
    LeviTarget P := by
  rcases h with h | ⟨K, _, _, _, n, -, -, g, -, hker⟩
  · exact leviTarget_of_bot h
  · exact leviTarget_of_sl2 g hker

theorem not_heInspCfg_G2
    {f : ℕ} (hf : 2 ≤ f) (hX : ChevalleyExceptionalModel X .G2 2 f) (hm : m = 3 ∨ m = 4) :
    ¬ HeInspCfg X m := by
  have hBT := (CFSG.LieType.BorelTits.holds_of_chevalleyExceptionalModel hX).holdsTits
  obtain ⟨-, K, hF, hFin, hcp, hK, ⟨e⟩⟩ := exists_mulEquiv_G2_model hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hU₀ : IsSylowTwoOf ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) ⊤ :=
    isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1)
  choose g hg hker using fun j : Fin 2 =>
    exists_levi_hom_adjoint (τ := Tag.G2) (K := K) hK hf (g2Index j)
  exact not_heInspCfg_of_model e hBT hU₀
    (noLinOver_of_residual G2_residualOvergroupsAt fun j => leviTarget_of_sl2 (g j) (hker j)) hm

theorem not_heInspCfg_D4
    {f : ℕ} (hf : 1 ≤ f) (hX : ChevalleyExceptionalModel X .trialityD4 2 f)
    (hm : m = 3 ∨ m = 4) : ¬ HeInspCfg X m := by
  have hBT := (CFSG.LieType.BorelTits.holds_of_chevalleyExceptionalModel hX).holdsTits
  obtain ⟨-, K, hF, hFin, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_triality_model hX
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨PU, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀).1
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUsyl : IsSylowTwoOf (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  exact not_heInspCfg_of_model e hBT (isSylowTwoOf_subgroupOf_top hUsyl)
    (noLinOver_of_residual (triality_residualOvergroupsAt σ) fun j =>
      leviTarget_of_leviData (fixed_leviData σ (d4Index j) hUsyl.2.1)) hm

end Sec1211He

end CFSG.Quasithin.H13
