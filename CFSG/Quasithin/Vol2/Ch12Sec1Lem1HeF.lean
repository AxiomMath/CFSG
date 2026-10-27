module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1HeE
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListLinear
public import CFSG.LieType.BorelTits.Tits
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLattice
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312Over

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a

namespace Sec1211He

variable {X : Type} [Group X] [Finite X] {m : ℕ}

theorem not_heInspCfg_L2 {f : ℕ} (hf : 2 ≤ f)
    (hX : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 2 f) (hm : m = 3 ∨ m = 4) :
    ¬ HeInspCfg X m := by
  have hBT := (CFSG.LieType.BorelTits.holds_of_statedClassicalModel hX).holdsTits
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hX
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 2) (by norm_num)
  have hT₀ : IsSylowTwoOf (projUnitriangular 2 K) ⊤ := hP ▸ isSylowTwoOf_top_of_sylow P
  exact not_heInspCfg_of_model (e.trans (statedSLEquivProjectiveSL 2 K)) hBT hT₀
    (noLinOver_of_solvable fun M hM hne =>
      Vol2Native.A312L.isSolvable_of_overgroup_two ⟨f, hcard⟩ M hM hne) hm

theorem not_heInspCfg_of_bender (hBT : CFSG.LieType.BorelTits.HoldsTits X 2)
    (hB : fusionIsBenderGroup X) (hm : m = 3 ∨ m = 4) : ¬ HeInspCfg X m := by
  have : IsSimpleGroup X := RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ := (Sylow.nonempty : Nonempty (Sylow 2 X))
  exact not_heInspCfg_of_noLinOver hBT (isSylowTwoOf_top_of_sylow Q)
    (noLinOver_of_solvable fun M hQM hM => Unc25G2.A312Sub.bender_overgroups hB Q hQM hM) hm

theorem not_heInspCfg_U3 {f : ℕ} (hf : 2 ≤ f)
    (hX : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 2 f) (hm : m = 3 ∨ m = 4) :
    ¬ HeInspCfg X m := by
  have hBT := (CFSG.LieType.BorelTits.holds_of_statedClassicalModel hX).holdsTits
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have hcard : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  let e' : X ≃* GLAProj (GLASUGroup (Fin 3) K (2 ^ f)) := e
  exact not_heInspCfg_of_bender hBT
    (Or.inr (Or.inl ⟨f, hf, ⟨e'.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative f hf hcard)⟩⟩))
    hm

theorem not_heInspCfg_Sz {f : ℕ} (hX : SuzukiModel X 2 f) (hm : m = 3 ∨ m = 4) :
    ¬ HeInspCfg X m := by
  have hBT := (CFSG.LieType.BorelTits.holds_of_suzukiModel hX).holdsTits
  obtain ⟨a, ha, ⟨e⟩⟩ := CFSG.LieType.Simplicity.exists_mulEquiv_suzukiMatrixGroup_of_suzukiModel hX
  exact not_heInspCfg_of_bender hBT
    (Or.inr (Or.inr ⟨a, ha, ⟨e.trans (CFSG.ShultStronglyClosedTI.suzukiCoverNativeEquiv a).symm⟩⟩))
    hm

theorem not_heInspCfg_Tits
    (hX : ReeTitsModel X .Tits 2 1) (hm : m = 3 ∨ m = 4) : ¬ HeInspCfg X m := by
  have hBT := CFSG.LieType.BorelTits.holdsTits_of_reeTitsModel_tits hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀⟩ := (Sylow.nonempty : Nonempty (Sylow 2 X))
  have hT := isSylowTwoOf_top_of_sylow P₀
  generalize (P₀ : Subgroup X) = U at hT
  obtain ⟨H, N, -, -, -, -, -, hlat, hHs, hNs⟩ :=
    CFSG.QuasithinUnique.Setup.X6.titsSylowOvergroupLattice X hX U hT
  refine not_heInspCfg_of_noLinOver hBT hT (noLinOver_of_solvable fun M hUM hMtop => ?_) hm
  rcases hlat M hUM with rfl | rfl | rfl | rfl
  · have := hT.2.1.isNilpotent
    infer_instance
  · exact hHs
  · exact hNs
  · exact absurd rfl hMtop

end Sec1211He

end CFSG.Quasithin.H13
