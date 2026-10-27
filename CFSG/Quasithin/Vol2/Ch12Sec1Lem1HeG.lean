module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1HeE
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

namespace Sec1211He

variable {X : Type} [Group X] [Finite X] {m : ℕ}

section L3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a

theorem not_heInspCfg_L3 {f : ℕ} (hf : 1 ≤ f)
    (hX : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 2 f) (hm : m = 3 ∨ m = 4) :
    ¬ HeInspCfg X m := by
  have hBT := (CFSG.LieType.BorelTits.holds_of_statedClassicalModel hX).holdsTits
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hX
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨f, hcard⟩
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  have hT₀ : IsSylowTwoOf (projUnitriangular 3 K) ⊤ := hP ▸ isSylowTwoOf_top_of_sylow P
  have hres := linear_three_residual_of_cover hK (proj 3 K) (proj_surjective 3 K)
    (ker_proj 3 K).le
  have hinj : ∀ j : Fin 2, ∀ x ∈ perfectCore (Q3 K j), ∀ y ∈ perfectCore (Q3 K j),
      proj 3 K x = proj 3 K y → x = y := by
    intro j x hx y hy hxy
    have hz : x⁻¹ * y ∈ (proj 3 K).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    have hzN : x⁻¹ * y ∈ perfectCore (Q3 K j) := mul_mem (inv_mem hx) hy
    have h1 := blk3_scalars j ⟨x⁻¹ * y, hzN⟩ ((ker_proj 3 K).le hz)
    exact inv_mul_eq_one.mp (congrArg Subtype.val h1)
  let eN : ∀ j : Fin 2, ↥(perfectCore (Q3 K j)) ≃* ↥(perfectCore ((Q3 K j).map (proj 3 K))) :=
    fun j => perfectCoreMapEquiv (proj 3 K) (Q3 K j) (hinj j)
  refine not_heInspCfg_of_model (e.trans (statedSLEquivProjectiveSL 3 K)) hBT hT₀
    (noLinOver_of_residual hres fun j =>
      leviTarget_of_sl2 ((blk3 j).comp (eN j).symm.toMonoidHom) fun z => ?_) hm
  obtain ⟨k, hk⟩ := blk3_ker_isPGroup hK j ⟨(eN j).symm z.1, z.2⟩
  have h1 : ((eN j).symm z.1) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  refine ⟨k, Subtype.ext ?_⟩
  show z.1 ^ 2 ^ k = 1
  have : (eN j).symm (z.1 ^ 2 ^ k) = 1 := by rw [map_pow]; exact h1
  exact (map_eq_one_iff _ (eN j).symm.injective).mp this

end L3

section Sp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Setup.X6

theorem not_heInspCfg_Sp4 {f : ℕ} (hf : 2 ≤ f)
    (hX : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp 2 2 f) (hm : m = 3 ∨ m = 4) :
    ¬ HeInspCfg X m := by
  have hBT := (CFSG.LieType.BorelTits.holds_of_statedClassicalModel hX).holdsTits
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hX
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨f, hcard⟩
  have hres : ResidualOvergroupsAt (StatedProj (StatedSp 2 K)) (projUnipotent 2 K)
      (fun j : Fin 2 => (Q2 K j).map (proj 2 K)) := symplectic_two_residualOvergroupsAt hK
  obtain ⟨P, hP⟩ := exists_sylow_projUnipotent (K := K) 2 (r := 2) (by norm_num)
  have hU : IsSylowTwoOf (projUnipotent 2 K) ⊤ := hP ▸ isSylowTwoOf_top_of_sylow P
  have hinj : ∀ j : Fin 2, ∀ x ∈ perfectCore (Q2 K j), ∀ y ∈ perfectCore (Q2 K j),
      proj 2 K x = proj 2 K y → x = y := fun j x _ y _ h => proj_injective_charTwo h
  let eN : ∀ j : Fin 2, ↥(perfectCore (Q2 K j)) ≃* ↥(perfectCore ((Q2 K j).map (proj 2 K))) :=
    fun j => perfectCoreMapEquiv (proj 2 K) (Q2 K j) (hinj j)
  refine not_heInspCfg_of_model e hBT hU
    (noLinOver_of_residual hres fun j =>
      leviTarget_of_sl2 ((blkN j).comp (eN j).symm.toMonoidHom) fun z => ?_) hm
  obtain ⟨k, hk⟩ := blkN_ker_isPGroup hK j ⟨(eN j).symm z.1, z.2⟩
  have h1 : ((eN j).symm z.1) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  refine ⟨k, Subtype.ext ?_⟩
  show z.1 ^ 2 ^ k = 1
  have : (eN j).symm (z.1 ^ 2 ^ k) = 1 := by rw [map_pow]; exact h1
  exact (map_eq_one_iff _ (eN j).symm.injective).mp this

end Sp4

end Sec1211He

end CFSG.Quasithin.H13
