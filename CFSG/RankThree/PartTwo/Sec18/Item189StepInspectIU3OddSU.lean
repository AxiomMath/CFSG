module

public import CFSG.RankThree.PartTwo.Sec18.Item189StepInspectIU3OddTools
public import CFSG.Open.PGLModelDefs
import CFSG.RankThree.PartTwo.Sec18.Item189StepInspectIU3OddWr
import CFSG.RankThree.PartTwo.Sec18.Item189StepInspectIU3OddSD
import CFSG.Open.PGLModelStated
import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.LieType.Steinberg.CentralExt.UnitaryThreeSylow

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG.LieType.Steinberg CFSG.LocalAnalysis.ComponentInitial

theorem eq_one_of_mem_normalizer_SUgram_u3odd189 {K : Type} [Field K] {p f : ℕ}
    (hK : UnitaryFieldData p f K) (hp2 : p ≠ 2) (hq3 : p ^ f % 3 = 1)
    (T : Sylow 2 (SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K)))
    {y : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K)}
    (hy : y ∈ Subgroup.normalizer
      ((T : Subgroup (SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K))) : Set _))
    (hy3 : y ^ 3 = 1) : y = 1 := by
  have hodd : p ^ f % 2 = 1 := Nat.odd_iff.1 (hK.prime.odd_of_ne_two hp2).pow
  rcases (by omega : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3) with h | h
  · exact eq_one_of_mem_normalizer_sylow_sd_u3odd189 hK hp2 hq3 h T hy hy3
  · exact eq_one_of_mem_normalizer_sylow_wr_u3odd189 hK hp2 hq3 h T hy hy3

theorem eq_one_of_mem_normalizer_projSU_u3odd189 {G : Type} [Group G] [Finite G] {p f : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq3 : p ^ f % 3 = 1)
    (e : G ≃* CFSG.PGLModel.projSU 3 p f) (S : Sylow 2 G) {y : G}
    (hy : y ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)) (hy3 : y ^ 3 = 1) : y = 1 := by
  have hK : UnitaryFieldData p f (GaloisField p (2 * f)) :=
    ⟨Fact.out, hf, GaloisField.card p (2 * f) (by omega)⟩
  have hF : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
    rw [GaloisField.card p (2 * f) (by omega), mul_comm, pow_mul]
  have hbot : (CFSG.Open.StatedScalars (Fin 3) (GaloisField p (2 * f))).subgroupOf
      (CFSG.Open.StatedSU 3 (p ^ f) (GaloisField p (2 * f))) = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [(CFSG.LinearGroups.unitary_scalar_kernel Fact.out hF (by norm_num)).2.2]
    have h3 : ¬ 3 ∣ p ^ f + 1 := by omega
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  have hSU : CFSG.Open.StatedSU 3 (p ^ f) (GaloisField p (2 * f)) =
      SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) (GaloisField p (2 * f))) := by
    rw [SUgram_bar_one hK 3, CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 3]
  let φ : G ≃* SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) (GaloisField p (2 * f))) :=
    ((e.trans (CFSG.PGLModel.projSUEquivStatedProj 3 p f)).trans
      ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot)).trans
      (MulEquiv.subgroupCongr hSU)
  exact eq_one_of_mulEquiv_u3odd189 φ
    (fun T y hy hy3 => eq_one_of_mem_normalizer_SUgram_u3odd189 hK hp2 hq3 T hy hy3) S hy hy3

end CFSG.RankThree.PartTwo.Sec18
