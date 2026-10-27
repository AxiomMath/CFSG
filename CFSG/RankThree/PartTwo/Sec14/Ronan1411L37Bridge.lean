module

public import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJCore
import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJInner
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1411L37

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (projImage)

variable {M : Type} [Group M] [Finite M] {Ybar Abar Xbar Rbar : Subgroup M} {abar : M}

theorem maximal_elemAbelian (hset : HJCoreSetting Ybar Abar Xbar Rbar abar) :
    Maximal (fun B : Subgroup M => CFSG.Assembly.IsElemAbelian 3 B) Abar := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨hset.isElemAbelian, fun B hB hAB => ?_⟩
  intro b hbB
  have hbM : b ∈ ((Ybar ⊔ Abar : Subgroup M) : Set M) := by
    rw [hset.sup_eq_top]
    exact Subgroup.mem_top b
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Ybar Abar hset.le_normalizer_Y] at hbM
  obtain ⟨y, hy, a, ha, rfl⟩ := hbM
  change y * a ∈ B at hbB
  change y * a ∈ Abar
  have hyB : y ∈ B := by
    have : y = y * a * a⁻¹ := by group
    rw [this]
    exact mul_mem hbB (inv_mem (hAB ha))
  have hyC : y ∈ Subgroup.centralizer (Abar : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact congrArg Subtype.val (hB.1.is_comm.comm ⟨z, hAB hz⟩ ⟨y, hyB⟩)
  have hy3 : y ^ 3 = 1 := hB.2 y hyB
  by_cases hy1 : y = 1
  · rw [hy1, one_mul]
    exact ha
  · exact mul_mem (hset.mem_A_of_three y hy hyC (orderOf_eq_prime hy3 hy1)) ha

theorem inf_centralizer_X (hset : HJCoreSetting Ybar Abar Xbar Rbar abar) :
    Abar ⊓ Subgroup.centralizer (Xbar : Set M) = Subgroup.zpowers abar := by
  refine le_antisymm (fun e he => ?_) ?_
  · obtain ⟨heA, heC⟩ := Subgroup.mem_inf.mp he
    refine hset.mem_zpowers e heA (Wales1411W.HJInner.le_centralizer_Y_of_X hset heA ?_)
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp heC x hx
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.mpr ⟨hset.mem_A, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (hset.le_centralizer_a (hset.le_Y hx))

theorem exists_model (hX : ∃ _ : Fact (Nat.Prime 7),
      Nonempty (↥Xbar ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))) :
    ∃ _ : Fact (Nat.Prime 7), IsoLThreePi ↥Xbar 7 1 ∧ IsSimpleGroup ↥Xbar ∧
      Nonempty (↥Xbar ≃* projImage (slPi true 3 (7 ^ 1) (GaloisField 7 1))) := by
  obtain ⟨h7, ⟨φ⟩⟩ := hX
  refine ⟨h7, Or.inl ⟨by norm_num, ⟨φ⟩⟩, ?_, ⟨φ.trans (MulEquiv.subgroupCongr
    (projSL_eq_projImage (7 ^ 1) (GaloisField 7 1)))⟩⟩
  haveI := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 7 1)
  exact φ.isSimpleGroup

end CFSG.RankThree.PartTwo.Sec14.Ronan1411L37
