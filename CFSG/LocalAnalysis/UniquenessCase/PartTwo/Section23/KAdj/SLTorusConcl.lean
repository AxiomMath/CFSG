module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Concl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLModel
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.NormalClosure
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLRootAct
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLRootHinf
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLBar2Quasi
import CFSG.RankThree.PartTwo.Sec18.Components

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)
open scoped commutatorElement

variable {k : ℕ} {K : Type} [Field K]

private theorem not_isPGroup_slRoot_B08 [NeZero k] [Finite K] (hk : 3 ≤ k) {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) : ¬ IsPGroup 2 ↥(slRoot k hk K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h2
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hgen : orderOf g = 2 ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  obtain ⟨Dg, hDg⟩ := exists_sl2_diagonal g.ne_zero
  have hmem : slRootEmb k hk K Dg ∈ slRoot k hk K := ⟨Dg, rfl⟩
  have h3 : orderOf (slRootEmb k hk K Dg) = 2 ^ n - 1 := by
    rw [orderOf_slRootEmb_diagonal hk g.ne_zero hDg, orderOf_units, hgen]
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 h2) ⟨slRootEmb k hk K Dg, hmem⟩
  have h3' : orderOf (slRootEmb k hk K Dg) = 2 ^ j := by
    rw [← hj]
    exact Subgroup.orderOf_coe ⟨slRootEmb k hk K Dg, hmem⟩
  rw [h3] at h3'
  have h2n : 4 ≤ 2 ^ n := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.pow_le_pow_right (by norm_num) hn
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rcases j with _ | j
  · simp at h3'
    omega
  · rw [pow_succ] at h3'
    omega

private theorem slRoot_mem_normalizer_B08 [NeZero k] (hk : 3 ≤ k) {c b : K} (hc0 : c ≠ 0)
    (hb2 : b ^ 2 = c⁻¹) {t' : ↥(StatedSL k K)}
    (h : slMat t' = Matrix.diagonal (slTorusDiag k c))
    {D : Matrix.SpecialLinearGroup (Fin 2) K}
    (hD : (D : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![b, b⁻¹]) :
    t' ∈ Subgroup.normalizer (slRoot k hk K : Set ↥(StatedSL k K)) := by
  have hconj : ∀ A, t' * slRootEmb k hk K A * t'⁻¹ = slRootEmb k hk K (D * A * D⁻¹) :=
    fun A => conj_slRootEmb_of_slMat_eq_diagonal hk hc0 hb2 h hD A
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨A, rfl⟩
    rw [hconj]
    exact ⟨_, rfl⟩
  · rintro ⟨B, hB⟩
    refine ⟨D⁻¹ * B * D, ?_⟩
    have h2 : t' * slRootEmb k hk K (D⁻¹ * B * D) * t'⁻¹ = t' * x * t'⁻¹ := by
      rw [hconj, ← hB]
      congr 2
      group
    exact mul_left_cancel (mul_right_cancel h2)

theorem kAdjConcl_slTorus [NeZero k] [Finite K] [CharP K 2] (hk : 3 ≤ k) {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) {r : ℕ} (hr : Odd r) {c : K}
    (hord : orderOf c = r) {t' : ↥(StatedSL k K)}
    (h : slMat t' = Matrix.diagonal (slTorusDiag k c)) :
    KAdjConcl (Hinf (slQZero k K)) t' r n := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.pow_le_pow_right (by norm_num) hn
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [orderOf_zero K] at hord
    rw [← hord] at hr
    exact absurd hr (by decide)
  obtain ⟨b, hb2, hbo⟩ := exists_sqrt_inv_of_orderOf_odd hr hord
  have hb0 : b ≠ 0 := by
    rintro rfl
    have hcinv : c⁻¹ = 0 := by rw [← hb2]; ring
    exact hc0 (inv_eq_zero.1 hcinv)
  obtain ⟨D, hD⟩ := exists_sl2_diagonal hb0
  have hXle : slRoot k hk K ≤ Hinf (slQZero k K) := slRoot_le_hinf hk hK4
  have hXperf : ⁅slRoot k hk K, slRoot k hk K⁆ = slRoot k hk K :=
    commutator_slRoot_eq_self hk hK4
  have hisSLn : IsSLn ↥(slRoot k hk K) 2 n := isSLn_slRoot hk hK
  have hqs : CFSG.Open.IsQuasisimple (Bar2 (Hinf (slQZero k K))) :=
    isQuasisimple_bar2_hinf_slQZero hk hK4
  have hperf : ⁅Hinf (slQZero k K), Hinf (slQZero k K)⁆ = Hinf (slQZero k K) :=
    CFSG.RankThree.PartTwo.Sec18.commutator_inSubgroup_perfectResidual (slQZero k K)
  have hconj : ∀ A, t' * slRootEmb k hk K A * t'⁻¹ = slRootEmb k hk K (D * A * D⁻¹) :=
    fun A => conj_slRootEmb_of_slMat_eq_diagonal hk hc0 hb2 h hD A
  refine ⟨slRoot k hk K, slRoot k hk K, hXle, hXle, ?_, ?_⟩
  · intro N hN hnormN hXN _
    exact normal_closure_top_of_perfect _ hperf hqs _ hXle hXperf
      (not_isPGroup_slRoot_B08 hk hK hn) N hN hnormN hXN
  · rintro X' (rfl | rfl)
    · exact ⟨hisSLn, slRoot_mem_normalizer_B08 hk hc0 hb2 h hD,
        slRootEmb k hk K D, ⟨D, rfl⟩,
        by rw [orderOf_slRootEmb_diagonal hk hb0 hD, hbo],
        by rintro x ⟨A, rfl⟩; rw [hconj, map_mul, map_mul, map_inv]⟩
    · exact ⟨hisSLn, slRoot_mem_normalizer_B08 hk hc0 hb2 h hD,
        slRootEmb k hk K D, ⟨D, rfl⟩,
        by rw [orderOf_slRootEmb_diagonal hk hb0 hD, hbo],
        by rintro x ⟨A, rfl⟩; rw [hconj, map_mul, map_mul, map_inv]⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE