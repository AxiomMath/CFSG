module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.RankThree.PartTwo.Sec12.Item125Basic
import CFSG.RankThree.PartTwo.Sec4.LThreePiAct
import CFSG.RankThree.PartTwo.Sec6.Item612Basic
import CFSG.RankThree.PartTwo.KFacts.K71Lift

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank

namespace Desc143X

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_inv_mul_mem_theta {A H : Subgroup G}
    (hAmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hAH : A ≤ Subgroup.normalizer (H : Set G)) {x : G} (hxH : x ∈ H) (hx3 : x ^ 3 = 1)
    (hfix : ∀ α ∈ A, x⁻¹ * (α * x * α⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) H) :
    ∃ α ∈ A, α⁻¹ * x ∈ inSubgroup (aschbacherSolvableCore 3) H := by
  set T := inSubgroup (aschbacherSolvableCore 3) H with hT
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAmax.1.2 g g.2)⟩
  obtain ⟨n, hn, hnfix⟩ := Sec12.exists_fixed_lift hA3 hAH hfix
  have hTH : T ≤ H := Subgroup.map_subtype_le _
  have hHT : H ≤ Subgroup.normalizer (T : Set G) := Sec6.le_normalizer_theta H
  set z := x * n with hz
  have hconj : ∀ k : ℕ, x ^ k * n * (x ^ k)⁻¹ ∈ T := fun k =>
    (Subgroup.mem_normalizer_iff.mp (hHT (pow_mem hxH k)) n).mp hn
  have hz3 : z ^ 3 ∈ T := by
    have e : z ^ 3 = (x ^ 1 * n * (x ^ 1)⁻¹) * (x ^ 2 * n * (x ^ 2)⁻¹) *
        (x ^ 3 * n * (x ^ 3)⁻¹) * x ^ 3 := by
      rw [hz, pow_three]
      group
    rw [e]
    exact mul_mem (mul_mem (mul_mem (hconj 1) (hconj 2)) (hconj 3)) (by rw [hx3]; exact one_mem _)
  obtain ⟨e, s, hs3, hzs⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos z).ne' 3 (by norm_num)
  set w := z ^ s with hw
  have hwT : w ^ 3 ∈ T := by
    rw [hw, ← pow_mul, mul_comm, pow_mul]
    exact pow_mem hz3 s
  have hw3e : (w ^ 3) ^ (3 ^ e) = 1 := by
    rw [hw, ← pow_mul, ← pow_mul, show s * (3 * 3 ^ e) = 3 ^ e * s * 3 by ring, pow_mul, ← hzs,
      pow_orderOf_eq_one, one_pow]
  have hw3 : w ^ 3 = 1 := by
    obtain ⟨u, hu, hue⟩ := hwT
    have hu3 : u ^ 3 ^ e = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [show ((u : H) : G) = w ^ 3 from hue]
      exact hw3e
    have h1 := KFacts.eq_one_of_mem_aschbacherSolvableCore_of_pow hu hu3
    rw [← hue, h1, map_one]
  have hwA : ∀ α ∈ A, α * w = w * α := by
    intro α hα
    have h1 : α * z = z * α := by
      have := hnfix α hα
      calc α * z = α * z * α⁻¹ * α := by group
        _ = z * α := by rw [this]
    exact (Commute.pow_right h1 s).eq
  have hwmem : w ∈ A := Sec4.mem_of_maximal_of_commute hAmax hw3 hwA
  have hss : s * s = 3 * (s * s / 3) + 1 := by
    have h1 : s % 3 = 1 ∨ s % 3 = 2 := by omega
    have h2 : s * s % 3 = 1 := by
      rw [Nat.mul_mod]
      rcases h1 with h1 | h1 <;> rw [h1]
    omega
  obtain ⟨k, hk⟩ : ∃ k : ℕ, s * s = 3 * k + 1 := ⟨s * s / 3, hss⟩
  refine ⟨w ^ s, pow_mem hwmem s, ?_⟩
  have hws : w ^ s = (z ^ 3) ^ k * z := by
    rw [hw, ← pow_mul, hk, pow_succ, pow_mul]
  have hxz : x = z * n⁻¹ := by rw [hz]; group
  have hcomm : Commute z ((z ^ 3) ^ k) := (Commute.refl z).pow_right _ |>.pow_right _
  have e2 : (w ^ s)⁻¹ * x = ((z ^ 3) ^ k)⁻¹ * n⁻¹ := by
    rw [hws, hxz, mul_inv_rev]
    calc z⁻¹ * ((z ^ 3) ^ k)⁻¹ * (z * n⁻¹)
        = z⁻¹ * (((z ^ 3) ^ k)⁻¹ * z) * n⁻¹ := by group
      _ = z⁻¹ * (z * ((z ^ 3) ^ k)⁻¹) * n⁻¹ := by
          rw [(hcomm.inv_right).eq]
      _ = ((z ^ 3) ^ k)⁻¹ * n⁻¹ := by group
  rw [e2]
  exact mul_mem (inv_mem (pow_mem hz3 _)) (inv_mem hn)

end Desc143X

end CFSG.RankThree.PartTwo.Sec14
