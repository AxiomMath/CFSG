module

public import CFSG.RankThree.PartTwo.Sec17.Item17TailData

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

namespace Proof17Res

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_cQuot (Y₀ : Subgroup G) :
    Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer ((cQuot Y₀ : Subgroup G) : Set G) := by
  set N := Subgroup.normalizer (Y₀ : Set G) with hN
  set O := CFSG.Open.pCoreOf 2 Y₀ with hO
  have hNO : N ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀
  intro m hm
  refine Subgroup.mem_normalizer_fintype fun k hk => ?_
  rw [SetLike.mem_coe, ← SetLike.mem_coe, coe_cQuot] at hk ⊢
  obtain ⟨hkN, hk⟩ := hk
  refine ⟨mul_mem (mul_mem hm hkN) (inv_mem hm), fun y hy => ?_⟩
  have hy' : m⁻¹ * y * m⁻¹⁻¹ ∈ Y₀ := (Subgroup.mem_normalizer_iff.mp (inv_mem hm) y).mp hy
  have h1 := hk _ hy'
  have h2 := (Subgroup.mem_normalizer_iff.mp (hNO hm) _).mp h1
  have e : m * (k * (m⁻¹ * y * m⁻¹⁻¹) * k⁻¹ * (m⁻¹ * y * m⁻¹⁻¹)⁻¹) * m⁻¹ =
      m * k * m⁻¹ * y * (m * k * m⁻¹)⁻¹ * y⁻¹ := by group
  rwa [e] at h2

end Proof17Res

end CFSG.RankThree.PartTwo.Sec17
