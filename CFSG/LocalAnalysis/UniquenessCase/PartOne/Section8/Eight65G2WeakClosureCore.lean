module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65InversionG2General
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65G2FixDimTorus
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65G2FixDimWeyl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint.Chevalley CFSG.AGLEmbedding.KFactProofs.G2Q

private theorem eq_one_or_eq_or_eq_inv_of_cube {L : Type} [Field L] {ω u : Lˣ} (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) (hu3 : u ^ 3 = 1) : u = 1 ∨ u = ω ∨ u = ω⁻¹ := by
  have hω3' : (ω : L) ^ 3 = 1 := by simpa using congrArg Units.val hω3
  have hu3' : (u : L) ^ 3 = 1 := by simpa using congrArg Units.val hu3
  have hω1' : (ω : L) - 1 ≠ 0 := sub_ne_zero.2 fun h => hω1 (Units.ext h)
  have hsum : (ω : L) ^ 2 + ω + 1 = 0 := by
    have h : ((ω : L) - 1) * ((ω : L) ^ 2 + ω + 1) = 0 := by linear_combination hω3'
    exact (mul_eq_zero.1 h).resolve_left hω1'
  have hprod : ((u : L) - 1) * (((u : L) - ω) * ((u : L) - ω ^ 2)) = 0 := by
    linear_combination hu3' + ((u : L) - (u : L) ^ 2) * hsum + ((u : L) - 1) * hω3'
  have hinv : ω⁻¹ = ω ^ 2 := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ']
    exact hω3
  rcases mul_eq_zero.1 hprod with h | h
  · exact Or.inl (Units.ext (sub_eq_zero.1 h))
  · rcases mul_eq_zero.1 h with h | h
    · exact Or.inr (Or.inl (Units.ext (sub_eq_zero.1 h)))
    · refine Or.inr (Or.inr ?_)
      rw [hinv]
      exact Units.ext (by simpa using sub_eq_zero.1 h)

theorem g2_conj_tz_mem_zpowers_of_mem_extSub
    {L : Type} [Field L] (h3 : (3 : L) ≠ 0) {m : ℕ} {ω : Lˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hExt : Ext3 (tzPart (L := L) m) (yq : ModGL .G2 L)) (g : ModGL .G2 L)
    (hx : g * (tz 1 ω⁻¹ : ModGL .G2 L) * g⁻¹ ∈ extSub hExt) :
    g * (tz 1 ω⁻¹ : ModGL .G2 L) * g⁻¹ ∈ Subgroup.zpowers (tz 1 ω⁻¹ : ModGL .G2 L) := by
  obtain ⟨t, ht, k, hk3, hxk⟩ := (mem_extSub_iff_lt hExt).1 hx
  obtain ⟨s, u, -, -, rfl⟩ : ∃ s u : Lˣ, s ^ m = 1 ∧ u ^ m = 1 ∧ t = tz s u := ht
  have hz8 : 8 ≤ g2AdjFixDim (tz 1 ω⁻¹ : ModGL .G2 L) :=
    eight_le_g2AdjFixDim_tz_one (by rw [inv_pow, hω3, inv_one])
  have hx8 : 8 ≤ g2AdjFixDim ((tz s u : ModGL .G2 L) * (yq : ModGL .G2 L) ^ k) := by
    rw [← hxk, g2AdjFixDim_conj]
    exact hz8
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    rw [pow_zero, mul_one] at hxk hx8
    obtain ⟨hs, hu3⟩ := eq_one_of_eight_le_g2AdjFixDim_tz hx8
    rw [hxk, hs]
    rcases eq_one_or_eq_or_eq_inv_of_cube hω3 hω1 hu3 with h | h | h
    · rw [h, tz_one_one]
      exact Subgroup.one_mem _
    · have e : (tz 1 ω : ModGL .G2 L) = (tz 1 ω⁻¹)⁻¹ := by rw [tz_inv, inv_one, inv_inv]
      rw [h, e]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
    · rw [h]
      exact Subgroup.mem_zpowers _
  · exact absurd hx8 (not_le.2 (lt_of_le_of_lt
      (g2AdjFixDim_tz_mul_yq_pow_le_four h3 s u (Nat.pos_iff_ne_zero.1 hkpos) hk3)
      (by norm_num)))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
