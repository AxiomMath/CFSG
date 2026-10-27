module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily

open Subgroup
open scoped commutatorElement

variable {X : Type} [Group X]

theorem isParabolicTwo_top_of_isNontrivialParabolic [Finite X] {J : Subgroup X}
    (hJ : S19.IsNontrivialParabolic X J) : CFSG.AGLEmbedding.IsParabolicTwo ⊤ J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨S, hS⟩, -, -⟩ := hJ
  refine ⟨le_top, (S : Subgroup X), ⟨le_top, S.isPGroup', ?_⟩, ?_⟩
  · rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
    exact S.not_dvd_index
  · rw [top_inf_eq]
    exact hS

theorem ne_inf_normalizer_of_isNontrivialParabolic {J : Subgroup X}
    (hJ : S19.IsNontrivialParabolic X J) (T : Subgroup X)
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) :
    J ≠ ⊤ ⊓ normalizer (T : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, S, hSJ⟩ := hJ
  obtain ⟨-, hT2, hTi⟩ := hT
  rw [← Subgroup.relIndex, Subgroup.relIndex_top_right] at hTi
  intro hJT
  rw [top_inf_eq] at hJT
  have hSN : (S : Subgroup X) ≤ normalizer (T : Set X) :=
    (Subgroup.le_normalizer.trans hSJ.le).trans hJT.le
  have hsup : (S : Subgroup X) ⊔ T = T := by
    have h := (hT2.toSylow hTi).is_maximal' (S.isPGroup'.to_sup_of_normal_right' hT2 hSN)
      (by rw [IsPGroup.toSylow_coe]; exact le_sup_right)
    rwa [IsPGroup.toSylow_coe] at h
  have hST : T = S := S.is_maximal' hT2 (sup_eq_right.mp hsup)
  exact hSJ.ne (by rw [hJT, hST]; rfl)

theorem center_eq_bot_of_isNontrivialParabolic (hX : IsSimpleGroup X) {J : Subgroup X}
    (hJ : S19.IsNontrivialParabolic X J) : center X = ⊥ := by
  have := hX
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X)).resolve_right fun hc => ?_
  obtain ⟨-, -, T, hTJ⟩ := hJ
  have hN : normalizer (T : Set X) = ⊤ := by
    refine eq_top_iff.mpr fun g _ => Subgroup.mem_normalizer_iff.mpr fun x => ?_
    have hg : g ∈ center X := hc ▸ mem_top g
    rw [← Subgroup.mem_center_iff.mp hg x, mul_inv_cancel_right]
  exact not_top_lt (hN ▸ hTJ)

theorem commutator_eq_top_of_isNontrivialParabolic (hX : IsSimpleGroup X) {J : Subgroup X}
    (hJ : S19.IsNontrivialParabolic X J) : commutator X = ⊤ := by
  have := hX
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X)).resolve_left fun hc => ?_
  have hZ := center_eq_bot_of_isNontrivialParabolic hX hJ
  obtain ⟨x, hx⟩ := exists_ne (1 : X)
  refine hx (Subgroup.mem_bot.mp (hZ ▸ Subgroup.mem_center_iff.mpr fun y => ?_))
  have h : ⁅y, x⁆ ∈ commutator X := Subgroup.commutator_mem_commutator (mem_top y) (mem_top x)
  rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily
