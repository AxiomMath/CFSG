module

import CFSG.GroupTheory.PerfectAbelianSylow
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNotLarge23.Parts
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Walter.AStar.Basic
public import CFSG.Walter.J1Props.Facts
public import CFSG.Walter.Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KS23

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup

theorem eq_bot_or_isSimpleGroup_of_isJ1 {S : Type} [Group S] [Finite S] (hS : IsJ1 S)
    (Y : Subgroup S) (hY : ⁅Y, Y⁆ = Y) : Y = ⊥ ∨ IsSimpleGroup ↥Y := by
  classical
  by_cases hbot : Y = ⊥
  · exact Or.inl hbot
  right
  haveI : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hY
  haveI : Nontrivial ↥Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hbot
  have hScard : Nat.card S = 175560 :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.KNL23.card_isJ1 hS
  obtain ⟨e⟩ := hS
  let ε : S ≃* CFSG.Open.walterJ1 := e.trans CFSG.Walter.walterJ1EquivNative.symm
  have hSylow : CFSG.Walter.HasAbelianSylowTwo S :=
    CFSG.Walter.HasAbelianSylowTwo.of_surjective (f := ε.symm) ε.symm.surjective
      CFSG.Walter.J1Props.hasAbelianSylowTwo
  have hYab : CFSG.Walter.HasAbelianSylowTwo ↥Y := hSylow.subgroup Y
  have hYdvd : Nat.card ↥Y ∣ Nat.card S := Subgroup.card_subgroup_dvd_card Y
  have h16 : ¬ 16 ∣ Nat.card ↥Y := by
    intro h
    have h' : 16 ∣ Nat.card S := h.trans hYdvd
    rw [hScard] at h'
    norm_num at h'
  have hsq : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ^ 2 ∣ Nat.card ↥Y := by
    intro p hp hp2 h
    have h' : p ^ 2 ∣ Nat.card S := h.trans hYdvd
    rw [hScard] at h'
    have hp175 : p ∣ 175560 := (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans h'
    rcases CFSG.Walter.J1Props.prime_dvd_card hp hp175 with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp2 rfl
    all_goals norm_num at h'
  exact CFSG.isSimpleGroup_of_isPerfect_of_card
    (fun P x hx y hy => by
      haveI := hYab P
      exact Subgroup.mul_comm_of_mem_isMulCommutative P hx hy) h16 hsq

end CFSG.LocalAnalysis.UniquenessCase.UC22.KS23

end
