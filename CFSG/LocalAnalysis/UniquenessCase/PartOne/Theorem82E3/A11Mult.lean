module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.Alternating.Multipliers.OddKernel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open Subgroup

theorem kMult_A11 (J : Type) [Group J] [Finite J] (hq : CFSG.Open.IsQuasisimple J)
    (N : Subgroup J) [N.Normal] (hN : N ≤ center J)
    (hA : CFSG.LocalAnalysis.UniquenessCase.UC22.IsAlt (J ⧸ N) 11)
    (hodd : Odd (Nat.card (center J))) : center J = ⊥ := by
  obtain ⟨e⟩ := hA
  have : Group.IsPerfect J := ⟨hq.1⟩
  let η : J →* alternatingGroup (Fin (9 + 2)) := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have hη : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective N)
  have hker : η.ker = N := by
    ext x
    simp [η]
  have hK : η.ker ≤ center J := hker ▸ hN
  have hoddK : Odd (Nat.card η.ker) := by
    rw [hker]
    exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hN)
  have h1 := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (m := 9) (by norm_num) η hη hK
    hoddK
  have hNbot : N = ⊥ := by
    rw [← hker]
    exact Subgroup.eq_bot_of_card_eq _ h1
  rw [eq_bot_iff]
  intro x hx
  have hηx : η x ∈ center (alternatingGroup (Fin 11)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x', rfl⟩ := hη y
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hx x')]
  rw [alternatingGroup.center_eq_bot (by simp)] at hηx
  have hxker : x ∈ η.ker := MonoidHom.mem_ker.2 (Subgroup.mem_bot.1 hηx)
  rw [hker, hNbot] at hxker
  exact hxker

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
