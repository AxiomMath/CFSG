module

public import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactURoot
public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary
import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsI

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

private theorem spUFix_traceZero_one {s : F}
    (hs : s + unitaryInvolution F 2 1 s = 0) : s = 0 ∨ s = 1 := by
  have hs' : s + s ^ 2 = 0 := by
    have hσ : unitaryInvolution F 2 1 s = s ^ 2 := by
      rw [unitaryInvolution_apply, pow_one]
    rw [← hσ]
    exact hs
  have h : s * (1 + s) = 0 := by
    have : s * (1 + s) = s + s ^ 2 := by ring
    rw [this]
    exact hs'
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · right
    have h11 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
    have h1' : 1 + s = 1 + 1 := by rw [h11]; exact h1
    exact add_left_cancel h1'

theorem exists_eq_spUFixRootU (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ} (hm : 4 ≤ m)
    (R : Subgroup (StatedProj (StatedSU m (2 ^ n) F))) (hR : Nat.card R = 2 ^ n)
    (hRt : ∀ x ∈ R, x ≠ 1 → IsUnitaryTransvectionIn m n x) :
    ∃ e : Fin m → F, e ≠ 0 ∧ herm (unitaryInvolution F 2 n) e e = 0 ∧
      R = spUFixRootU hF m e := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst n
    exfalso
    have h2 : 1 < Nat.card F := Finite.one_lt_card
    rw [hF] at h2
    exact absurd h2 (by norm_num)
  · rcases lt_or_ge 1 n with hn2 | hn1
    · obtain ⟨e, he0, he, hiff⟩ := kFacts_su_rootGroup hF (by omega) hm R hR hRt
      exact ⟨e, he0, he,
        Subgroup.ext fun x => (hiff x).trans (mem_spUFixRootU hF he).symm⟩
    · have hn1' : n = 1 := by omega
      subst n
      have hR2 : Nat.card R = 2 := by simpa using hR
      obtain ⟨r, hrR, hr1⟩ : ∃ r ∈ R, r ≠ 1 := by
        by_contra hcon
        have hbot : R = ⊥ := (Subgroup.eq_bot_iff_forall R).mpr fun x hx => by
          by_contra hx1
          exact hcon ⟨x, hx, hx1⟩
        rw [hbot, Subgroup.card_bot] at hR2
        omega
      obtain ⟨e, he0, he, hre⟩ := kFacts_su_exists_centre hF (hRt r hrR hr1)
      have h1 : (1 : F) + unitaryInvolution F 2 1 1 = 0 := by
        rw [map_one]
        exact CharTwo.add_self_eq_zero 1
      have hT0 : kFactsSuProjTv hF m e 0 = 1 := by
        unfold kFactsSuProjTv
        rw [kFacts_suTv_zero_param hF he, map_one]
      refine ⟨e, he0, he, le_antisymm ?_ ?_⟩
      · intro x hx
        rw [mem_spUFixRootU hF he]
        by_cases hx1 : x = 1
        · exact ⟨0, by simp, by rw [hx1, hT0]⟩
        · obtain ⟨e', he0', he', hxe'⟩ := kFacts_su_exists_centre hF (hRt x hx hx1)
          obtain ⟨μ, hμ⟩ := kFacts_su_smul_of_mem hF hm R hRt he0 he he0' he'
            (hre ▸ hrR) (hxe' ▸ hx)
          refine ⟨unitaryInvolution F 2 1 μ * μ * 1, ?_, ?_⟩
          · have hσs : unitaryInvolution F 2 1 (unitaryInvolution F 2 1 μ * μ * 1) =
                unitaryInvolution F 2 1 μ * μ * 1 := by
              rw [map_mul, map_mul, map_one, unitaryInvolution_involutive hF μ]
              ring
            rw [hσs]
            exact CharTwo.add_self_eq_zero _
          · rw [hxe', hμ, kFacts_suProjTv_smul_vec hF he h1 μ]
      · unfold spUFixRootU
        rw [Subgroup.closure_le]
        rintro x ⟨s, hs, rfl⟩
        rcases spUFix_traceZero_one hs with hs0 | hs1
        · rw [hs0, hT0]
          exact R.one_mem
        · rw [hs1]
          exact hre ▸ hrR

end CFSG.LocalAnalysis.WeakClosure81

end
