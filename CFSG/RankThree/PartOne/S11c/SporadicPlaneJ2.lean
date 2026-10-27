module

public import CFSG.RankThree.PartOne.KS.J2
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneKit

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem j2_two_part_le :
    ∀ y ∈ j2P, orderOf y = 5 → ∀ R2 : Subgroup (Equiv.Perm (Fin 315)), IsPGroup 2 R2 →
      R2 ≤ j2R ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 315))) → Nat.card R2 ≤ 4 := by
  obtain ⟨⟨hQP, -, -, -, hQsyl⟩, ⟨hlines, -⟩, hrec, hgood, hbad⟩ :=
    R3E_J2_full_five_centralizer_structure
  refine twoPart_le_of_lines Nat.prime_five j2_autModel.le hQsyl hlines (fun j => ?_)
  refine ⟨j, ⟨1, j2R.one_mem, by simp⟩, fun R2 hR2 hle => ?_⟩
  obtain ⟨hC, -⟩ := hrec j
  have hle' : R2 ≤ j2FiveC j := by rwa [hC]
  by_cases hg : j.val = 0 ∨ j.val = 1 ∨ j.val = 4
  · obtain ⟨hc, -⟩ := hgood j hg
    have h4 := card_le_of_isPGroup_two_of_le (a := 1) (m := 25) (by rw [hc]; norm_num)
      (by norm_num) hR2 hle'
    omega
  · have hbad' : j.val = 2 ∨ j.val = 3 ∨ j.val = 5 := by
      have := j.2
      omega
    obtain ⟨hc, -⟩ := hbad j hbad'
    have h4 := card_le_of_isPGroup_two_of_le (a := 2) (m := 75) (by rw [hc]; norm_num)
      (by norm_num) hR2 hle'
    omega

theorem sporadicPlanesCentralize_J2 :
    SporadicPlanesCentralize (Carrier .J2) := by
  refine sporadicPlanesCentralize_of_model j2_autModel j2_card_le j2PermEquiv (S := {5})
    (fun p hp hp3 => ?_) (fun p hp => ?_)
  · by_cases hp5 : p = 5
    · exact Or.inl (by simp [hp5])
    · refine Or.inr ?_
      rw [card_j2R, show (1209600 : ℕ) = 2 ^ 8 * 3 ^ 3 * 5 ^ 2 * 7 by norm_num]
      exact not_sq_dvd_mul_of_coprime (B := 2) hp (coprime_two_three_five_pow hp hp3 hp5 8 3 2)
        (by norm_num) (by decide) (by norm_num)
  · rw [Finset.mem_singleton] at hp
    subst hp
    exact ⟨4, Or.inl ⟨rfl, by norm_num⟩, moveBound_of_plain j2_two_part_le⟩

end CFSG.RankThree.PartOne
