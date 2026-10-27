module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155F1Bal
import CFSG.RankThree.PartTwo.Sec13.Item135CritProofTrans
public import CFSG.RankThree.PartTwo.Sec13.Item13Plane
public import CFSG.RankThree.PartTwo.Sec17.RouteWire14

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14

variable {G : Type} [Group G] [Finite G]

namespace Sylow155F1

theorem ncard_omegaA_le_nine {A B : Subgroup G} (hA : Late.IsE27 A) (hB : IsHyperplane A B)
    (hfree : ∀ b ∈ B, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A) : (omegaA A).ncard ≤ 9 := by
  have hB9 : Nat.card B = 9 := by
    have h := hB.2
    rw [hA.2] at h
    omega
  obtain ⟨a, haA, haB⟩ : ∃ a ∈ A, a ∉ B := by
    by_contra h
    push Not at h
    have h27 := Subgroup.card_le_of_le (show A ≤ B from h)
    rw [hA.2, hB9] at h27
    omega
  have hAB : A ⊓ B = B := inf_eq_right.mpr hB.1
  have hAa : A = Subgroup.zpowers a ⊔ B := by
    have h := TransProof.sup_eq_of_card (L := B) hA.2 (by rw [hAB]; exact hB9) haA haB
    rw [hAB] at h
    exact h.symm
  have hsub : omegaA A ⊆ pointsOff A B := by
    rintro F ⟨hFA, hF3, x, rfl, hx⟩
    refine ⟨hFA, hF3, fun hFB => ?_⟩
    have hx1 : x ≠ 1 := by
      rintro rfl
      rw [Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hF3
      norm_num at hF3
    exact hfree x (hFB (Subgroup.mem_zpowers x)) hx1 ⟨hFA, hF3, x, rfl, hx⟩
  calc (omegaA A).ncard ≤ (pointsOff A B).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = 9 := ncard_pointsOff hA.1 haA hAa haB hB9

theorem exists_mem_omegaA_of_ten_le_ncard {A B : Subgroup G} (hA : Late.IsE27 A)
    (hB : IsHyperplane A B) (h10 : 10 ≤ (omegaA A).ncard) :
    ∃ b ∈ B, b ≠ 1 ∧ Subgroup.zpowers b ∈ omegaA A := by
  by_contra h
  push Not at h
  have := ncard_omegaA_le_nine hA hB h
  omega

end Sylow155F1

theorem step155BalW_of_ten_le_ncard {A : Subgroup G} {c : G} {L : Subgroup G}
    (h10 : 10 ≤ (omegaA A).ncard) : Step155BalW A c L := by
  intro h X K Y M T P _ _ _ _ _ _ _ g _ _ _ B hB hfree
  obtain ⟨b, hb, hb1, hΩ⟩ := Sylow155F1.exists_mem_omegaA_of_ten_le_ncard h.isE27 hB h10
  exact absurd hΩ (hfree b hb hb1)

theorem step155F1ZeroW_of_ten_le_ncard {A : Subgroup G} {c : G} {L : Subgroup G}
    (h142 : Concl142S14) (h10 : 10 ≤ (omegaA A).ncard) : Step155F1ZeroW A c L := fun h =>
  step155F1ZeroW_of_bal (h142 G A c L h) (step155BalW_of_ten_le_ncard h10) h

theorem step155HostCharSupW_of_ten_le_ncard {A : Subgroup G} {c : G} {L : Subgroup G}
    (h142 : Concl142S14) (h1444 : Item1444S14) (h10 : 10 ≤ (omegaA A).ncard) :
    Step155HostCharSupW A c L := fun h =>
  step155HostCharSupW_of_f1Zero (h1444 G A c L h) (step155F1ZeroW_of_ten_le_ncard h142 h10) h

end CFSG.RankThree.PartTwo.Sec15
