module

public import CFSG.RankThree.PartOne.K156.Gen
public import CFSG.RankThree.PartOne.S15K.LayerData

public section

namespace CFSG.RankThree.PartOne.K156

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K
open CFSG.RankThree.PartOne.S15K (Sec13Avail)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G]

theorem node156_of_E_eq_A
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS13 : Sec13Avail) (h1322 : Node1322) (h1320 : Node1320Struct)
    {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} (h15 : Sec15Hyp G p A c L E)
    (hEA : E = A) :
    ∀ X ∈ thetaCompZeroStarE p E, X ≤ lieGenerated p E := by
  intro X hX
  have h := h15.h12
  have hE3 : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  have hnot5 : ¬ Outcome152Five p E A (lieGenerated p E) := by
    rintro ⟨-, -, -, -, -, -, hne, -⟩
    exact hne hEA
  have hF13 := hS13 G p A c L E h hnot5
  obtain ⟨B, c', hB, hc'B, hc'1, h', hF'⟩ := hF13.reinstantiate X hX
  have hEB : E = B :=
    (Subgroup.eq_of_le_of_card_ge hB.1 (by rw [hE3, hB.2.2.1])).symm
  have hnot5' : ¬ Outcome152Five p E B (lieGenerated p E) := by
    rintro ⟨-, -, -, -, -, hE4, -, -⟩
    rw [hE3] at hE4
    have : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right h.prime.one_lt (by norm_num)
    omega
  have hF13' := hS13 G p B c' X E h' hnot5'
  by_cases hL3 : IsLThreeTypeAt p X
  ·
    obtain ⟨f, hf1, hpf, hm⟩ := hL3
    obtain ⟨hclos, r, hr1, hr12, -, hweyl, -, -⟩ := hF'.three
    obtain ⟨s, hs, s', hs', hne⟩ := exists_noncommuting_of_closure hclos
      (nonabelian_of_rowWeylIso hr1 hr12 hweyl)
    exact row1_le_of_ne hGA h' hF' hEB hpf hf1 hm hs.1 hs.2 hs'.1 hs'.2
      (fun hss => hne (by rw [hss]))
  ·
    obtain ⟨hrow578, -, -⟩ := h1320 G p B c' X E h' hF' hF13' hnot5' hEB hL3
    obtain ⟨-, ⟨e⟩⟩ := h1322 G p B c' X E h' hF' hF13' hnot5' hEB hL3
    rcases hrow578 with ⟨f, hf1, hpf, hm⟩ | ⟨f, hf1, hpf, hm⟩ | ⟨f, hf1, hpf, hm⟩
    · exact row5_le hGA h' hF' hF13' hnot5' hEB hf1 hpf hm e
    · exact row7_le hGA h' hF' hF13' hnot5' hEB hf1 hpf hm e
    · exact row8_le hGA h' hF' hF13' hEB hf1 hpf hm

end CFSG.RankThree.PartOne.K156
