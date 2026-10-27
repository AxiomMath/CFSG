module

public import CFSG.RankThree.PartOne.S13K.Row1

public section

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.GroupTheory

theorem exists_reflection_of_facts {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (hF : Sec12Facts G p A c L E) :
    ∃ t ∈ reflectionSet p E, t ∈ torusImage E L := by
  obtain ⟨hclosure, r, -, -, -, hweyl, -⟩ := hF.three
  by_contra hne
  push Not at hne
  have hempty : reflectionSet p E ∩ (torusImage E L : Set (MulAut E)) = ∅ := by
    ext t
    simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_empty_iff_false, iff_false]
    exact fun ⟨ht, htL⟩ => hne t ht htL
  rw [hempty, Subgroup.closure_empty] at hclosure
  have hnt := Sec12Three.nontrivial_of_rowWeylIso hweyl
  obtain ⟨⟨g, hg⟩, hg1⟩ := exists_ne (1 : ↥(torusImage E L))
  apply hg1
  apply Subtype.ext
  have : g ∈ (⊥ : Subgroup (MulAut E)) := hclosure ▸ hg
  exact Subgroup.mem_bot.mp this

theorem kf132AtEx_of_at {r : ℕ} (h : KF132At r) : KF132AtEx r := by
  intro G _ _ p A c L E hH hF hF13 hT hr4 hrow hrA hr9
  obtain ⟨t, ht, htL⟩ := exists_reflection_of_facts hF
  exact ⟨t, ht, htL, h G p A c L E hH hF hF13 hT hr4 hrow hrA hr9 t ht htL⟩

theorem kf132AtEx_row1 (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF132AtEx 1 :=
  kf132AtEx_of_at (kf132At_row1 hGA)

end CFSG.RankThree.PartOne.S13K
