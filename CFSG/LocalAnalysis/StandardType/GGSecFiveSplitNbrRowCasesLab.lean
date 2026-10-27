module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem rowLab_SA {p : ℕ} {lab : LargeEvenLabel} (h : ggRowP_SA p lab) :
    GGNSRowLab p lab := by simp only [GGNSRowLab, h, true_or, or_true]

private theorem rowLab_SD {p : ℕ} {lab : LargeEvenLabel} (h : ggRowP_SD p lab) :
    GGNSRowLab p lab := by simp only [GGNSRowLab, h, true_or, or_true]

private theorem rowLab_SE6 {p : ℕ} {lab : LargeEvenLabel} (h : ggRowP_SE6 p lab) :
    GGNSRowLab p lab := by simp only [GGNSRowLab, h, true_or, or_true]

private theorem rowLab_SE7 {p : ℕ} {lab : LargeEvenLabel} (h : ggRowP_SE7 p lab) :
    GGNSRowLab p lab := by simp only [GGNSRowLab, h, true_or, or_true]

private theorem rowLab_SE8 {p : ℕ} {lab : LargeEvenLabel} (h : ggRowP_SE8 p lab) :
    GGNSRowLab p lab := by simp only [GGNSRowLab, h, true_or, or_true]

private theorem rowLab_ESU {p : ℕ} {lab : LargeEvenLabel} (h : ggRowP_ESU p lab) :
    GGNSRowLab p lab := by simp only [GGNSRowLab, h, true_or, or_true]

private theorem rowLab_EOmP {p : ℕ} {lab : LargeEvenLabel} (h : ggRowP_EOmP p lab) :
    GGNSRowLab p lab := by simp only [GGNSRowLab, h, true_or, or_true]

private theorem rowLab_EOmM {p : ℕ} {lab : LargeEvenLabel} (h : ggRowP_EOmM p lab) :
    GGNSRowLab p lab := by simp only [GGNSRowLab, h, true_or, or_true]

private theorem rowLab_ETwE6 {p : ℕ} {lab : LargeEvenLabel} (h : ggRowP_ETwE6 p lab) :
    GGNSRowLab p lab := by simp only [GGNSRowLab, h, true_or, or_true]

private theorem rowLab_EE7 {p : ℕ} {lab : LargeEvenLabel} (h : ggRowP_EE7 p lab) :
    GGNSRowLab p lab := by simp only [GGNSRowLab, h, true_or, or_true]

private theorem rowLab_EE8 {p : ℕ} {lab : LargeEvenLabel} (h : ggRowP_EE8 p lab) :
    GGNSRowLab p lab := by simp only [GGNSRowLab, h, true_or, or_true]

private theorem rowLab_NB {p : ℕ} {lab : LargeEvenLabel} (h : ggRowP_NB p lab) :
    GGNSRowLab p lab := by simp only [GGNSRowLab, h, true_or, or_true]

private theorem rowLab_NF4 {p : ℕ} {lab : LargeEvenLabel} (h : ggRowP_NF4 p lab) :
    GGNSRowLab p lab := by simp only [GGNSRowLab, h, true_or, or_true]

private theorem rowLab_NAP {p : ℕ} {lab : LargeEvenLabel} (h : ggRowP_NAP p lab) :
    GGNSRowLab p lab := by simp only [GGNSRowLab, h, true_or, or_true]

private theorem rowLab_NTwAM {p : ℕ} {lab : LargeEvenLabel} (h : ggRowP_NTwAM p lab) :
    GGNSRowLab p lab := by simp only [GGNSRowLab, h, true_or, or_true]

private theorem rowLab_NDOdd {p : ℕ} {lab : LargeEvenLabel} (h : ggRowP_NDOdd p lab) :
    GGNSRowLab p lab := by simp only [GGNSRowLab, h, true_or, or_true]

private theorem rowLab_NTwD {p : ℕ} {lab : LargeEvenLabel} (h : ggRowP_NTwD p lab) :
    GGNSRowLab p lab := by simp only [GGNSRowLab, h, true_or, or_true]

private theorem rowLab_NE6 {p : ℕ} {lab : LargeEvenLabel} (h : ggRowP_NE6 p lab) :
    GGNSRowLab p lab := by simp only [GGNSRowLab, h, true_or, or_true]

private theorem rowLab_Small {p : ℕ} {lab : LargeEvenLabel} (h : ggRowP_Small p lab) :
    GGNSRowLab p lab := by simp only [GGNSRowLab, h, true_or, or_true]

private theorem rowLab_ZA8 {p : ℕ} {lab : LargeEvenLabel} (h : ggRowP_ZA8 p lab) :
    GGNSRowLab p lab := by simp only [GGNSRowLab, h, true_or, or_true]

private theorem rowLab_ZE6 {p : ℕ} {lab : LargeEvenLabel} (h : ggRowP_ZE6 p lab) :
    GGNSRowLab p lab := by simp only [GGNSRowLab, h, true_or, or_true]

private theorem rowLab_smallA {p r n : ℕ} (h : r ≤ 2) : GGNSRowLab p ⟨.A, r, n⟩ :=
  rowLab_Small (.inl ⟨rfl, h⟩)

private theorem rowLab_smallBC {p r n : ℕ} {t : LargeEvenLieTag} (ht : t = .B ∨ t = .C)
    (h : r = 2) : GGNSRowLab p ⟨t, r, n⟩ :=
  rowLab_Small (.inr (.inl ⟨ht, h⟩))

private theorem rowLab_smallTwA {p r n : ℕ} (h : r ≤ 2) : GGNSRowLab p ⟨.twA, r, n⟩ :=
  rowLab_Small (.inr <| .inr <| .inr <| .inr <| .inr <| .inl ⟨rfl, h⟩)

private theorem rowLab_smallTwD {p r n : ℕ} (h : r = 2) : GGNSRowLab p ⟨.twD, r, n⟩ :=
  rowLab_Small (.inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl ⟨rfl, h⟩)

private theorem rowLab_smallTag {p r n : ℕ} {t : LargeEvenLieTag}
    (ht : t = .B2der ∨ t = .G2 ∨ t = .G2der ∨ t = .triD4 ∨ t = .twB2 ∨ t = .twF4 ∨
      t = .twF4der) : GGNSRowLab p ⟨t, r, n⟩ := by
  refine rowLab_Small ?_
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inr <| .inr <| .inl rfl
  · exact .inr <| .inr <| .inr <| .inl rfl
  · exact .inr <| .inr <| .inr <| .inr <| .inl rfl
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl rfl
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl rfl
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl rfl
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr rfl

private theorem halfSplit_dvd_or {p : ℕ} {lab : LargeEvenLabel} {c : Prop}
    (h : LargeEvenHalfSplit p lab c) :
    p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1 ∨ ggRowP_ZA8 p lab ∨ ggRowP_ZE6 p lab := by
  rcases h with (⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨hn, hp⟩) | ⟨-, h⟩ | ⟨-, h⟩ |
      ⟨-, -, hn, -, hp⟩ | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inl h
  · exact .inr (.inl (by norm_num [hn, hp]))
  · exact .inr (.inl h)
  · exact .inl h
  · exact .inr (.inl (by norm_num [hn, hp]))
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))

private theorem rowLab_of_sub {p : ℕ} {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hm : p ∣ 2 ^ lab.n - 1) : GGNSRowLab p lab := by
  obtain ⟨t, r, n⟩ := lab
  cases t
  case A =>
    by_cases h3 : 3 ≤ r
    · exact rowLab_SA ⟨.inl ⟨rfl, h3⟩, hm⟩
    · exact rowLab_smallA (by omega)
  case twA =>
    by_cases h3 : 3 ≤ r
    · exact rowLab_NTwAM ⟨.inl ⟨rfl, h3⟩, hm⟩
    · exact rowLab_smallTwA (by omega)
  case B =>
    have hr : 2 ≤ r := hlab.2.1
    by_cases h3 : 3 ≤ r
    · exact rowLab_NB ⟨.inl rfl, h3, .inl hm⟩
    · exact rowLab_smallBC (.inl rfl) (by omega)
  case C =>
    have hr : 2 ≤ r := hlab.2.1
    by_cases h3 : 3 ≤ r
    · exact rowLab_NB ⟨.inr rfl, h3, .inl hm⟩
    · exact rowLab_smallBC (.inr rfl) (by omega)
  case D =>
    have hr : 3 ≤ r := hlab.2
    by_cases h4 : 4 ≤ r
    · exact rowLab_SD ⟨rfl, h4, hm⟩
    · exact rowLab_SA ⟨.inr ⟨rfl, (by omega : r = 3)⟩, hm⟩
  case twD =>
    have hr : 2 ≤ r := hlab.2
    by_cases h4 : 4 ≤ r
    · exact rowLab_NTwD ⟨rfl, h4, .inr hm⟩
    · by_cases h3 : r = 3
      · exact rowLab_NTwAM ⟨.inr ⟨rfl, h3⟩, hm⟩
      · exact rowLab_smallTwD (by omega)
  case E6 => exact rowLab_SE6 ⟨rfl, hm⟩
  case E7 => exact rowLab_SE7 ⟨rfl, hm⟩
  case E8 => exact rowLab_SE8 ⟨rfl, hm⟩
  case F4 => exact rowLab_NF4 ⟨rfl, .inl hm⟩
  case twE6 => exact rowLab_NE6 (.inr ⟨rfl, hm⟩)
  all_goals exact rowLab_smallTag (by decide)

private theorem rowLab_of_add {p : ℕ} {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hp : p ∣ 2 ^ lab.n + 1) : GGNSRowLab p lab := by
  obtain ⟨t, r, n⟩ := lab
  cases t
  case A =>
    by_cases h3 : 3 ≤ r
    · exact rowLab_NAP ⟨.inl ⟨rfl, h3⟩, hp⟩
    · exact rowLab_smallA (by omega)
  case twA =>
    by_cases h3 : 3 ≤ r
    · exact rowLab_ESU ⟨.inl ⟨rfl, h3⟩, hp⟩
    · exact rowLab_smallTwA (by omega)
  case B =>
    have hr : 2 ≤ r := hlab.2.1
    by_cases h3 : 3 ≤ r
    · exact rowLab_NB ⟨.inl rfl, h3, .inr hp⟩
    · exact rowLab_smallBC (.inl rfl) (by omega)
  case C =>
    have hr : 2 ≤ r := hlab.2.1
    by_cases h3 : 3 ≤ r
    · exact rowLab_NB ⟨.inr rfl, h3, .inr hp⟩
    · exact rowLab_smallBC (.inr rfl) (by omega)
  case D =>
    have hr : 3 ≤ r := hlab.2
    by_cases h4 : 4 ≤ r
    · rcases Nat.even_or_odd r with he | ho
      · exact rowLab_EOmP ⟨rfl, h4, he, hp⟩
      · obtain ⟨k, hk⟩ := ho
        exact rowLab_NDOdd ⟨rfl, (by omega : 5 ≤ r), ⟨k, hk⟩, hp⟩
    · exact rowLab_NAP ⟨.inr ⟨rfl, (by omega : r = 3)⟩, hp⟩
  case twD =>
    have hr : 2 ≤ r := hlab.2
    by_cases h4 : 4 ≤ r
    · rcases Nat.even_or_odd r with he | ho
      · exact rowLab_NTwD ⟨rfl, h4, .inl ⟨he, hp⟩⟩
      · obtain ⟨k, hk⟩ := ho
        exact rowLab_EOmM ⟨rfl, (by omega : 5 ≤ r), ⟨k, hk⟩, hp⟩
    · by_cases h3 : r = 3
      · exact rowLab_ESU ⟨.inr ⟨rfl, h3⟩, hp⟩
      · exact rowLab_smallTwD (by omega)
  case E6 => exact rowLab_NE6 (.inl ⟨rfl, hp⟩)
  case E7 => exact rowLab_EE7 ⟨rfl, hp⟩
  case E8 => exact rowLab_EE8 ⟨rfl, hp⟩
  case F4 => exact rowLab_NF4 ⟨rfl, .inr hp⟩
  case twE6 => exact rowLab_ETwE6 ⟨rfl, hp⟩
  all_goals exact rowLab_smallTag (by decide)

theorem ggNSRowLab_of_halfSplit {p : ℕ} {lab : LargeEvenLabel} {c : Prop}
    (hlab : LargeEvenInLambda2 lab) (h : LargeEvenHalfSplit p lab c) : GGNSRowLab p lab := by
  rcases halfSplit_dvd_or h with hm | hp | h8 | h6
  · exact rowLab_of_sub hlab hm
  · exact rowLab_of_add hlab hp
  · exact rowLab_ZA8 h8
  · exact rowLab_ZE6 h6

end CFSG.StandardType

end
