module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplit

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGNbrNonSplitVacLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twB2 ∨ lab.tag = .twF4 ∨ lab.tag = .twF4der ∨ lab.tag = .triD4 ∨
    lab.tag = .B2der ∨ lab.tag = .G2der ∨ ((lab.tag = .twA ∨ lab.tag = .twD) ∧ lab.rank = 2) ∨
    (lab.tag = .twD ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .A ∧ lab.rank ≤ 4) ∨
    (lab.tag = .D ∧ lab.rank = 3) ∨ ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 2)

@[expose] def GGNbrNonSplitUnitaryLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ((lab.tag = .twA ∧ 3 ≤ lab.rank ∧ ¬ (lab.rank = 5 ∧ p = 3)) ∨
      (lab.tag = .twD ∧ lab.rank = 3)) ∧ p ∣ 2 ^ lab.n + 1

@[expose] def GGNbrNonSplitUnitaryHypLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ lab.rank = 5 ∧ p ∣ 2 ^ lab.n - 1

@[expose] def GGNbrNonSplitOrthLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .D ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1) ∨
    (lab.tag = .twD ∧ 4 ≤ lab.rank ∧ (p ∣ 2 ^ lab.n + 1 ∨ p ∣ 2 ^ lab.n - 1))

@[expose] def GGNbrNonSplitSympLinLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ((lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1) ∨
    (lab.tag = .A ∧ 5 ≤ lab.rank ∧ lab.n = 1 ∧ p = 3) ∨
    (lab.tag = .A ∧ lab.rank = 5 ∧ lab.n = 2 ∧ p = 5)

@[expose] def GGNbrNonSplitExcPlusLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ((lab.tag = .F4 ∧ p ≠ 3) ∨ lab.tag = .E7 ∨ lab.tag = .E8) ∧ p ∣ 2 ^ lab.n + 1

@[expose] def GGNbrNonSplitE6TwoLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E6 ∧ lab.n = 1 ∧ p = 3

@[expose] def GGNbrNonSplitTwE6Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twE6 ∧ ((p ≠ 3 ∧ p ∣ 2 ^ lab.n + 1) ∨ p ∣ 2 ^ lab.n - 1)

theorem ggNbrNonSplitLabel_cover {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGNbrNonSplitLabel p lab)
    (hF4 : ¬ GGF4ThreeLabel p lab) (hU6 : ¬ GGUSixThreeLabel p lab) :
    GGNbrNonSplitVacLabel p lab ∨ GGNbrNonSplitUnitaryLabel p lab ∨
      GGNbrNonSplitUnitaryHypLabel p lab ∨ GGNbrNonSplitOrthLabel p lab ∨
      GGNbrNonSplitSympLinLabel p lab ∨ GGNbrNonSplitExcPlusLabel p lab ∨
      GGNbrNonSplitE6TwoLabel p lab ∨ GGNbrNonSplitTwE6Label p lab := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨hHS, hq, hns, hbad⟩ := h
  obtain ⟨hn1, hl⟩ := hlab
  simp only [GGF4ThreeLabel, GGUSixThreeLabel, GGTwE6BadLabel, GGNbrSplitLabel,
      LargeEvenHalfSplit,
    LargeEvenSplit] at hF4 hU6 hbad hns hHS
  dsimp only at hn1 hl hq hns hbad hF4 hU6 hHS
  have hsub : LargeEvenUntwisted t → ¬ p ∣ 2 ^ n - 1 := fun hu hd => by
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain rfl : n = 1 := by omega
      exact hp.ne_one (Nat.dvd_one.mp (by simpa using hd))
    · exact hns ⟨hu, h2, hd⟩
  rcases hHS with (⟨hu, hd⟩ | ⟨hu, ht, hd⟩ | ⟨ht, hd⟩ | ⟨rfl, rfl⟩) | ⟨ht, hd⟩ | ⟨ht, hd⟩ |
    ⟨ht, hr, hn, -, hp5⟩ | ⟨ht, -, hn, hp7⟩ | ⟨ht, hn, hp7⟩
  · exact absurd hd (hsub hu)
  ·
    cases t with
    | twA =>
      dsimp only at hl
      rcases Nat.lt_or_ge r 3 with hr | hr
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨Or.inl rfl, (by omega : r = 2)⟩)))))))
      · exact Or.inr (Or.inl ⟨Or.inl ⟨rfl, hr, fun h53 => hU6 ⟨rfl, h53.1, h53.2, h53.2 ▸ hd⟩⟩, hd⟩)
    | twD =>
      dsimp only at hl
      rcases Nat.lt_or_ge r 4 with hr | hr
      · rcases Nat.lt_or_ge r 3 with hr' | hr'
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨Or.inr rfl, (by omega : r = 2)⟩)))))))
        · exact Or.inr (Or.inl ⟨Or.inr ⟨rfl, (by omega : r = 3)⟩, hd⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨rfl, hr, Or.inl hd⟩))))
    | twE6 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl, Or.inl
        ⟨fun hp3 => hbad ⟨rfl, hp3, hp3 ▸ hd⟩, hd⟩⟩)))))))
    | twB2 => exact Or.inl (Or.inl rfl)
    | twF4 => exact Or.inl (Or.inr (Or.inl rfl))
    | twF4der => exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
    | triD4 => exact absurd rfl ht
    | _ => exact absurd trivial hu
  ·
    rcases ht with rfl | rfl
    · dsimp only at hl
      rcases Nat.lt_or_ge r 4 with hr | hr
      · rcases Nat.lt_or_ge r 3 with hr' | hr'
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨Or.inr rfl, (by omega : r = 2)⟩)))))))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨rfl, (by omega : r = 3), hd⟩))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨rfl, hr, Or.inr hd⟩))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  ·
    have hd : (3 : ℕ) ∣ 2 ^ 1 + 1 := by norm_num
    cases t with
    | A =>
      dsimp only at hl
      rcases Nat.lt_or_ge r 5 with hr | hr
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨rfl, (by omega : r ≤ 4)⟩)))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl ⟨rfl, hr, rfl, rfl⟩))))))
    | twA =>
      dsimp only at hl
      by_cases hr5 : r = 5
      · exact absurd ⟨rfl, hr5, rfl, hd⟩ hU6
      · exact Or.inr (Or.inl ⟨Or.inl ⟨rfl, (by omega : 3 ≤ r), fun h53 => hr5 h53.1⟩, hd⟩)
    | B =>
      dsimp only at hl
      rcases Nat.lt_or_ge r 3 with hr | hr
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (⟨Or.inl rfl, (by omega : r = 2)⟩)))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨Or.inl rfl, hr, hd⟩)))))
    | C =>
      dsimp only at hl
      rcases Nat.lt_or_ge r 3 with hr | hr
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (⟨Or.inr rfl, (by omega : r = 2)⟩)))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨Or.inr rfl, hr, hd⟩)))))
    | D =>
      dsimp only at hl
      rcases Nat.lt_or_ge r 4 with hr | hr
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨rfl, (by omega : r = 3)⟩))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, hr, hd⟩))))
    | twD =>
      dsimp only at hl
      rcases Nat.lt_or_ge r 4 with hr | hr
      · rcases Nat.lt_or_ge r 3 with hr' | hr'
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨Or.inr rfl, (by omega : r = 2)⟩)))))))
        · exact Or.inr (Or.inl ⟨Or.inr ⟨rfl, (by omega : r = 3)⟩, hd⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨rfl, hr, Or.inl hd⟩))))
    | E6 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))))
    | E7 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), hd⟩)))))
    | E8 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inr rfl), hd⟩)))))
    | F4 => exact absurd ⟨rfl, rfl, hd⟩ hF4
    | twE6 => exact absurd ⟨rfl, rfl, hd⟩ hbad
    | triD4 => exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | G2 =>
      dsimp only at hl
      omega
    | twB2 => exact Or.inl (Or.inl rfl)
    | twF4 => exact Or.inl (Or.inr (Or.inl rfl))
    | B2der => exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | G2der => exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    | twF4der => exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
  ·
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · dsimp only at hl
      rcases Nat.lt_or_ge r 3 with hr | hr
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (⟨Or.inl rfl, (by omega : r = 2)⟩)))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨Or.inl rfl, hr, hd⟩)))))
    · dsimp only at hl
      rcases Nat.lt_or_ge r 4 with hr | hr
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨rfl, (by omega : r = 3)⟩))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, hr, hd⟩))))
    · by_cases hp3 : p = 3
      · exact absurd ⟨rfl, hp3, hp3 ▸ hd⟩ hF4
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl ⟨rfl, hp3⟩, hd⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), hd⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inr rfl), hd⟩)))))
  ·
    rcases ht with ⟨rfl, rfl⟩ | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hd⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl, Or.inr hd⟩)))))))
  ·
    subst ht hr hn hp5
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩))))))
  ·
    subst hn hp7
    norm_num at hq
  ·
    subst hn hp7
    norm_num at hq

theorem ggNbrTableBWeylNonSplitOn_of_families
    (hV : GGNbrTableBWeylNonSplitOn GGNbrNonSplitVacLabel)
    (hC1 : GGNbrTableBWeylNonSplitOn GGNbrNonSplitUnitaryLabel)
    (hC2 : GGNbrTableBWeylNonSplitOn GGNbrNonSplitUnitaryHypLabel)
    (hC3 : GGNbrTableBWeylNonSplitOn GGNbrNonSplitOrthLabel)
    (hC4 : GGNbrTableBWeylNonSplitOn GGNbrNonSplitSympLinLabel)
    (hE3 : GGNbrTableBWeylNonSplitOn GGNbrNonSplitExcPlusLabel)
    (hE4 : GGNbrTableBWeylNonSplitOn GGNbrNonSplitE6TwoLabel)
    (hE5 : GGNbrTableBWeylNonSplitOn GGNbrNonSplitTwE6Label) :
    GGNbrTableBWeylNonSplitOn fun p lab => ¬ GGF4ThreeLabel p lab ∧ ¬ GGUSixThreeLabel p lab :=
        by
  intro p hp hp2 lab hlab hU hns
  rcases ggNbrNonSplitLabel_cover hp hp2 hlab hns hU.1 hU.2 with h | h | h | h | h | h | h | h
  · exact hV p hp hp2 lab hlab h hns
  · exact hC1 p hp hp2 lab hlab h hns
  · exact hC2 p hp hp2 lab hlab h hns
  · exact hC3 p hp hp2 lab hlab h hns
  · exact hC4 p hp hp2 lab hlab h hns
  · exact hE3 p hp hp2 lab hlab h hns
  · exact hE4 p hp hp2 lab hlab h hns
  · exact hE5 p hp hp2 lab hlab h hns

end CFSG.StandardType

end
