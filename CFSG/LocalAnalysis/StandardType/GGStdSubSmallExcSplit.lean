module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeSp
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMore

public section

namespace CFSG.StandardType.SmallExc

open CFSG.Assembly

@[expose] def ExcFieldLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .E6 ∧ p ∣ 2 ^ lab.n - 1 ∧ p ≠ 3 ∧ p ∣ lab.n) ∨
    ((lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∧ p ∣ 2 ^ lab.n - 1 ∧ p ∣ lab.n)

@[expose] def ExcTwoThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∧ lab.n = 1 ∧ p = 3

theorem ggStdSubSmallInputOn_mono_split {S T : ℕ → LargeEvenLabel → Prop}
    (h : GGStdSubSmallInputOn T)
    (hST : ∀ p lab, p.Prime → LargeEvenInLambda2 lab → LargeEvenSplit p lab → S p lab →
      T p lab) :
    GGStdSubSmallInputOn S := by
  intro G _ _ p B Bs x L D J hcfg hM hsm
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨hperf, lab, hlab, hraw⟩ := hM
  exact h G p B Bs x L D J hcfg ⟨hperf, lab, hlab, largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, hS, hP⟩ => ⟨hs, hna, θ, hST p lab hp hlab hP.1 hS, hP⟩) hraw⟩ hsm

theorem hsRLabel_cases {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (hs : LargeEvenSplit p lab)
    (h : ((((GGStdSubSmallRest5Label p lab ∧ ¬ GGLinTwoLabel p lab) ∧
      ¬ GGStdSubSmallOrthLabel p lab) ∧ ¬ (GGUnitDvd63Label p lab ∧ 2 ≤ lab.n)) ∧
        ¬ GGSpTwoThreeLabel p lab) ∧ ¬ GGUnitDvd63Label p lab) :
    GGIOneExcSplitLabel p lab ∨ GGIOneMoreE6CoprimeLabel p lab ∨ GGIOneMoreE6ThreeLabel p lab ∨
      ExcFieldLabel p lab ∨ ExcTwoThreeLabel p lab ∨ GGIOneMoreTwE6Label p lab := by
  obtain ⟨⟨⟨⟨⟨⟨hR4, hU5⟩, hL2⟩, hO⟩, -⟩, hSp⟩, hU⟩ := h
  have hEFour (ht : lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4)
      (hq : p ∣ 2 ^ lab.n - 1 ∨ (lab.n = 1 ∧ p = 3)) :
      GGIOneExcSplitLabel p lab ∨ GGIOneMoreE6CoprimeLabel p lab ∨
        GGIOneMoreE6ThreeLabel p lab ∨ ExcFieldLabel p lab ∨ ExcTwoThreeLabel p lab ∨
          GGIOneMoreTwE6Label p lab := by
    rcases hq with hq | ⟨hn, hp3⟩
    · by_cases hpn : p ∣ lab.n
      · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨ht, hq, hpn⟩))))
      · exact Or.inl ⟨ht, hq, hpn⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr ht, hn, hp3⟩))))
  rcases ggStdSubSmallRest4Label_cases hp hlab hR4 hs with
    ⟨ht, hq, hl, hd⟩ | ⟨hp3, hn, ⟨ht, hl⟩ | ⟨ht, hl⟩⟩ | hD | hE6 | hE7 | hE8 | hF4 | hT
  ·
    have hUD : GGUnitDvdLabel p lab := ⟨ht, hl, hq, hd⟩
    have h53 : lab.rank = 5 ∧ p = 3 := not_not.mp fun h53 => hU5 ⟨hUD, h53⟩
    exact (hU ⟨hUD, h53⟩).elim
  · exact (hL2 ⟨ht, hl, hn, hp3⟩).elim
  · exact (hSp ⟨hp3, hn, ht⟩).elim
  · exact (hO hD).elim
  ·
    rcases (largeEvenSplit_E_iff (Or.inl hE6)).mp hs with hq | ⟨hn, hp3⟩
    · by_cases hp3 : p = 3
      · exact Or.inr (Or.inr (Or.inl ⟨hE6, hp3, hq⟩))
      · by_cases hpn : p ∣ lab.n
        · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨hE6, hq, hp3, hpn⟩))))
        · exact Or.inr (Or.inl ⟨hE6, hq, hp3, hpn⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl hE6, hn, hp3⟩))))
  · exact hEFour (Or.inl hE7) ((largeEvenSplit_E_iff (Or.inr (Or.inl hE7))).mp hs)
  · exact hEFour (Or.inr (Or.inl hE8)) ((largeEvenSplit_E_iff (Or.inr (Or.inr hE8))).mp hs)
  · exact hEFour (Or.inr (Or.inr hF4)) ((largeEvenSplit_F4_iff hF4).mp hs)
  ·
    have hq : p ∣ 2 ^ lab.n + 1 := by
      rcases hs with ⟨hu, -⟩ | ⟨-, -, hq⟩ | ⟨ht, -⟩ | ⟨hn, rfl⟩
      · rw [hT] at hu
        exact (hu : False).elim
      · exact hq
      · simp [hT] at ht
      · rw [hn]
        norm_num
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hT, hq⟩))))

theorem ggStdSubSmallInputOn_hsR_of_cases (h1 : GGStdSubSmallInputOn GGIOneExcSplitLabel)
    (h2 : GGStdSubSmallInputOn GGIOneMoreE6CoprimeLabel)
    (h3 : GGStdSubSmallInputOn GGIOneMoreE6ThreeLabel) (h4 : GGStdSubSmallInputOn ExcFieldLabel)
    (h5 : GGStdSubSmallInputOn ExcTwoThreeLabel)
    (h6 : GGStdSubSmallInputOn GGIOneMoreTwE6Label) :
    GGStdSubSmallInputOn fun p lab =>
      ((((GGStdSubSmallRest5Label p lab ∧ ¬ GGLinTwoLabel p lab) ∧
        ¬ GGStdSubSmallOrthLabel p lab) ∧ ¬ (GGUnitDvd63Label p lab ∧ 2 ≤ lab.n)) ∧
          ¬ GGSpTwoThreeLabel p lab) ∧ ¬ GGUnitDvd63Label p lab :=
  ggStdSubSmallInputOn_mono_split (h1.or (h2.or (h3.or (h4.or (h5.or h6)))))
    fun _ _ hp hlab hs h => hsRLabel_cases hp hlab hs h

end CFSG.StandardType.SmallExc

end
