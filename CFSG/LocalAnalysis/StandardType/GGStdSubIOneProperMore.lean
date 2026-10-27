module

public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreField
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreE6Two

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGIOneMoreOrthPlusEvenLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .D ∧ 4 ≤ lab.rank ∧ Even lab.rank ∧ lab.n = 1 ∧ p = 3

@[expose] def GGIOneMoreOrthMinusOddLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twD ∧ 5 ≤ lab.rank ∧ Odd lab.rank ∧ p ∣ 2 ^ lab.n + 1

@[expose] def GGIOneMoreE6ThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E6 ∧ p = 3 ∧ p ∣ 2 ^ lab.n - 1

@[expose] def GGIOneMoreExcTwoLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∧ lab.n = 1 ∧ p = 3

@[expose] def GGIOneProperRestTwoLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGIOneMoreUnitaryLabel p lab ∨ GGIOneMoreTwDThreeLabel p lab ∨ GGIOneMoreSpTwoLabel p lab ∨
    GGIOneMoreOrthPlusEvenLabel p lab ∨ GGIOneMoreOrthMinusOddLabel p lab ∨
      GGIOneMoreExcTwoLabel p lab ∨ GGIOneMoreTwE6Label p lab ∨ GGIOneMoreE6ThreeLabel p lab

@[expose] def GGIOneProperRestFieldLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGIOneProperRestTwoLabel p lab ∨ GGIOneMoreFieldLabel p lab

theorem ggIOneProperRestLabel_cover {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime) (hp2 : p ≠ 2)
    (hlab : LargeEvenInLambda2 lab) (hs : LargeEvenSplit p lab) (h : GGIOneProperRestLabel p lab) :
    GGIOneMoreTypeACoprimeLabel p lab ∨ GGIOneMoreOrthEqLabel p lab ∨
      GGIOneMoreE6CoprimeLabel p lab ∨ GGIOneMoreE6TwoLabel p lab ∨
        GGIOneProperRestFieldLabel p lab := by
  rcases (ggIOneProperRestLabel_iff hp hp2 hlab hs).mp h with
    ⟨ht, hpn, hpl⟩ | hU | hS | ⟨ht, hl, hn, hp3⟩ | hT | ⟨ht, hl, hpn⟩ | ⟨ht, hE⟩ |
      ⟨ht, hE⟩ | hE6
  · by_cases hpn' : p ∣ lab.n
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, hpn, hpl, hpn'⟩)))))
    · exact Or.inl ⟨ht, hpn, hpl, hpn'⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl hU)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl hS)))))))
  · rcases Nat.even_or_odd lab.rank with he | ho
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨ht, hl, he, hn, hp3⟩))))))))
    · have hl5 : 5 ≤ lab.rank := by
        obtain ⟨k, hk⟩ := ho
        omega
      exact Or.inr (Or.inl (Or.inr ⟨ht, hl5, ho, hn, hp3⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl hT))))))
  · rcases Nat.even_or_odd lab.rank with he | ho
    · by_cases hpn' : p ∣ lab.n
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨ht, hl, he, hpn, hpn'⟩))))))
      · exact Or.inr (Or.inl (Or.inl ⟨ht, hl, he, hpn, hpn'⟩))
    · have hl5 : 5 ≤ lab.rank := by
        obtain ⟨k, hk⟩ := ho
        omega
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨ht, hl5, ho, hpn⟩)))))))))
  · rcases hE with hpn | ⟨hn, hp3⟩
    · by_cases hp3 : p = 3
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr ⟨ht, hp3, hpn⟩)))))))))))
      · by_cases hpn' : p ∣ lab.n
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨ht, hpn, hp3, hpn'⟩)))))))
        · exact Or.inr (Or.inr (Or.inl ⟨ht, hpn, hp3, hpn'⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, hn, hp3⟩)))
  · rcases hE with ⟨hpn, hpn'⟩ | ⟨hn, hp3⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨ht, hpn, hpn'⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨ht, hn, hp3⟩))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl hE6)))))))))))

end CFSG.StandardType
