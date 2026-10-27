module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeOrthSp
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThree
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoTableB

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem GGBstarInputOn.mono {S T : ℕ → LargeEvenLabel → Prop} (hT : GGBstarInputOn T)
    (hST : ∀ p lab, LargeEvenInLambda2 lab → LargeEvenSplit p lab → S p lab → T p lab) :
    GGBstarInputOn S := by
  intro G _ _ p B x L hI hM
  obtain ⟨hperf, lab, hlab, hraw⟩ := hM
  exact hT G p B x L hI ⟨hperf, lab, hlab, largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ', hS, hP⟩ => ⟨hs, hna, θ', hST p lab hlab hP.1 hS, hP⟩) hraw⟩

theorem GGStdSubPreInputOn.mono {S T : ℕ → LargeEvenLabel → Prop} (hT : GGStdSubPreInputOn T)
    (hST : ∀ p lab, LargeEvenInLambda2 lab → LargeEvenSplit p lab → S p lab → T p lab) :
    GGStdSubPreInputOn S := by
  intro G _ _ p B x L hI hM
  obtain ⟨hperf, lab, hlab, hraw⟩ := hM
  exact hT G p B x L hI ⟨hperf, lab, hlab, largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ', hS, hP⟩ => ⟨hs, hna, θ', hST p lab hlab hP.1 hS, hP⟩) hraw⟩

theorem twoThree_of_linearRest {p : ℕ} {lab : LargeEvenLabel} (hsplit : LargeEvenSplit p lab)
    (hL : GGTableBLinearLabel lab) (hnp : ¬ GGTableBProvedLabel p lab) :
    GGTwoThreeLabel p lab ∨ GGSpTwoThreeLabel p lab := by
  obtain ⟨t, l, n⟩ := lab
  rcases hsplit with ⟨-, hpn⟩ | ⟨hu, -, -⟩ | ⟨ht, -⟩ | ⟨hn, hp⟩
  · exfalso
    apply hnp
    rcases hL with h | h | h | ⟨h, hl⟩ <;> dsimp only at h <;> subst h
    · by_cases hd : p ∣ l + 1
      · exact Or.inl (Or.inr ⟨rfl, hpn, hd⟩)
      · exact Or.inl (Or.inl (Or.inl ⟨rfl, hpn, hd⟩))
    · exact Or.inr ⟨Or.inl rfl, hpn⟩
    · exact Or.inr ⟨Or.inr rfl, hpn⟩
    · exact Or.inl (Or.inl (Or.inr (Or.inl ⟨rfl, hl, hpn⟩)))
  · exfalso
    rcases hL with h | h | h | ⟨h, -⟩ <;> dsimp only at h <;> subst h <;>
      simp [LargeEvenUntwisted] at hu
  · exfalso
    rcases hL with h | h | h | ⟨h, -⟩ <;> dsimp only at h <;> subst h <;> simp at ht
  · rcases hL with h | h | h | ⟨h, hl⟩
    · exact Or.inl ⟨hp, hn, Or.inl h⟩
    · exact Or.inr ⟨hp, hn, Or.inl h⟩
    · exact Or.inr ⟨hp, hn, Or.inr h⟩
    · exact Or.inl ⟨hp, hn, Or.inr ⟨h, hl⟩⟩

theorem ggBstarInputOn_linearRest : GGBstarInputOn (GGTableBRest GGTableBLinearLabel) :=
  (ggBstarInputOn_twoThree.or ggBstarInputOn_spTwoThree).mono fun _ _ _ hsplit h =>
    twoThree_of_linearRest hsplit h.1 h.2

theorem ggStdSubPreInputOn_linearRest : GGStdSubPreInputOn (GGTableBRestB GGTableBLinearLabel) :=
  (ggStdSubPreInputOn_twoThree.or ggStdSubPreInputOn_spTwoThree).mono fun _ _ _ hsplit h =>
    twoThree_of_linearRest hsplit h.1 fun hp => h.2 (Or.inl hp)

end CFSG.StandardType
