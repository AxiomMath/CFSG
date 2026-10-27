module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightCaseOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightCaseThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G]

theorem odd_of_isSz {X : Type} [Group X] {a : ℕ} (h : IsSz X a) : Odd a := by
  obtain ⟨-, -, -, -, hodd, -⟩ := h.admissible
  exact hodd

theorem s23_8_of (D : Data G) (Ch : Choice2011 G) {W : ∀ (X : Type) [Group X], MulAut X → Prop}
    (hE : UC22P20gExcFacts) (h207 : S20_7 D) (h52 : S23_5_2 D Ch) (h53 : S23_5_3 D Ch)
    (h54 : S23_5_4 D Ch) (h215 : S21_5 D Ch) (h218 : S21_8N D Ch) (h219 : S21_9NFull D Ch)
    (h2111 : S21_11N D Ch W) (h2115 : S21_15N D Ch) (h2116 : S21_16 D Ch) (h2117 : S21_17 D Ch)
    (h2119 : S21_19 D Ch) (h846 : F08.R846 D) (h8107 : F08.R8107 D) (hWSp : KWSp4 W)
    (hWU : KWU3 W) (hBor : KBor) (hCent : KCentL2)
    (hCen : UCK.U3Center) (hsig : D.sig.Nonempty) (hSz : S23_8_Sz D Ch) : S23_8 D Ch := by
  intro h1930 c K hK
  have hI : ∀ K' ∈ calC D.M, ∀ a : ℕ, ¬ (Odd a ∧ IsSp4 (Bar2 K') a) ∧ ¬ IsSU3 (Bar2 K') a :=
    fun K' hK' a =>
      ⟨fun h => c.false_of_isSp4 hE h207 h52 h53 h54 h215 h218 h2111 hWSp hBor h1930 hK' h.1 h.2,
        fun h => c.false_of_isSU3 hE h207 h52 h53 h54 h215 h219 h2117 h2111 h846 hWU hBor hCen h1930
          hK' h⟩
  have hIII : ∀ {a : ℕ}, IsL2 (Bar2 K) a → (K.subgroupOf D.M).Normal ∧
      (Odd a ∨ barImage D.M K = Opp 3 (CFSG.layer (Bar2 D.M))) := fun hL2 =>
    c.normal_of_isL2 hE h207 h52 h53 h54 h215 h2115 h2116 h8107 hBor hCent hsig h1930 hI hK hL2
  have hII : IsJ1 (Bar2 K) ∨ (∃ p : ℕ, p.Prime ∧ 5 < p ∧ IsL2Odd (Bar2 K) p) →
      (K.subgroupOf D.M).Normal ∧ barImage D.M K = Opp 3 (CFSG.layer (Bar2 D.M)) :=
    c.normal_and_barImage_of_isJ1_or_isL2Odd hE h207 h52 h53 h54 h215 h2116 h2117 h2119 h1930 hI
      hK
  rcases h2116 h1930 c.toCtx21 K hK with ⟨a, ha, hSp⟩ | ⟨a, hSU⟩ | ⟨a, hL2⟩ | ⟨a, hSz'⟩ |
      ⟨p, hp, hp2, hL2O⟩ | hJ
  · exact ((hI K hK a).1 ⟨ha, hSp⟩).elim
  · exact ((hI K hK a).2 hSU).elim
  · obtain ⟨hN, hodd | hbar⟩ := hIII hL2
    · exact ⟨hN, Or.inl ⟨a, hodd, Or.inl hL2⟩⟩
    · rcases Nat.even_or_odd a with ⟨k, rfl⟩ | hodd
      · exact ⟨hN, Or.inr ⟨Or.inr (Or.inr ⟨k, by rwa [← two_mul] at hL2⟩), hbar⟩⟩
      · exact ⟨hN, Or.inl ⟨a, hodd, Or.inl hL2⟩⟩
  · exact ⟨hSz h1930 c K hK a hSz', Or.inl ⟨a, odd_of_isSz hSz', Or.inr hSz'⟩⟩
  · have hp3 : p ≠ 3 := ne_three_of_isL2Odd hL2O
    by_cases hp5 : p = 5
    · subst hp5
      obtain ⟨hN, hodd | hbar⟩ := hIII (PartTwo.s13_isL2_two_of_isL2Odd_five hL2O)
      · exact absurd hodd (by decide : ¬ Odd 2)
      · exact ⟨hN, Or.inr ⟨Or.inl ⟨5, hp, hp2, hL2O⟩, hbar⟩⟩
    · have hp4 : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
      have h5 : 5 < p := by have := hp.two_le; omega
      obtain ⟨hN, hbar⟩ := hII (Or.inr ⟨p, hp, h5, hL2O⟩)
      exact ⟨hN, Or.inr ⟨Or.inl ⟨p, hp, hp2, hL2O⟩, hbar⟩⟩
  · obtain ⟨hN, hbar⟩ := hII (Or.inl hJ)
    exact ⟨hN, Or.inr ⟨Or.inr (Or.inl hJ), hbar⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
