module

public import CFSG.Quasithin.Vol2.Ch11SecO7a
public import CFSG.Quasithin.Vol2.Ch11SecO7l

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE.C10KH

open CFSG.Open CFSG.Blueprint

@[expose] def list3Orders : Finset ℕ :=
  {2520, 7560, 7800, 372000, 378000, 126000, 443520, 1330560, 10200960, 175560, 604800,
    86775571046077562880, 44352000, 145926144000}


variable {X : Type} [Group X]

theorem list3_cases (h : List11_1_1Three X) (hA : ¬ A36Case4 X) (hE : ¬ IsSL2pE X) :
    (∃ p, p.Prime ∧ 11 ≤ p ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ IsPSL 2 p 1 X) ∨
      Nat.card X ∈ list3Orders := by
  have hm : ∀ N, Nat.card X = N → N ∈ list3Orders → Nat.card X ∈ list3Orders :=
    fun N h1 h2 => h1 ▸ h2
  rcases h with h | h | ⟨p, hp, h5, h8, h⟩ | h | ⟨s, h | h⟩ | ⟨⟨e⟩⟩ | h | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ |
    ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | h | h
  · exact Or.inr (hm _ (card_of_isAlt7 h) (by simp [list3Orders]))
  · exact Or.inr (hm _ (card_of_isHatAlt7 h) (by simp [list3Orders]))
  · exact Or.inl ⟨p, hp, eleven_le_of_mod_five hp h5, h8, h⟩
  · exact Or.inr (hm 7800 (by rw [H13.NotLie.card_psl2 h]; norm_num) (by simp [list3Orders]))
  · cases s
    · exact Or.inr (hm _ (card_of_isSU35 h) (by simp [list3Orders]))
    · exact Or.inr (hm _ (card_of_isSL35 h) (by simp [list3Orders]))
  · cases s
    · exact Or.inr (hm _ (card_of_isPSU35 h) (by simp [list3Orders]))
    · exact Or.inr (hm _ (H13.NotLie.card_psl35 h) (by simp [list3Orders]))
  · exact Or.inr (hm _ ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M22)
      (by simp [list3Orders]))
  · exact Or.inr (hm 1330560 (by rw [SecA.C10KH.card_of_isHat h, show Nat.card
      (NativeSporadic.Carrier .M22) = 443520 from CFSG.Sporadic.Mathieu.card_M22])
      (by simp [list3Orders]))
  · exact Or.inr (hm _ ((Nat.card_congr e.toEquiv).trans card_nativeM23_1522)
      (by simp [list3Orders]))
  · exact Or.inr (hm _ ((Nat.card_congr (e.trans CFSG.Sporadic.J1.nativeEquiv).toEquiv).trans
      CFSG.Sporadic.J1.card_J) (by simp [list3Orders]))
  · exact Or.inr (hm _ ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J2.card_J2)
      (by simp [list3Orders]))
  · exact Or.inr (hm _ ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J4.card_J4)
      (by simp [list3Orders]))
  · exact Or.inr (hm _ ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.HS.card_HS)
      (by simp [list3Orders]))
  · exact Or.inr (hm _ ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Ru.card_Ru)
      (by simp [list3Orders]))
  · exact absurd h hA
  · exact absurd h hE

theorem list3_ge (h : List11_1_1Three X) (hA : ¬ A36Case4 X) (hE : ¬ IsSL2pE X) :
    Nat.card X = 660 ∨ 1080 < Nat.card X := by
  rcases list3_cases h hA hE with ⟨p, hp, hp11, -, hL⟩ | hm
  · have hN := card_mul_two_of_psl2 hp (by omega) hL
    by_cases h11 : p = 11
    · subst h11
      left
      norm_num at hN
      omega
    · right
      have h12 : p ≠ 12 := by
        rintro rfl
        norm_num at hp
      have := cube_sub_le (by norm_num : 1 ≤ 13) (show 13 ≤ p by omega)
      norm_num at this
      omega
  · right
    have : ∀ N ∈ list3Orders, 1080 < N := by decide
    exact this _ hm

theorem list3_three_dvd (h : List11_1_1Three X) (hA : ¬ A36Case4 X) (hE : ¬ IsSL2pE X) :
    3 ∣ Nat.card X := by
  rcases list3_cases h hA hE with ⟨p, hp, hp11, -, hL⟩ | hm
  · have hN := card_mul_two_of_psl2 hp (by omega) hL
    have h3 := (SecA.C10KH.three_dvd_psl2 hp hp11).1
    rwa [← Nat.eq_div_of_mul_eq_left (by norm_num) hN] at h3
  · have : ∀ N ∈ list3Orders, 3 ∣ N := by decide
    exact this _ hm

end CFSG.Quasithin.Vol2.Ch11.SecE.C10KH
