module

public import CFSG.Quasithin.EmptyFaithful.E22PRes

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open

variable {Γ : Type} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem typeOneRes_or_lieCases {H T M K : Subgroup Γ} (hc : E2.E22CasesNoN H T M K) :
    E2.E22N.TypeOneRes ↥(E2.star M H K) ∨ E2.E22LieCases H T M K := by
  dsimp only [E2.E22CasesNoN] at hc
  dsimp only [E2.E22LieCases]
  rcases hc with ⟨hJ, t, ht, hne, hM, ⟨n, hn2, hty, hB⟩ | ⟨p, hp, hp8, hK, -, -⟩⟩ |
      ⟨hTK, hJ, ⟨n, hBen, hB⟩ | ⟨n, hn1, hK, hD, hB⟩ | ⟨p, e, hp, hp3, he, hpe8, hK, -, -⟩ |
        ⟨p, hp, hp2, hK, -⟩⟩
  · exact Or.inr (Or.inl ⟨hJ, t, ht, hne, hM, n, hn2, hty, hB⟩)
  · left
    have h2 := hp.two_le
    exact Or.inr (Or.inr (Or.inl ⟨p, 1, hp, by omega, Or.inl rfl, by simpa using hp8, hK⟩))
  · exact Or.inr (Or.inr ⟨hTK, hJ, Or.inl ⟨n, hBen, hB⟩⟩)
  · rcases Nat.lt_or_ge n 2 with hlt | hge
    · left
      obtain rfl : n = 1 := by omega
      rcases hK with hK | hK
      · exact Or.inl hK
      · exact Or.inr (Or.inl (by simpa [E2.IsSp4Prime] using hK))
    · right
      refine Or.inr ⟨hTK, hJ, Or.inr ⟨n, hge, ?_, hD, hB⟩⟩
      rcases hK with hK | hK
      · exact Or.inl hK
      · right
        rw [E2.IsSp4Prime] at hK
        split_ifs at hK with h1
        · omega
        · exact hK
  · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨p, e, hp, hp3, he, hpe8, hK⟩)))
  · left
    rcases hK with ⟨h4, hK⟩ | ⟨h4, hK, -⟩
    · exact Or.inr (Or.inr (Or.inr ⟨false, p, hp, hp2, by simp, fun _ => h4, hK⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨true, p, hp, hp2, fun _ => h4, by simp, hK⟩))

end CFSG.Quasithin.Vol2.Ch11.SecB
