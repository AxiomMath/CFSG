module

public import CFSG.Quasithin.Vol2.Ch11SecEFacts6
public import CFSG.Quasithin.Vol2.Ch11SecEFacts8
public import CFSG.Quasithin.Vol2.Ch11SecAKE12
public import CFSG.Quasithin.Vol2.Ch11SecAKE14

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint

section Two


theorem list11_1_1TwoQuasisimpleFact_holds : List11_1_1TwoQuasisimpleFact :=
  fun X _ _ n hn h => (SecA.factList2Table_holds X n hn h).1

end Two

theorem eleven_le_of_mod_five {p : ℕ} (hp : p.Prime) (h5 : p % 5 = 1 ∨ p % 5 = 4) : 11 ≤ p := by
  by_contra h
  interval_cases p <;> simp_all <;> norm_num at hp

section Three


theorem list11_1_1ThreeQuasisimpleFact_holds : List11_1_1ThreeQuasisimpleFact := by
  intro X _ _ h hA hE
  obtain ⟨h1, h2⟩ := SecA.factList3Table_holds
  rcases h with h | h | ⟨p, hp, h5, -, h⟩ | h | ⟨s, h | h⟩ | h | h | h | h | h | h | h | h | h | h
  · exact (h1 X (Or.inl h)).1
  · exact (h1 X (Or.inr (Or.inl h))).1
  · exact (h2 X (Or.inl ⟨p, hp, eleven_le_of_mod_five hp h5, h⟩)).1
  · exact (h2 X (Or.inr (Or.inl h))).1
  · cases s
    · exact (h1 X (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl h))))))))))).1
    · exact (h2 X (Or.inr (Or.inr (Or.inl h)))).1
  · cases s
    · exact (h1 X (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr h))))))))))).1
    · exact (h2 X (Or.inr (Or.inr (Or.inr (Or.inl h))))).1
  · exact (h1 X (Or.inr (Or.inr (Or.inl h)))).1
  · exact (h1 X (Or.inr (Or.inr (Or.inr (Or.inl h))))).1
  · exact (h1 X (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))).1
  · exact (h2 X (Or.inr (Or.inr (Or.inr (Or.inr h))))).1
  · exact (h1 X (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))).1
  · exact (h1 X (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))).1
  · exact (h1 X (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))).1
  · exact (h1 X (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h)))))))))).1
  · exact absurd h hA
  · exact absurd h hE

end Three

end CFSG.Quasithin.Vol2.Ch11.SecE
