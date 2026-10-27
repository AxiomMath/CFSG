module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54ThmA
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporGen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem asch80ThmA54Case_spor_of_gen (h : ∀ s, s ≠ .Th → Asch54SporGenAt s)
    (hTh : Asch54SporThGen) : Asch80ThmA54Case fun X _ => CFSG.Models.SporadicRep X :=
  asch80ThmA54Case_of_forall fun Q _ _ L T _ hLn _ _ hC hP _ hT => by
    obtain ⟨s, hs⟩ := hP
    by_cases hsTh : s = .Th
    · subst hsTh
      obtain ⟨h1, h2⟩ := hTh Q L T hLn hs hC hT
      exact Or.inr ⟨3, Nat.prime_three, by norm_num, h1, h2⟩
    · exact Or.inl (h s hsTh Q L T hLn hs hC hT)

end CFSG.LocalAnalysis.WeakClosure81

end
