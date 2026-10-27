module

public import CFSG.Quasithin.EmptyFaithful.S152He6CaseB
public import CFSG.Quasithin.EmptyFaithful.S152He6AutEven
public import CFSG.Quasithin.EmptyFaithful.S152He6AutOdd

public section

namespace CFSG.Quasithin.He6

open scoped MatrixGroups

theorem autL2SylowInner_holds : AutL2SylowInner := by
  intro G _ hfam α ⟨S, hS⟩
  rcases hfam with ⟨f, -, hf2, ⟨e⟩⟩ | ⟨p, hp, hp5, ⟨e⟩⟩
  · have : Finite G := Finite.of_equiv _ e.toEquiv.symm
    exact Aut.autInner_of_equiv e
      (fun α' S' h => Aut.autInner_psl2_even hf2 α' S' h) α S hS
  · have : Fact p.Prime := ⟨hp⟩
    have : Finite G := Finite.of_equiv _ e.toEquiv.symm
    exact Aut.autInner_of_equiv e
      (fun α' S' h => Aut.autInner_psl2_prime hp5 α' S' h) α S hS

end CFSG.Quasithin.He6
