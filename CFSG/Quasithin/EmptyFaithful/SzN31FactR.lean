module

public import CFSG.Quasithin.EmptyFaithful.SzN31FactRC
public import CFSG.Quasithin.EmptyFaithful.SzN31FactRStmt

public section

namespace CFSG.Quasithin.SzN31

theorem factR : FactRStmt := by
  intro p hp hp2 Q _ _ hQ hrank Bh _ _ act hB
  obtain ⟨N, hNn, hNi, hNc, hNC⟩ :=
    exists_selfCentralizing_normal_abelian_invariant hp hp2 hQ act hB
  exact card_le_four_of_selfCentralizing hp hp2 hQ hrank act hB hNn hNi hNc hNC

end CFSG.Quasithin.SzN31
