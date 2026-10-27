module

public import CFSG.Quasithin.EmptyFaithful.S151S9F
public import CFSG.Quasithin.EmptyFaithful.S151S9G
public import CFSG.Quasithin.EmptyFaithful.S151S6B
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def SimpleTypeMaxRest15120 (Q : Type) [Group Q] : Prop :=
  (IsPSU 3 3 1 Q ∨ Is3D4 2 1 Q) ∨
    (IsSporadic .M11 Q ∨ IsSporadic .M12 Q ∨ IsSporadic .J2 Q ∨ IsSporadic .HS Q ∨
      IsSporadic .He Q)

@[expose] def Input15120CentMaxRest : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (P : Subgroup Q), IsPGroup 2 ↥P → ¬ 2 ∣ P.index →
    SimpleTypeMaxRest15120 Q → ∀ W : Subgroup Q, W ≤ centerOf P → W ≠ ⊥ →
      IsMaxSubgroupIn ⊤ (Subgroup.centralizer (W : Set Q))

theorem input15120CentMaxSimple_of_rest
    (hR : Input15120CentMaxRest) : Input15120CentMaxSimple := by
  intro Q _ _ P hP2 hPi hT W hW hW0
  rcases hT with (h | h | h) | ((h | h | h | h | h) | h)
  · exact hR Q P hP2 hPi (Or.inl (Or.inl h)) W hW hW0
  · obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv Q 2 1 h
    exact (centMaxProp_titsD.of_mulEquiv e.symm) P hP2 hPi W hW hW0
  · exact hR Q P hP2 hPi (Or.inl (Or.inr h)) W hW hW0
  · exact hR Q P hP2 hPi (Or.inr (Or.inl h)) W hW hW0
  · exact hR Q P hP2 hPi (Or.inr (Or.inr (Or.inl h))) W hW hW0
  · exact hR Q P hP2 hPi (Or.inr (Or.inr (Or.inr (Or.inl h)))) W hW hW0
  · exact hR Q P hP2 hPi (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) W hW hW0
  · exact hR Q P hP2 hPi (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))) W hW hW0
  · obtain ⟨e⟩ := h
    exact (centMaxProp_ruP.of_mulEquiv (e.trans CFSG.Sporadic.RuSchreier.ruEquivP).symm) P hP2 hPi
      W hW hW0

end CFSG.Quasithin
