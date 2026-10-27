module

public import CFSG.Sporadic.Fi23.Fischer
public import CFSG.Fischer.OpenTranslation

public section

namespace CFSG.Sporadic.Fi23

open CFSG.Open CFSG.Blueprint.Fischer CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem centerlessPair_open : fischerEUIsCenterlessPair D23 :=
  ⟨((CFSG.Fischer.pair_iff D23).1 pair_J).2, center_J, isSimpleGroup_commutator_J⟩

theorem centerlessF22_of_equiv
    {Q : Type} [Group Q] (φ : ↥Fi22.J ≃* Q) :
    ∃ D' : Set Q, fischerEUIsCenterlessPair D' ∧ fischerEUTypeF22 D' := by
  obtain ⟨hZ, hS, hT, -, -⟩ :=
    @Fi22.ExistenceF22.congr (↥Fi22.J) Q inferInstance inferInstance Fi22.D Fi22.existence_J φ
  exact ⟨φ '' Fi22.D, ⟨((CFSG.Fischer.pair_iff _).1 hT.1).2, hZ, hS⟩, F22.typeF22_open hT⟩

theorem localStructure_open
    {x : J} (hx : x ∈ D23) : fischerEULocalStructure 23 x := by
  obtain ⟨-, h1, -⟩ := localStructureAt_of_mem hx
  obtain ⟨hc, hz, -, ⟨iso⟩⟩ := h1 rfl
  exact ⟨fun h => absurd h (by decide), fun _ => ⟨⟨hc, hz⟩,
    centerlessF22_of_equiv (iso.trans Fi22.fi22EquivJ).symm⟩, fun h => absurd h (by decide)⟩

theorem open_existence_23 :
    ∃ (G : Type) (_ : Group G) (_ : Finite G) (D' : Set G),
      fischerEUIsCenterlessPair D' ∧ fischerEUType 23 D' ∧
        (∀ D'' : Set G, fischerEUIsPair D'' → D'' = D') ∧
        ∀ d ∈ D', fischerEULocalStructure 23 d :=
  ⟨J, inferInstance, inferInstance, D23, centerlessPair_open,
    Or.inr (Or.inl ⟨rfl, F23.typeF23_open f23_J⟩),
    fun D'' hD'' => pair_eq_D23 D'' ((CFSG.Fischer.pair_iff D'').2 ⟨inferInstance, hD''⟩),
    fun _ hx => localStructure_open hx⟩

end CFSG.Sporadic.Fi23
