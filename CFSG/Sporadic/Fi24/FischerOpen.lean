module

public import CFSG.Sporadic.Fi24.Complete
public import CFSG.Fischer.OpenTranslationHigh

public section

namespace CFSG.Sporadic.Fi24

open CFSG.Open CFSG.Blueprint.Fischer CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem centerlessPair_open :
    fischerEUIsCenterlessPair D24 :=
  ⟨((CFSG.Fischer.pair_iff D24).1 pair_R).2, center_R, isSimpleGroup_commutator_R⟩

theorem centerlessF23_of_equiv
    {Q : Type} [Group Q] (φ : ↥Fi23.J ≃* Q) :
    ∃ D' : Set Q, fischerEUIsCenterlessPair D' ∧ fischerEUTypeF23 D' := by
  obtain ⟨hZ, hS, hT, -, -⟩ :=
    @Fi23.ExistenceF23.congr (↥Fi23.J) Q inferInstance inferInstance Fi23.D23 Fi23.existence_J φ
  exact ⟨φ '' Fi23.D23, ⟨((CFSG.Fischer.pair_iff _).1 hT.1).2, hZ, hS⟩, F23.typeF23_open hT⟩

theorem localStructure_open
    {x : R} (hx : x ∈ D24) : fischerEULocalStructure 24 x := by
  obtain ⟨-, -, h2⟩ := localStructureAt_of_mem hx
  obtain ⟨L, ⟨iso⟩, hC, hinf, -⟩ := h2 rfl
  refine ⟨fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ =>
    ⟨L, ?_, ?_, ?_, centerlessF23_of_equiv (Fi23.fi23EquivJ.symm.trans iso.symm)⟩⟩
  · rw [hC]
    exact le_sup_right
  · rw [inf_comm]
    exact hinf
  · rw [sup_comm, hC]

theorem open_existence_24
    (hPF : PolarFacts) :
    ∃ (G : Type) (_ : Group G) (_ : Finite G) (D' : Set G),
      fischerEUIsCenterlessPair D' ∧ fischerEUType 24 D' ∧
        (∀ D'' : Set G, fischerEUIsPair D'' → D'' = D') ∧
        ∀ d ∈ D', fischerEULocalStructure 24 d :=
  ⟨R, inferInstance, pair_R.1, D24, centerlessPair_open,
    Or.inr (Or.inr ⟨rfl, F24.typeF24_open f24_R⟩),
    fun D'' hD'' => pair_eq_D24 hPF D'' ((CFSG.Fischer.pair_iff D'').2 ⟨pair_R.1, hD''⟩),
    fun _ hx => localStructure_open hx⟩

theorem open_uniqueness_24
    (hPF : PolarFacts) (hHF : HyperovalFacts) (hFF : Fi22Facts)
    {tr cs : Set (Set Fi23.D23)} {r : tr} (hTF : Fi23Facts tr cs r)
    (G H : Type) [Group G] [Group H] [Finite G] [Finite H] (D : Set G) (E : Set H)
    (hD : fischerEUIsCenterlessPair D) (hDT : fischerEUTypeF24 D)
    (hE : fischerEUIsCenterlessPair E) (hET : fischerEUTypeF24 E) :
    ∃ φ : G ≃* H, φ '' D = E := by
  have hPD : Pair G D := (CFSG.Fischer.pair_iff D).2 ⟨inferInstance, hD.1⟩
  have hPE : Pair H E := (CFSG.Fischer.pair_iff E).2 ⟨inferInstance, hE.1⟩
  exact F24.exists_mulEquiv hPF hHF hFF hTF (F24_of_typeF24_open hPD hDT)
    (F24_of_typeF24_open hPE hET) hD.2.1 hE.2.1 hD.2.2 hE.2.2

end CFSG.Sporadic.Fi24
