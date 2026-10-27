module

public import CFSG.Fischer.Uniq.F22Uniq
public import CFSG.Fischer.OpenTranslation
public import CFSG.Sporadic.Fi22.Fischer

public section

namespace CFSG.Sporadic.Fi22

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem fischer_uniqueness_zero
    (hPF : PolarFacts) (X : Type) [Group X] (E : Set X)
    (_hP : Pair X E) (hZ : Subgroup.center X = ⊥) (hS : IsSimpleGroup (commutator X))
    (hT : HasType 0 X E) : ∃ iso : X ≃* Carrier 0, iso '' E = D22 := by
  obtain ⟨hZ0, hS0, hT0, -, -⟩ := existence_carrier
  exact F22.exists_mulEquiv hPF (hT : F22 X E) hT0 hZ hZ0 hS hS0

theorem open_uniqueness_22
    (hPF : PolarFacts) (G H : Type) [Group G] [Group H] [Finite G]
    [Finite H] (D : Set G) (E : Set H) (hD : fischerEUIsCenterlessPair D)
    (hDT : fischerEUTypeF22 D) (hE : fischerEUIsCenterlessPair E) (hET : fischerEUTypeF22 E) :
    ∃ φ : G ≃* H, φ '' D = E := by
  have hPD : Pair G D := (CFSG.Fischer.pair_iff D).2 ⟨inferInstance, hD.1⟩
  have hPE : Pair H E := (CFSG.Fischer.pair_iff E).2 ⟨inferInstance, hE.1⟩
  exact F22.exists_mulEquiv hPF (F22_of_typeF22_open hPD hDT) (F22_of_typeF22_open hPE hET)
    hD.2.1 hE.2.1 hD.2.2 hE.2.2

end CFSG.Sporadic.Fi22
