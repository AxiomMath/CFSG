module

public import CFSG.Fischer.Uniq.F23Uniq
public import CFSG.Fischer.OpenTranslationHigh
public import CFSG.Sporadic.Fi23.Fischer

public section

namespace CFSG.Sporadic.Fi23

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem fischer_uniqueness_one
    (hPF : PolarFacts) (hHF : HyperovalFacts) (hFF : Fi22Facts)
    (X : Type) [Group X] (E : Set X) (_hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) (hT : HasType 1 X E) :
    ∃ iso : X ≃* Carrier 1, iso '' E = D23c := by
  obtain ⟨hZ0, hS0, hT0, -, -⟩ := existence_carrier
  exact F23.exists_mulEquiv hPF hHF hFF (hT : F23 X E) hT0 hZ hZ0 hS hS0

theorem open_uniqueness_23
    (hPF : PolarFacts) (hHF : HyperovalFacts) (hFF : Fi22Facts)
    (G H : Type) [Group G] [Group H] [Finite G] [Finite H] (D : Set G) (E : Set H)
    (hD : fischerEUIsCenterlessPair D) (hDT : fischerEUTypeF23 D)
    (hE : fischerEUIsCenterlessPair E) (hET : fischerEUTypeF23 E) :
    ∃ φ : G ≃* H, φ '' D = E := by
  have hPD : Pair G D := (CFSG.Fischer.pair_iff D).2 ⟨inferInstance, hD.1⟩
  have hPE : Pair H E := (CFSG.Fischer.pair_iff E).2 ⟨inferInstance, hE.1⟩
  exact F23.exists_mulEquiv hPF hHF hFF (F23_of_typeF23_open hPD hDT)
    (F23_of_typeF23_open hPE hET) hD.2.1 hE.2.1 hD.2.2 hE.2.2

end CFSG.Sporadic.Fi23
