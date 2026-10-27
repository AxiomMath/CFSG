module

public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldSemilinear
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldOuter
public import CFSG.RankThree.PartOne.KC.SymplecticNoninnerPlane

public section

namespace CFSG.RankThree.PartOne

open CFSG.ComponentClassification.UnbalancedCatalog (descentField)
open CFSG.RankThree.PartOne.KCSpComm

theorem symplectic_prime_subfield_clause : SymplecticSubfieldClause := by
  intro ℓ f r p K _ _ hℓ hp hp3 hpℓ hf hr hK σ hσ
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hσp : σ ^ p = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have : NeZero r := ⟨by omega⟩
  exact ⟨solvableRadical_fixedGroup hr hodd hσp,
    centralizer_fixedGroup_eq_zpowers_of_inputs hℓ hf hr hK hp hp3 hσ
      (fun β h => mem_spSemilinearAutGroup_of_fixes_subfield hℓ hf hr hK (descentField σ) h)
      (fun α hα h => exists_fieldAut_of_fixes_subfield (descentField σ) hα h)⟩

theorem symplectic_noninner_plane_local_core_product_odd :
    SymplecticNoninnerPlaneLocalCoreOdd :=
  symplectic_noninner_plane_local_core_product_odd_of_clause symplectic_prime_subfield_clause

end CFSG.RankThree.PartOne
