module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.M23
public import CFSG.Quasithin.Background.A318POutCheap
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint
open CFSG.AGLEmbeddingD2.Wilson.ThreeCore CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M23
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def m23ClassWord (w : List ℤ) : NativeSporadic.M23 :=
  ⟨CFSG.Sporadic.Th.wordG letG w, wordG_mem w⟩

@[expose] def m23ClassRep : NativeSporadic.M23 := m23ClassWord xW

@[expose] def m23ClassWit : NativeSporadic.M23 := m23ClassWord [1, 2, 1, 2, 2, 1, 2, 1, -2, 1]

theorem m23ClassRep_pow_three : m23ClassRep ^ 3 = 1 := by
  decide +kernel

theorem m23ClassWit_facts :
    (m23ClassWit * m23ClassRep * m23ClassWit⁻¹) * m23ClassRep =
        m23ClassRep * (m23ClassWit * m23ClassRep * m23ClassWit⁻¹) ∧
      m23ClassWit * m23ClassRep * m23ClassWit⁻¹ ≠ m23ClassRep ∧
      m23ClassWit * m23ClassRep * m23ClassWit⁻¹ ≠ m23ClassRep⁻¹ ∧
      m23ClassWit * m23ClassRep * m23ClassWit⁻¹ ≠ 1 := by
  decide +kernel

theorem m23_conj_rep
    (t : Equiv.Perm (Fin 23)) (ht : t ∈ NativeSporadic.M23) (ht3 : orderOf t = 3) :
    ∃ g ∈ NativeSporadic.M23, t = g * CFSG.Sporadic.Th.wordG letG xW * g⁻¹ :=
  m23_cover t ht ht3

theorem m23_conj_rep_sub
    (z : NativeSporadic.M23) (hz : orderOf z = 3) :
    ∃ h : NativeSporadic.M23, z = h * m23ClassRep * h⁻¹ := by
  have hz' : orderOf (z : Equiv.Perm (Fin 23)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hz
  obtain ⟨g, hg, hgz⟩ := m23_conj_rep (z : Equiv.Perm (Fin 23)) z.2 hz'
  exact ⟨⟨g, hg⟩, Subtype.ext hgz⟩

theorem listRow_m23 :
    ListRow NativeSporadic.M23 :=
  listRow_of_class_witness (κ := Unit) (fun _ => m23ClassRep) (fun _ => m23ClassWit)
    (fun z hz => ⟨(), m23_conj_rep_sub z hz⟩) (fun _ => m23ClassRep_pow_three)
    (fun _ _ => m23ClassWit_facts)

theorem outerRow_m23 :
    OuterRow NativeSporadic.M23 := by
  apply outerRow_of_not_three_dvd_outer
  have h2 : Nat.card (Outer NativeSporadic.M23) ≤ 2 :=
    (CFSG.Sporadic.Schreier.at_m23_schreier).1
  haveI : Finite (NativeSporadic.Carrier .M23) := inferInstanceAs (Finite NativeSporadic.M23)
  exact CFSG.Quasithin.A318P.not_dvd_outer_of_carrier (S := NativeSporadic.M23) (s := .M23)
    (MulEquiv.refl _) h2 Nat.prime_three (by norm_num)

theorem row_carrier_m23 :
    RowOf (NativeSporadic.Carrier .M23) := by
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv (S := NativeSporadic.M23) e.symm ⟨listRow_m23, outerRow_m23⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
