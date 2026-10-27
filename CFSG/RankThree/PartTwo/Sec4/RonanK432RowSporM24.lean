module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThreeM24
public import CFSG.Quasithin.Background.A318POutSpor
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint
open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree (tp_eq_of_rep)
open CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24 (rep_wT)

@[expose] def m24ClassWord (w : List ℤ) : NativeSporadic.M24 :=
  ⟨CFSG.Sporadic.Th.wordG CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24.letG w,
    CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24.wordG_mem w⟩

@[expose] def m24RA : NativeSporadic.M24 :=
  m24ClassWord CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24.xW

@[expose] def m24RB : NativeSporadic.M24 :=
  m24ClassWord CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24.x2W

@[expose] def m24WA : NativeSporadic.M24 :=
  m24ClassWord [1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1]

@[expose] def m24WB : NativeSporadic.M24 :=
  m24ClassWord [2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1,
    2, 1, 2, 1, -2]

theorem m24RA_pow_three : m24RA ^ 3 = 1 := by
  decide +kernel

theorem m24RB_pow_three : m24RB ^ 3 = 1 := by
  decide +kernel

theorem m24WA_facts :
    (m24WA * m24RA * m24WA⁻¹) * m24RA = m24RA * (m24WA * m24RA * m24WA⁻¹) ∧
      m24WA * m24RA * m24WA⁻¹ ≠ m24RA ∧ m24WA * m24RA * m24WA⁻¹ ≠ m24RA⁻¹ ∧
      m24WA * m24RA * m24WA⁻¹ ≠ 1 := by
  decide +kernel

theorem m24WB_facts :
    (m24WB * m24RB * m24WB⁻¹) * m24RB = m24RB * (m24WB * m24RB * m24WB⁻¹) ∧
      m24WB * m24RB * m24WB⁻¹ ≠ m24RB ∧ m24WB * m24RB * m24WB⁻¹ ≠ m24RB⁻¹ ∧
      m24WB * m24RB * m24WB⁻¹ ≠ 1 := by
  decide +kernel

theorem m24_conj_cover
    (z : NativeSporadic.M24) (hz : orderOf z = 3) :
    ∃ k : Fin 2, ∃ h : NativeSporadic.M24, z = h * ![m24RA, m24RB] k * h⁻¹ := by
  have hz' : orderOf (z : Equiv.Perm (Fin 24)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hz
  obtain ⟨r, hr, g, hg, hgz⟩ := CFSG.AGLEmbeddingD2.Wilson.Census219.m24_cover z.2 hz'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have e : CFSG.Sporadic.SmallOddCore.tp 24
        CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24.m24Row3A.rep =
          CFSG.Sporadic.Th.wordG CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24.letG
            CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24.xW :=
      tp_eq_of_rep (rep_wT CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24.xW)
    rw [e] at hgz
    exact ⟨0, ⟨g, hg⟩, Subtype.ext hgz⟩
  · have e : CFSG.Sporadic.SmallOddCore.tp 24
        CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24.m24Row3B.rep =
          CFSG.Sporadic.Th.wordG CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24.letG
            CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24.x2W :=
      tp_eq_of_rep (rep_wT CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24.x2W)
    rw [e] at hgz
    exact ⟨1, ⟨g, hg⟩, Subtype.ext hgz⟩

theorem listRow_m24 :
    ListRow NativeSporadic.M24 := by
  refine listRow_of_class_witness (κ := Fin 2) ![m24RA, m24RB] ![m24WA, m24WB]
    m24_conj_cover ?_ ?_
  · intro k
    fin_cases k
    · exact m24RA_pow_three
    · exact m24RB_pow_three
  · intro k _
    fin_cases k
    · exact m24WA_facts
    · exact m24WB_facts

theorem outerRow_m24 :
    OuterRow NativeSporadic.M24 := by
  apply outerRow_of_not_three_dvd_outer
  exact CFSG.Quasithin.A318P.not_dvd_outer_M24 (S := NativeSporadic.M24) (MulEquiv.refl _)
    Nat.prime_three (by norm_num)

theorem row_carrier_m24 :
    RowOf (NativeSporadic.Carrier .M24) := by
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv (S := NativeSporadic.M24) e.symm ⟨listRow_m24, outerRow_m24⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
