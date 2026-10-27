module

public import CFSG.RankThree.PartOne.S12.Sec12A
import CFSG.RankThree.PartOne.S12.Sec125Moved
import CFSG.RankThree.PartOne.S10.ThetaNodesUnconditional
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.LocalAnalysis.ComponentInitial

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElementaryAbelian_of_le {p : ℕ} {E B : Subgroup G} (hE : IsElementaryAbelian p E)
    (hBE : B ≤ E) : IsElementaryAbelian p B := CFSG.IsElementaryAbelian.of_le hE hBE

theorem exists_zeroStar_above_E (hS : SchreierFor InCatalog) {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h : Sec12Hyp G p A c L E) {I : Subgroup G} (hI : I ∈ thetaCompE p E)
    (hB : ∀ b ∈ E, b ≠ 1 → ∀ J ∈ thetaComponentsAt p b, sectionTenRel p I J →
      ∃ B : Subgroup G, B ≤ E ∧ Nat.card B = p ^ 3 ∧ b ∈ B ∧ I ∈ sectionTenZero p B) :
    ∃ J ∈ thetaCompZeroStarE p E, sectionTenRel p I J := by
  classical
  have hp := h.prime
  have hp3 := h.three_lt
  have : IsSimpleGroup G := h.setup.1
  have hUsub : thetaCompE p E ⊆ thetaComponentFamily p E := by
    rintro X ⟨B, hBadm, hXB⟩
    obtain ⟨b, hbB, hb1, hXb⟩ := mem_thetaComponentFamily_iff.1 hXB
    exact mem_thetaComponentFamily_iff.2 ⟨b, hBadm.1 hbB, hb1, hXb⟩
  have htrans : ∀ X ∈ thetaCompE p E, ∀ Y ∈ thetaCompE p E, ∀ Z ∈ thetaCompE p E,
      sectionTenRel p X Y → sectionTenRel p Y Z → sectionTenRel p X Z :=
    fun X hX Y hY Z hZ hXY hYZ =>
      section_ten_component_supplement_transitivity hS G h.setup.2.1 h.setup.2.2.1
        (sectionTenSetup_evenRank_eq h.setup).le p hp hp3 E h.E_elem X (hUsub hX) Y (hUsub hY)
        Z (hUsub hZ) hXY hYZ
  obtain ⟨J, hJU, hIJ, hJmax⟩ := Sec125.exists_maximal_above (sectionTenRel p) (thetaCompE p E)
    (fun a _ => sectionTenRel_refl p a) htrans hI
  obtain ⟨B', hB'adm, hJB'⟩ := hJU
  obtain ⟨b, hbB', hb1, hJb⟩ := mem_thetaComponentFamily_iff.1 hJB'
  obtain ⟨B, hBE, hBcard, hbB, hIB⟩ := hB b (hB'adm.1 hbB') hb1 J hJb hIJ
  have hJB : J ∈ thetaComponentFamily p B := mem_thetaComponentFamily_iff.2 ⟨b, hbB, hb1, hJb⟩
  have hBel : IsElementaryAbelian p B := isElementaryAbelian_of_le h.E_elem hBE
  have hJ0 : J ∈ sectionTenZero p B :=
    section_ten_moving_two_stratum_upward_closure G (sectionTenSetup_evenRank_eq h.setup).le p hp
      hp3 (sectionTenSetup_vanishing h.setup) B hBel hBcard I hIB.1 J hJB hIJ hIB
  obtain ⟨-, S, -, hS1, hS2, hSB, -⟩ := hIB
  have hBadm : B ∈ admissibleTriples p E := ⟨hBE, hBel, hBcard, S, hS1, hS2, hSB⟩
  have hJU : J ∈ thetaCompE p E := ⟨B', hB'adm, hJB'⟩
  exact ⟨J, ⟨⟨B, hBadm, hJ0⟩, hJU, fun J' hJ' hJJ' => hJmax J' hJ' hJJ'⟩, hIJ⟩

end CFSG.RankThree.PartOne.K133
