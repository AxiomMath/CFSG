module

public import CFSG.RankThree.PartOne.K133B.Glue
public import CFSG.RankThree.PartOne.K133B.NC5Geom

public section

namespace CFSG.RankThree.PartOne.K133B

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K1320X
  CFSG.RankThree.PartOne.Q1327T
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem false_of_E_le (hSLB : N143.SectionListBound) (hInsp : Row8U3Inspection)
    (h : Sec12Hyp G p A c L E) (hEA : E = A) {t : MulAut E} (ht : t ∈ reflectionSet p E)
    {K : Subgroup G} (hK : KtLift p E t K) {g : ℕ} (hmod : StatedClassicalModel ↥K .PSL 2 2 g)
    (hpg : p ∣ 2 ^ g + 1) {e : G} (he1 : e ≠ 1) (hetE : e ∈ autFixedInG E t)
    {I : Subgroup G} (hI : I ∈ thetaComponentsAt p e) (hKI : K ≤ I) (hEI : E ≤ I) : False := by
  have hp := h.prime
  have hp5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hcard : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  have hd := RefFacts.ElemData.of_isElementaryAbelian hp hp2 h.E_elem
  obtain ⟨v, hv, hve⟩ := Subgroup.mem_map.1 hetE
  have hvt : t v = v := hv
  have hveE : (v : G) = e := hve
  have hv1 : v ≠ 1 := fun h1 => he1 (by rw [← hveE, h1]; rfl)
  obtain ⟨c₀', x', hc₀1, hc₀fix, hx, hx1, hcardP, hFixgen, hvP, hEtop⟩ :=
    single_geometry hd hcard ht.1 hv1 hvt
  have hPI : (Subgroup.zpowers c₀' ⊔ Subgroup.zpowers x').map E.subtype ≤ I :=
    (Subgroup.map_subtype_le _).trans hEI
  obtain ⟨P, PD⟩ := planeData_of_geometry hSLB h hEA hK hmod hpg he1 hI hKI hveE hc₀1 hc₀fix hx
    hx1 hcardP rfl hFixgen hvP hEtop hPI
  have hZ : Subgroup.center (↥I ⧸ aschbacherSolvableCore p ↥I) = ⊥ :=
    (hInsp _ p g _ trivial PD.conf).1
  exact e_not_mem hp PD hZ (hEI PD.e_mem)

end CFSG.RankThree.PartOne.K133B
