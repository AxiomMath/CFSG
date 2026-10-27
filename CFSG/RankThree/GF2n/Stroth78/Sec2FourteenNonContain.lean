module

public import CFSG.RankThree.GF2n.Stroth78.Sec2FourteenQa2
public import CFSG.RankThree.GF2n.Stroth78.Sec2Eleven
public import CFSG.GroupTheory.PCore.CentralizerJoin

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem centralizer_centerIn_inf_not_le
    (S : Setting z E F) {a : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a) (haZ : a ∉ ZQ z) (hza : z ∈ QaOf a) :
    ¬ Subgroup.centralizer ((ZQ z ⊓ centerIn (QaOf a) : Subgroup G) : Set G) ≤
      (Subgroup.centralizer ({z} : Set G) ⊓
        Subgroup.centralizer ((ZQ z ⊓ centerIn (QaOf a) : Subgroup G) : Set G)) ⊔
        inSubgroup (pPrimeCore 2)
          (Subgroup.centralizer ((ZQ z ⊓ centerIn (QaOf a) : Subgroup G) : Set G)) := by
  intro hle
  let C : Subgroup G :=
    Subgroup.centralizer ((ZQ z ⊓ centerIn (QaOf a) : Subgroup G) : Set G)
  let P : Subgroup G := QaOf a
  have hPC : P ≤ C := QaOf_le_centralizer_centerIn_inf S a
  have hP : IsPGroup 2 P := QaOf_isPGroup S hconj
  have hzP : z ∈ P := hza
  have hle' : C ≤ (Subgroup.centralizer ({z} : Set G) ⊓ C) ⊔
      inSubgroup (pPrimeCore 2) C := by
    simpa [C] using hle
  have hcent : P ≤ Subgroup.centralizer ({z} : Set G) :=
    CFSG.le_centralizer_of_le_sup_pPrimeCore (p := 2) hzP hPC hP hle'
  have hzCent : z ∈ centerIn (QaOf a) := by
    change z ∈ QaOf a ⊓ Subgroup.centralizer (QaOf a : Set G)
    refine Subgroup.mem_inf.mpr ⟨hza, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hcent hy) z (Set.mem_singleton z)).symm
  exact z_not_mem_centerIn_Qa S haQ hconj haZ hza hzCent

theorem centerIn_Qa_not_le_Q
    (S : Setting z E F) {a : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a) (haZ : a ∉ ZQ z) (hza : z ∈ QaOf a)
    (h212 : Stroth78Assumption212 z) :
    ¬ centerIn (QaOf a) ≤ Q z :=
  centerIn_Qa_not_le_Q_of_Qa_isPGroup_of_hyperplane S haQ hconj haZ hza
    (centralizer_centerIn_inf_not_le S haQ hconj haZ hza) h212

end CFSG.RankThree.GF2n.Stroth78
