module

public import CFSG.RankThree.PartOne.KF.RowCore
public import CFSG.RankThree.PartOne.S12.Sec12Three
import CFSG.RankThree.PartOne.S9.Planes.Basic
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem table_core_of (h : Sec12Hyp G p A c L E) (hG : Sec12TwoGeneric p c L E) :
    Table123Core p L (A ⊓ L) (E ⊓ L) :=
  { prime := h.prime
    five_le := Sec12Three.five_le h
    quasisimple := hG.quasisimple
    center_pPrime := hG.center_pPrime
    A₀_le := inf_le_right
    A₀_elem := Planes.isElementaryAbelian_of_le inf_le_left h.A_elem
    A₀_card := Sec12Three.card_A_inf_L h hG (Sec12Three.c_not_mem_L h hG.center_pPrime)
    A₀_invariant := Sec12Three.invariant_A_inf_L h hG
    F_le := inf_le_right
    F_elem := Planes.isElementaryAbelian_of_le inf_le_left h.E_elem
    A₀_le_F := inf_le_inf_right L h.A_le_E
    F_le_centralizer := fun f hf a ha => by
      have hfE := (Subgroup.mem_inf.1 hf).1
      have haA := (Subgroup.mem_inf.1 ha).1
      exact (Subgroup.mem_centralizer_iff.1 (h.E_le hfE) a haA)
    F_max := fun F' hF'L hF'el hF'c hFF' =>
      Sec12Three.F_max_generic h hG F' hF'L hF'el hF'c hFF' }

end CFSG.RankThree.PartOne.KFOUT3
