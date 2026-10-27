module

public import CFSG.Monster.GMS.S57
public import CFSG.Monster.GMS.Facts.Section37
public import CFSG.Monster.GMS.Facts.Interfaces

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S37

section Gamma

variable {G : Type*} [Group G] {a z₀ x y : G}

theorem mem_gammaNbr_iff : y ∈ gammaNbr a z₀ x ↔ y = x ∨ ∃ K, y ∈ typeSet a z₀ x K := by
  simp only [gammaNbr, Set.mem_insert_iff, Set.mem_iUnion]

theorem isConj_of_mem_gammaNbr (hx : IsConj a x) (h : y ∈ gammaNbr a z₀ x) : IsConj a y := by
  rcases mem_gammaNbr_iff.mp h with rfl | ⟨K, hK⟩
  · exact hx
  · exact isConj_of_mem_typeSet hK

theorem self_mem_gammaNbr : x ∈ gammaNbr a z₀ x := Set.mem_insert _ _

end Gamma

section One

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ x y : G}

theorem mem_gammaNbr_of_even
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hx : IsConj a x) (hy : IsConj a y) (hev : Even (orderOf (x * y))) :
    y ∈ gammaNbr a z₀ x := by
  refine Or.inr (Set.mem_iUnion.2 ?_)
  rcases table7_cases I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG hx hy hev with
    h | h | h | h | h
  · exact ⟨.twoA, h⟩
  · exact ⟨.twoB, h⟩
  · exact ⟨.fourA, h⟩
  · exact ⟨.fourB, h⟩
  · exact ⟨.sixA, h⟩

theorem mem_gammaNbr_of_oddNbr
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hx : IsConj a x) (hmem : y ∈ oddNbr a z₀ x) : y ∈ gammaNbr a z₀ x := by
  refine Or.inr (Set.mem_iUnion.2 ?_)
  obtain ⟨k, hk, -⟩ := s348_type I.sls I.tableV I.leech I.leechOddPair I.tableIV hG hx hmem
  match k, hk with
  | 0, hk => exact ⟨.threeA, hmem, hk⟩
  | 1, hk => exact ⟨.threeC, hmem, hk⟩
  | 2, hk => exact ⟨.fiveA, hmem, hk⟩

theorem mem_gammaNbr_of_twoB
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hx : IsConj a x) (hy : IsConj a y)
    (h : ∃ w ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}, IsConj z₀ w) :
    y ∈ gammaNbr a z₀ x := by
  by_cases hyx : y = x
  · exact Or.inl hyx
  rcases Nat.even_or_odd (orderOf (x * y)) with hev | hodd
  · exact mem_gammaNbr_of_even I hG hx hy hev
  · exact mem_gammaNbr_of_oddNbr I hG hx ⟨hy, hyx, hodd, h⟩

theorem mem_gammaNbr_of_twoA
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hCN : CommonNbrTwoB a z₀) (hx : IsConj a x) (hy : IsConj a y)
    (h : ∃ t, t ∈ twoANbr a x ∩ twoANbr a y) : y ∈ gammaNbr a z₀ x := by
  by_cases hyx : y = x
  · exact Or.inl hyx
  rcases Nat.even_or_odd (orderOf (x * y)) with hev | hodd
  · exact mem_gammaNbr_of_even I hG hx hy hev
  obtain ⟨t, htx, hty⟩ := h
  have hyt : y ∈ twoANbr a t := (S57.mem_twoANbr_comm hy htx.1).mp hty
  obtain ⟨K, hK, hKo⟩ := S57.exists_class_of_mem_inter I.sls I.tableV I.leech I.tableIII
    I.tableIVBaby hG hx htx hty hy hyx hodd
  have hK3 : K = .three_A := by
    cases K <;> first | rfl | (exfalso; rw [hKo] at hodd; revert hodd; decide)
  subst hK3
  have h3 : orderOf (x * y) = 3 := hKo
  obtain ⟨w, hw, hwB⟩ := hCN x y t hx htx hyt h3
  exact mem_gammaNbr_of_twoB I hG hx hy ⟨w, hw, hwB⟩

end One

end S37

section Headline

open S37

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ x y : G}

theorem s371_one
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hCN : CommonNbrTwoB a z₀)
    (hx : IsConj a x) (hy : IsConj a y)
    (h : (∃ w ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}, IsConj z₀ w) ∨
      (∃ t ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y},
        t ∈ twoANbr a x ∩ twoANbr a y) ∨ Even (orderOf (x * y))) :
    y ∈ gammaNbr a z₀ x := by
  rcases h with h | ⟨t, -, ht⟩ | h
  · exact mem_gammaNbr_of_twoB I hG hx hy h
  · exact mem_gammaNbr_of_twoA I hG hCN hx hy ⟨t, ht⟩
  · exact mem_gammaNbr_of_even I hG hx hy h

end Headline

end CFSG.Monster.GMS
