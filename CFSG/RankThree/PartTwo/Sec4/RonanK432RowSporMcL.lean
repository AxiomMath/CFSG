module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432CoverIndex
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Invariant
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.Quasithin.Background.A318POutCheap
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint CFSG.Sporadic.Recognition CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section McL


set_option linter.unusedSectionVars false

theorem listRow_of_two_classes {S : Type} [Group S] [Finite S] {x x₁ x₂ y : S}
    (hcov : ∀ z : S, orderOf z = 3 → IsConj z x₁ ∨ IsConj z x₂)
    (hx1 : IsConj x x₁) (hidx : 3 ∣ (Subgroup.centralizer ({x₂} : Set S)).index)
    (hc : x * y = y * x) (hn : y ∉ Subgroup.zpowers x) (hxy : IsConj x y) : ListRow S := by
  refine listRow_of_forall_not_weaklyClosed fun z hz => ?_
  rcases hcov z hz with hz1 | hz2
  · have hzx : IsConj x z := (hz1.trans hx1.symm).symm
    obtain ⟨k, hk⟩ := isConj_iff.mp hzx
    obtain ⟨hc', hn'⟩ := commute_notMem_of_conj k hc hn (Or.inl hk)
    have hconj : IsConj z (k * y * k⁻¹) :=
      hzx.symm.trans (hxy.trans (isConj_iff.mpr ⟨k, rfl⟩))
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    refine not_weaklyClosed_of_commute_conj (g := g) ?_ ?_
    · rw [hg]
      exact hc'
    · rw [hg]
      exact hn'
  · refine not_weaklyClosed_of_three_dvd_index hz ?_
    rw [index_centralizer_eq_of_isConj hz2]
    exact hidx

theorem exists_pair_of_threeLocal {G : Type} [Group G] {x : G} {R T A : Subgroup G}
    (hL : ThreeLocal G x R T A) :
    ∃ y : G, x * y = y * x ∧ y ∉ Subgroup.zpowers x ∧ IsConj x y := by
  have hx3 : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hL.order_x] at this
  have hxR : x ∈ R := by
    have : x ∈ R ⊓ Subgroup.centralizer (R : Set G) := by
      rw [hL.center_R]
      exact Subgroup.mem_zpowers x
    exact this.1
  have hxT : x ∈ T := hL.R_le_T hxR
  have hAX : ∀ y ∈ ((T : Set G) ∩ {y | IsConj x y}), y ∈ A := fun y hy => by
    rw [hL.A_eq]
    exact Subgroup.subset_closure hy
  have hxX : x ∈ ((T : Set G) ∩ {y | IsConj x y}) := ⟨hxT, IsConj.refl x⟩
  obtain ⟨y₁, hy₁X, hy₁ne⟩ : ∃ y ∈ ((T : Set G) ∩ {y | IsConj x y}), y ∉ ({x, x⁻¹} : Set G) := by
    by_contra hcon
    push Not at hcon
    have hsub : ((T : Set G) ∩ {y | IsConj x y}) ⊆ ({x, x⁻¹} : Set G) := fun y hy => hcon y hy
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2' : ({x, x⁻¹} : Set G).ncard ≤ 2 := by
      calc ({x, x⁻¹} : Set G).ncard ≤ ({x⁻¹} : Set G).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    have h20 : ((T : Set G) ∩ {y | IsConj x y}).ncard = 20 := hL.card_class_inter
    omega
  have hy₁A : y₁ ∈ A := hAX y₁ hy₁X
  have hxA : x ∈ A := hAX x hxX
  haveI : CFSG.IsElementaryAbelian 3 A := hL.A_elementaryAbelian
  have hcomm : x * y₁ = y₁ * x := Subgroup.mul_comm_of_mem_isMulCommutative A hxA hy₁A
  have hy₁conj : IsConj x y₁ := hy₁X.2
  have hy₁1 : y₁ ≠ 1 := by
    intro h
    rw [h, isConj_one_left] at hy₁conj
    have := hL.order_x
    rw [hy₁conj, orderOf_one] at this
    omega
  refine ⟨y₁, hcomm, ?_, hy₁conj⟩
  intro hmem
  rcases mem_zpowers_cases_of_pow_three hx3 hmem with h | h | h
  · exact hy₁1 h
  · exact hy₁ne (Or.inl h)
  · exact hy₁ne (Or.inr h)

theorem listRow_mcl : ListRow NativeSporadic.McL := by
  obtain ⟨x₁, x₂, h1, h2, hc1, hc2, hnc, hcov⟩ := mcl_two_classes_order_three_of_certificate
  obtain ⟨x, R, T, A, hL⟩ := mcl_threeLocal_of_certificate
  have hL' := hL.toThreeLocal
  have hG : Nat.card NativeSporadic.McL = 898128000 := CFSG.Sporadic.McL.card_McL
  have hidx : ∀ g : NativeSporadic.McL, Nat.card (Subgroup.centralizer ({g} : Set _)) *
      (Subgroup.centralizer ({g} : Set NativeSporadic.McL)).index = 898128000 := fun g => by
    rw [Subgroup.card_mul_index, hG]
  have hi2 : (Subgroup.centralizer ({x₂} : Set NativeSporadic.McL)).index = 924000 := by
    have := hidx x₂
    rw [hc2] at this
    omega
  have hix : (Subgroup.centralizer ({x} : Set NativeSporadic.McL)).index = 30800 := by
    have := hidx x
    rw [hL'.card_centralizer] at this
    omega
  have hx1 : IsConj x x₁ := by
    rcases hcov x hL'.order_x with h | h
    · exact h
    · exfalso
      rw [index_centralizer_eq_of_isConj h, hi2] at hix
      omega
  obtain ⟨y, hc, hn, hxy⟩ := exists_pair_of_threeLocal hL'
  exact listRow_of_two_classes hcov hx1 (by rw [hi2]; norm_num) hc hn hxy

theorem outerRow_mcl : OuterRow NativeSporadic.McL := by
  apply outerRow_of_not_three_dvd_outer
  have h2 : Nat.card (Outer NativeSporadic.McL) ≤ 2 := CFSG.Sporadic.Schreier.McL_outer_card_le_two.1
  exact CFSG.Quasithin.A318P.not_dvd_outer_of_carrier (S := NativeSporadic.McL) (s := .McL)
    (MulEquiv.refl _) h2 Nat.prime_three (by norm_num)

theorem row_carrier_mcl : RowOf (NativeSporadic.Carrier .McL) := by
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv (S := NativeSporadic.McL) e.symm ⟨listRow_mcl, outerRow_mcl⟩

end McL

end CFSG.RankThree.PartTwo.Sec4.RonanK432
