module

public import CFSG.OddTranspositions.PartThree.LocalBenderCenter
public import CFSG.OddTranspositions.PartThree.LocalBenderInvolutions
public import CFSG.OddTranspositions.PartThree.WidthThree
public import CFSG.OddTranspositions.PartThree.WidthKind
public import Certificates.Certificate113

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem widthLe_three_of_isBenderGroup (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {z u v : G} (hz1 : z ≠ 1) (hu : u ∈ centSet D z) (hv : v ∈ centSet D z) (huv : u ≠ v)
    (hc : Commute u v) (huvz : u * v * z ∈ D)
    (htrans : ∀ x ∈ centSet D z, ∀ y ∈ centSet D z, ∃ h ∈ localGroup D z, h * x * h⁻¹ = y)
    (hQ : CFSG.pCore 2 (localGroup D z) ≤ Subgroup.center (localGroup D z))
    (hB : CFSG.BenderSuzuki.IsBenderGroup
      (localGroup D z ⧸ CFSG.solvableRadical (localGroup D z)))
    (hzD : z ∉ D) :
    WidthLe D 3 :=
  widthLe_three_of_mul_mem_of_conj_eq hS hrad hz1 hzD hu hv huv hc
    (mul_mul_mem_of_isBenderGroup hS hu hv huv htrans
      (solvableRadical_le_center_localGroup hS hu hv huv hc huvz htrans hQ)
      (eq_one_or_eq_of_mem_center_localGroup hS hz1 hu hv huv hc huvz htrans hQ hB)
      hB
      (not_mem_commutator_localGroup hS hz1 hu hv huv hc huvz htrans hQ hB))
    (conj_eq_of_isBenderGroup hS hu hv huv hc huvz hzD htrans
      (solvableRadical_le_center_localGroup hS hu hv huv hc huvz htrans hQ)
      (eq_one_or_eq_of_mem_center_localGroup hS hz1 hu hv huv hc huvz htrans hQ hB) hB)

theorem lemma8_4 (h2 : AschbacherTheoremTwo) (hS : Setup G D)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {u w v : G} (ht : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n)
    (htrans : ∀ x ∈ centSet D ((u * v * w) ^ n), ∀ y ∈ centSet D ((u * v * w) ^ n),
      ∃ h ∈ localGroup D ((u * v * w) ^ n), h * x * h⁻¹ = y)
    (hQ : CFSG.pCore 2 (localGroup D ((u * v * w) ^ n)) ≤
      Subgroup.center (localGroup D ((u * v * w) ^ n)))
    (hB : CFSG.BenderSuzuki.IsBenderGroup
      (localGroup D ((u * v * w) ^ n) ⧸
        CFSG.solvableRadical (localGroup D ((u * v * w) ^ n)))) :
    (u * v * w) ^ n ∈ D ∨ QZ.O4PairData G D := by
  by_cases hzD : (u * v * w) ^ n ∈ D
  · exact Or.inl hzD
  · right
    obtain ⟨-, hz1, hzu, hzv, -, huvzD⟩ := ht.third_kind hS.oddT hS.normal hn hord
    have hu : u ∈ centSet D ((u * v * w) ^ n) := ⟨ht.1, hzu.symm⟩
    have hv : v ∈ centSet D ((u * v * w) ^ n) := ⟨ht.2.1, hzv.symm⟩
    have hw3 : WidthLe D 3 :=
      widthLe_three_of_isBenderGroup hS hrad hz1 hu hv ht.2.2.2.1 ht.2.2.2.2.1 huvzD
        htrans hQ hB hzD
    exact o4PairData_of_widthLe_three_of_thirdKind h2 hS hC hrad hw3 ht ⟨n, hn, hn1, hord⟩

end CFSG.OddTranspositions.PartThree
