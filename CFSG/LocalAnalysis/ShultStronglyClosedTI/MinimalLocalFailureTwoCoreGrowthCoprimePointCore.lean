module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthCoprimeExtraPrime
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthStructure

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TwoCoreGrowthCoprime

open CFSG.ShultStronglyClosedTI.TwoCoreGrowth

universe u

theorem point_two_core_internal_actor_data
    {G : Type u} [Group G] (H Q X J : Subgroup G)
    (hHQ : H ≤ Subgroup.normalizer (Q : Set G))
    (hXH : X ≤ H) (hJH : J ≤ H) :
    (Q.subgroupOf (pointTwoCoreImage H)).Normal ∧
      X ≤ Subgroup.normalizer (pointTwoCoreImage H : Set G) ∧
      J ≤ Subgroup.normalizer (pointTwoCoreImage H : Set G) ∧
      X ≤ Subgroup.normalizer (Q : Set G) ∧
      J ≤ Subgroup.normalizer (Q : Set G) := by
  have hHM : H ≤ Subgroup.normalizer (pointTwoCoreImage H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (pointTwoCoreImage_le H)).mp
      (pointTwoCoreImage_normal H)
  exact ⟨Subgroup.normal_subgroupOf_of_le_normalizer ((pointTwoCoreImage_le H).trans hHQ),
    hXH.trans hHM, hJH.trans hHM, hXH.trans hHQ, hJH.trans hHQ⟩

theorem point_two_core_scalar_centralizer_orders_coprime
    {G : Type u} [Group G] [Finite G] (H Q X J : Subgroup G)
    (hHQ : H ≤ Subgroup.normalizer (Q : Set G))
    (hQM : Q ≤ pointTwoCoreImage H) (hQproper : ¬ pointTwoCoreImage H ≤ Q)
    (hXH : X ≤ H) (hJH : J ≤ H)
    (hInv : ∀ m : G, m ∈ pointTwoCoreImage H → orderOf m = 2 → m ∈ Q)
    (hXcard : Nat.card X = Nat.card Q - 1)
    (hJX : J ≤ Subgroup.centralizer (X : Set G))
    (hJQ : J ≤ Subgroup.centralizer (Q : Set G)) (hdis : Disjoint X J)
    (hscalar : ∀ x : G, x ∈ X → x ≠ 1 →
      ∀ m : G, m ∈ pointTwoCoreImage H → m ∈ Q → x * m * x⁻¹ = m → m = 1)
    (hJkernel : ∀ y : G, y ∈ J → y ≠ 1 → Odd (orderOf y) →
      ∀ m : G, m ∈ pointTwoCoreImage H → y * m * y⁻¹ = m → m ∈ Q) :
    Nat.Coprime (Nat.card X) (Nat.card J) := by
  obtain ⟨hQnormal, hXM, hJM, hXQ, hJnQ⟩ :=
    point_two_core_internal_actor_data H Q X J hHQ hXH hJH
  let : (Q.subgroupOf (pointTwoCoreImage H)).Normal := hQnormal
  let : Subgroup.Normalizes X (pointTwoCoreImage H) := ⟨hXM⟩
  let : Subgroup.Normalizes J (pointTwoCoreImage H) := ⟨hJM⟩
  have hM := pointTwoCoreImage_isPGroup H
  obtain ⟨e, he, hQcard, hQeven, hXodd⟩ :=
    two_group_root_scalar_order_data (pointTwoCoreImage H) Q X hM hQM hXcard
  have hJfixQ : ∀ y : G, y ∈ J → ∀ m : G, m ∈ Q → y * m * y⁻¹ = m := by
    intro y hy m hm
    exact Commute.mul_inv_cancel
      (show Commute y m from (Subgroup.mem_centralizer_iff.mp (hJQ hy) m hm).symm)
  exact scalar_centralizer_orders_coprime (pointTwoCoreImage H) Q X J hM hQproper hInv
    hXodd hXQ hJnQ hJX hdis hJfixQ hscalar hJkernel

theorem point_two_core_extra_prime_full_product_data
    {G : Type u} [Group G] [Finite G] (H Q X J B : Subgroup G) [IsCyclic X]
    (hHQ : H ≤ Subgroup.normalizer (Q : Set G))
    (hQM : Q ≤ pointTwoCoreImage H) (hQproper : ¬ pointTwoCoreImage H ≤ Q)
    (hXH : X ≤ H) (hJH : J ≤ H) (hBH : B ≤ H)
    (hInv : ∀ m : G, m ∈ pointTwoCoreImage H → orderOf m = 2 → m ∈ Q)
    (hQB : Q ⊓ B = ⊥) (hindex : B.relIndex H = Nat.card Q ^ 3)
    (hXcard : Nat.card X = Nat.card Q - 1)
    (hJX : J ≤ Subgroup.centralizer (X : Set G))
    (hJQ : J ≤ Subgroup.centralizer (Q : Set G)) (hdis : Disjoint X J)
    (hscalar : ∀ x : G, x ∈ X → x ≠ 1 →
      ∀ m : G, m ∈ pointTwoCoreImage H → m ∈ Q → x * m * x⁻¹ = m → m = 1)
    (hJkernel : ∀ y : G, y ∈ J → y ≠ 1 → Odd (orderOf y) →
      ∀ m : G, m ∈ pointTwoCoreImage H → y * m * y⁻¹ = m → m ∈ Q)
    {p : ℕ} (hp : p.Prime) (hpJ : p ∣ Nat.card J) (hpPlus : p ∣ Nat.card Q + 1) :
    Nat.Coprime (Nat.card X) (Nat.card J) ∧ Odd p ∧ ¬ p ∣ Nat.card Q - 1 ∧
      Nat.card (pointTwoCoreImage H) = Nat.card Q ^ 3 ∧
      pointTwoCoreImage H ⊓ B = ⊥ ∧ pointTwoCoreImage H ⊔ B = H ∧
      Nat.card (pointTwoCoreImage H ⧸ Q.subgroupOf (pointTwoCoreImage H)) = Nat.card Q ^ 2 ∧
      ∃ y : G, y ∈ J ∧ orderOf y = p ∧
        IsCyclic (X ⊔ Subgroup.zpowers y : Subgroup G) ∧
        Nat.card (X ⊔ Subgroup.zpowers y : Subgroup G) = p * (Nat.card Q - 1) ∧
        p * (Nat.card Q - 1) ∣ Nat.card Q ^ 2 - 1 := by
  obtain ⟨hQnormal, hXM, hJM, hXQ, hJnQ⟩ :=
    point_two_core_internal_actor_data H Q X J hHQ hXH hJH
  let : (Q.subgroupOf (pointTwoCoreImage H)).Normal := hQnormal
  let : Subgroup.Normalizes X (pointTwoCoreImage H) := ⟨hXM⟩
  let : Subgroup.Normalizes J (pointTwoCoreImage H) := ⟨hJM⟩
  have hM := pointTwoCoreImage_isPGroup H
  have hJfixQ : ∀ y : G, y ∈ J → ∀ m : G, m ∈ Q → y * m * y⁻¹ = m := by
    intro y hy m hm
    exact Commute.mul_inv_cancel
      (show Commute y m from (Subgroup.mem_centralizer_iff.mp (hJQ hy) m hm).symm)
  obtain ⟨hcop, hpOdd, hnot, y, hyJ, hy, hEcyc, hEcard, hdiv,
    e, d, hQcard, hdcard, he, hd, hexp, hdouble, hlower⟩ :=
    scalar_centralizer_extra_prime_cubic_data (pointTwoCoreImage H) Q X J hM hQM
      hQproper hInv hXcard hXQ hJnQ hJX hdis hJfixQ hscalar hJkernel hp hpJ hpPlus
  have hintersection : pointTwoCoreImage H ⊓ B = ⊥ :=
    pair_intersection_eq_bot_of_involutions_in_root (pointTwoCoreImage H) Q B hM hInv hQB
  have hbound : Nat.card (pointTwoCoreImage H) ∣ Nat.card Q ^ 3 := by
    rw [← hindex]
    exact point_two_core_card_dvd_pair_index H B hBH hintersection
  have hcard : Nat.card (pointTwoCoreImage H) = Nat.card Q ^ 3 :=
    le_antisymm (Nat.le_of_dvd (pow_pos (Nat.card_pos (α := Q)) 3) hbound) hlower
  have hjoin : pointTwoCoreImage H ⊔ B = H :=
    point_two_core_join_pair_eq_point_of_full_order H B hBH hintersection (hcard.trans hindex.symm)
  have hQMcard : Nat.card (Q.subgroupOf (pointTwoCoreImage H)) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQM).toEquiv
  have hquotcard :
      Nat.card (pointTwoCoreImage H ⧸ Q.subgroupOf (pointTwoCoreImage H)) = Nat.card Q ^ 2 := by
    apply Nat.mul_left_cancel (Nat.card_pos (α := Q))
    calc
      Nat.card Q * Nat.card (pointTwoCoreImage H ⧸ Q.subgroupOf (pointTwoCoreImage H)) =
          Nat.card (pointTwoCoreImage H) := by
        rw [← hQMcard]
        exact (Q.subgroupOf (pointTwoCoreImage H)).card_mul_index
      _ = Nat.card Q ^ 3 := hcard
      _ = Nat.card Q * Nat.card Q ^ 2 := by ring
  exact ⟨hcop, hpOdd, hnot, hcard, hintersection, hjoin, hquotcard,
    y, hyJ, hy, hEcyc, hEcard, by simpa only [hquotcard] using hdiv⟩

end CFSG.ShultStronglyClosedTI.TwoCoreGrowthCoprime
