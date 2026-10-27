module

public import CFSG.Sporadic.Schreier.CountSpec

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

variable {n : ℕ}

@[expose] def orderTables (Q : RawSchreierDatum n) (m : ℕ) : List Table :=
  filterProducts n (ordTest n m) (levelTables Q) (idT n) []

theorem forall₂_orderTables (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) {m : ℕ} (hm : 0 < m) :
    List.Forall₂ (Rep n) (orderTables Q m)
      ((enumeration Q).filter fun h => decide (orderOf h = m)).reverse := by
  have h := filterProducts_spec (P := fun h : Equiv.Perm (Fin n) => orderOf h = m)
    (fun T g hT => ordTest_iff perm_faithful hT hm) (forall₂_levelTables hn Q) (Rep.idT hn)
    (acc := []) (accG := []) List.Forall₂.nil
  simp only [one_mul, List.map_id', List.append_nil] at h
  exact h

theorem card_orderOf_coe (H : Subgroup (Equiv.Perm (Fin n))) (m : ℕ) :
    Nat.card {x : H // orderOf x = m} = Nat.card {x : H // orderOf (x : Equiv.Perm (Fin n)) = m} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [Subgroup.orderOf_coe])

theorem card_orderOf_eq (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {m : ℕ} (hm : 0 < m) :
    Nat.card {x : Q.originalSubgroup // orderOf x = m} = (orderTables Q m).length := by
  rw [(forall₂_orderTables hn Q hm).length_eq, List.length_reverse,
    ← List.countP_eq_length_filter, card_orderOf_coe,
    card_subtype_eq_countP Q.originalSubgroup (enumeration Q) (enumeration_nodup Q hQ)
      (mem_enumeration_iff Q hQ) (fun h => orderOf h = m)]

theorem card_image_pairs_eq (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {mx my r s : ℕ} (hmx : 0 < mx) (hmy : 0 < my) (hr : 0 < r) (hs : 0 < s) :
    Nat.card {p : Q.originalSubgroup × Q.originalSubgroup // orderOf p.1 = mx ∧
      orderOf p.2 = my ∧ orderOf (p.1 * p.2) = r ∧ orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = s} =
      pairCount (orderTables Q mx) (orderTables Q my) (pairTest n r s mx my) := by
  set L := enumeration Q
  have hcoe : ∀ p : Q.originalSubgroup × Q.originalSubgroup,
      (orderOf p.1 = mx ∧ orderOf p.2 = my ∧ orderOf (p.1 * p.2) = r ∧
        orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = s) ↔
      (orderOf (p.1 : Equiv.Perm (Fin n)) = mx ∧ orderOf (p.2 : Equiv.Perm (Fin n)) = my ∧
        (orderOf ((p.1 : Equiv.Perm (Fin n)) * p.2) = r ∧
          orderOf ((p.1 : Equiv.Perm (Fin n)) * p.2 * (p.1 : Equiv.Perm (Fin n))⁻¹ *
            (p.2 : Equiv.Perm (Fin n))⁻¹) = s)) := fun p => by
    simp only [← Subgroup.orderOf_coe, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hcoe),
    card_pairs_eq_sum Q.originalSubgroup L (enumeration_nodup Q hQ) (mem_enumeration_iff Q hQ)
      (fun h => orderOf h = mx) (fun h => orderOf h = my)
      (fun x y => orderOf (x * y) = r ∧ orderOf (x * y * x⁻¹ * y⁻¹) = s),
    pairCount_spec (forall₂_orderTables hn Q hmx) (forall₂_orderTables hn Q hmy)
      (R := fun x y => orderOf (x * y) = r ∧ orderOf (x * y * x⁻¹ * y⁻¹) = s) ?_,
    List.map_reverse, List.sum_reverse]
  · congr 1
    refine List.map_congr_left fun x _ => ?_
    rw [List.countP_reverse]
  · intro x xg y yg hx hy hxg hyg
    rw [List.mem_reverse, List.mem_filter, decide_eq_true_eq] at hxg hyg
    rw [pairTest_iff perm_faithful hx hy hr hs hxg.2 hyg.2 hmx hmy]

end CFSG.Sporadic.Schreier
