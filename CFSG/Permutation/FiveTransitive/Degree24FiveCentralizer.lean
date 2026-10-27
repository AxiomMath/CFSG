module

public import CFSG.Permutation.FiveTransitive.Degree24LocalCentralizerSupport
public import CFSG.Permutation.FiveTransitive.Degree24FiveOrderIncidence
public import CFSG.Permutation.FiveTransitive.Degree24SylowFixedAction

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

theorem sylow_five_centralizer_card_dvd_seven_hundred_fifty
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 (fixingSubgroup P s))
    (hScard : Nat.card S = 5)
    (hfixed :
      Nat.card (sylowFixedPoints X P s S) = 9) :
    Nat.card
        (Subgroup.centralizer
          (S : Set (fixingSubgroup P s))) ∣
      750 := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
  letI : IsCyclic S :=
    isCyclic_of_prime_card hScard
  obtain ⟨u, huRaw⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have hu : orderOf u = 5 :=
    huRaw.trans hScard
  have huNe : u ≠ 1 := by
    intro huOne
    rw [huOne, orderOf_one] at hu
    omega
  let g : Equiv.Perm X := ((u : H) : P)
  have huH : orderOf (u : H) = 5 := by
    calc
      orderOf (u : H) = orderOf u :=
        Subgroup.orderOf_coe _
      _ = 5 := hu
  have hg : orderOf g = 5 := by
    calc
      orderOf g = orderOf ((u : H) : P) :=
        Subgroup.orderOf_coe _
      _ = orderOf (u : H) :=
        Subgroup.orderOf_coe _
      _ = 5 := huH
  have hfixedEq :
      sylowFixedPoints X P s S =
        Function.fixedPoints g := by
    simpa only [H, g] using
      sylowFixedPoints_eq_fixedPoints_generator
        X P s S hScard u huNe
  have hsupportCases :
      g.support.card = 10 ∨
        g.support.card = 15 := by
    simpa only [H, g] using
      order_five_mem_five_stabilizer_support_eq_ten_or_fifteen
        X P hcard h5 hnotAlt s hs (u : H) huH
  have hsupport : g.support.card = 15 := by
    rcases hsupportCases with hten | hfifteen
    · have hfixedFourteen :
          Nat.card (sylowFixedPoints X P s S) = 14 := by
        rw [hfixedEq, Nat.card_eq_fintype_card,
          Equiv.Perm.card_fixedPoints,
          Equiv.Perm.sum_cycleType, hcard, hten]
      omega
    · exact hfifteen
  have hgPrime : (orderOf g).Prime := by
    rw [hg]
    norm_num
  obtain ⟨k, hk⟩ :=
    Equiv.Perm.cycleType_prime_order hgPrime
  have hsum := g.sum_cycleType
  rw [hk, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hg, hsupport] at hsum
  have hkThree : k + 1 = 3 := by
    omega
  have hgCycleType : g.cycleType = {5, 5, 5} := by
    rw [hk, hg, hkThree]
    norm_num
  let gSupport : Equiv.Perm g.support :=
    g.subtypePerm (fun _ => g.apply_mem_support)
  have hgSupportExtend :
      Equiv.Perm.ofSubtype gSupport = g := by
    exact Equiv.Perm.ofSubtype_subtypePerm
      (fun _ => g.apply_mem_support)
      (fun x hx => Equiv.Perm.mem_support.mpr hx)
  have hgSupportCycleType :
      gSupport.cycleType = g.cycleType := by
    rw [← Equiv.Perm.cycleType_ofSubtype,
      hgSupportExtend]
  have hsupportSubtypeCard :
      Fintype.card g.support = 15 := by
    calc
      Fintype.card g.support = g.support.card :=
        Fintype.card_coe _
      _ = 15 := hsupport
  have hsupportCentralizerCard :
      Nat.card
          (Subgroup.centralizer
            ({gSupport} :
              Set (Equiv.Perm g.support))) = 750 := by
    rw [Equiv.Perm.nat_card_centralizer,
      hgSupportCycleType, hgCycleType,
      hsupportSubtypeCard]
    norm_num
  have hdvd :
      Nat.card
          (Subgroup.centralizer
            ((S : Subgroup H) : Set H)) ∣
        Nat.card
          (Subgroup.centralizer
            ({gSupport} :
              Set (Equiv.Perm g.support))) := by
    simpa only [H, g, gSupport] using
      local_centralizer_card_dvd_support_centralizer
        X P hcard h5 hnotAlt s hs
          (S : Subgroup H) u (by
            change 12 ≤ g.support.card
            omega)
  have hSset :
      ((S : Subgroup H) : Set H) = (S : Set H) :=
    rfl
  rw [hSset] at hdvd
  rw [hsupportCentralizerCard] at hdvd
  simpa only [H] using hdvd

end FiveTransitive.Degree24

end CFSG
