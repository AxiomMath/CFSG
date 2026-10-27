module

public import CFSG.Permutation.FiveTransitive.OneOrbitOrderFourSemiregular
public import CFSG.Permutation.FiveTransitive.OrderFourNormalizerPair

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.OneOrbitOrderFourCentralizerConsumer

open MulAction FixedNormalizerAction

private theorem pair_commute
    {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) (hQ : Nat.card Q = 4)
    (K : Subgroup (Normalizer Q))
    (hK2 : ∀ k : K, k ^ 2 = 1) (hKcomm : IsMulCommutative K)
    (a b c : K) (haQ : a.val ∈ Inside Q) (ha : a ≠ 1)
    (hbcard : Nat.card ((Subgroup.centralizer ({(b.val : G)} : Set G)).subgroupOf Q) = 2)
    (hccard : Nat.card ((Subgroup.centralizer ({(c.val : G)} : Set G)).subgroupOf Q) = 2) :
    ∀ q : Q, Commute (q : G) ((b.val : G) * (c.val : G)) := by
  let aQ : Q := ⟨a.val.val, haQ⟩
  have haQ1 : aQ ≠ 1 := by
    intro h
    have hval : a.val.val = 1 := congrArg (fun q : Q => q.val) h
    exact ha (Subtype.ext (Subtype.ext hval))
  have hcomm (k : K) : Commute k.val.val aQ.val := by
    exact congrArg (fun k : K => k.val.val) ((isMulCommutative_iff.mp hKcomm) k a)
  have hc2 : c.val.val * c.val.val = 1 := by
    simpa only [pow_two, Subgroup.coe_mul, Subgroup.coe_one] using
      congrArg (fun k : K => k.val.val) (hK2 c)
  have hp := OrderFourNormalizerPair.mul_mem_centralizer Q hQ aQ haQ1
    b.val c.val (hcomm b) (hcomm c) hbcard hccard hc2
  intro q
  exact Subgroup.mem_centralizer_iff.mp hp q.val q.property

theorem semiregular_of_centralizer_card_two
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (hmax : ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ 7)
    (Q : Subgroup G) (hQ : Nat.card Q = 4)
    (B K : Subgroup (Normalizer Q)) (hB : IsPGroup 2 B) (hKB : K ≤ B)
    (hker : B ⊓ (toPermHom (Normalizer Q) (Fixed (X := X) Q)).ker = Inside Q)
    (himage : K.map (toPermHom (Normalizer Q) (Fixed (X := X) Q)) =
      B.map (toPermHom (Normalizer Q) (Fixed (X := X) Q)))
    (hK2 : ∀ k : K, k ^ 2 = 1) (hKcomm : IsMulCommutative K)
    (a b c d : K) (haQ : a.val ∈ Inside Q) (ha : a ≠ 1)
    (e : Fin 6 ↪ Fixed (X := X) Q)
    (hb : toPermHom (Normalizer Q) (Fixed (X := X) Q) b.val = Equiv.swap (e 0) (e 1))
    (hc : toPermHom (Normalizer Q) (Fixed (X := X) Q) c.val = Equiv.swap (e 2) (e 3))
    (hd : toPermHom (Normalizer Q) (Fixed (X := X) Q) d.val = Equiv.swap (e 4) (e 5))
    (hbcard : Nat.card ((Subgroup.centralizer ({(b.val : G)} : Set G)).subgroupOf Q) = 2)
    (hccard : Nat.card ((Subgroup.centralizer ({(c.val : G)} : Set G)).subgroupOf Q) = 2)
    (hdcard : Nat.card ((Subgroup.centralizer ({(d.val : G)} : Set G)).subgroupOf Q) = 2)
    (O : Set X)
    (hsemi : ∀ (k : K) (z : X), z ∉ O → (k.val : G) • z = z → k = 1) :
    ∀ (u : B) (z : X), z ∉ O → (u.val : G) • z = z → u = 1 := by
  apply OneOrbitOrderFourSemiregular.semiregular_of_pair_central hmax Q hQ B K hB hKB
    hker himage hK2 hKcomm a b c d haQ ha e hb hc hd
    (pair_commute Q hQ K hK2 hKcomm a b c haQ ha hbcard hccard)
    (pair_commute Q hQ K hK2 hKcomm a b d haQ ha hbcard hdcard) O hsemi

end FiveTransitive.OneOrbitOrderFourCentralizerConsumer

end CFSG
