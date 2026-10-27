module

public import CFSG.Permutation.FiveTransitive.SixPointNormalizerRotation
public import CFSG.Permutation.FiveTransitive.TripleOrbitDivisibility
public import CFSG.Permutation.FiveTransitive.OyamaThreeOrbitDegree

public section

namespace CFSG

namespace FiveTransitive.OyamaThreeOrbitDivisibility

open MulAction

private theorem three_divides_complement
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (horb:OyamaThreeOrbitOrders.ThreeOrbits G X) :
    3∣Nat.card X-3 := by
  obtain ⟨A,hA,hF,g,hg,hg3,hgfree,s,hs,hbase,hpres⟩ :=
    SixPointNormalizerRotation.exists_rotation hcond horb
  have heven:Even (Nat.card X) := Nat.even_iff.mpr
    (EvenSixDegreeBound.degree_mod_two (by have := hcond.1; omega) hcond.2.1)
  have hfour:OyamaTripleSylow.FourFixedSix G X := by
    intro t ht T
    exact (EvenSixTupleLocal.to_set_property hcond.2.1 t ht T).1
  exact TripleOrbitDivisibility.three_dvd heven hfour A hA hF g hg hg3 hgfree
    s hs hbase hpres (horb s hs)

theorem contradiction
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (horb:OyamaThreeOrbitOrders.ThreeOrbits G X) : False := by
  have hd := three_divides_complement hcond horb
  rcases OyamaThreeOrbitDegree.degree_ten_or_fourteen hcond horb with h|h <;>
    rw [h] at hd <;> norm_num at hd

end FiveTransitive.OyamaThreeOrbitDivisibility

end CFSG
