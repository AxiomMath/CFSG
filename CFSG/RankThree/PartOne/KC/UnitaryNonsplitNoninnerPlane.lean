module

public import CFSG.RankThree.PartOne.KC.UnitaryNoninnerPlaneGeneral
public import CFSG.RankThree.PartOne.KC.UnitaryNonsplitInnerActorCommutators
public import CFSG.RankThree.Classical.SteinbergBTNonsplitUnitaryPrimeSubfield

public section

namespace CFSG.RankThree.PartOne

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.Classical

theorem nonsplit_unitary_noninner_plane_local_core_product_odd :
    NonsplitUnitaryNoninnerPlaneLocalCoreOdd := by
  intro ℓ f n p K _ h hp hp3 hpℓ hpq hn hne B hB A hAB hAel hAcard hAnot
  have hg : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1) := fun hd => hpq (hd.trans (Nat.gcd_dvd_right _ _))
  exact unitary_noninner_plane_general h hn hne hp hp3 hpℓ hg
    (fun σ hσ => by
      obtain ⟨-, -, -, -, -, -, -, -, -, hsim, hexc72⟩ :=
        nonsplit_unitary_prime_subfield_fixed_group_and_full_centralizer h hn hne hp hp3 hpℓ hpq
          σ hσ
      exact ⟨hsim, fun h' => (hexc72 h').2⟩)
    (fun h3q B hB t ht htp A hAB hA =>
      (nonsplit_unitary_inner_actor_local_core_commutators_odd h h3q hn hp hp3 hpℓ hpq B hB t ht
        htp A hAB hA).1)
    B hB A hAB hAel hAcard hAnot

end CFSG.RankThree.PartOne
