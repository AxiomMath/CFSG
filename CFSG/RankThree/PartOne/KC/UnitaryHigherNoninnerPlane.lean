module

public import CFSG.RankThree.PartOne.KC.UnitaryNoninnerPlaneGeneral
public import CFSG.RankThree.PartOne.KC.UnitaryHigherInnerPrimeCommutators
public import CFSG.RankThree.Classical.SteinbergBTHigherUnitaryPrimeSubfield

public section

namespace CFSG.RankThree.PartOne

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.Classical

theorem higher_unitary_noninner_plane_local_core_product_odd :
    HigherUnitaryNoninnerPlaneLocalCoreOdd := by
  intro ℓ f n p K _ h hp hpℓ hn3 hnp hne B hB A hAB hAel hAcard hAnot
  have hp3 : 3 < p := by omega
  have hg : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1) := fun hd => by
    have h1 := Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by omega)) hd
    have h2 := Nat.gcd_le_left (ℓ ^ f + 1) (by omega : 0 < n)
    omega
  obtain ⟨hcard, hpf, h2p, h3q, hSa, hI, ht⟩ := unitary_noninner_plane_general h hn3 hne hp hp3
    hpℓ hg
    (fun σ hσ => by
      obtain ⟨-, -, -, -, -, -, -, -, -, hsim, hexc72⟩ :=
        higher_unitary_prime_subfield_fixed_group_and_full_centralizer h hn3 hnp hp hne σ hσ
      exact ⟨hsim, fun h' => (hexc72 h').2⟩)
    (fun h3q B hB t ht htp A hAB hA =>
      (higher_unitary_inner_prime_local_core_commutators_odd h h3q hn3 hnp hp hpℓ B hB t ht htp A
        hAB hA).1)
    B hB A hAB hAel hAcard hAnot
  exact ⟨hpf, h2p, h3q, hcard, hSa, hI, fun t htA ht1 => ⟨(ht t htA ht1).1, (ht t htA ht1).2.1⟩⟩

end CFSG.RankThree.PartOne
