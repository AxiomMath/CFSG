module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.M11Spec
import Certificates.Kernel.HN1408.M11Facts
import Certificates.Kernel.HN1408.M11Defs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeVSpec

public section

namespace Certificates

open CFSG.EvenSporadicStandard.HNRecog in
theorem certificate441602 :
    Nat.card ↥m11K = 7920 ∧ orderOf (elemW y0Word) = 11 ∧ orderOf (elemW vWord) = 11 ∧
      elemW y0Word * elemW vWord ≠ elemW vWord * elemW y0Word ∧
      (∀ w ∈ m11Relators, CFSG.Sporadic.Bridge.wordProd (fun i => if i = 0 then elemW y0Word else
        if i = 1 then elemW vWord else 1) w = 1) ∧
      (∀ g ∈ m11K, TwoHSData.M11Order (orderOf g)) ∧
      orderOf (elemW i0Word) = 2 ∧ elemW i0Word ∈ m11K ∧
      Subgroup.closure ({elemW y0Word, elemW i0Word} : Set (Equiv.Perm (Fin 1408))) = m11K ∧
      elemW n1Word * elemW y0Word * (elemW n1Word)⁻¹ = elemW y0Word ^ 7 ∧
      ((CFSG.Sporadic.SmallOddCore.conjClass P1408 elemZ).ncard = 5775 →
        ∀ g ∈ CFSG.Sporadic.SmallOddCore.conjClass P1408 elemZ, m11Prop g) ∧
      ((CFSG.Sporadic.SmallOddCore.conjClass P1408 (elemA * elemZ)).ncard = 5775 →
        ∀ g ∈ CFSG.Sporadic.SmallOddCore.conjClass P1408 (elemA * elemZ), m11Prop g) ∧
      orderOf (elemW rho0Word) = 5 ∧ elemW rho0Word ∈ m11K ∧
      (∀ k : ℕ, 0 < k → k < 5 → ∃ c ∈ m11K, c * elemW rho0Word * c⁻¹ = elemW rho0Word ^ k) ∧
      elemW cBWord * elemW rho0Word * (elemW cBWord)⁻¹ = elemW fix5B.rep := CFSG.KD.HN1408.m11_facts

end Certificates
