module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Chain
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43CoverData
public import CFSG.Sporadic.SmallOddCore.CentSpec
import Certificates.Kernel.U43Cube.Glue

public section

namespace Certificates

open CertificateChecks.KernelU43Cube.Glue

open CFSG.EvenSporadicStandard.HSStd.U43 CFSG.EvenSporadicStandard.M24Std.CU43
  CFSG.Sporadic.SmallOddCore in
theorem certificate27271 : (CFSG.Sporadic.SmallOddCore.tp 820 yATab ∈ P ∧ CFSG.Sporadic.SmallOddCore.tp 820 yBTab ∈ P ∧ CFSG.Sporadic.SmallOddCore.tp 820 yCTab ∈ P ∧ CFSG.Sporadic.SmallOddCore.tp 820 yDTab ∈ P) ∧
    (orderOf (CFSG.Sporadic.SmallOddCore.tp 820 yATab) = 3 ∧ orderOf (CFSG.Sporadic.SmallOddCore.tp 820 yBTab) = 3 ∧ orderOf (CFSG.Sporadic.SmallOddCore.tp 820 yCTab) = 3 ∧
      orderOf (CFSG.Sporadic.SmallOddCore.tp 820 yDTab) = 3) ∧
    (Nat.card ↥(P ⊓ Subgroup.centralizer ({CFSG.Sporadic.SmallOddCore.tp 820 yATab} : Set (Equiv.Perm (Fin 820)))) = 5832 ∧
      Nat.card ↥(P ⊓ Subgroup.centralizer ({CFSG.Sporadic.SmallOddCore.tp 820 yBTab} : Set (Equiv.Perm (Fin 820)))) = 972 ∧
      Nat.card ↥(P ⊓ Subgroup.centralizer ({CFSG.Sporadic.SmallOddCore.tp 820 yCTab} : Set (Equiv.Perm (Fin 820)))) = 972 ∧
      Nat.card ↥(P ⊓ Subgroup.centralizer ({CFSG.Sporadic.SmallOddCore.tp 820 yDTab} : Set (Equiv.Perm (Fin 820)))) = 81) ∧
    ∀ β ∈ P, β * β * β = 1 → β ≠ 1 → ∃ g ∈ P,
      β = g * CFSG.Sporadic.SmallOddCore.tp 820 yATab * g⁻¹ ∨ β = g * CFSG.Sporadic.SmallOddCore.tp 820 yBTab * g⁻¹ ∨ β = g * CFSG.Sporadic.SmallOddCore.tp 820 yCTab * g⁻¹ ∨
        β = g * CFSG.Sporadic.SmallOddCore.tp 820 yDTab * g⁻¹ :=
  ⟨⟨yA_facts.2.1, yB_facts.2.1, yC_facts.2.1, yD_facts.2.1⟩,
    ⟨yA_facts.2.2, yB_facts.2.2, yC_facts.2.2, yD_facts.2.2⟩, ⟨cardA, cardB, cardC, cardD⟩,
    fun β hβ h3 h1 => by
      obtain ⟨c, hc, g, hg, h⟩ := cover β hβ h3 h1
      refine ⟨g, hg, ?_⟩
      interval_cases c
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))⟩

end Certificates
