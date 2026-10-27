module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BJ2V
import Certificates.Kernel.R148Dc.J2Facts
import Certificates.Kernel.R148Dc.J2CFact

public section

namespace Certificates

open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 (GJ xJ zJ Ej) in
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.J2 (tJ) in
open CFSG.RankThree.PartTwo.Sec14.Ronan148B.J2 (VJ) in
theorem certificate148014 :     (∀ Z : Subgroup GJ, Ej 0 ⊔ VJ 0 ≤ Z → Z = ⊤ ∨ Nat.card Z ∣ 2 ^ 7 * 3 ^ 3 ∨
      ∃ S : Set GJ, zJ ∈ S ∧ Nat.card S ≤ 4 ∧ ∀ y ∈ Z, ∀ s ∈ S, y * s * y⁻¹ ∈ S) ∧
    (∀ Z : Subgroup GJ, Ej 0 ⊔ VJ 3 ≤ Z → Z = ⊤ ∨ Nat.card Z ∣ 2 ^ 7 * 3 ^ 3 ∨
      ∃ S : Set GJ, zJ ∈ S ∧ Nat.card S ≤ 4 ∧ ∀ y ∈ Z, ∀ s ∈ S, y * s * y⁻¹ ∈ S) ∧
    ∃ c : GJ, c * xJ * c⁻¹ = xJ * zJ ∧ c * zJ * c⁻¹ = zJ ∧
      ∀ j < 6, ∀ p < 3, ∃ q < 3,
        c * tJ (3 * j + p) * c⁻¹ = tJ (3 * ((j + 1) % 3 + 3 * (j / 3)) + q) := by
  exact ⟨CFSG.KD.R148Dc.J2A.lat_facts, CFSG.KD.R148Dc.J2B.lat_facts, CFSG.KD.R148Dc.J2C.c_fact⟩

end Certificates
