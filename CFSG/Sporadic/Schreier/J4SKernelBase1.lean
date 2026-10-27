
module

public import CFSG.Sporadic.Schreier.J4SKernelBase

public import CFSG.Sporadic.Schreier.J4SFiveBase1
public import CFSG.Sporadic.Schreier.J4SPointwise
public meta import CFSG.Sporadic.J4.PrimSpec
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import Certificates.Certificate2173
public import CFSG.Sporadic.Schreier.J4SPrimes
public meta import CFSG.Sporadic.Schreier.J4SPrimes
public import CFSG.Sporadic.J4.Local

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.LocalAnalysis.ComponentInitial MulAction

theorem conj_mem_N_of_mem_H : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N := fun _ hh n hn =>
  (Subgroup.mem_normalizer_iff.1 (H_le_normalizer hh) n).1 hn

theorem N_comm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
  intro a ha b hb
  obtain ⟨i, -, rfl⟩ := exists_η_eq ha
  obtain ⟨k, -, rfl⟩ := exists_η_eq hb
  rw [← η_xor, ← η_xor, Nat.xor_comm]

theorem isPGroup_N : IsPGroup 2 N := IsPGroup.of_card card_N

theorem classes_check : ∀ c ∈ ({2, 5, 6} : Finset (Fin 7)), ∀ T : Finset (Fin 7),
    (c ∈ T → (∑ i ∈ T, subSizesF i) ∣ 501397585920 → T = {c}) ∧
      ((∑ i ∈ T, subSizesF i) = subSizesF c → T = {c}) :=
  Certificates.certificate2173

end CFSG.Sporadic.J4Schreier
