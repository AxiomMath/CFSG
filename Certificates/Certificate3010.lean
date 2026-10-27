module

public import Certificates.Certificate3010Base

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeData
import Certificates.Kernel.UnitarySix.ChainFacts
import Certificates.Kernel.UnitarySix.Sbar3010
import Certificates.Kernel.UnitarySix.Beta3010
import Certificates.Kernel.UnitarySix.Cent3010

public section

open CFSG.EvenSmallLie.UnitarySix CFSG.Sporadic.Schreier CFSG.Certificates
open scoped Pointwise

public section

namespace Certificates

open CertificateChecks.KernelU6

open CFSG.EvenSmallLie.UnitarySix CFSG.Sporadic.Schreier CFSG.Certificates
open scoped Pointwise

open CertificateChecks.KernelU6

theorem certificate3010 : 
      (chainsCheck = true)
    ∧ ((∀ x ∈ aGens, orderOf x = 2 ∧ ∀ y ∈ aGens, x * y = y * x) ∧
        (∀ k ∈ kGens ++ tGens, ∀ a ∈ aGens, k * a * k⁻¹ ∈ closureU aGens) ∧
        ∀ g ∈ tGens, g ∈ closureU kGens)
    ∧ ({p : Fin 693 | j3 p = p} = finSet 693 fixA ∧
        (∀ a ∈ aGens, ∀ p ∈ finSet 693 fixA, a p = p) ∧
        891 ≤ (Set.range fun g : closureU u62Letters => g • finSet 693 fixA).ncard)
    ∧ ((∀ a ∈ closureU aGens, a ≠ 1 → a ∈ conjClass (closureU kGens) j1 ∨
          a ∈ conjClass (closureU kGens) j2 ∨ a ∈ conjClass (closureU kGens) j3) ∧
        (conjClass (closureU kGens) j1).ncard = 21 ∧
        (conjClass (closureU kGens) j2).ncard = 210 ∧
        (conjClass (closureU kGens) j3).ncard = 280 ∧
        orderOf j1 = 2 ∧ orderOf j2 = 2 ∧ orderOf j3 = 2 ∧
        {p : Fin 693 | j1 p = p}.ncard = 181 ∧ {p : Fin 693 | j2 p = p}.ncard = 53 ∧
        {p : Fin 693 | j3 p = p}.ncard = 21 ∧
        ∀ k ∈ closureU kGens, (∀ a ∈ aGens, k * a = a * k) → k = 1)
    ∧ ((∀ u ∈ closureU sGens, orderOf u = 2 →
          ∃ r ∈ sReps, ∃ c ∈ closureU sGens, u = c * r * c⁻¹) ∧
        (∀ r ∈ sReps, orderOf r = 2) ∧
        (∀ p ∈ List.zip sConjs sReps, p.1 * p.2 * p.1⁻¹ ∈ closureU aGens) ∧
        (∀ g ∈ sGens, j1 * g = g * j1) ∧
        (∀ x ∈ closureU sGens, (∀ g ∈ sGens, x * g = g * x) → x = 1 ∨ x = j1) ∧
        ∀ r ∈ sReps,
          ({p : Fin 693 | r p = p}.ncard = 53 → 2 ≤ (conjClass (closureU sGens) r).ncard) ∧
          ({p : Fin 693 | r p = p}.ncard = 21 → 8 ≤ (conjClass (closureU sGens) r).ncard))
    ∧ ((∀ x ∈ closureU tGens, (∀ g ∈ tGens, x * g = g * x) ∨
          Nat.card {y : closureU tGens // (y : Equiv.Perm (Fin 693)) * x = x * y} ≤ 16) ∧
        Nat.card {x : closureU tGens // ∀ g ∈ tGens, (x : Equiv.Perm (Fin 693)) * g = g * x} ≤
          16 ∧
        (∀ x ∈ closureU tGens, x ≠ 1 →
          Nat.card {a : closureU aGens // (a : Equiv.Perm (Fin 693)) * x = x * a} ≤ 32) ∧
        (∀ x ∈ closureU tGens, x * x ≠ 1 →
          Nat.card {a : closureU aGens // (a : Equiv.Perm (Fin 693)) * x = x * a} ≤ 16) ∧
        ∀ b ∈ closureU tGens, ∀ c ∈ closureU tGens, b ≠ c → b ≠ 1 → c ≠ 1 → b * b = 1 →
          c * c = 1 → b * c = c * b →
          Nat.card {a : closureU aGens // (a : Equiv.Perm (Fin 693)) * b = b * a ∧
            (a : Equiv.Perm (Fin 693)) * c = c * a} ≤ 16)
    ∧ (orderOf o1 = 3 ∧ orderOf o2 = 3 ∧ o1 * j1 = j1 * o1 ∧ o2 * j1 = j1 * o2 ∧
        (o1 * o2) ^ 2 = j1 ∧ y2 ^ 2 = j2 ∧
        ∀ k ∈ closureU kGens, k * j3 = j3 * k → ∀ a ∈ closureU aGens, (a * k) ^ 2 ≠ j3)
    ∧ (betaCheck = true) := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := orbit3010
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := squareBase3010
  exact ⟨chains3010, struct3010, fix3010, ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, cent3010.1⟩,
    sylow3010, thompson3010, ⟨q1, q2, q3, q4, q5, q6, cent3010.2⟩, beta3010⟩

end Certificates

end
