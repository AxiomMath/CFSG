module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelUNormal
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelConj

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {m n : ℕ} {F : Type} [Field F] [Finite F]

theorem exists_mem_normalizer_conj_ne_statedProjSU (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 < n)
    (hm : 3 ≤ m) {t₀ : StatedProj (StatedSU m (2 ^ n) F)} (ht : IsUnitaryTransvectionIn m n t₀)
    (P : Sylow 2 (StatedProj (StatedSU m (2 ^ n) F)))
    (hP : ∀ p ∈ (P : Subgroup (StatedProj (StatedSU m (2 ^ n) F))), p * t₀ = t₀ * p) :
    ∃ d ∈ Subgroup.normalizer
        ((P : Subgroup (StatedProj (StatedSU m (2 ^ n) F))) :
          Set (StatedProj (StatedSU m (2 ^ n) F))),
      d * t₀ * d⁻¹ ≠ t₀ := by
  obtain ⟨d₀, t₁, hd₀, hne, hC⟩ := borel86_un_exists_conj_ne
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩ hn hm ht
  exact borel86_conj_exists_mem_normalizer_conj_ne P hP hd₀ hC hne

end CFSG.LocalAnalysis.WeakClosure81

end
