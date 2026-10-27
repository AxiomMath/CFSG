module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKSymplectic
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelSpNormal
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelConj

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {k n : ℕ} {F : Type} [Field F] [Finite F]

theorem exists_mem_normalizer_conj_ne_statedSp (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    {t₀ : ↥(StatedSp k F)} (ht : IsSymplecticTransvectionIn k t₀)
    (P : Sylow 2 ↥(StatedSp k F)) (hP : ∀ p ∈ (P : Subgroup ↥(StatedSp k F)), p * t₀ = t₀ * p) :
    ∃ d ∈ Subgroup.normalizer ((P : Subgroup ↥(StatedSp k F)) : Set ↥(StatedSp k F)),
      d * t₀ * d⁻¹ ≠ t₀ := by
  obtain ⟨d₀, t₁, hd₀, hne, hC⟩ := borel86_spn_exists_conj_ne hF hn ht
  exact borel86_conj_exists_mem_normalizer_conj_ne P hP hd₀ hC hne

end CFSG.LocalAnalysis.WeakClosure81

end
