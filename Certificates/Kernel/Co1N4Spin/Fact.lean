module

public import Certificates.Kernel.Co1N4Spin.Check
public import Certificates.Kernel.Co1M.C10071
public import CFSG.Certificates.Kernel.F2AlgRankSound
public import CFSG.Sporadic.Co1.Module.LeechOddChecksInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCo1N4Spin

open CFSG.KC.F2AlgRank CFSG.KC.Co1F2 CertificateChecks.KernelCo1M CFSG.Sporadic.SmallF2
  CFSG.Sporadic.Co1.Module.Odd
open scoped Matrix

theorem t_isT2 : isT2 t = true := by
  exact (c71_isT2 t).trans (by quickRfl)

theorem t_lt : t < 2 ^ 24 := by decide

theorem t_ne : t ≠ code4 := by decide

theorem spinFact : ∀ U : Submodule (ZMod 2) (Fin 24 → ZMod 2), toVecD 24 code4 ∈ U →
    (∀ u ∈ U, rowsMatrix 24 (rr 23) *ᵥ u ∈ U) → (∀ u ∈ U, rowsMatrix 24 (rr 17) *ᵥ u ∈ U) →
    ∀ y ∈ U, y ∉ Submodule.span (ZMod 2) {toVecD 24 code4} →
    ∃ u ∈ U, u ≠ toVecD 24 code4 ∧ ∃ x < 2 ^ 24, toVecD 24 x = u ∧ isT2 x = true := by
  intro U hw h23 h17 y hy hyw
  have e23 : rr 23 = unpackR 24 (getL 0 cmRP71 23) := c71_rr (by rw [c71_len]; norm_num)
  have e17 : rr 17 = unpackR 24 (getL 0 cmRP71 17) := c71_rr (by rw [c71_len]; norm_num)
  have hG : ∀ g ∈ gens, ∀ u ∈ U, rowsMatrix 24 (unpackR 24 g) *ᵥ u ∈ U := by
    intro g hg
    simp only [gens, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · rw [← e23]
      exact h23
    · rw [← e17]
      exact h17
  have hc : code4 = 10075731 := rfl
  rw [hc] at hw hyw
  refine ⟨toVecD 24 t, sepK_sound sep_ok U hG hw hy hyw, fun e => ?_, t, t_lt, rfl, t_isT2⟩
  exact t_ne (toVecD_injective t_lt (by rw [hc]; norm_num) e)

end CertificateChecks.KernelCo1N4Spin

end
