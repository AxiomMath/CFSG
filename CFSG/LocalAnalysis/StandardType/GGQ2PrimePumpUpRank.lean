module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpAut
public import CFSG.LocalAnalysis.StandardType.GGTableBRank

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models CFSG.Assembly CFSG.StandardType

theorem PumpUpAut.false_of_ggTorusLift {K : Type} [Group K] [Finite K] {W Wk : Subgroup K}
    {ζ ξ : MulAut K} {Q A : Subgroup (MulAut K)} (h : PumpUpAut W Wk ζ ξ Q A) {R : Type}
    [Group R] (e : K ⧸ center K ≃* R) {r : ℕ} (hr : 6 ≤ r) (hT : GGTorusLift 3 r R) : False := by
  set ψ : K →* R := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hψ : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker = center K := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk x) = 1 ↔ _
    rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff]
  obtain ⟨U, E, hU1, hU, hEU, hE, hEc, hEZ⟩ := hT K ψ hψ hker.le h.quasi.1
  have h1 := h.rank E U hE hU hU1 hEU
  rw [← hker, hEZ, Subgroup.card_bot, mul_one, hEc] at h1
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h1
  omega

end CFSG.GGQ2Prime
