module

public import CFSG.LocalAnalysis.StandardType.GGTBFixLabels
public import CFSG.LocalAnalysis.StandardType.GGTableB

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggTorusNoFix_of_irred {p r : ℕ} (hp : 1 < p) {R : Type} [Group R] {I : Set (MulAut R)}
    (h : GGTorusIrred p r R I) : GGTorusNoFix p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 a ha hfix
  obtain ⟨W, hW, hinv, -, -⟩ := h L' ψ hψ hker hperf A hA hAI hr h3
  have hap : a ^ p = 1 := hA.2 a ha
  have hle : Subgroup.zpowers a ≤ A := (Subgroup.zpowers_le).mpr ha
  have hinv' := hinv (Subgroup.zpowers a) hle (by
    intro n hn b hb
    have hfn : MulAut.conj n * a * (MulAut.conj n)⁻¹ = a := hfix n (hW n hn)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [show MulAut.conj n * a ^ k * (MulAut.conj n)⁻¹ =
        (MulAut.conj n * a * (MulAut.conj n)⁻¹) ^ k by simp [conj_zpow], hfn]
    exact Subgroup.zpow_mem_zpowers a k)
  rcases hinv' with hbot | htop
  · rw [Subgroup.zpowers_eq_bot] at hbot
    exact hbot
  · exfalso
    have hcard : Nat.card A ≤ p := by
      rw [← htop, Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by omega) hap
    have : p ^ 3 ≤ p := h3.trans hcard
    have hp3 : p < p ^ 3 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 3 := Nat.pow_lt_pow_right hp (by norm_num)
    omega

end CFSG.StandardType
