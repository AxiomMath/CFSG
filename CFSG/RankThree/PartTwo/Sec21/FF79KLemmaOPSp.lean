module

public import Mathlib
public import CFSG.Open.StatedDefs
public import CFSG.RankThree.PartTwo.Sec21.FF79KLemmaOSp

import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256h

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremB.MovingAround

theorem lemmaO_symplectic_gen {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) {r ℓ f : ℕ} (hm : StatedClassicalModel S .PSp r ℓ f)
    (hℓ3 : ℓ ≠ 3) {α : MulAut S} (hα : α ^ 3 = 1) (hout : ∀ c : S, α ≠ MulAut.conj c)
    {K : Subgroup S}
    (hK : CFSG.Open.IsComponentOf K (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α))
    (hA : Nonempty (↥K ≃* alternatingGroup (Fin 5))) : False := by
  have h3f := three_dvd_of_outer_psp hm hα hout
  have hℓ : 2 ≤ ℓ := hm.1.1.two_le
  have hf3 : 3 ≤ f := Nat.le_of_dvd (Nat.pos_of_ne_zero fun h => by
    have := hm.1.2.1; omega) h3f
  have h8 : 8 ≤ ℓ ^ f :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ ℓ ^ 3 := Nat.pow_le_pow_left hℓ 3
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right (by omega) hf3
  obtain ⟨eA⟩ := hA
  exact Inputs256h.noA5_psp hna hm hℓ3 h8 hα hK (nonempty_centerQuot_a5 eA)

end CFSG.RankThree.PartTwo.Sec21.FF79
