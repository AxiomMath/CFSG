
module

public import CFSG.Sporadic.Schreier.LyData

@[expose] public section

namespace CFSG.Sporadic.Ly

open CFSG.Sporadic.LySchreier CFSG.Sporadic.Ly.Omega MulAction

theorem zmod5_eq_one_of_pow : ∀ c : ZMod 5, c ^ 111 = 1 → c = 1 := by decide

theorem eq_one_of_scalar [LySeed] {g : J} {c : ZMod 5} (h : mat g = c • 1) : g = 1 := by
  have hdet := (det_and_form g).1
  rw [h, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  have hc : c = 1 := zmod5_eq_one_of_pow c hdet
  apply mat_injective
  rw [h, hc, one_smul, mat_one]

section


end

end CFSG.Sporadic.Ly
