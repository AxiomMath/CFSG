module

public import CFSG.LocalAnalysis.StandardType.GGK1ADefs

public section

namespace CFSG.StandardType

lemma ggK1A_glEnd_eq_toLin {N : ℕ} {K : Type} [Field K] (g : GL (Fin N) K) :
    ggK1A_glEnd g = (Matrix.GeneralLinearGroup.toLin g : Module.End K (Fin N → K)) := by
  rw [ggK1A_glEnd]
  change Matrix.toLin' (g : Matrix (Fin N) (Fin N) K) = _
  rw [Matrix.GeneralLinearGroup.coe_toLin]
  rfl

lemma ggK1A_glEnd_one {N : ℕ} {K : Type} [Field K] :
    ggK1A_glEnd (1 : GL (Fin N) K) = 1 := by
  simp [ggK1A_glEnd, Module.End.one_eq_id]

lemma ggK1A_glEnd_mul {N : ℕ} {K : Type} [Field K] (a b : GL (Fin N) K) :
    ggK1A_glEnd (a * b) = ggK1A_glEnd a * ggK1A_glEnd b := by
  simp only [ggK1A_glEnd, Units.val_mul, Matrix.toLin'_mul, Module.End.mul_eq_comp]

lemma ggK1A_glEnd_pow {N : ℕ} {K : Type} [Field K] (g : GL (Fin N) K) (k : ℕ) :
    ggK1A_glEnd (g ^ k) = ggK1A_glEnd g ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, ggK1A_glEnd_one]
  | succ k ih => rw [pow_succ, pow_succ, ggK1A_glEnd_mul, ih]

lemma ggK1A_glEnd_injective {N : ℕ} {K : Type} [Field K] :
    Function.Injective (ggK1A_glEnd (N := N) (K := K)) :=
  fun _ _ h => Units.ext (Matrix.toLin'.injective h)

end CFSG.StandardType

end
