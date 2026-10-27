module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bModelW0

public section

namespace CFSG.Quasithin.H13.C1294.Model

open CFSG.Quasithin

theorem Eev_e0 : ∀ c : VM, inU c → Eev c e0 = e0 := by
  intro c ⟨h1, h2⟩
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [Eev, bM, qM, e0, mkV, ex, xp, yp, dotProduct, Fin.sum_univ_three, h1, h2]

theorem Eev_qM : ∀ c v : VM, inU c → qM (Eev c v) = qM v := by
  intro c v ⟨h1, h2⟩
  have h : (2 : ZMod 2) = 0 := rfl
  simp only [Eev, bM, qM, e0, mkV, ex, xp, yp, dotProduct, Fin.sum_univ_three, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Sum.elim_inl, Sum.elim_inr, h1, h2]
  simp [Pi.single_apply]
  ring_nf
  simp [h]

theorem Eev_involutive : ∀ c v : VM, inU c → Eev c (Eev c v) = v := by
  intro c v ⟨h1, h2⟩
  have h : (2 : ZMod 2) = 0 := rfl
  have h' : (4 : ZMod 2) = 0 := rfl
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [Eev, bM, qM, e0, mkV, ex, xp, yp, dotProduct, Fin.sum_univ_three, h1, h2,
      Pi.single_apply] <;> ring_nf <;> simp [h, h']

end CFSG.Quasithin.H13.C1294.Model

end
