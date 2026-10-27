module

public import CFSG.Quasithin.EmptyFaithful.S146zNFinG

public section

namespace CFSG.Quasithin.A6Fin

open Equiv Equiv.Perm

@[expose] def w3 (p q : Perm (Fin 6)) : Perm (Fin 6) := p * q * p * (q * q * q) * p * q * q

theorem sign_x0P : sign x0P = 1 := by decide

theorem sign_y0P : sign y0P = 1 := by decide

set_option maxRecDepth 100000 in
theorem rel_x0y0 : x0P * x0P = 1 ∧ y0P * y0P * y0P * y0P = 1 ∧
    (x0P * y0P) * (x0P * y0P) * (x0P * y0P) * (x0P * y0P) * (x0P * y0P) = 1 ∧
    (x0P * (y0P * y0P)) * (x0P * (y0P * y0P)) * (x0P * (y0P * y0P)) * (x0P * (y0P * y0P)) *
      (x0P * (y0P * y0P)) = 1 := by
  unfold x0P y0P
  decide +kernel

set_option maxRecDepth 100000 in
theorem w3_x0y0 : w3 x0P y0P * w3 x0P y0P * w3 x0P y0P = 1 ∧ w3 x0P y0P ≠ 1 ∧
    ∃ i, w3 x0P y0P i = i := by
  unfold w3 x0P y0P
  decide +kernel

set_option maxRecDepth 100000 in
theorem cent_x0y0 : ∀ s : Perm (Fin 6), s * x0P = x0P * s → s * y0P = y0P * s → s = 1 := by
  unfold x0P y0P
  decide +kernel

set_option maxRecDepth 100000 in
theorem pairs_conj_x0 : ∀ q : Perm (Fin 6), q * q * q * q = 1 → sign q = 1 →
    (x0P * q) * (x0P * q) * (x0P * q) * (x0P * q) * (x0P * q) = 1 →
    (x0P * (q * q)) * (x0P * (q * q)) * (x0P * (q * q)) * (x0P * (q * q)) * (x0P * (q * q)) = 1 →
    w3 x0P q * w3 x0P q * w3 x0P q = 1 → w3 x0P q ≠ 1 → (∃ i, w3 x0P q i = i) →
    ∃ s : Perm (Fin 6), s * x0P = x0P * s ∧ s * y0P = q * s := by
  unfold w3 x0P y0P
  decide +kernel

end CFSG.Quasithin.A6Fin
