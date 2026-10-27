
module


public import Certificates.Certificate7039

public section

namespace CFSG.Quasithin.L34Amalgam

theorem module_unique (u : Fin 4 → Fin 16)
    (hu : ∀ x, lin u (lin u x) = x)
    (v : Fin 4 → Fin 16) (hv : ∀ x, lin v (lin v (lin v x)) = x)
    (hfpf : ∀ x, x ≠ 0 → lin v x ≠ x) (h5 : ∀ x, (lin u ∘ lin v)^[5] x = x) :
    ∃ w : Fin 16, (∀ x y, lin (conjMap u v w) x = lin (conjMap u v w) y → x = y) ∧
      (∀ x, lin (conjMap u v w) (lin refA x) = lin u (lin (conjMap u v w) x)) ∧
      ∀ x, lin (conjMap u v w) (lin refB x) = lin v (lin (conjMap u v w) x) :=
  Certificates.certificate7039 u hu v hv hfpf h5

end CFSG.Quasithin.L34Amalgam
