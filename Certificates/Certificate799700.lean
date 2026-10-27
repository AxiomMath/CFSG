module

public import CFSG.RankThree.PartTwo.Sec21.FF81GL6Defs
import Certificates.Kernel.FF81Forms.Glue
public import Certificates.Certificate113

public section

namespace Certificates

open Matrix CFSG.RankThree.PartTwo.Sec21.FF81.GL6 in
theorem certificate799700 : ∀ P : Matrix (Fin 6) (Fin 6) (ZMod 2), Pᵀ = P → (∀ i, P i i = 0) → P ≠ J0 →
    ∃ s w : G6, s ∈ Sp0 ∧ w * u0 = u0 * w ∧ w ∉ Sp0 ∧
      (w : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ *
          ((s : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ * P * (s : Matrix (Fin 6) (Fin 6) (ZMod 2))) *
          (w : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        (s : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ * P * (s : Matrix (Fin 6) (Fin 6) (ZMod 2)) :=
  CFSG.KD.FF81F.forms_witness

end Certificates
