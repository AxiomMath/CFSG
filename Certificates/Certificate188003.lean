module

public import CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Stab
import Certificates.Kernel.Huppert.C188003Assembly

public section

namespace Certificates

open CFSG.Fischer CFSG.RankThree.PartTwo.Sec10.KS1012GL34 in
theorem certificate188003 :
    (∀ (t x w z : Matrix.GeneralLinearGroup (Fin 3) F4) (μ : F4),
      (μ = 1 ∨ μ = F4.ω ∨ μ = om2) → Good3 (t : Matrix (Fin 3) (Fin 3) F4) →
      (x : Matrix (Fin 3) (Fin 3) F4) = Xd → (w : Matrix (Fin 3) (Fin 3) F4) = Wm μ →
      (z : Matrix (Fin 3) (Fin 3) F4) = Zs →
      (∀ g ∈ SLsub, g ∈ Subgroup.closure ({x, w, z, t} : Set (Matrix.GeneralLinearGroup (Fin 3) F4))) ∨
        (μ = 1 ∧ ∃ i : Fin 6,
          Subgroup.closure ({x, w, z, t} : Set (Matrix.GeneralLinearGroup (Fin 3) F4)) = P i)) ∧
    (∀ (i : Fin 6) (Y : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)),
      P i < Y → Y ≤ SLsub → Y = SLsub) :=
  ⟨CFSG.KD.C188003.c188003_T3, CFSG.KD.C188003.c188003_T4⟩

end Certificates
