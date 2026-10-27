module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13OneBetaB
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13OneBetaC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem false_of_nonabelian_seven {t : MulAut W} {P : Subgroup (MulAut W)}
    (h : InvCfg131 7 t P) (hnab : ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x)
    (hcen : ∀ z ∈ P, (∀ y ∈ P, y * z = z * y) → t * z * t⁻¹ = z) : False := by
  obtain ⟨x, z, y, -, -, -, hx, hz, htx, htz, hxz, hyx, hyz⟩ := beta2_exists_heisenberg h hnab hcen
  exact false_of_heisenberg_seven h.hW h.ht h.hrk hx hz htx htz hxz hyx hyz

end CFSG.LocalAnalysis.WeakClosure81
