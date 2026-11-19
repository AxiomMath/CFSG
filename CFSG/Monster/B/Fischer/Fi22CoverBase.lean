
module

public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Monster.B.Fischer.Fi22OuterBase

@[expose] public noncomputable section

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates CFSG.Certificates.ChainArrays CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

theorem fi22OuterLines3510_bound : ∀ f < 10,
    (fi22OuterLines3510.getD f (0, 0)).1 + (fi22OuterLines3510.getD f (0, 0)).2 ≤ 151 := by
  decide

theorem orderOf_eq_two_of_eqA {t : Array ℕ} {g : Equiv.Perm (Fin 3510)} (ht : Rep 3510 t g)
    (h1 : eqA 3510 t (idA 3510) = false)
    (h2 : eqA 3510 (compA 3510 t t) (idA 3510) = true) : orderOf g = 2 := by
  refine orderOf_eq_prime ?_ fun hg => ?_
  · rw [pow_two]
    exact eq_of_eqA (rep_compA ht ht) rep_idA h2
  · rw [← Bool.not_eq_true, eqA_iff ht rep_idA] at h1
    exact h1 hg

theorem fi22OuterR_length : fi22OuterR.length = 256 := by
  simp only [fi22OuterR, fi22FinList, List.length_map, fi22OuterTPointsNat, hex3List,
    List.length_range]

theorem fi22OuterChainT_baseCount : fi22OuterChainT.baseCount = 6 := rfl

def fi22TProd (x : Fin 1024 × Fin 32 × Fin 4) : Equiv.Perm (Fin 3510) :=
  levT 3510 (fi22OuterStrong3510 4) #[0, 1, 2, 3, 6, 4] 0 x.1 *
    levT 3510 (fi22OuterStrong3510 4) #[0, 1, 2, 3, 6, 4] 1 x.2.1 *
    levT 3510 (fi22OuterStrong3510 4) #[0, 1, 2, 3, 6, 4] 2 x.2.2

end CFSG.Monster.B.Fischer
