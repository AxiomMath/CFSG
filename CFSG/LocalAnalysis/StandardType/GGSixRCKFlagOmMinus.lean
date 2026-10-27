module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKFlagOmGen

public section

namespace CFSG.StandardType.RCKFlag

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.StandardType.RCKC1 CFSG.Open
  CFSG.LieType.Universal

private theorem rckFlag_spinMatrix_injective_OmMinus (n g : ℕ) :
    Function.Injective (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 g)
      (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : GaloisField 2 g) = 0 := CharP.cast_eq_zero (GaloisField 2 g) 2
  exact (MonoidHom.ker_eq_bot_iff _).1
    (Spin.ker_spinMatrix_quadMinus_eq_bot (minusCoeffs_irr 2 g) h2)

theorem rckFlagIrredW_OmMinus (n g : ℕ) (hg : 1 ≤ g) :
    FlagIrredW (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 g)
        (minusCoeffs 2 g).1 (minusCoeffs 2 g).2))
      (some (QuadraticMap.polar (Spin.quadMinus n (GaloisField 2 g)
        (minusCoeffs 2 g).1 (minusCoeffs 2 g).2))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact rckFlagIrredW_quadratic (Spin.quadMinus n (GaloisField 2 g)
      (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)
    (fun x hx => (Spin.nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField 2 g)
      (minusCoeffs_irr 2 g)).1 x (fun y => by simpa using hx y))
    (rckFlag_spinMatrix_injective_OmMinus n g)

theorem rckFlagCent_OmMinus (n g : ℕ) (hg : 1 ≤ g) :
    FlagCentU (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 g)
        (minusCoeffs 2 g).1 (minusCoeffs 2 g).2))
      (some (QuadraticMap.polar (Spin.quadMinus n (GaloisField 2 g)
        (minusCoeffs 2 g).1 (minusCoeffs 2 g).2))) :=
  flagCentU_of_irredW _ _ (rckFlag_spinMatrix_injective_OmMinus n g)
    (rckFlagIrredW_OmMinus n g hg)

end CFSG.StandardType.RCKFlag
