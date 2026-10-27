module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKFlagOmGen

public section

namespace CFSG.StandardType.RCKFlag

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.StandardType.RCKC1 CFSG.Open
  CFSG.LieType.Universal

private theorem rckFlag_spinMatrix_injective_OmPlus (n g : ℕ) :
    Function.Injective (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 g))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : GaloisField 2 g) = 0 := CharP.cast_eq_zero (GaloisField 2 g) 2
  exact (MonoidHom.ker_eq_bot_iff _).1 (Spin.ker_spinMatrix_quadPlus_eq_bot h2)

theorem rckFlagIrredW_OmPlus (n g : ℕ) (hg : 1 ≤ g) :
    FlagIrredW (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 g)))
      (some (QuadraticMap.polar (Spin.quadPlus n (GaloisField 2 g)))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact rckFlagIrredW_quadratic (Spin.quadPlus n (GaloisField 2 g))
    (fun x hx => (Spin.nondegenerate_polarBilin_quadPlus n (GaloisField 2 g)).1 x
      (fun y => by simpa using hx y))
    (rckFlag_spinMatrix_injective_OmPlus n g)

theorem rckFlagCent_OmPlus (n g : ℕ) (hg : 1 ≤ g) :
    FlagCentU (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 g)))
      (some (QuadraticMap.polar (Spin.quadPlus n (GaloisField 2 g)))) :=
  flagCentU_of_irredW _ _ (rckFlag_spinMatrix_injective_OmPlus n g)
    (rckFlagIrredW_OmPlus n g hg)

end CFSG.StandardType.RCKFlag
