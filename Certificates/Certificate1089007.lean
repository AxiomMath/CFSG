module

public import Certificates.Data.J2Sylow5Data
meta import Certificates.Data.J2Sylow5Data
meta import CFSG.Sporadic.Bridge.J2Native
meta import Mathlib.Data.ZMod.Basic

public section

namespace Certificates

theorem certificate1089007 : CFSG.Sporadic.Bridge.J2.toM CFSG.Sporadic.Bridge.J2.mP5a ^ 5 = 1 ∧
    CFSG.Sporadic.Bridge.J2.toM CFSG.Sporadic.Bridge.J2.mP5b ^ 5 = 1 ∧
    CFSG.Sporadic.Bridge.J2.toM CFSG.Sporadic.Bridge.J2.mP5a *
      CFSG.Sporadic.Bridge.J2.toM CFSG.Sporadic.Bridge.J2.mP5b =
        CFSG.Sporadic.Bridge.J2.toM CFSG.Sporadic.Bridge.J2.mP5b *
          CFSG.Sporadic.Bridge.J2.toM CFSG.Sporadic.Bridge.J2.mP5a ∧
    CFSG.Sporadic.Bridge.J2.toM CFSG.Sporadic.J2.Sylow5Data.mZg ^ 3 = 1 ∧
    CFSG.Sporadic.Bridge.J2.toM CFSG.Sporadic.J2.Sylow5Data.mZg *
      CFSG.Sporadic.Bridge.J2.toM CFSG.Sporadic.Bridge.J2.mP5a =
      (CFSG.Sporadic.Bridge.J2.toM CFSG.Sporadic.Bridge.J2.mP5a) ^ 4 *
        (CFSG.Sporadic.Bridge.J2.toM CFSG.Sporadic.Bridge.J2.mP5b) ^ 2 *
          CFSG.Sporadic.Bridge.J2.toM CFSG.Sporadic.J2.Sylow5Data.mZg ∧
    CFSG.Sporadic.Bridge.J2.toM CFSG.Sporadic.J2.Sylow5Data.mZg *
      CFSG.Sporadic.Bridge.J2.toM CFSG.Sporadic.Bridge.J2.mP5b =
      (CFSG.Sporadic.Bridge.J2.toM CFSG.Sporadic.Bridge.J2.mP5a) ^ 2 *
        CFSG.Sporadic.Bridge.J2.toM CFSG.Sporadic.J2.Sylow5Data.mZg ∧
    CFSG.Sporadic.Bridge.J2.toM CFSG.Sporadic.Bridge.J2.mP5a ≠ 1 ∧
    CFSG.Sporadic.Bridge.J2.toM CFSG.Sporadic.Bridge.J2.mP5b ≠ 1 ∧
    CFSG.Sporadic.Bridge.J2.toM CFSG.Sporadic.Bridge.J2.mP5b ≠
      CFSG.Sporadic.Bridge.J2.toM CFSG.Sporadic.Bridge.J2.mP5a ∧
    CFSG.Sporadic.Bridge.J2.toM CFSG.Sporadic.Bridge.J2.mP5b ≠
      (CFSG.Sporadic.Bridge.J2.toM CFSG.Sporadic.Bridge.J2.mP5a) ^ 2 ∧
    CFSG.Sporadic.Bridge.J2.toM CFSG.Sporadic.Bridge.J2.mP5b ≠
      (CFSG.Sporadic.Bridge.J2.toM CFSG.Sporadic.Bridge.J2.mP5a) ^ 3 ∧
    CFSG.Sporadic.Bridge.J2.toM CFSG.Sporadic.Bridge.J2.mP5b ≠
      (CFSG.Sporadic.Bridge.J2.toM CFSG.Sporadic.Bridge.J2.mP5a) ^ 4 :=
  by decide +kernel

end Certificates
