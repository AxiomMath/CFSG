
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzThreeInputs
public import CFSG.Sporadic.SuzOddCore.Perms
public import CFSG.RankThree.Native.PermEnumeration
import Certificates.Kernel.SuzThree13637.Glue
import CFSG.Sporadic.SuzOddCore.ArraysCheckInputs
import CFSG.Sporadic.SuzOddCore.SmallChainCheckInputs
meta import CFSG.Sporadic.SuzOddCore.ArraysCheck
meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Certificates.LiftedSchreierData

public section

namespace Certificates

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT CFSG.RankThree.Native in
open CFSG.Sporadic.SuzOddCore (suzM) in
open CFSG.Monster.B.Co2 (permOfArr) in
theorem certificate13637 :
    Subgroup.closure (permsA 1782 (qGensS ())) ≤ suzM ∧
    Nat.card (Subgroup.closure (permsA 1782 (qGensS ()))) = 2187 ∧
    (∀ i < 5, CFSG.RankThree.Native.validA 1782 (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.dGens ())[i]! = true ∧ CFSG.Monster.B.Co2.permOfArr 1782 (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.dGens ())[i]! ∈ suzM ∧
      CFSG.Monster.B.Co2.permOfArr 1782 (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.dGens ())[i]! ^ 3 = 1) ∧
    (∀ i < 5, ∀ j < 5, Commute (CFSG.Monster.B.Co2.permOfArr 1782 (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.dGens ())[i]!) (CFSG.Monster.B.Co2.permOfArr 1782 (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.dGens ())[j]!)) ∧
    (∀ k < 243, ∀ k' < 243, CFSG.Monster.B.Co2.permOfArr 1782 (dElts ())[k]! = CFSG.Monster.B.Co2.permOfArr 1782 (dElts ())[k']! →
      k = k') ∧
    (∀ B : Subgroup (Equiv.Perm (Fin 1782)), (∀ b ∈ B, ∃ k < 243, b = CFSG.Monster.B.Co2.permOfArr 1782 (dElts ())[k]!) →
      Nat.card B * 3 = 243 → ∀ c ∈ Subgroup.centralizer (B : Set (Equiv.Perm (Fin 1782))) ⊓ suzM,
        ∃ k < 243, c = CFSG.Monster.B.Co2.permOfArr 1782 (dElts ())[k]!) ∧
    CFSG.RankThree.Native.validA 1782 (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.yArr (levels ())) = true ∧ CFSG.Monster.B.Co2.permOfArr 1782 (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.yArr (levels ())) ∈ suzM ∧
    CFSG.Monster.B.Co2.permOfArr 1782 (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.yArr (levels ())) ^ 3 = 1 ∧ CFSG.Monster.B.Co2.permOfArr 1782 (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.yArr (levels ())) ≠ 1 ∧
    Subgroup.closure (permsA 1782 (cGens (levels ()))) =
      Subgroup.centralizer ({CFSG.Monster.B.Co2.permOfArr 1782 (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.yArr (levels ()))} : Set (Equiv.Perm (Fin 1782))) ⊓
        suzM ∧
    Nat.card (Subgroup.closure (permsA 1782 (cGens (levels ())))) = 3240 ∧
    CFSG.RankThree.Native.enumOK 1782 (cGens (levels ())) cKeys (cCert (levels ())) = true ∧
    (∀ w ∈ Subgroup.closure (permsA 1782 (cGens (levels ()))), w ≠ 1 → (w ^ 2 = 1 ∨ w ^ 5 = 1) →
      Nat.card ↥(Subgroup.centralizer ({w} : Set (Equiv.Perm (Fin 1782))) ⊓
        Subgroup.closure (permsA 1782 (cGens (levels ())))) < 81) ∧
    (∀ x ∈ suzM, orderOf x = 3 → ∃ h ∈ suzM, (∃ k < 243, h * x * h⁻¹ = CFSG.Monster.B.Co2.permOfArr 1782 (dElts ())[k]!) ∨
      h * x * h⁻¹ = CFSG.Monster.B.Co2.permOfArr 1782 (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.yArr (levels ())) ∨
      h * x * h⁻¹ = CFSG.Monster.B.Co2.permOfArr 1782 (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.yArr (levels ())) ^ 2) := CFSG.KD.SuzThree13637.body13637

end Certificates
