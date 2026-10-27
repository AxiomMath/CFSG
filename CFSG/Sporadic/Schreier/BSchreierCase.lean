module

public import CFSG.Monster.B.Final.PinnedBOrder
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseCbar
public import CFSG.LocalAnalysis.ComponentClassification.SporadicSchreierDispatch
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingOuterBound
public import Certificates.Certificate2049
public import Certificates.Certificate2051
public import Certificates.Certificate2053
public import Certificates.Certificate2054
public import Certificates.Certificate2055
public import Certificates.Certificate2056
public import Certificates.Certificate2057
public import Certificates.Certificate2058
public import Certificates.Certificate2059
public import Certificates.Certificate2060
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3027
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate6001
public import Certificates.Certificate6002
public import Certificates.Certificate6003
public import Certificates.Certificate6004
public import Certificates.Certificate6005
public import Certificates.Certificate6007
public import Certificates.Certificate16026
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Schreier.RuLocal
public import CFSG.Sporadic.SchreierLemmas.FrattiniProfile

public section

namespace CFSG.Sporadic.BSchreier

open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.SporadicSchreierDispatch

noncomputable def nativeBEquivCbar :
    NativeSporadic.B ≃* CFSG.Monster.B.Cbar :=
  (CFSG.Monster.B.pinned_B_explicit_native_isomorphism_simplicity_and_order.2.1.choose).trans
    (MulEquiv.inv' CFSG.Monster.B.Cbar).symm

theorem AT_B_model_Schreier :
    Group.IsSolvable (Outer NativeSporadic.B) ∧
      ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], (∃ a b : T, a * b ≠ b * a) →
        Nonempty (T ≃* NativeSporadic.B) → Group.IsSolvable (Outer T) := by
  have hB : Group.IsSolvable (Outer NativeSporadic.B) :=
    (@CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism NativeSporadic.B CFSG.Monster.B.Cbar
      Units.instGroup (QuotientGroup.Quotient.group _) nativeBEquivCbar).2.2
      CFSG.ComponentClassification.BMCase.native_B_generated_quotient_Schreier
  exact ⟨hB, fun T instT _ _ _ ⟨e⟩ =>
    (@CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism T NativeSporadic.B instT
      Units.instGroup e).2.2 hB⟩

theorem sporadicSchreierCase_B :
    SporadicSchreierCase .B :=
  sporadicSchreierCase_of_outer AT_B_model_Schreier.1

end CFSG.Sporadic.BSchreier
