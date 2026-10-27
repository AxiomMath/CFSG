module

public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.Monster.B.Final.PinnedBOrder
import CFSG.LocalAnalysis.ComponentClassification.BMCaseCbar
import CFSG.LocalAnalysis.ComponentClassification.BMCaseGeneric
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
public import CFSG.Monster.AxisCount.BabyCount
public import CFSG.Monster.AxisCount.BabyCover
public import CFSG.Monster.AxisCount.BabyCoverCheck
public import CFSG.Monster.AxisCount.BabyCoverSpec
public import CFSG.Monster.AxisCount.BabyIdentCheck
public import CFSG.Monster.AxisCount.BabyInvCheck
public import CFSG.Monster.Visible.SignCompat
public import CFSG.Open.MonsterY443Defs
public import CFSG.Sporadic.Co1Base
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.Sporadic.Schreier.RuLocal
import CFSG.Sporadic.SchreierLemmas.FrattiniProfile

public section

open CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

namespace CFSG.RankThree.PartOne.SPOR

theorem allInner_B :
    ∀ α : MulAut (NativeSporadic.Carrier .B), ∃ g : NativeSporadic.Carrier .B,
      α = MulAut.conj g := by
  obtain ⟨-, ⟨e, -⟩, -⟩ :=
    CFSG.Monster.B.pinned_B_explicit_native_isomorphism_simplicity_and_order
  exact CFSG.ComponentClassification.BMCase.inner_of_equiv
    (e.trans (MulEquiv.inv' CFSG.Monster.B.Cbar).symm)
    CFSG.ComponentClassification.BMCase.cbar_inner

theorem card_outer_B :
    Nat.card (Outer (NativeSporadic.Carrier .B)) = 1 := by
  have h := CFSG.ComponentClassification.BMCase.subsingleton_outer_of_inner (allInner_B)
  exact Nat.card_eq_one_iff_unique.2 ⟨h, inferInstance⟩

end CFSG.RankThree.PartOne.SPOR
