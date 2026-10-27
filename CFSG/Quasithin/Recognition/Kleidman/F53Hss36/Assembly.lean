module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.EndgameE3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Hss32Final
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Assembly2

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher Equiv
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

structure Hss36Inputs (H M S : Subgroup G) : Prop where
  claim4 : Claim4Spec H M S
  claim5 : Claim5Spec H M S
  claim6 : Claim6Spec H M S
  ivBound : IvBoundSpec H M S
  star : StarSpec H M S

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem false_of_inputs (hin : Hss36Inputs H M S) (hH6 : FactH6 G) (hH7 : FactH7)
    (hH8 : FactH8) (hH11 : FactH11) (hH12 : FactH12) : False := by
  have hb5 := C.hb5
  obtain ⟨h4, h5, h6, hI8, hstar⟩ := hin
  obtain ⟨P⟩ := critPath_nonempty C.hc
  have h7 := C.seven h4 hH8 h6 hI8 hH7 hH6 hstar hH11 hH12 P
  have hb := C.bMin_eq_five h4 h5 P h7
  obtain ⟨μ, C'⟩ := C.exists_mirror
  have hμ : μ ∈ nbrs α' := mem_nbrs_comm C'.hc.adj
  have hd : dist μ β = bMin H M := C'.hc.dist_eq
  set P' := mirrorPath P hμ hd (by omega) with hP'
  have h7' := C'.seven h4 hH8 h6 hI8 hH7 hH6 hstar hH11 hH12 P'
  have hP'γ : P'.γ = P.p 2 := by
    show P'.p (bMin H M - 1) = P.p 2
    rw [hP', mirrorPath_p P hμ hd (by omega) (by omega)]
    congr 1
    omega
  have hP'δ : P'.δ = P.p 3 := by
    show P'.p (bMin H M - 2) = P.p 3
    rw [hP', mirrorPath_p P hμ hd (by omega) (by omega)]
    congr 1
    omega
  exact C.false_of_five h4 h5 h6 hI8 hH8 hH11 hH12 hb P h7 C' P' h7' hP'γ hP'δ

end Ctx

theorem hss36NatAt_of_inputs (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (h34 : Hss34At H M)
    (hin : Hss36Inputs H M S) (hH6 : FactH6 G) (hH7 : FactH7) (hH8 : FactH8) (hH11 : FactH11)
    (hH12 : FactH12) : Hss36NatAt H M := by
  intro α β α' hc hv hcomm hnat
  obtain ⟨hZα, hZβ, hb1, -⟩ := h34 α β α' hc hv hcomm
  have hodd : Odd (bMin H M) := (hss114_ab hA hc hcomm hb1).2.1
  by_contra hb3
  have hb5 : 5 ≤ bMin H M := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have C : Ctx H M S α β α' := ⟨hA, hss28At_of_hss26A hA h26, hss32At_of_hss26A_only hA h26, hc, hv,
    hcomm, hZα, hZβ, hnat, hb5⟩
  exact C.false_of_inputs hin hH6 hH7 hH8 hH11 hH12

end CFSG.Quasithin.Kleidman.F53Hss36
