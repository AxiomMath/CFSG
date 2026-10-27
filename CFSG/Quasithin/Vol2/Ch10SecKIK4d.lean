module

public import CFSG.Quasithin.Vol2.Ch10SecKIK4c
public import CFSG.Quasithin.EmptyFaithful.T1515dA

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement IsMulCommutative

section List


theorem not_naturalList2 {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {U Z : Subgroup V}
    (hX : Nat.card ↥L = 2520) (hperf : commutator ↥L = ⊤) (h : B51NaturalList2 L U Z) :
    False := by
  rcases h with ⟨n, K, _, _, hK, π, hR⟩ | ⟨n, K, _, _, hK, π, hR⟩ | ⟨n, K, _, _, hK, π, hR⟩ |
      ⟨π, hR⟩ | ⟨π, hR⟩ | ⟨K, _, _, hK, π, hR⟩ | ⟨K, _, _, hK, π, hR⟩
  · exact false_of_sl2 hK hX π hR.1
  · exact false_of_sp4 hK hX π hR.1
  · exact false_of_g2 hK hX hperf π hR.1
  · exact false_of_alt (n := 6) (by norm_num) (by norm_num) hX π hR.1
  · exact false_of_alt (n := 8) (by norm_num) (by norm_num) hX π hR.1
  · exact false_of_g2d (by rw [hK]; norm_num) hX π hR.1
  · exact false_of_sl3 hK hX π hR.1

end List

variable {G : Type} [Group G] [Finite G]

theorem fixV_autOn_eq_bot (h51 : AsB51) {H R J W : Subgroup G} [IsMulCommutative ↥W]
    (hS : IsSylowTwoOf R H) (hJH : J ≤ H) (hHJ : H ≤ Subgroup.normalizer (J : Set G))
    (h2 : ∀ h ∈ H, ∃ e : ℕ, h ^ 2 ^ e ∈ J) (hWe : IsElemAbelian 2 W)
    (hred : IsTwoReducedIn H W) (hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J))
    (hsimple : IsSimpleGroup (↥J ⧸ CFSG.pCore 2 ↥J)) (hSQ : SQTKGroup ↥J)
    (hJW : ¬ J ≤ Subgroup.centralizer (W : Set G)) (hJ : J = ⁅J, thompsonJ R⁆)
    (hX : Nat.card ↥(autOn J W) = 2520) (hcomm : ⁅W, J⁆ = W) : fixV (autOn J W) = ⊥ := by
  have hB := b51Hyp_1527d hS hJH hHJ h2 hWe hred hq hsimple hSQ hJW hJ
  have hV2 : ∀ v : ↥W, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [sq] using hWe.2 v v.2)
  obtain ⟨-, ⟨-, hP2⟩, -⟩ := h51 ↥W hV2 _ _ hB
  have hperf : commutator ↥(autOn J W) = ⊤ := hB.2.1.1.commutator_eq_top
  have hdir : IsIntDirect (commV (autOn J W)) (fixV (autOn J W)) ⊤ := by
    by_contra hnd
    exact not_naturalList2 hX hperf (hP2 hnd).2
  have hU : commV (autOn J W) = ⊤ :=
    InternalSec.commV_autOn_eq_top (hJH.trans hred.2.1) hcomm
  have hinf := hdir.2
  rwa [hU, top_inf_eq] at hinf

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
