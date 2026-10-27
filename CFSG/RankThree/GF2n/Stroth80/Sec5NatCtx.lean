module

public import CFSG.RankThree.GF2n.Stroth80.Sec5NatPairing
public import CFSG.RankThree.GF2n.Stroth80.Sec5Model
public import CFSG.RankThree.GF2n.Stroth80.Sec5Vt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.Z_central (hc : Ctx M Q Z B) {z x : G} (hz : z ∈ Z) (hx : x ∈ Q) : x * z = z * x := by
  have hz' : z ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := by
    rw [← cen_eq, ← hc.hyp.hZ]
    exact hz
  exact Subgroup.mem_centralizer_iff.mp hz'.2 x hx

theorem Ctx.natCommData (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    (hV : Vt M (LB M Q B) B Z t = Ut Q Z t)
    (hW : Wt Q (Vt M (LB M Q B) B Z t) = Q1 hc t) :
    NatCommData Q (Vt M (LB M Q B) B Z t) Z (Rt M (LB M Q B) t) t := by
  have htM : t ∈ M := hc.LB_le_M ht
  have hchi := hc.isChiIso_Q1_Ut ht
  refine
    { VQ := hc.Vt_le_Q t
      ZV := le_sup_left
      comm_Z := fun x hx y hy => hc.hyp.toHyp79.comm_mem_V hx hy
      Z_central := fun z hz x hx => ?_
      comm_t_mem := fun y hy => ?_
      lift := fun v hv => ?_
      ker_central := fun y hy hyZ v hv => ?_
      R_normQ := fun r hr x hx => ?_
      R_centZ := fun r hr z hz => ?_
      R_equiv := fun r hr x hx => hchi.2.2.2.2 r hr x hx }
  · exact hc.Z_central hz hx
  · rw [hV]
    exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hy (Subgroup.mem_zpowers t))
  · rw [hV] at hv
    exact hchi.2.1 v hv
  · have hty : ⁅t, y⁆ ∈ Z := by
      rw [← commutatorElement_inv]
      exact Z.inv_mem hyZ
    have hy1 : y ∈ Q1 hc t := (hc.mem_Q1_iff htM).mpr ⟨hy, hty⟩
    have hyW : y ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
      rw [hW]
      exact hy1
    exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp hyW.2 v hv)
  · exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hr)) x).mp hx
  · have h : r ∈ M ⊓ Subgroup.centralizer (Z : Set G) := hc.Rt_le_H0 t hr
    have h1 : z * r = r * z := Subgroup.mem_centralizer_iff.mp h.2 z hz
    calc r * z * r⁻¹ = z * r * r⁻¹ := by rw [h1]
      _ = z := mul_inv_cancel_right z r

end CFSG.RankThree.GF2n.Stroth80
