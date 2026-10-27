module

public import CFSG.RankThree.GF2n.Stroth80.Sec713O2Steps
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailCaseA
import CFSG.RankThree.GF2n.Stroth80.Sec713O2XActs
import CFSG.RankThree.GF2n.Stroth80.Sec715CentProof
import CFSG.RankThree.GF2n.Stroth80.Sec85Comm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG
open scoped commutatorElement


theorem step713CentralN_of (h79 : Stroth79Statement) (hZN6 : Sec717ZNStatement)
    (h711 : Stroth711StrongStatement) (hSch : Sec7SchurStatement) (h34 : Stroth34Statement)
    (h51 : Stroth51Statement) (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement)
    (hZcard : Sec7ZCardStatement) : Step713CentralNStatement := by
  intro G _ _ M Q Z B _ hc n t hs hn4 Z0 hZ0 x hx hxN hxR hxV hxW hxNc
  classical
  have h5 := hs.toSec5
  have ht : t ∈ LB M Q B := h5.mem
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun y hy => (Ctx.mem_CN.1 hy).1
  have hQn : ∀ g ∈ M, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := fun g hg q hq =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) q).mp hq
  have hZ0N : Z0 ≤ hc.CN t := sec7ctr_Z0_le_CN hc hs hZ0
  have hNn : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ hc.CN t, r * y * r⁻¹ ∈ hc.CN t :=
    fun r hr y hy => hc.CN_conj_mem ht hr hy
  have hxD : x ∈ O2NormPre M Q Z Z0 := mem_O2NormPre.mpr hx
  have hxK : x ∈ NormH0 M Z Z0 := O2NormPre_le_NormH0 (sec713_Q_le_NormH0 hc ht hZ0) hxD
  have hxH : x ∈ H0 M Z := hxK.1
  have hxM : x ∈ M := hxH.1
  have hZN : IsCentrePre Z0 (hc.CN t) Q := by
    by_cases h6 : OmegaPlusNat hc t 3
    · exact hZN6 G M Q Z B hc n t hs h6 Z0 hZ0
    · have hZ : ∀ a ∈ hc.CN t, (∀ b ∈ hc.CN t, ⁅a, b⁆ ∈ Q) → a ∈ Z0 := by
        rcases h79 G M Q Z B hc n t h5 hs.large hs.notPlus4 hs.orth with
          ⟨Z0', hZ0', hirr⟩ | h6' | ⟨h8, -⟩
        · have hZeq : Z0' = Z0 := Subgroup.ext fun y => (hZ0' y).trans (hZ0 y).symm
          subst hZeq
          exact sec85_centre_le hQn hRM hNR hNn hZ0N (fun z hz b hb => hZ0'.comm_mem hz (hNR hb))
            hirr.2.2.2 (h711 G M Q Z B hc n t hs)
        · exact absurd h6' h6
        · exact absurd h8 hn4
      intro y
      exact ⟨fun hy => ⟨hZ0N hy, fun b hb => hZ0.comm_mem hy (hNR hb)⟩,
        fun ⟨hyN, hyb⟩ => hZ y hyN hyb⟩
  have hxN' : ∀ y ∈ hc.CN t, ⁅x, y⁆ ∈ Q := fun y hy => by
    rw [← commutatorElement_inv]
    exact Q.inv_mem (hxNc y hy)
  have hxRQ : ∀ r ∈ Rt M (LB M Q B) t, ⁅x, r⁆ ∈ Q :=
    sec715_comm_Rt_mem_Q h51 hA hZcard hc hs hZ0 hZN hxM hxN'
  have hwR : ∀ ρ ∈ Rt M (LB M Q B) t, ⁅ρ⁻¹, x⁆ ∈ Q := fun ρ hρ => by
    rw [← commutatorElement_inv]
    exact Q.inv_mem (hxRQ _ ((Rt M (LB M Q B) t).inv_mem hρ))
  have hwV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅v, x⁆ ∈ Z := fun v hv => by
    rw [← commutatorElement_inv]
    exact Z.inv_mem (hxV v hv)
  have hwW : ∀ y ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅y, x⁆ ∈ Vt M (LB M Q B) B Z t := fun y hy => by
    rw [← commutatorElement_inv]
    exact (Vt M (LB M Q B) B Z t).inv_mem (hxW y hy)
  have hWZ := sec715_comm_Wt_mem_Z h34 h52a hA sec7VtIrred_holds hc hs hxM hwR hwV hwW
  refine hxN (hZ0N (hSch G M Q Z B hc n t hs Z0 hZ0 x hxH (fun a ha => hxRQ a ?_) fun u hu => ?_))
  · exact Subgroup.commutator_le_self _ ha
  · rw [← commutatorElement_inv]
    exact Z.inv_mem (hWZ u hu)

end CFSG.RankThree.GF2n.Stroth80

end
