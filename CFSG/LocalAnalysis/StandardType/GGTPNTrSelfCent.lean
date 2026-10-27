module

public import CFSG.LocalAnalysis.StandardType.GGTPNDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTPNTrSelfCent_holds : GGTPNTrSelfCent := by
  intro G _ _ p B Bs x L D J y K hc hL hK hn hN
  intro t ht htp
  have hcent : (t : G) ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have ha : K.normalizerMonoidHom ⟨b, hN hb⟩ ∈ ggAutsOf K Bs hN :=
      (mem_ggAutsOf hN).mpr ⟨b, hb, rfl⟩
    have hfix : K.normalizerMonoidHom ⟨b, hN hb⟩ t = t := ht _ ha
    have hval : b * (t : G) * b⁻¹ = (t : G) := by
      simpa only [normalizerMonoidHom_apply_coe] using congrArg (fun z : ↥K => (z : G)) hfix
    have hb' : b * (t : G) = (t : G) * b := by
      have := congrArg (· * b) hval
      simpa [mul_assoc] using this
    exact hb'
  have htp' : (t : G) ^ p = 1 := by
    simpa using congrArg (fun z : ↥K => (z : G)) htp
  have htBs : (t : G) ∈ Bs := hc.2.1.2.2.2 (t : G) hcent htp'
  refine (mem_ggAutsOf hN).mpr ⟨(t : G), htBs, ?_⟩
  ext k
  rw [normalizerMonoidHom_apply_coe, MulAut.conj_apply]
  simp

end CFSG.StandardType

end
