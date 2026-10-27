module

public import CFSG.LocalAnalysis.StandardType.GGNbrBalancePumpup
import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosurePComp

public section

namespace CFSG.StandardType

open CFSG.Assembly

open scoped commutatorElement

theorem ggNbr_pumpup_of_moves (hPU : GGPumpupInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hpJ : p ∣ Nat.card J) {d : G} (hD : D = Subgroup.closure {x, d}) {r : MulAut ↥Bs}
    (hr : r ∈ ggAutomizer (ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J) Bs)
    (hmove : ∃ xb : ↥Bs, (xb : G) = x ∧ r xb ≠ xb) :
    GGNbr p B x D J d (ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J) := by
  obtain ⟨-, -, -, hcase⟩ := pumpup_of_stdSub hPU hcfg.1 hcfg.2.2 hpJ hD
  refine hcase.resolve_right fun hc => ?_
  obtain ⟨xb, hxb, hrx⟩ := hmove
  haveI := Fact.mk hcfg.1.2.2.2.2.2.1.1
  have hxBs : x ∈ Bs := hxb ▸ xb.2
  have hstab : ggAutomizer (ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J) Bs ≤
      MulAction.stabilizer (MulAut ↥Bs) xb := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro φ ⟨g, hgK, -, hφ⟩
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, MulAut.smul_def]
    apply Subtype.ext
    rw [hφ xb, hxb]
    have hu : ⁅g, x⁆ ∈ LargeEvenPPrimeCoreOf p
        (ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J) :=
      hc (Subgroup.commutator_mem_commutator hgK (Subgroup.mem_zpowers x))
    have hgx : g * x * g⁻¹ ∈ Bs := by
      have h := (φ xb).2
      rwa [hφ xb, hxb] at h
    have huBs : ⁅g, x⁆ ∈ Bs := by
      rw [commutatorElement_def]
      exact Bs.mul_mem hgx (Bs.inv_mem hxBs)
    have h1 := eq_one_of_mem_largeEvenPPrimeCoreOf hu (hcfg.2.1.2.1.2 _ huBs)
    rwa [commutatorElement_def, mul_inv_eq_one] at h1
  exact hrx (MulAction.mem_stabilizer_iff.mp (hstab hr))

end CFSG.StandardType

end
