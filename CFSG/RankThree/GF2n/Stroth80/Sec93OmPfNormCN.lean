module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec93TA
public import CFSG.RankThree.GF2n.Stroth80.Sec5Core
public import CFSG.RankThree.GF2n.Stroth80.Sec5Main

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem conj_LB_eq_of_mem_CN (hc : Ctx M Q Z B) {x : G} (hxL : x ∈ LB M Q B) {y : G}
    (hy : y ∈ hc.CN x) : conjSubgroup y (LB M Q B) = LB M Q B :=
  conj_LB_eq_of_forall_comm_mem_Z hc (hc.Rt_le_M x (Ctx.mem_CN.mp hy).1)
    fun b hb => (Ctx.mem_CN.mp hy).2 b (hc.B_le_Vt hxL hb)

theorem CN_conj_mem_of_stronglyClosed {hc : Ctx M Q Z B} {x : G} (hxL : x ∈ LB M Q B)
    {Z0 : Subgroup G} (hZ0L : Z0 ≤ LB M Q B) (hsc : StronglyClosedMod M Z0 (LB M Q B))
    {y : G} (hy : y ∈ hc.CN x) {z : G} (hz : z ∈ Z0) : y * z * y⁻¹ ∈ Z0 := by
  have hyM : y ∈ M := hc.Rt_le_M x (Ctx.mem_CN.mp hy).1
  have hL := conj_LB_eq_of_mem_CN hc hxL hy
  have hzL : z ∈ LB M Q B := hZ0L hz
  have hconj : y * z * y⁻¹ ∈ conjSubgroup y (LB M Q B) := by
    rw [mem_conjSubgroup]
    have e : y⁻¹ * (y * z * y⁻¹) * y = z := by group
    rw [e]
    exact hzL
  rw [hL] at hconj
  exact hsc z hz y hyM hconj

theorem comm_mem_inf_CN {hc : Ctx M Q Z B} {x : G} (hxL : x ∈ LB M Q B) {Z0 : Subgroup G}
    (hZ0L : Z0 ≤ LB M Q B) (hsc : StronglyClosedMod M Z0 (LB M Q B)) {z f : G} (hz : z ∈ Z0)
    (hf : f ∈ hc.CN x) : ⁅z, f⁆ ∈ Z0 ⊓ hc.CN x := by
  have hzR : z ∈ Rt M (LB M Q B) x := le_Rt (M := M) (LB M Q B) hxL (hZ0L hz)
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have h2 := CN_conj_mem_of_stronglyClosed hxL hZ0L hsc hf (Z0.inv_mem hz)
    have e : ⁅z, f⁆ = z * (f * z⁻¹ * f⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact Z0.mul_mem hz h2
  · have h3 := hc.CN_conj_mem hxL hzR hf
    have e : ⁅z, f⁆ = (z * f * z⁻¹) * f⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact (hc.CN x).mul_mem h3 ((hc.CN x).inv_mem hf)

end HS9

end CFSG.RankThree.GF2n.Stroth80
