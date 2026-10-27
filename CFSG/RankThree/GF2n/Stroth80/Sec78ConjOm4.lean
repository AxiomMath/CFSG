module

public import CFSG.RankThree.GF2n.Stroth80.Sec78U4

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


theorem sec7ConjOm4_of_inputs (h34 : Stroth34Statement) (hA7 : Sec7AExistsStatement)
    (hPtsΩ : Sec5NatPointsOmegaStatement) (hZt : Sec7ZtStatement) : Sec7ConjOm4Statement := by
  intro G _ _ M Q Z B hc n t hs hom Z0 hZ0 s hsZ x hxL hx
  by_cases hsQ : s ∈ Q
  · refine ⟨1, M.one_mem, Subgroup.one_mem _, ?_⟩
    obtain ⟨hxM, g, hg, hQ⟩ := hx
    have hgs : g * s * g⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) s).mp hsQ
    have hxQ : x ∈ Q := by
      have h1 := Q.mul_mem hQ hgs
      have e : x * (g * s * g⁻¹)⁻¹ * (g * s * g⁻¹) = x := by group
      rwa [e] at h1
    have h2 := Q.mul_mem hxQ (Q.inv_mem hsQ)
    have e2 : x * s⁻¹ = x * (1 * s * 1⁻¹)⁻¹ := by group
    rwa [← e2]
  · obtain ⟨hxM, g, hg, hQ⟩ := hx
    have hgi : g⁻¹ ∈ M := M.inv_mem hg
    have hgsL : g * s * g⁻¹ ∈ LB M Q B := by
      have e : g * s * g⁻¹ = (x * (g * s * g⁻¹)⁻¹)⁻¹ * x := by group
      rw [e]
      exact (LB M Q B).mul_mem ((LB M Q B).inv_mem (sec39_Q_le_LB hQ)) hxL
    have hsh : s ∈ LB M Q (conjSubgroup g⁻¹ B) := by
      rw [hc.LB_conj hgi, mem_conjSubgroup, inv_inv]
      exact hgsL
    obtain ⟨ρ, hρ, hBZ⟩ := sec7ctr_U4 h34 hA7 hPtsΩ hZt hc hs hom hZ0 hsZ hsQ hgi hsh
    have hρM : ρ ∈ M := hc.Rt_le_M t hρ
    have hLF := hc.conj_LB_eq_of_conj_BZ hgi hρM hBZ
    refine ⟨g * ρ, M.mul_mem hg hρM, ?_, ?_⟩
    · refine conjSubgroup_eq_self_iff.mp ?_
      rw [conjSubgroup_mul, ← hLF, ← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
    · have hq' : ⁅ρ, s⁆ ∈ Q := by
        rw [← commutatorElement_inv]
        exact Q.inv_mem (hZ0.comm_mem hsZ hρ)
      have e : x * ((g * ρ) * s * (g * ρ)⁻¹)⁻¹ =
          (x * (g * s * g⁻¹)⁻¹) * (g * ⁅ρ, s⁆ * g⁻¹)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Q.mul_mem hQ
        (Q.inv_mem ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) _).mp hq'))

end CFSG.RankThree.GF2n.Stroth80
