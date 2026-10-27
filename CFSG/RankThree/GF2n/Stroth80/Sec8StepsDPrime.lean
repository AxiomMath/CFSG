module

public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsConj
public import CFSG.RankThree.GF2n.Stroth80.Sec84Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClConj
public import CFSG.RankThree.GF2n.Stroth80.Sec34Wc

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement


theorem sec8DPrime_of (h51 : Stroth51Statement) (hA : Sec8AExistsStatement)
    (hT3 : Sec8PointsTransStatement) (hpt : Sec8PointTIStatement) : Sec8DPrimeStatement := by
  intro G _ _ M Q Z B hc n t hs hna Z0 hZ0 g hg hlt
  classical
  have h5 := hs.toSec5
  have ht : t ∈ LB M Q B := h5.mem
  have hZL : Z0 ≤ LB M Q B := sec8_Z0_le_LB h51 hA hc hs hZ0
  have hnormQ : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ)) y).mp hy
  obtain ⟨u, hu, huZ⟩ := SetLike.exists_of_lt hlt
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp hu
  obtain ⟨h, hhR, huh⟩ := hT3 G M Q Z B hc n t hs u hu1 huZ
  have hhM : h ∈ M := hc.Rt_le_M t hhR
  have hs' : Sec8Hyp (hc.conj_of_mem hg) n (g * t * g⁻¹) := hs.conjM hg
  have hZg : conjSubgroup g Z = Z := hc.conj_Z_eq hg
  have hVg : Vt M (LB M Q (conjSubgroup g B)) (conjSubgroup g B) Z (g * t * g⁻¹) =
      conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    rw [(rt_vt_conj hc hg _).2, conjSubgroup_Vt_eq hg hZg]
  have hRg : Rt M (LB M Q (conjSubgroup g B)) (g * t * g⁻¹) =
      conjSubgroup g (Rt M (LB M Q B) t) := by
    rw [(rt_vt_conj hc hg _).1, conjSubgroup_Rt_eq hg]
  obtain ⟨h', hh'R, huh'⟩ := hT3 G M Q Z (conjSubgroup g B) (hc.conj_of_mem hg) n
    (g * t * g⁻¹) hs' u (by rw [hVg]; exact hu2) huZ
  rw [hRg] at hh'R
  have hkR : g⁻¹ * h' * g ∈ Rt M (LB M Q B) t := mem_conjSubgroup.mp hh'R
  have hh'g : h' * g = g * (g⁻¹ * h' * g) := by group
  have hh'M : h' ∈ M := by
    have e : h' = g * (g⁻¹ * h' * g) * g⁻¹ := by group
    rw [e]
    exact M.mul_mem (M.mul_mem hg (hc.Rt_le_M t hkR)) (M.inv_mem hg)
  have hk₂M : h' * g * h⁻¹ ∈ M := M.mul_mem (M.mul_mem hh'M hg) (M.inv_mem hhM)
  have hconj : conjSubgroup (h' * g * h⁻¹) (conjSubgroup h B) = conjSubgroup (h' * g) B := by
    rw [← conjSubgroup_mul, inv_mul_cancel_right]
  have hpt' := hpt G M Q Z (conjSubgroup h B) (hc.conj_of_mem hhM) (h' * g * h⁻¹) hk₂M
    ⟨u, huh, by
      rw [hconj, conjSubgroup_mul]
      exact huh', huZ⟩
  have hk₂N : h' * g * h⁻¹ ∈ Subgroup.normalizer ((conjSubgroup h B ⊔ Z : Subgroup G) : Set G) := by
    refine conjSubgroup_eq_self_iff.mp ?_
    rw [conjSubgroup_sup', hc.conj_Z_eq hk₂M, hpt']
  have hno_h : NoA2 Q Z (LB M Q (conjSubgroup h B)) := hc.noA2_conj h5.noA2 hhM
  have hk₂L : h' * g * h⁻¹ ∈ Subgroup.normalizer (LB M Q (conjSubgroup h B) : Set G) :=
    ((hc.conj_of_mem hhM).mem_normalizer_LB_iff' h5.width h5.n_gt hno_h hk₂M).mpr hk₂N
  have eqL : conjSubgroup (h' * g) (LB M Q B) = conjSubgroup h (LB M Q B) := by
    have h1 := conjSubgroup_eq_self_iff.mpr hk₂L
    rw [hc.LB_conj hhM, ← conjSubgroup_mul, inv_mul_cancel_right] at h1
    exact h1
  refine ⟨h, hhR, ?_⟩
  intro y hy
  obtain ⟨s, hsZ0, rfl⟩ : ∃ s ∈ Z0, y = g * s * g⁻¹ :=
    ⟨g⁻¹ * y * g, mem_conjSubgroup.mp hy, by group⟩
  have hsk : (g⁻¹ * h' * g)⁻¹ * s * (g⁻¹ * h' * g) ∈ Z0 := by
    have := (Subgroup.mem_normalizer_iff.mp
      (hZ0.mem_normalizer hnormQ ((Rt M (LB M Q B) t).inv_mem hkR)) s).mp hsZ0
    simpa using this
  have hyL : g * s * g⁻¹ ∈ conjSubgroup h (LB M Q B) := by
    rw [← eqL, mem_conjSubgroup]
    have e : (h' * g)⁻¹ * (g * s * g⁻¹) * (h' * g) =
        (g⁻¹ * h' * g)⁻¹ * s * (g⁻¹ * h' * g) := by
      rw [hh'g]
      group
    rw [e]
    exact hZL hsk
  refine ⟨hyL, ?_⟩
  have hyL' : h⁻¹ * (g * s * g⁻¹) * h ∈ LB M Q B := mem_conjSubgroup.mp hyL
  have hyN : h⁻¹ * (g * s * g⁻¹) * h ∈ hc.CN t := by
    by_contra hnot
    apply hna
    unfold Conc81a Conc71a
    refine ⟨s, hZ0.le hsZ0, fun r hr => hZ0.comm_mem hsZ0 hr, h⁻¹ * g,
      M.mul_mem (M.inv_mem hhM) hg, ?_, ?_⟩
    · have e : h⁻¹ * g * s * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * s * g⁻¹) * h := by group
      rw [e]
      exact hyL'
    · have e : h⁻¹ * g * s * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * s * g⁻¹) * h := by group
      rw [e]
      exact hnot
  have h1 := hc.CN_conj_mem ht hhR hyN
  have e : h * (h⁻¹ * (g * s * g⁻¹) * h) * h⁻¹ = g * s * g⁻¹ := by group
  rwa [e] at h1

end CFSG.RankThree.GF2n.Stroth80
