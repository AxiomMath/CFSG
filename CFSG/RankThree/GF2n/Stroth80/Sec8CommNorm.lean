module

public import CFSG.RankThree.GF2n.Stroth80.Sec10Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsClose81
public import CFSG.RankThree.GF2n.Stroth80.Sec8RtConj

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_conj_R_of_comm (hc : Ctx M Q Z B) {t x : G} (htM : t ∈ M) (hxM : x ∈ M)
    (hxt : ⁅x, t⁆ ∈ Q) :
    conjSubgroup x (Rt M (LB M Q B) t) = Rt M (LB M Q B) t := by
  have hy : t⁻¹ * ⁅x, t⁆ * t ∈ Q := by
    have h := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem htM)) ⁅x, t⁆).mp hxt
    rwa [inv_inv] at h
  have e : x * t * x⁻¹ = t * (t⁻¹ * ⁅x, t⁆ * t) := by
    simp only [commutatorElement_def]
    group
  rw [conjSubgroup_Rt_eq hxM t, e, Rt_mul_of_mem_Q hc hy]

theorem sec8_comm_mem_CN (hc : Ctx M Q Z B) {t x : G} (ht : t ∈ LB M Q B) (hxM : x ∈ M)
    (hxt : ⁅x, t⁆ ∈ Q) (hxV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∈ Z) {ρ : G}
    (hρ : ρ ∈ Rt M (LB M Q B) t) : ρ * x * ρ⁻¹ * x⁻¹ ∈ hc.CN t := by
  have htM : t ∈ M := hc.LB_le_M ht
  have hρM : ρ ∈ M := hc.Rt_le_M t hρ
  have hxR : conjSubgroup x (Rt M (LB M Q B) t) = Rt M (LB M Q B) t :=
    sec8_conj_R_of_comm hc htM hxM hxt
  have hxN : x ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    sec8_normV_of_comm hc hxM hxt
  have hρN : ρ ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    hc.Rt_normalizes_Vt ht hρ
  have hconj : ∀ y ∈ M, ∀ a b : G, a * b⁻¹ ∈ Z → (y * a * y⁻¹) * (y * b * y⁻¹)⁻¹ ∈ Z := by
    intro y hy a b hab
    have e : (y * a * y⁻¹) * (y * b * y⁻¹)⁻¹ = y * (a * b⁻¹) * y⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hy) (a * b⁻¹)).mp hab
  refine Ctx.mem_CN.mpr ⟨?_, fun v hv => ?_⟩
  · have hxρ : x * ρ⁻¹ * x⁻¹ ∈ Rt M (LB M Q B) t :=
      (Subgroup.mem_normalizer_iff.mp (conjSubgroup_eq_self_iff.mp hxR) ρ⁻¹).mp
        ((Rt M (LB M Q B) t).inv_mem hρ)
    have e : ρ * x * ρ⁻¹ * x⁻¹ = ρ * (x * ρ⁻¹ * x⁻¹) := by group
    rw [e]
    exact (Rt M (LB M Q B) t).mul_mem hρ hxρ
  ·
    have hu : x⁻¹ * v * x ∈ Vt M (LB M Q B) B Z t := by
      have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) v).mp hv
      rwa [inv_inv] at h
    have hw : ρ⁻¹ * v * ρ ∈ Vt M (LB M Q B) B Z t := by
      have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hρN) v).mp hv
      rwa [inv_inv] at h
    have F1 : v * (x⁻¹ * v * x)⁻¹ ∈ Z := by
      have e : ⁅x, x⁻¹ * v * x⁆ = v * (x⁻¹ * v * x)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [← e]
      exact hxV _ hu
    have F2 : (ρ⁻¹ * v * ρ) * (ρ⁻¹ * (x⁻¹ * v * x) * ρ)⁻¹ ∈ Z := by
      have h := hconj ρ⁻¹ (M.inv_mem hρM) v (x⁻¹ * v * x) F1
      rwa [inv_inv] at h
    have F3 := hconj x hxM _ _ F2
    have F4 := hconj ρ hρM _ _ F3
    have F5' : x * (ρ⁻¹ * v * ρ) * x⁻¹ * (ρ⁻¹ * v * ρ)⁻¹ ∈ Z := by
      have h := hxV _ hw
      rwa [commutatorElement_def] at h
    have F5 := hconj ρ hρM _ _ F5'
    have hwρ : ρ * (ρ⁻¹ * v * ρ) * ρ⁻¹ = v := by group
    rw [hwρ] at F5
    have key := Z.mul_mem (Z.inv_mem F4) F5
    convert key using 2
    simp only [commutatorElement_def]
    group

end CFSG.RankThree.GF2n.Stroth80
