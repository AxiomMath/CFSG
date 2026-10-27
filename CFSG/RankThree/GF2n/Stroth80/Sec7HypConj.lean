module

public import CFSG.RankThree.GF2n.Stroth80.Sec10Conj
public import CFSG.RankThree.GF2n.Stroth80.Sec7Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec39Rt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem rt_conj_of_mem (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) (t : G) :
    Rt M (LB M Q (conjSubgroup m B)) (m * t * m⁻¹) = conjSubgroup m (Rt M (LB M Q B) t) := by
  have h := CFSG.RankThree.GF2n.Smith81.Rt_conj m M (LB M Q B) t
  rw [hc.conj_M_eq hm] at h
  rw [hc.LB_conj hm]
  exact h

theorem vt_conj_of_mem (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) (t : G) :
    Vt M (LB M Q (conjSubgroup m B)) (conjSubgroup m B) Z (m * t * m⁻¹) =
      conjSubgroup m (Vt M (LB M Q B) B Z t) := by
  have h := Vt_conjG m M (LB M Q B) B Z t
  rw [hc.conj_M_eq hm, hc.conj_Z_eq hm] at h
  rw [hc.LB_conj hm]
  exact h

theorem cn_conj_of_mem (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) (t : G) :
    (hc.conj_of_mem hm).CN (m * t * m⁻¹) = conjSubgroup m (hc.CN t) := by
  have hZn : ∀ a ∈ M, ∀ z ∈ Z, a * z * a⁻¹ ∈ Z := fun a ha z hz =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 ha) z).mp hz
  ext x
  rw [Ctx.mem_CN, rt_conj_of_mem hc hm t, vt_conj_of_mem hc hm t]
  have hR : x ∈ conjSubgroup m (Rt M (LB M Q B) t) ↔ m⁻¹ * x * m ∈ Rt M (LB M Q B) t :=
    mem_conjSubgroup
  have hN : x ∈ conjSubgroup m (hc.CN t) ↔ m⁻¹ * x * m ∈ hc.CN t := mem_conjSubgroup
  rw [hN, Ctx.mem_CN, hR]
  constructor
  · rintro ⟨hxR, hxV⟩
    refine ⟨hxR, fun v hv => ?_⟩
    have hv' : m * v * m⁻¹ ∈ conjSubgroup m (Vt M (LB M Q B) B Z t) := by
      rw [mem_conjSubgroup]
      have e : m⁻¹ * (m * v * m⁻¹) * m = v := by group
      rw [e]
      exact hv
    have h1 := hZn m⁻¹ (M.inv_mem hm) _ (hxV _ hv')
    have e : m⁻¹ * ⁅x, m * v * m⁻¹⁆ * m⁻¹⁻¹ = ⁅m⁻¹ * x * m, v⁆ := by
      simp only [commutatorElement_def]
      group
    rwa [e] at h1
  · rintro ⟨hxR, hxV⟩
    refine ⟨hxR, fun v hv => ?_⟩
    have hv' : m⁻¹ * v * m ∈ Vt M (LB M Q B) B Z t := mem_conjSubgroup.mp hv
    have h1 := hZn m hm _ (hxV _ hv')
    have e : m * ⁅m⁻¹ * x * m, m⁻¹ * v * m⁆ * m⁻¹ = ⁅x, v⁆ := by
      simp only [commutatorElement_def]
      group
    rwa [e] at h1

theorem omegaPlusNat_conj_of_mem (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) (t : G) (k : ℕ) :
    OmegaPlusNat (hc.conj_of_mem hm) (m * t * m⁻¹) k ↔ OmegaPlusNat hc t k := by
  unfold OmegaPlusNat
  simp only [rt_conj_of_mem hc hm, vt_conj_of_mem hc hm, cn_conj_of_mem hc hm]
  constructor
  · rintro ⟨K, hK, hKf, hcard, hrep⟩
    refine ⟨K, hK, hKf, hcard, ?_⟩
    have h := hrep.conjG m⁻¹
    rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one, ← conjSubgroup_mul,
      inv_mul_cancel, conjSubgroup_one, ← conjSubgroup_mul, inv_mul_cancel,
      conjSubgroup_one, hc.conj_Z_eq (M.inv_mem hm)] at h
    exact h
  · rintro ⟨K, hK, hKf, hcard, hrep⟩
    refine ⟨K, hK, hKf, hcard, ?_⟩
    have h := hrep.conjG m
    rw [hc.conj_Z_eq hm] at h
    exact h

theorem omegaMinusNat_conj_of_mem (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) (t : G) (k : ℕ) :
    OmegaMinusNat (hc.conj_of_mem hm) (m * t * m⁻¹) k ↔ OmegaMinusNat hc t k := by
  unfold OmegaMinusNat
  simp only [rt_conj_of_mem hc hm, vt_conj_of_mem hc hm, cn_conj_of_mem hc hm]
  constructor
  · rintro ⟨K, hK, hKf, hcard, b, c, hirr, hrep⟩
    refine ⟨K, hK, hKf, hcard, b, c, hirr, ?_⟩
    have h := hrep.conjG m⁻¹
    rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one, ← conjSubgroup_mul,
      inv_mul_cancel, conjSubgroup_one, ← conjSubgroup_mul, inv_mul_cancel,
      conjSubgroup_one, hc.conj_Z_eq (M.inv_mem hm)] at h
    exact h
  · rintro ⟨K, hK, hKf, hcard, b, c, hirr, hrep⟩
    refine ⟨K, hK, hKf, hcard, b, c, hirr, ?_⟩
    have h := hrep.conjG m
    rw [hc.conj_Z_eq hm] at h
    exact h

theorem sec7Hyp_conj_of_mem (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {m : G}
    (hm : m ∈ M) : Sec7Hyp (hc.conj_of_mem hm) n (m * t * m⁻¹) where
  toSec5 :=
    { width := hs.toSec5.width
      n_gt := hs.toSec5.n_gt
      noA2 := hc.noA2_conj hs.toSec5.noA2 hm
      gen := hs.toSec5.gen.conj_of_mem hm
      mem := by
        rw [hc.LB_conj hm, mem_conjSubgroup]
        have e : m⁻¹ * (m * t * m⁻¹) * m = t := by group
        rw [e]
        exact hs.toSec5.mem
      notQ := fun h => by
        have h1 : m * t * m⁻¹ ∈ conjSubgroup m Q := by
          rw [hc.conj_Q_eq hm]
          exact h
        have e : m⁻¹ * (m * t * m⁻¹) * m = t := by group
        rw [mem_conjSubgroup, e] at h1
        exact hs.toSec5.notQ h1 }
  notPlus4 := fun h => hs.notPlus4 ((omegaPlusNat_conj_of_mem hc hm t 2).mp h)
  orth := by
    obtain ⟨k, hk, h⟩ := hs.orth
    exact ⟨k, hk, h.imp (fun h => (omegaPlusNat_conj_of_mem hc hm t k).mpr h)
      (fun h => (omegaMinusNat_conj_of_mem hc hm t k).mpr h)⟩
  large := by
    rw [cn_conj_of_mem hc hm t, card_conjSubgroup]
    exact hs.large

end CFSG.RankThree.GF2n.Stroth80
