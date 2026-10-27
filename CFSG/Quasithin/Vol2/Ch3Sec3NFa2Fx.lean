module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Basic

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.CosetGeom CFSG.ASVolI.ChF
open CFSG.Quasithin.H13.Ch3Sec3
open scoped IsMulCommutative commutatorElement

theorem cent_of_second_commutator {G : Type*} [Group G] {x v w w2 : G} {V : Subgroup G}
    (hV2 : ∀ a ∈ V, a ^ 2 = 1) (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hx3 : x ^ 3 = 1) (hv : v ∈ V) (hw : w = x * v * x⁻¹) (hw2 : w2 = x * w * x⁻¹)
    (hwV : w ∈ V) (hw2V : w2 ∈ V)
    (hk : ⁅⁅v, x⁆, x⁆ * x = x * ⁅⁅v, x⁆, x⁆) : v * x = x * v := by
  have hww : w * w = 1 := (pow_two w).symm.trans (hV2 w hwV)
  have hwI : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hwc : w * w2 = w2 * w := hVc w hwV w2 hw2V
  have hvw : v * w = w * v := hVc v hv w hwV
  have hu2 : ⁅⁅v, x⁆, x⁆ = v * w2 := by
    have e : ⁅⁅v, x⁆, x⁆ = (v * w⁻¹) * (w * w2⁻¹)⁻¹ := by
      subst hw2 hw
      simp only [commutatorElement_def]
      group
    rw [e, mul_inv_rev, inv_inv, hwI]
    calc v * w * (w2 * w) = v * (w * w2) * w := by group
      _ = v * (w2 * w) * w := by rw [hwc]
      _ = v * w2 * (w * w) := by group
      _ = v * w2 := by rw [hww, mul_one]
  have hxxx : x * x * x = 1 := by simpa [pow_succ, mul_assoc] using hx3
  have hx2 : x * w2 * x⁻¹ = v := by
    have e : x * w2 * x⁻¹ = x * x * x * v * (x * x * x)⁻¹ := by
      subst hw2 hw
      group
    rw [e, hxxx]
    simp
  rw [hu2] at hk
  have hA : v * w2 = w * v := by
    calc v * w2 = v * w2 * x * x⁻¹ := by group
      _ = x * (v * w2) * x⁻¹ := by rw [hk]
      _ = (x * v * x⁻¹) * (x * w2 * x⁻¹) := by group
      _ = w * v := by rw [← hw, hx2]
  have hw2w : w2 = w := mul_left_cancel (hA.trans hvw.symm)
  have hfix : x * w * x⁻¹ = w := hw2.symm.trans hw2w
  have hvw' : v = w := by
    calc v = x⁻¹ * (x * v * x⁻¹) * x := by group
      _ = x⁻¹ * w * x := by rw [← hw]
      _ = x⁻¹ * (x * w * x⁻¹) * x := by rw [hfix]
      _ = w := by group
  calc v * x = (x * v * x⁻¹) * x := by rw [← hw, hvw']
    _ = x * v := by group

theorem A2Cfg.not_comm_le_Z {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G} {q : ℕ}
    (hLSCV : Leaf_LSCV) (c : A2Cfg G T M L D H K q) {x : G}
    (hxY : x ∈ oTwoUpper H) (hx3 : orderOf x = 3) :
    ¬ ⁅⁅a2V L T, oTwoUpper H⁆, Subgroup.zpowers x⁆ ≤ a2Z T := by
  intro hcomm
  obtain ⟨hVe, hLV, hTV, -, -, -, -⟩ := L3321.setting_facts c.nf.hyp c.TL
  have hV2 : ∀ a ∈ vPlus L T, a ^ 2 = 1 := hVe.2
  have hVc : ∀ a ∈ vPlus L T, ∀ b ∈ vPlus L T, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (isMulCommutative_iff.1 hVe.1 ⟨a, ha⟩ ⟨b, hb⟩)
  have hxH : x ∈ H := CFSG.Quasithin.oTwoUpper_le H hxY
  rw [c.Heq] at hxH
  obtain ⟨hxLT, hxZ⟩ := Subgroup.mem_inf.1 hxH
  have hxN : x ∈ Subgroup.normalizer (vPlus L T : Set G) := (sup_le hLV hTV) hxLT
  have hconj : ∀ v ∈ vPlus L T, x * v * x⁻¹ ∈ vPlus L T := fun v hv =>
    (Subgroup.mem_normalizer_iff.1 hxN v).1 hv
  have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  have hcent : ∀ v ∈ vPlus L T, v * x = x * v := by
    intro v hv
    have hu₁ : ⁅v, x⁆ ∈ ⁅vPlus L T, oTwoUpper H⁆ := Subgroup.commutator_mem_commutator hv hxY
    have hu₂ : ⁅⁅v, x⁆, x⁆ ∈ ⁅⁅vPlus L T, oTwoUpper H⁆, Subgroup.zpowers x⁆ :=
      Subgroup.commutator_mem_commutator hu₁ (Subgroup.mem_zpowers x)
    have hu₂Z : ⁅⁅v, x⁆, x⁆ ∈ quasithinOmegaOneCenter T := hcomm hu₂
    exact cent_of_second_commutator hV2 hVc hx3' hv rfl rfl (hconj v hv)
      (hconj _ (hconj v hv)) ((Subgroup.mem_centralizer_iff.1 hxZ) _ hu₂Z)
  have hxC : x ∈ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun v hv => hcent v hv
  have hxP : x ∈ pCoreOf 2 (L ⊔ T) := hLSCV G T M L D H K q c (Subgroup.mem_inf.2 ⟨hxLT, hxC⟩)
  obtain ⟨k, hk⟩ :=
    (IsPGroup.iff_orderOf.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T))) ⟨x, hxP⟩
  rw [Subgroup.orderOf_mk, hx3] at hk
  have h3 : (3 : ℕ) ∣ 2 ^ k := ⟨1, by omega⟩
  have h32 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  norm_num at h32

end CFSG.Quasithin.H13.NFa2
