module

public import CFSG.RankThree.GF2n.Parrott.Section4HPrimeIndex
public import CFSG.RankThree.GF2n.Parrott.FixDimConj
public import CFSG.GroupTheory.HyperplaneDecomposition

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem fixDimV_eq_two_of_qH_sigma2 (h : Tim79a.ParrottHyp z)
    {σ : ↥(H z)} (hq : qH (z := z) D σ =
      (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    fixDimV h σ = 2 := by
  let τ : ↥(H z) := uH (z := z) D * sigma1Nine (z := z) D * (uH (z := z) D)⁻¹
  have hqτ : qH (z := z) D τ =
      (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) := by
    show qH (z := z) D
      (uH (z := z) D * sigma1Nine (z := z) D * (uH (z := z) D)⁻¹) = _
    rw [map_mul, map_mul, map_inv, qH_uH, qH_sigma1Nine]
    apply Subtype.ext
    exact sigma1_conj_u
  have hτdim : fixDimV h τ = 2 := by
    calc fixDimV h τ = fixDimV h (sigma1Nine (z := z) D) :=
          fixDimV_conj (z := z) h (x := sigma1Nine (z := z) D) (y := τ)
            (g := uH (z := z) D) rfl
      _ = 2 := fixDimV_sigma1Nine (z := z) (D := D) h
  have hker : σ * τ⁻¹ ∈ (qH (z := z) D).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hq, hqτ, mul_inv_cancel]
  rw [ker_qH] at hker
  have hj : ((σ * τ⁻¹ : ↥(H z)) : G) ∈ J z :=
    Subgroup.mem_subgroupOf.mp hker
  have hσeq : σ = (σ * τ⁻¹) * τ := by
    group
  have hconjV : conjV h σ = conjV h τ := by
    rw [hσeq, conjV_mem_J_mul (z := z) h hj]
  have hfix : fixSubmodule h σ = fixSubmodule h τ := by
    unfold fixSubmodule
    rw [hconjV]
  have hdim : fixDimV h σ = fixDimV h τ := by
    unfold fixDimV
    rw [hfix]
  rw [hdim, hτdim]

theorem fixDimV_eq_two_sigma2_of_not_equalityBranch (h : Tim79a.ParrottHyp z)
    (_hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h)
    {σ₂ : ↥(H z)} (_hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (_hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) :
    fixDimV h σ₂ = 2 :=
  fixDimV_eq_two_of_qH_sigma2 (z := z) D h hq₂

@[expose] noncomputable def conjVRepresentation (h : Tim79a.ParrottHyp z) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    Representation (ZMod 2) ↥(H z) (Additive (QuotientV.V z)) := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  exact
    { toFun := conjVLinearMap h
      map_one' := conjVLinearMap_one h
      map_mul' := conjVLinearMap_mul h }

theorem invariants_zpowers_eq_fixSubmodule (h : Tim79a.ParrottHyp z) (x : ↥(H z)) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    Representation.invariants
        ((conjVRepresentation h).comp (Subgroup.zpowers x).subtype) =
      fixSubmodule h x := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  ext v
  rw [Representation.mem_invariants]
  constructor
  · intro hv
    rw [mem_fixSubmodule_iff, mem_autFixedSubgroup]
    have hfix := hv ⟨x, Subgroup.mem_zpowers x⟩
    have hfix' : conjVLinearMap h x v = v := by
      simpa [conjVRepresentation] using hfix
    simpa [conjVLinearMap_apply] using congrArg Additive.toMul hfix'
  · intro hv
    have hgen : ∀ a : Subgroup.zpowers x,
        a ∈ Subgroup.zpowers (⟨x, Subgroup.mem_zpowers x⟩ : Subgroup.zpowers x) := by
      intro a
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext hk⟩
    have hiff :
        (∀ a : Subgroup.zpowers x,
          ((conjVRepresentation h).comp (Subgroup.zpowers x).subtype) a v = v) ↔
        ((conjVRepresentation h).comp (Subgroup.zpowers x).subtype)
          ⟨x, Subgroup.mem_zpowers x⟩ v = v :=
      Representation.mem_invariants_iff_of_forall_mem_zpowers
        (ρ := (conjVRepresentation h).comp (Subgroup.zpowers x).subtype)
        (g := ⟨x, Subgroup.mem_zpowers x⟩) hgen v
    rw [hiff]
    have hfix : conjV h x (Additive.toMul v) = Additive.toMul v := by
      rw [← mem_autFixedSubgroup]
      exact (mem_fixSubmodule_iff h x v).mp hv
    have hfix' : conjVLinearMap h x v = v := by
      rw [conjVLinearMap_apply]
      exact congrArg Additive.ofMul hfix
    simpa [conjVRepresentation] using hfix'

theorem finrank_invariants_zpowers (h : Tim79a.ParrottHyp z) (x : ↥(H z)) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    Module.finrank (ZMod 2)
        (Representation.invariants
          ((conjVRepresentation h).comp (Subgroup.zpowers x).subtype)) =
      fixDimV h x := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  rw [invariants_zpowers_eq_fixSubmodule]
  rfl

theorem mem_centralizerJ_of_conjV_pi_eq (h : Tim79a.ParrottHyp z)
    {σ : ↥(H z)} (hσ3 : σ ^ 3 = 1) (hZ : conjZ z σ = 1) {j : J z}
    (hfix : conjV h σ (QuotientV.pi z j) = QuotientV.pi z j) :
    j ∈ centralizerJ σ := by
  let ζJ : J z := conjJ' z σ j * j⁻¹
  have hζker : ζJ ∈ (QuotientV.pi z).ker := by
    rw [MonoidHom.mem_ker]
    change QuotientV.pi z (conjJ' z σ j * j⁻¹) = 1
    rw [map_mul, map_inv, ← conjV_mk h σ j, hfix, mul_inv_cancel]
  rw [QuotientV.pi_ker] at hζker
  let ζ : centerIn (J z) := ⟨(ζJ : G), Subgroup.mem_subgroupOf.mp hζker⟩
  have hζcoe : (ζJ : G) = (ζ : G) := rfl
  have hfixζ : conjJ' z σ ζJ = ζJ := by
    apply Subtype.ext
    change (conjJ' z σ ζJ : G) = (ζ : G)
    rw [conjJ'_apply_coe, hζcoe]
    have hcent : (ζ : G) ∈ Subgroup.centralizer ({(σ : G)} : Set G) :=
      centerIn_le_centralizer_of_conjZ_eq_one (z := z) hZ ζ.2
    have hcomm : (ζ : G) * (σ : G) = (σ : G) * (ζ : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hcent
    rw [← hcomm]
    group
  have hrel : conjJ' z σ j = ζJ * j := by
    rw [show ζJ = conjJ' z σ j * j⁻¹ from rfl]
    group
  have hpow : ∀ k : ℕ, ((conjJ' z σ : MulAut (J z)) ^ k) j = ζJ ^ k * j := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc ((conjJ' z σ : MulAut (J z)) ^ (k + 1)) j
            = (conjJ' z σ) (((conjJ' z σ : MulAut (J z)) ^ k) j) := by
              rw [pow_succ']
              rfl
          _ = (conjJ' z σ) (ζJ ^ k * j) := by rw [ih]
          _ = (conjJ' z σ) (ζJ ^ k) * (conjJ' z σ) j := by rw [map_mul]
          _ = ζJ ^ k * (ζJ * j) := by rw [map_pow, hfixζ, hrel]
          _ = ζJ ^ (k + 1) * j := by group
  have h3 : (conjJ' z σ : MulAut (J z)) ^ 3 = 1 := by
    rw [← map_pow, hσ3, map_one]
  have hj3 : ((conjJ' z σ : MulAut (J z)) ^ 3) j = j := by rw [h3]; rfl
  have hζ3 : ζJ ^ 3 = 1 := by
    have h := hpow 3
    rw [hj3] at h
    exact mul_right_cancel (by rw [one_mul]; exact h.symm)
  have hζ2 : (ζ : G) * (ζ : G) = 1 := centerIn_J_sq h ζ.2
  have hζ3G : (ζ : G) ^ 3 = 1 := by
    have := congrArg (fun y : J z => (y : G)) hζ3
    simpa [hζcoe] using this
  have hζeq : (ζ : G) = 1 := by
    have hcube : (ζ : G) ^ 3 = (ζ : G) * ((ζ : G) * (ζ : G)) := by
      rw [pow_succ, pow_two]
      group
    rw [hcube, hζ2, mul_one] at hζ3G
    exact hζ3G
  have hζJ_one : ζJ = 1 := by
    apply Subtype.ext
    exact hζeq
  have hconj : conjJ' z σ j = j := by rw [hrel, hζJ_one, one_mul]
  rw [mem_centralizerJ_iff]
  have hcoe := congrArg (fun y : J z => (y : G)) hconj
  rw [conjJ'_apply_coe] at hcoe
  have hσj : (σ : G) * (j : G) = (j : G) * (σ : G) := by
    calc (σ : G) * (j : G)
        = ((σ : G) * (j : G) * (σ : G)⁻¹) * (σ : G) := by group
      _ = (j : G) * (σ : G) := by rw [hcoe]
  exact hσj.symm

theorem inf_CJ_eq_centerIn_of_centralizerJ_ne (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    (hne : centralizerJ (sigma1Nine (z := z) D) ≠ centralizerJ σ₂) :
    CJ z (sigma1Nine (z := z) D : G) ⊓ CJ z (σ₂ : G) = centerIn (J z) := by
  set σ₁ : ↥(H z) := sigma1Nine (z := z) D with hσ₁
  have hneG : CJ z (σ₁ : G) ≠ CJ z (σ₂ : G) := fun heq =>
    hne (congrArg (fun K : Subgroup G => K.subgroupOf (J z)) heq)
  have hconjZ2 : conjZ z σ₂ = 1 :=
    conjZ_eq_one_of_qH_mem_QP45 (z := z) D h σ₂
      (by rw [hq₂]; exact sigma2_mem_Q)
  have hZ1 : centerIn (J z) ≤ CJ z (σ₁ : G) :=
    centerIn_le_CJ_of_conjZ_eq_one (z := z) (conjZ_sigma1Nine (z := z) h D)
  have hZ2 : centerIn (J z) ≤ CJ z (σ₂ : G) :=
    centerIn_le_CJ_of_conjZ_eq_one (z := z) hconjZ2
  have hc1 : Nat.card ↥(CJ z (σ₁ : G)) = 16 := by
    rw [card_CJ_eq_card_centralizerJ]
    exact card_centralizerJ_sigma1Nine (z := z) h D
  have hc2 : Nat.card ↥(CJ z (σ₂ : G)) = 16 := by
    rw [card_CJ_eq_card_centralizerJ]
    have hform := card_centralizerJ_eq_card_inf_mul_card_pow_fixDim_of_orderOf_eq_three
      (z := z) (h := h) (x := σ₂) hσ₂
    have hZJ : centralizerJ σ₂ ⊓ Subgroup.center (J z) = Subgroup.center (J z) := by
      refine inf_eq_right.mpr fun j hj => ?_
      rw [mem_centralizerJ_iff]
      have hjZ : (j : G) ∈ centerIn (J z) := by
        have hj' : j ∈ (centerIn (J z)).subgroupOf (J z) := by
          rwa [QuotientV.centerIn_subgroupOf_eq_center]
        exact Subgroup.mem_subgroupOf.mp hj'
      exact Subgroup.mem_centralizer_singleton_iff.mp
        (centerIn_le_centralizer_of_conjZ_eq_one (z := z) hconjZ2 hjZ)
    rw [hZJ, card_center_subgroupOf_J (z := z) h,
      fixDimV_eq_two_of_qH_sigma2 (z := z) D h hq₂] at hform
    norm_num at hform
    exact hform
  have hcZ : Nat.card ↥(centerIn (J z)) = 4 := card_centerIn_J (z := z) h
  have hcommG : (σ₂ : G) * (σ₁ : G) = (σ₁ : G) * (σ₂ : G) := by
    simpa only [Subgroup.coe_mul] using congrArg Subtype.val hcomm
  have h3 : (σ₂ : G) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← hσ₂, pow_orderOf_eq_one, Subgroup.coe_one]
  have hmod := card_CJ_modEq_card_inf_CJ (z := z) σ₂.2 hcommG h3
  rw [hc1] at hmod
  set S := CJ z (σ₁ : G) ⊓ CJ z (σ₂ : G) with hS
  have hZS : centerIn (J z) ≤ S := le_inf hZ1 hZ2
  have hS1 : S ≤ CJ z (σ₁ : G) := inf_le_left
  have hle16 : Nat.card S ≤ 16 :=
    hc1 ▸ Nat.le_of_dvd (by rw [hc1]; norm_num)
      (Subgroup.card_dvd_of_le hS1)
  have hdvd4 : 4 ∣ Nat.card S := hcZ ▸ Subgroup.card_dvd_of_le hZS
  have hS16 : Nat.card S ≠ 16 := by
    intro h16
    have hEq : S = CJ z (σ₁ : G) := Subgroup.eq_of_le_of_card_ge hS1 (by rw [h16, hc1])
    have hle : CJ z (σ₁ : G) ≤ CJ z (σ₂ : G) := hEq ▸ inf_le_right
    exact hneG (Subgroup.eq_of_le_of_card_ge hle (by rw [hc1, hc2]))
  have hS4 : Nat.card S = 4 := by
    unfold Nat.ModEq at hmod
    omega
  exact (Subgroup.eq_of_le_of_card_ge hZS (by rw [hS4, hcZ])).symm

theorem fixSubmodule_inf_eq_bot_of_inf_CJ_eq_centerIn (h : Tim79a.ParrottHyp z)
    {σ₁ σ₂ : ↥(H z)} (hσ1 : orderOf σ₁ = 3) (hσ2 : orderOf σ₂ = 3)
    (hZ1 : conjZ z σ₁ = 1) (hZ2 : conjZ z σ₂ = 1)
    (hCJ : CJ z (σ₁ : G) ⊓ CJ z (σ₂ : G) = centerIn (J z)) :
    fixSubmodule h σ₁ ⊓ fixSubmodule h σ₂ = ⊥ := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf] at hv
  have hfix1 : conjV h σ₁ (Additive.toMul v) = Additive.toMul v := by
    rw [← mem_autFixedSubgroup]
    exact (mem_fixSubmodule_iff h σ₁ v).mp hv.1
  have hfix2 : conjV h σ₂ (Additive.toMul v) = Additive.toMul v := by
    rw [← mem_autFixedSubgroup]
    exact (mem_fixSubmodule_iff h σ₂ v).mp hv.2
  obtain ⟨j, hj⟩ := QuotientV.pi_surjective z (Additive.toMul v)
  have hvj : v = Additive.ofMul (QuotientV.pi z j) := by
    rw [hj]
    rfl
  have hfix1' : conjV h σ₁ (QuotientV.pi z j) = QuotientV.pi z j := by
    simpa [hj] using hfix1
  have hfix2' : conjV h σ₂ (QuotientV.pi z j) = QuotientV.pi z j := by
    simpa [hj] using hfix2
  have hj1 : j ∈ centralizerJ σ₁ :=
    mem_centralizerJ_of_conjV_pi_eq (z := z) h
      (by rw [← hσ1]; exact pow_orderOf_eq_one σ₁) hZ1 hfix1'
  have hj2 : j ∈ centralizerJ σ₂ :=
    mem_centralizerJ_of_conjV_pi_eq (z := z) h
      (by rw [← hσ2]; exact pow_orderOf_eq_one σ₂) hZ2 hfix2'
  have hamb1 : (j : G) ∈ CJ z (σ₁ : G) :=
    mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr
      (mem_centralizerJ_iff.mp hj1), j.2⟩
  have hamb2 : (j : G) ∈ CJ z (σ₂ : G) :=
    mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr
      (mem_centralizerJ_iff.mp hj2), j.2⟩
  have hjZ : (j : G) ∈ centerIn (J z) := by
    rw [← hCJ]
    exact Subgroup.mem_inf.mpr ⟨hamb1, hamb2⟩
  have hker : j ∈ (QuotientV.pi z).ker := by
    rw [QuotientV.pi_ker]
    exact Subgroup.mem_subgroupOf.mpr hjZ
  have hpi : QuotientV.pi z j = 1 := MonoidHom.mem_ker.mp hker
  rw [hvj, hpi]
  rfl

theorem isElemAbelian_zpowers_sup (h : Tim79a.ParrottHyp z) {σ₁ σ₂ : ↥(H z)}
    (hσ1 : orderOf σ₁ = 3) (hσ2 : orderOf σ₂ = 3)
    (hcomm : σ₂ * σ₁ = σ₁ * σ₂) :
    CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers σ₁ ⊔ Subgroup.zpowers σ₂) := by
  have hc : Commute σ₁ σ₂ := (commute_iff_eq σ₁ σ₂).mpr hcomm.symm
  have hEcomm : IsMulCommutative (Subgroup.zpowers σ₁ ⊔ Subgroup.zpowers σ₂ : Subgroup (H z)) := by
    rw [Subgroup.sup_eq_closure]
    apply Subgroup.isMulCommutative_closure
    intro x hx y hy _
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact setLike_mul_comm (s := Subgroup.zpowers σ₁) hx hy
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (hc.zpow_left i).zpow_right j
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (hc.symm.zpow_left i).zpow_right j
    · exact setLike_mul_comm (s := Subgroup.zpowers σ₂) hx hy
  constructor
  · exact hEcomm
  · intro x hx
    rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction (p := fun y (_ : y ∈ Subgroup.closure
      ((Subgroup.zpowers σ₁ : Set (H z)) ∪ (Subgroup.zpowers σ₂ : Set (H z)))) =>
        y ^ 3 = 1) ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with hy | hy
      · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        have hcubeNat : σ₁ ^ 3 = 1 := by
          rw [← hσ1]
          exact pow_orderOf_eq_one σ₁
        have hcube : σ₁ ^ (3 : ℤ) = 1 := by
          rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
          exact hcubeNat
        rw [← zpow_natCast]
        rw [← zpow_mul]
        rw [zpow_eq_zpow_emod (i * (↑(3 : ℕ) : ℤ)) hcube]
        have h0 : (i * (↑(3 : ℕ) : ℤ)) % (3 : ℤ) = 0 := by omega
        rw [h0, zpow_zero]
      · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        have hcubeNat : σ₂ ^ 3 = 1 := by
          rw [← hσ2]
          exact pow_orderOf_eq_one σ₂
        have hcube : σ₂ ^ (3 : ℤ) = 1 := by
          rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
          exact hcubeNat
        rw [← zpow_natCast]
        rw [← zpow_mul]
        rw [zpow_eq_zpow_emod (i * (↑(3 : ℕ) : ℤ)) hcube]
        have h0 : (i * (↑(3 : ℕ) : ℤ)) % (3 : ℤ) = 0 := by omega
        rw [h0, zpow_zero]
    · exact one_pow 3
    · intro y z hy hz ihy ihz
      have hyE : y ∈ Subgroup.zpowers σ₁ ⊔ Subgroup.zpowers σ₂ := by
        rw [Subgroup.sup_eq_closure]
        exact hy
      have hzE : z ∈ Subgroup.zpowers σ₁ ⊔ Subgroup.zpowers σ₂ := by
        rw [Subgroup.sup_eq_closure]
        exact hz
      have hyz : Commute y z :=
        (commute_iff_eq y z).mpr
          (congrArg Subtype.val (hEcomm.is_comm.comm ⟨y, hyE⟩ ⟨z, hzE⟩))
      rw [hyz.mul_pow, ihy, ihz, one_mul]
    · intro y hy ihy
      rw [inv_pow, ihy, inv_one]

theorem invariants_zpowers_sup_eq_bot_of_not_equalityBranch (h : Tim79a.ParrottHyp z)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) :
    letI : CommGroup (QuotientV.V z) := commGroupV h
    letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
    Representation.invariants
        ((conjVRepresentation h).comp
          (Subgroup.zpowers (sigma1Nine (z := z) D) ⊔ Subgroup.zpowers σ₂).subtype) = ⊥ := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  have hne : centralizerJ (sigma1Nine (z := z) D) ≠ centralizerJ σ₂ :=
    centralizerJ_ne_of_not_equalityBranch (z := z) h D hIII hσ₂ hq₂
  have hCJ := inf_CJ_eq_centerIn_of_centralizerJ_ne (z := z) D h hσ₂ hq₂ hc₂ hne
  have hfix := fixSubmodule_inf_eq_bot_of_inf_CJ_eq_centerIn (z := z) h
    (sigma1Nine_order (z := z) D) hσ₂ (conjZ_sigma1Nine (z := z) h D)
    (conjZ_eq_one_of_qH_mem_QP45 (z := z) D h σ₂
      (by rw [hq₂]; exact sigma2_mem_Q)) hCJ
  rw [CFSG.SolvableHall.invariants_comp_subtype_sup]
  rw [invariants_zpowers_eq_fixSubmodule, invariants_zpowers_eq_fixSubmodule, hfix]

theorem mem_zpowers_iff_eq_one_or_eq_or_sq {G : Type*} [Group G] {x y : G}
    (hx : orderOf x = 3) :
    y ∈ Subgroup.zpowers x ↔ y = 1 ∨ y = x ∨ y = x ^ 2 := by
  constructor
  · intro hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h3 : x ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, ← hx]
      exact pow_orderOf_eq_one x
    rw [← hk, zpow_eq_zpow_emod k h3]
    have h : k % (3 : ℤ) = 0 ∨ k % (3 : ℤ) = 1 ∨ k % (3 : ℤ) = 2 := by omega
    rcases h with h | h | h
    · left
      rw [h, zpow_zero]
    · right; left
      rw [h]
      norm_num
    · right; right
      rw [h]
      norm_num
  · rintro (h1 | h2 | h3)
    · rw [h1]
      exact Subgroup.one_mem _
    · rw [h2]
      exact Subgroup.mem_zpowers x
    · rw [h3]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 2

theorem E9FixedDimRelation_of_not_equalityBranch (h : Tim79a.ParrottHyp z)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) :
    fixDimV h (sigma1Nine (z := z) D) + fixDimV h σ₂ +
      fixDimV h (sigma1Nine (z := z) D * σ₂) +
      fixDimV h (sigma1Nine (z := z) D * σ₂⁻¹) = 8 := by
  classical
  let σ₁ : ↥(H z) := sigma1Nine (z := z) D
  let E : Subgroup ↥(H z) := Subgroup.zpowers σ₁ ⊔ Subgroup.zpowers σ₂
  have hσ1 : orderOf σ₁ = 3 := sigma1Nine_order (z := z) D
  have hcard1 : Nat.card (Subgroup.zpowers σ₁) = 3 := by
    rw [Nat.card_zpowers, hσ1]
  have hcard2 : Nat.card (Subgroup.zpowers σ₂) = 3 := by
    rw [Nat.card_zpowers, hσ₂]
  have hne : centralizerJ σ₁ ≠ centralizerJ σ₂ :=
    centralizerJ_ne_of_not_equalityBranch (z := z) h D hIII hσ₂ hq₂
  have hcl : ∀ {x y : ↥(H z)}, y ∈ Subgroup.zpowers x →
      centralizerJ x ≤ centralizerJ y := by
    intro x y hy j hj
    rw [mem_centralizerJ_iff] at hj ⊢
    have hcomm : Commute (j : G) (x : G) := (commute_iff_eq _ _).mpr hj
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hcoe : (y : G) = (x : G) ^ k := by
      rw [← hk, Subgroup.coe_zpow]
    rw [hcoe]
    exact (hcomm.zpow_right k).eq
  have hvX : σ₂ ∉ Subgroup.zpowers σ₁ := by
    intro hmem
    have hle : Subgroup.zpowers σ₂ ≤ Subgroup.zpowers σ₁ :=
      Subgroup.zpowers_le.mpr hmem
    have heq : Subgroup.zpowers σ₂ = Subgroup.zpowers σ₁ :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard1, hcard2])
    have h1 : centralizerJ σ₁ ≤ centralizerJ σ₂ := by
      refine hcl ?_
      rw [← heq]
      exact Subgroup.mem_zpowers σ₂
    have h2 : centralizerJ σ₂ ≤ centralizerJ σ₁ := by
      refine hcl ?_
      rw [heq]
      exact Subgroup.mem_zpowers σ₁
    exact hne (le_antisymm h1 h2)
  have hcommAll : ∀ a ∈ Subgroup.zpowers σ₁, a * σ₂ = σ₂ * a := by
    intro a ha
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← hk]
    exact (Commute.zpow_left ((commute_iff_eq _ _).mpr hc₂.symm) k).eq
  have hEea : CFSG.Open.IsElemAbelian 3 E :=
    isElemAbelian_zpowers_sup (z := z) h hσ1 hσ₂ hc₂
  have hinf : Subgroup.zpowers σ₁ ⊓ Subgroup.zpowers σ₂ = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    by_contra ha1
    have ha1' : a ∈ Subgroup.zpowers σ₁ := (Subgroup.mem_inf.mp ha).1
    have ha2' : a ∈ Subgroup.zpowers σ₂ := (Subgroup.mem_inf.mp ha).2
    have haE : a ∈ E := Subgroup.mem_sup_right ha2'
    have horda : orderOf a = 3 := orderOf_eq_prime (hEea.2 a haE) ha1
    have hcarda : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, horda]
    have hle1 : Subgroup.zpowers a ≤ Subgroup.zpowers σ₁ := Subgroup.zpowers_le.mpr ha1'
    have heq1 : Subgroup.zpowers a = Subgroup.zpowers σ₁ :=
      Subgroup.eq_of_le_of_card_ge hle1 (by rw [hcarda, hcard1])
    have hle2 : Subgroup.zpowers a ≤ Subgroup.zpowers σ₂ := Subgroup.zpowers_le.mpr ha2'
    have heq2 : Subgroup.zpowers a = Subgroup.zpowers σ₂ :=
      Subgroup.eq_of_le_of_card_ge hle2 (by rw [hcarda, hcard2])
    have heq12 : Subgroup.zpowers σ₁ = Subgroup.zpowers σ₂ := heq1.symm.trans heq2
    exact hvX (heq12 ▸ Subgroup.mem_zpowers σ₂)
  have hcommAll' : ∀ x ∈ Subgroup.zpowers σ₁, ∀ y ∈ Subgroup.zpowers σ₂,
      x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow ((commute_iff_eq _ _).mpr hc₂.symm) i j).eq
  have hEcard : Nat.card E = 9 := by
    have hc := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (Subgroup.zpowers σ₁) (Subgroup.zpowers σ₂) hcommAll').1
    rw [hinf, Subgroup.card_bot, mul_one, hcard1, hcard2] at hc
    exact hc
  have hmem : ∀ i j : Fin 3, σ₁ ^ (i : ℕ) * σ₂ ^ (j : ℕ) ∈ E := by
    intro i j
    exact Subgroup.mul_mem_sup (Subgroup.pow_mem _ (Subgroup.mem_zpowers σ₁) _)
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers σ₂) _)
  let coord : Fin 3 × Fin 3 → ↥E :=
    fun p => ⟨σ₁ ^ (p.1 : ℕ) * σ₂ ^ (p.2 : ℕ), hmem p.1 p.2⟩
  have hcoord_apply : ∀ p : Fin 3 × Fin 3,
      ((coord p : ↥E) : ↥(H z)) = σ₁ ^ (p.1 : ℕ) * σ₂ ^ (p.2 : ℕ) := fun _ => rfl
  have hsurj : Function.Surjective coord := by
    intro x
    letI : CommGroup ↥E :=
      { (inferInstance : Group ↥E) with mul_comm := fun a b => hEea.1.is_comm.comm a b }
    have hsup : ((Subgroup.zpowers σ₁).subgroupOf E ⊔
        (Subgroup.zpowers σ₂).subgroupOf E : Subgroup ↥E) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (show Subgroup.zpowers σ₁ ≤ E from le_sup_left)
        (show Subgroup.zpowers σ₂ ≤ E from le_sup_right), Subgroup.subgroupOf_self]
    have hx : x ∈ ((Subgroup.zpowers σ₁).subgroupOf E ⊔
        (Subgroup.zpowers σ₂).subgroupOf E : Subgroup ↥E) := by
      rw [hsup]
      exact Subgroup.mem_top x
    rw [Subgroup.mem_sup] at hx
    obtain ⟨u, hu, v, hv, huv⟩ := hx
    have hu' : (u : ↥(H z)) ∈ Subgroup.zpowers σ₁ := Subgroup.mem_subgroupOf.mp hu
    have hv' : (v : ↥(H z)) ∈ Subgroup.zpowers σ₂ := Subgroup.mem_subgroupOf.mp hv
    have hxval : (x : ↥(H z)) = (u : ↥(H z)) * (v : ↥(H z)) := by
      rw [← huv]
      rfl
    rcases (mem_zpowers_iff_eq_one_or_eq_or_sq hσ1).mp hu' with hu1 | hu1 | hu1 <;>
      rcases (mem_zpowers_iff_eq_one_or_eq_or_sq hσ₂).mp hv' with hv1 | hv1 | hv1
    · exact ⟨(0,0), by apply Subtype.ext; simp [coord, hxval, hu1, hv1]⟩
    · exact ⟨(0,1), by apply Subtype.ext; simp [coord, hxval, hu1, hv1]⟩
    · exact ⟨(0,2), by apply Subtype.ext; simp [coord, hxval, hu1, hv1]⟩
    · exact ⟨(1,0), by apply Subtype.ext; simp [coord, hxval, hu1, hv1]⟩
    · exact ⟨(1,1), by apply Subtype.ext; simp [coord, hxval, hu1, hv1]⟩
    · exact ⟨(1,2), by apply Subtype.ext; simp [coord, hxval, hu1, hv1]⟩
    · exact ⟨(2,0), by apply Subtype.ext; simp [coord, hxval, hu1, hv1]⟩
    · exact ⟨(2,1), by apply Subtype.ext; simp [coord, hxval, hu1, hv1]⟩
    · exact ⟨(2,2), by apply Subtype.ext; simp [coord, hxval, hu1, hv1]⟩
  letI : Fintype ↥E := Fintype.ofFinite _
  have hcardcoord : Fintype.card (Fin 3 × Fin 3) = Fintype.card ↥E := by
    have h9 : Fintype.card ↥E = 9 := by
      rw [← Nat.card_eq_fintype_card]
      exact hEcard
    rw [h9]
    simp
  let e : Fin 3 × Fin 3 ≃ ↥E :=
    Equiv.ofBijective coord ((Fintype.bijective_iff_surjective_and_card coord).mpr
      ⟨hsurj, hcardcoord⟩)
  have e_apply : ∀ p : Fin 3 × Fin 3,
      ((e p : ↥E) : ↥(H z)) = σ₁ ^ (p.1 : ℕ) * σ₂ ^ (p.2 : ℕ) := fun p => rfl

  have hnot2 : σ₁ ∉ Subgroup.zpowers σ₂ := by
    intro hmem
    have hle : Subgroup.zpowers σ₁ ≤ Subgroup.zpowers σ₂ := Subgroup.zpowers_le.mpr hmem
    have heq : Subgroup.zpowers σ₁ = Subgroup.zpowers σ₂ :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard2, hcard1])
    exact hvX (heq ▸ Subgroup.mem_zpowers σ₂)
  have hσ12mem : σ₁ * σ₂ ∈ E :=
    Subgroup.mul_mem_sup (Subgroup.mem_zpowers σ₁) (Subgroup.mem_zpowers σ₂)
  have hσ12ne : σ₁ * σ₂ ≠ 1 := by
    intro h1
    have hσ1eq : σ₁ = σ₂⁻¹ := eq_inv_of_mul_eq_one_left h1
    exact hnot2 (by rw [hσ1eq]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers σ₂))
  have hσ12ord : orderOf (σ₁ * σ₂) = 3 :=
    orderOf_eq_prime (hEea.2 _ hσ12mem) hσ12ne
  have hσ12invmem : σ₁ * σ₂⁻¹ ∈ E :=
    Subgroup.mul_mem_sup (Subgroup.mem_zpowers σ₁)
      (Subgroup.inv_mem _ (Subgroup.mem_zpowers σ₂))
  have hσ12invne : σ₁ * σ₂⁻¹ ≠ 1 := by
    intro h1
    have hσ1eq : σ₁ = σ₂ := by simpa using eq_inv_of_mul_eq_one_left h1
    exact hnot2 (by rw [hσ1eq]; exact Subgroup.mem_zpowers σ₂)
  have hσ12invord : orderOf (σ₁ * σ₂⁻¹) = 3 :=
    orderOf_eq_prime (hEea.2 _ hσ12invmem) hσ12invne
  have hσ2cube : σ₂ ^ 3 = 1 := by rw [← hσ₂]; exact pow_orderOf_eq_one σ₂
  have hinv2 : σ₂⁻¹ = σ₂ ^ 2 := by
    rw [inv_eq_of_mul_eq_one_right]
    rw [← pow_succ']
    exact hσ2cube
  have hcomm12 : Commute σ₁ σ₂ := (commute_iff_eq _ _).mpr hc₂.symm
  have hsq12 : (σ₁ * σ₂) ^ 2 = σ₁ ^ 2 * σ₂ ^ 2 := hcomm12.mul_pow 2
  have hsqg : (σ₁ * σ₂⁻¹) ^ 2 = σ₁ ^ 2 * σ₂ := by
    have hb4 : (σ₂ ^ 2) ^ 2 = σ₂ := by
      rw [← pow_mul]
      rw [show (2:ℕ) * 2 = 4 from rfl]
      rw [show (4:ℕ) = 3 + 1 from rfl, pow_succ, hσ2cube, one_mul]
    rw [Commute.mul_pow (hcomm12.inv_right) 2, hinv2, hb4]
  have hB1mem : ∀ x : ↥E, (x : ↥(H z)) ∈ Subgroup.zpowers σ₁ ↔
      x = e (0,0) ∨ x = e (1,0) ∨ x = e (2,0) := by
    intro x
    rw [mem_zpowers_iff_eq_one_or_eq_or_sq hσ1]
    constructor
    · rintro (h | h | h)
      · exact Or.inl (Subtype.ext (by rw [e_apply]; simpa using h))
      · exact Or.inr (Or.inl (Subtype.ext (by rw [e_apply]; simpa using h)))
      · exact Or.inr (Or.inr (Subtype.ext (by rw [e_apply]; simpa using h)))
    · rintro (h | h | h)
      · left; rw [h, e_apply]; simp
      · right; left; rw [h, e_apply]; simp
      · right; right; rw [h, e_apply]; simp
  have hB2mem : ∀ x : ↥E, (x : ↥(H z)) ∈ Subgroup.zpowers σ₂ ↔
      x = e (0,0) ∨ x = e (0,1) ∨ x = e (0,2) := by
    intro x
    rw [mem_zpowers_iff_eq_one_or_eq_or_sq hσ₂]
    constructor
    · rintro (h | h | h)
      · exact Or.inl (Subtype.ext (by rw [e_apply]; simpa using h))
      · exact Or.inr (Or.inl (Subtype.ext (by rw [e_apply]; simpa using h)))
      · exact Or.inr (Or.inr (Subtype.ext (by rw [e_apply]; simpa using h)))
    · rintro (h | h | h)
      · left; rw [h, e_apply]; simp
      · right; left; rw [h, e_apply]; simp
      · right; right; rw [h, e_apply]; simp
  have hB3mem : ∀ x : ↥E, (x : ↥(H z)) ∈ Subgroup.zpowers (σ₁ * σ₂) ↔
      x = e (0,0) ∨ x = e (1,1) ∨ x = e (2,2) := by
    intro x
    rw [mem_zpowers_iff_eq_one_or_eq_or_sq hσ12ord]
    constructor
    · rintro (h | h | h)
      · exact Or.inl (Subtype.ext (by rw [e_apply]; simpa using h))
      · exact Or.inr (Or.inl (Subtype.ext (by rw [e_apply]; simpa using h)))
      · refine Or.inr (Or.inr (Subtype.ext ?_))
        rw [e_apply]; simp; rw [← hsq12]; exact h
    · rintro (h | h | h)
      · left; rw [h, e_apply]; simp
      · right; left; rw [h, e_apply]; simp
      · right; right; rw [h, e_apply, hsq12]; simp
  have hB4mem : ∀ x : ↥E, (x : ↥(H z)) ∈ Subgroup.zpowers (σ₁ * σ₂⁻¹) ↔
      x = e (0,0) ∨ x = e (1,2) ∨ x = e (2,1) := by
    intro x
    rw [mem_zpowers_iff_eq_one_or_eq_or_sq hσ12invord]
    constructor
    · rintro (h | h | h)
      · exact Or.inl (Subtype.ext (by rw [e_apply]; simpa using h))
      · refine Or.inr (Or.inl (Subtype.ext ?_))
        rw [e_apply]; simp; rw [← hinv2]; exact h
      · refine Or.inr (Or.inr (Subtype.ext ?_))
        rw [e_apply]; simp; rw [← hsqg]; exact h
    · rintro (h | h | h)
      · left; rw [h, e_apply]; simp
      · right; left
        rw [h, e_apply]; simp; rw [hinv2]
      · right; right
        rw [h, e_apply]; simp; rw [hsqg]

  have hB1le : Subgroup.zpowers σ₁ ≤ E := le_sup_left
  have hB2le : Subgroup.zpowers σ₂ ≤ E := le_sup_right
  have hB3le : Subgroup.zpowers (σ₁ * σ₂) ≤ E := Subgroup.zpowers_le.mpr hσ12mem
  have hB4le : Subgroup.zpowers (σ₁ * σ₂⁻¹) ≤ E := Subgroup.zpowers_le.mpr hσ12invmem
  have hB1rel : (Subgroup.zpowers σ₁).relIndex E = 3 := by
    have h := Subgroup.relIndex_mul_card (H := Subgroup.zpowers σ₁) (K := E)
    rw [inf_eq_left.mpr hB1le, hcard1, hEcard] at h
    omega
  have hB2rel : (Subgroup.zpowers σ₂).relIndex E = 3 := by
    have h := Subgroup.relIndex_mul_card (H := Subgroup.zpowers σ₂) (K := E)
    rw [inf_eq_left.mpr hB2le, hcard2, hEcard] at h
    omega
  have hB3card : Nat.card (Subgroup.zpowers (σ₁ * σ₂)) = 3 := by
    rw [Nat.card_zpowers, hσ12ord]
  have hB4card : Nat.card (Subgroup.zpowers (σ₁ * σ₂⁻¹)) = 3 := by
    rw [Nat.card_zpowers, hσ12invord]
  have hB3rel : (Subgroup.zpowers (σ₁ * σ₂)).relIndex E = 3 := by
    have h := Subgroup.relIndex_mul_card (H := Subgroup.zpowers (σ₁ * σ₂)) (K := E)
    rw [inf_eq_left.mpr hB3le, hB3card, hEcard] at h
    omega
  have hB4rel : (Subgroup.zpowers (σ₁ * σ₂⁻¹)).relIndex E = 3 := by
    have h := Subgroup.relIndex_mul_card (H := Subgroup.zpowers (σ₁ * σ₂⁻¹)) (K := E)
    rw [inf_eq_left.mpr hB4le, hB4card, hEcard] at h
    omega
  have hB1neB2 : Subgroup.zpowers σ₁ ≠ Subgroup.zpowers σ₂ := by
    intro hEq
    have hmem : (e (1,0) : ↥(H z)) ∈ Subgroup.zpowers σ₂ := by
      rw [← hEq, e_apply]; simp
    rw [hB2mem (e (1,0))] at hmem
    rcases hmem with h | h | h
    · exact absurd (e.injective h) (by decide)
    · exact absurd (e.injective h) (by decide)
    · exact absurd (e.injective h) (by decide)
  have hB1neB3 : Subgroup.zpowers σ₁ ≠ Subgroup.zpowers (σ₁ * σ₂) := by
    intro hEq
    have hmem : (e (1,0) : ↥(H z)) ∈ Subgroup.zpowers (σ₁ * σ₂) := by
      rw [← hEq, e_apply]; simp
    rw [hB3mem (e (1,0))] at hmem
    rcases hmem with h | h | h
    · exact absurd (e.injective h) (by decide)
    · exact absurd (e.injective h) (by decide)
    · exact absurd (e.injective h) (by decide)
  have hB1neB4 : Subgroup.zpowers σ₁ ≠ Subgroup.zpowers (σ₁ * σ₂⁻¹) := by
    intro hEq
    have hmem : (e (1,0) : ↥(H z)) ∈ Subgroup.zpowers (σ₁ * σ₂⁻¹) := by
      rw [← hEq, e_apply]; simp
    rw [hB4mem (e (1,0))] at hmem
    rcases hmem with h | h | h
    · exact absurd (e.injective h) (by decide)
    · exact absurd (e.injective h) (by decide)
    · exact absurd (e.injective h) (by decide)
  have hB2neB3 : Subgroup.zpowers σ₂ ≠ Subgroup.zpowers (σ₁ * σ₂) := by
    intro hEq
    have hmem : (e (0,1) : ↥(H z)) ∈ Subgroup.zpowers (σ₁ * σ₂) := by
      rw [← hEq, e_apply]; simp
    rw [hB3mem (e (0,1))] at hmem
    rcases hmem with h | h | h
    · exact absurd (e.injective h) (by decide)
    · exact absurd (e.injective h) (by decide)
    · exact absurd (e.injective h) (by decide)
  have hB2neB4 : Subgroup.zpowers σ₂ ≠ Subgroup.zpowers (σ₁ * σ₂⁻¹) := by
    intro hEq
    have hmem : (e (0,1) : ↥(H z)) ∈ Subgroup.zpowers (σ₁ * σ₂⁻¹) := by
      rw [← hEq, e_apply]; simp
    rw [hB4mem (e (0,1))] at hmem
    rcases hmem with h | h | h
    · exact absurd (e.injective h) (by decide)
    · exact absurd (e.injective h) (by decide)
    · exact absurd (e.injective h) (by decide)
  have hB3neB4 : Subgroup.zpowers (σ₁ * σ₂) ≠ Subgroup.zpowers (σ₁ * σ₂⁻¹) := by
    intro hEq
    have hmem : (e (1,1) : ↥(H z)) ∈ Subgroup.zpowers (σ₁ * σ₂⁻¹) := by
      rw [← hEq, e_apply]; simp
    rw [hB4mem (e (1,1))] at hmem
    rcases hmem with h | h | h
    · exact absurd (e.injective h) (by decide)
    · exact absurd (e.injective h) (by decide)
    · exact absurd (e.injective h) (by decide)
  let b : Fin 4 → {B : Subgroup ↥(H z) // B ≤ E ∧ B.relIndex E = 3} :=
    ![⟨Subgroup.zpowers σ₁, hB1le, hB1rel⟩,
      ⟨Subgroup.zpowers σ₂, hB2le, hB2rel⟩,
      ⟨Subgroup.zpowers (σ₁ * σ₂), hB3le, hB3rel⟩,
      ⟨Subgroup.zpowers (σ₁ * σ₂⁻¹), hB4le, hB4rel⟩]
  have hcover : ∀ B : {B : Subgroup ↥(H z) // B ≤ E ∧ B.relIndex E = 3},
      B = b 0 ∨ B = b 1 ∨ B = b 2 ∨ B = b 3 := by
    intro B
    have hBcard : Nat.card B.1 = 3 := by
      have h := Subgroup.relIndex_mul_card (H := B.1) (K := E)
      rw [inf_eq_left.mpr B.2.1, B.2.2, hEcard] at h
      omega
    haveI : Nontrivial ↥B.1 := Finite.one_lt_card_iff_nontrivial.mp (by rw [hBcard]; norm_num)
    obtain ⟨x, hx1⟩ := exists_ne (1 : ↥B.1)
    have hxmem : (x : ↥(H z)) ∈ B.1 := x.2
    have hxne : (x : ↥(H z)) ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hxord : orderOf (x : ↥(H z)) = 3 :=
      orderOf_eq_prime (hEea.2 _ (B.2.1 hxmem)) hxne
    have hxBz : B.1 = Subgroup.zpowers (x : ↥(H z)) := by
      refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
      · exact Subgroup.zpowers_le.mpr hxmem
      · rw [hBcard, Nat.card_zpowers, hxord]
    obtain ⟨p, hp⟩ := hsurj ⟨(x : ↥(H z)), B.2.1 hxmem⟩
    obtain ⟨i, j⟩ := p
    have hxcoord : (x : ↥(H z)) = σ₁ ^ (i : ℕ) * σ₂ ^ (j : ℕ) := by
      have h := congrArg (fun w : ↥E => (w : ↥(H z))) hp
      simpa [hcoord_apply] using h.symm
    have hp_ne : (i, j) ≠ (0, 0) := by
      intro h0
      apply hxne
      have hi : i = 0 := congrArg Prod.fst h0
      have hj : j = 0 := congrArg Prod.snd h0
      rw [hxcoord, hi, hj]
      simp
    have hxmem4 : (x : ↥(H z)) ∈ Subgroup.zpowers σ₁ ∨
        (x : ↥(H z)) ∈ Subgroup.zpowers σ₂ ∨
        (x : ↥(H z)) ∈ Subgroup.zpowers (σ₁ * σ₂) ∨
        (x : ↥(H z)) ∈ Subgroup.zpowers (σ₁ * σ₂⁻¹) := by
      fin_cases i <;> fin_cases j
      · exact absurd rfl hp_ne
      · exact Or.inr (Or.inl (by rw [hxcoord]; simp))
      · exact Or.inr (Or.inl (by rw [hxcoord]; simp))
      · exact Or.inl (by rw [hxcoord]; simp)
      · exact Or.inr (Or.inr (Or.inl (by rw [hxcoord]; simp)))
      · refine Or.inr (Or.inr (Or.inr ?_))
        rw [hxcoord]; simp; rw [← hinv2]; exact Subgroup.mem_zpowers _
      · exact Or.inl (by rw [hxcoord]; simp)
      · refine Or.inr (Or.inr (Or.inr ?_))
        rw [hxcoord]; simp; rw [← hsqg]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
      · refine Or.inr (Or.inr (Or.inl ?_))
        rw [hxcoord]
        simp
        rw [← hsq12]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
    rcases hxmem4 with hx1mem | hx2mem | hx3mem | hx4mem
    · left
      have hle : Subgroup.zpowers (x : ↥(H z)) ≤ Subgroup.zpowers σ₁ :=
        Subgroup.zpowers_le.mpr hx1mem
      have heq : Subgroup.zpowers (x : ↥(H z)) = Subgroup.zpowers σ₁ :=
        Subgroup.eq_of_le_of_card_ge hle (by simp [hxord, hcard1])
      apply Subtype.ext
      show B.1 = Subgroup.zpowers σ₁
      rw [hxBz, heq]
    · right; left
      have hle : Subgroup.zpowers (x : ↥(H z)) ≤ Subgroup.zpowers σ₂ :=
        Subgroup.zpowers_le.mpr hx2mem
      have heq : Subgroup.zpowers (x : ↥(H z)) = Subgroup.zpowers σ₂ :=
        Subgroup.eq_of_le_of_card_ge hle (by simp [hxord, hcard2])
      apply Subtype.ext
      show B.1 = Subgroup.zpowers σ₂
      rw [hxBz, heq]
    · right; right; left
      have hle : Subgroup.zpowers (x : ↥(H z)) ≤ Subgroup.zpowers (σ₁ * σ₂) :=
        Subgroup.zpowers_le.mpr hx3mem
      have heq : Subgroup.zpowers (x : ↥(H z)) = Subgroup.zpowers (σ₁ * σ₂) :=
        Subgroup.eq_of_le_of_card_ge hle (by simp [hxord, hB3card])
      apply Subtype.ext
      show B.1 = Subgroup.zpowers (σ₁ * σ₂)
      rw [hxBz, heq]
    · right; right; right
      have hle : Subgroup.zpowers (x : ↥(H z)) ≤ Subgroup.zpowers (σ₁ * σ₂⁻¹) :=
        Subgroup.zpowers_le.mpr hx4mem
      have heq : Subgroup.zpowers (x : ↥(H z)) = Subgroup.zpowers (σ₁ * σ₂⁻¹) :=
        Subgroup.eq_of_le_of_card_ge hle (by simp [hxord, hB4card])
      apply Subtype.ext
      show B.1 = Subgroup.zpowers (σ₁ * σ₂⁻¹)
      rw [hxBz, heq]
  have hb_surj : Function.Surjective b := by
    intro B
    rcases hcover B with h | h | h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩
    · exact ⟨3, h.symm⟩
  have hb_inj : Function.Injective b := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd (congrArg Subtype.val hij) hB1neB2
    · exact absurd (congrArg Subtype.val hij) hB1neB3
    · exact absurd (congrArg Subtype.val hij) hB1neB4
    · exact absurd (congrArg Subtype.val hij) (Ne.symm hB1neB2)
    · rfl
    · exact absurd (congrArg Subtype.val hij) hB2neB3
    · exact absurd (congrArg Subtype.val hij) hB2neB4
    · exact absurd (congrArg Subtype.val hij) (Ne.symm hB1neB3)
    · exact absurd (congrArg Subtype.val hij) (Ne.symm hB2neB3)
    · rfl
    · exact absurd (congrArg Subtype.val hij) hB3neB4
    · exact absurd (congrArg Subtype.val hij) (Ne.symm hB1neB4)
    · exact absurd (congrArg Subtype.val hij) (Ne.symm hB2neB4)
    · exact absurd (congrArg Subtype.val hij) (Ne.symm hB3neB4)
    · rfl

  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  have hσ1ne : σ₁ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hσ1
    norm_num at hσ1
  have hfix : Representation.invariants
      ((conjVRepresentation h).comp E.subtype) = ⊥ :=
    invariants_zpowers_sup_eq_bot_of_not_equalityBranch (z := z) D h hIII hσ₂ hq₂ hc₂
  have hA1 : E ≠ ⊥ := by
    intro hbot
    have hmem : σ₁ ∈ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers σ₁)
    rw [hbot] at hmem
    exact hσ1ne (Subgroup.mem_bot.mp hmem)
  have hIndep := CFSG.SolvableHall.iSupIndep_invariants_hyperplanes
    (conjVRepresentation h) Nat.prime_two Nat.prime_three (by norm_num) hEea hfix
  have hTop := CFSG.SolvableHall.iSup_invariants_hyperplanes_eq_top
    (conjVRepresentation h) Nat.prime_two Nat.prime_three (by norm_num) hEea hA1
  let P : {B : Subgroup ↥(H z) // B ≤ E ∧ B.relIndex E = 3} → Type :=
    fun B => ↥(Representation.invariants ((conjVRepresentation h).comp B.1.subtype))
  letI : Fintype {B : Subgroup ↥(H z) // B ≤ E ∧ B.relIndex E = 3} := Fintype.ofFinite _
  haveI : Finite (Additive (QuotientV.V z)) := inferInstance
  haveI : ∀ B, Module.Free (ZMod 2) (P B) := fun B => Module.Free.of_divisionRing (ZMod 2) (P B)
  haveI : ∀ B, Module.Finite (ZMod 2) (P B) := fun B => Module.Finite.of_finite
  have hdim : Module.finrank (ZMod 2) (Additive (QuotientV.V z)) =
      ∑ B : {B : Subgroup ↥(H z) // B ≤ E ∧ B.relIndex E = 3},
        Module.finrank (ZMod 2) (P B) := by
    calc Module.finrank (ZMod 2) (Additive (QuotientV.V z))
        = Module.finrank (ZMod 2)
            (Π₀ B : {B : Subgroup ↥(H z) // B ≤ E ∧ B.relIndex E = 3}, P B) :=
          (LinearEquiv.finrank_eq (hIndep.linearEquiv hTop)).symm
      _ = Module.finrank (ZMod 2)
            (Π B : {B : Subgroup ↥(H z) // B ≤ E ∧ B.relIndex E = 3}, P B) :=
          LinearEquiv.finrank_eq (DFinsupp.linearEquivFunOnFintype (R := ZMod 2) (M := P))
      _ = ∑ B : {B : Subgroup ↥(H z) // B ≤ E ∧ B.relIndex E = 3},
            Module.finrank (ZMod 2) (P B) := Module.finrank_pi_fintype (R := ZMod 2) (M := P)
  let e4 : Fin 4 ≃ {B : Subgroup ↥(H z) // B ≤ E ∧ B.relIndex E = 3} :=
    Equiv.ofBijective b ⟨hb_inj, hb_surj⟩
  have hsum_eval : ∑ B : {B : Subgroup ↥(H z) // B ≤ E ∧ B.relIndex E = 3},
      Module.finrank (ZMod 2) (P B) =
      Module.finrank (ZMod 2) (P (b 0)) + Module.finrank (ZMod 2) (P (b 1)) +
      Module.finrank (ZMod 2) (P (b 2)) + Module.finrank (ZMod 2) (P (b 3)) := by
    rw [← Equiv.sum_comp e4 (fun B => Module.finrank (ZMod 2) (P B))]
    change ∑ i : Fin 4, Module.finrank (ZMod 2) (P (b i)) = _
    exact Fin.sum_univ_four _
  have hf0 : Module.finrank (ZMod 2) (P (b 0)) = fixDimV h σ₁ :=
    finrank_invariants_zpowers h σ₁
  have hf1 : Module.finrank (ZMod 2) (P (b 1)) = fixDimV h σ₂ :=
    finrank_invariants_zpowers h σ₂
  have hf2 : Module.finrank (ZMod 2) (P (b 2)) = fixDimV h (σ₁ * σ₂) :=
    finrank_invariants_zpowers h (σ₁ * σ₂)
  have hf3 : Module.finrank (ZMod 2) (P (b 3)) = fixDimV h (σ₁ * σ₂⁻¹) :=
    finrank_invariants_zpowers h (σ₁ * σ₂⁻¹)
  have hfinal : fixDimV h σ₁ + fixDimV h σ₂ + fixDimV h (σ₁ * σ₂) +
      fixDimV h (σ₁ * σ₂⁻¹) = 8 := by
    rw [← hf0, ← hf1, ← hf2, ← hf3, ← hsum_eval, ← hdim, finrank_addV h]
  exact hfinal

@[expose] def E27LineCountData (h : Tim79a.ParrottHyp z) (D : QuotientData (z := z) hN)
    (σ₂ : ↥(H z)) : Prop :=
  3 * fixDimV h (sigma1Nine (z := z) D * σ₂) +
      6 * fixDimV h (sigma1Nine (z := z) D * σ₂⁻¹) = 24

theorem fixDimV_sigma1Nine_mul_sigma2_eq_zero_of_not_equalityBranch
    (h : Tim79a.ParrottHyp z)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    (hE27 : E27LineCountData (z := z) (D := D) h σ₂) :
    fixDimV h (sigma1Nine (z := z) D * σ₂) = 0 := by
  have hd2 : fixDimV h σ₂ = 2 :=
    fixDimV_eq_two_sigma2_of_not_equalityBranch (z := z) D h hIII hσ₂ hq₂ hc₂
  have hd1 : fixDimV h (sigma1Nine (z := z) D) = 2 :=
    fixDimV_sigma1Nine (z := z) (D := D) h
  have hE9 : fixDimV h (sigma1Nine (z := z) D) + fixDimV h σ₂ +
      fixDimV h (sigma1Nine (z := z) D * σ₂) +
      fixDimV h (sigma1Nine (z := z) D * σ₂⁻¹) = 8 :=
    E9FixedDimRelation_of_not_equalityBranch (z := z) D h hIII hσ₂ hq₂ hc₂
  unfold E27LineCountData at hE27
  omega

theorem fixDimV_sigma1Nine_mul_sigma2_inv_eq_four_of_not_equalityBranch
    (h : Tim79a.ParrottHyp z)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    (hE27 : E27LineCountData (z := z) (D := D) h σ₂) :
    fixDimV h (sigma1Nine (z := z) D * σ₂⁻¹) = 4 := by
  have hd2 : fixDimV h σ₂ = 2 :=
    fixDimV_eq_two_sigma2_of_not_equalityBranch (z := z) D h hIII hσ₂ hq₂ hc₂
  have hd1 : fixDimV h (sigma1Nine (z := z) D) = 2 :=
    fixDimV_sigma1Nine (z := z) (D := D) h
  have hE9 : fixDimV h (sigma1Nine (z := z) D) + fixDimV h σ₂ +
      fixDimV h (sigma1Nine (z := z) D * σ₂) +
      fixDimV h (sigma1Nine (z := z) D * σ₂⁻¹) = 8 :=
    E9FixedDimRelation_of_not_equalityBranch (z := z) D h hIII hσ₂ hq₂ hc₂
  unfold E27LineCountData at hE27
  omega

end CFSG.RankThree.GF2n.Parrott
