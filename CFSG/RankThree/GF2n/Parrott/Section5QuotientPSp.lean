module

public import CFSG.RankThree.GF2n.Parrott.Section5QuotientC
public import CFSG.RankThree.GF2n.Parrott.Section5LocalT
public import CFSG.Sporadic.Co2Smith.GlC0JankoA

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z z₁ : G}

theorem nonempty_quotientDataPSp_quotW (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) :
    Nonempty (QuotientDataPSp (quotW hzC) (J_subgroupOf_normal (quotW hzC))) := by
  classical
  obtain ⟨_, ⟨D⟩⟩ := parrottQuotientDataExists h
  let D' : QuotientData z (J_subgroupOf_normal z) := D
  let C : Subgroup G := Subgroup.centralizer ({z₁} : Set G)
  let H₁ : Subgroup G := H z ⊓ C
  have hJH₁ : J z ≤ H₁ := by
    simpa only [H₁, C] using J_le_inf_centralizer_z1 (z := z) (z₁ := z₁) hz₁
  let K₁ : Subgroup ↥H₁ := (J z).comap H₁.subtype
  let ψ : ↥H₁ →* ↥QP45.originalSubgroup :=
    (Subgroup.subgroupOfEquivOfLe QP45_le_QA45).toMonoidHom.comp
      (((qH D').comp (Subgroup.inclusion inf_le_left)).codRestrict
        (QP45.originalSubgroup.subgroupOf QA45.originalSubgroup)
        (fun x => (mem_centralizer_z1_iff_qH_mem_QP45 (z := z) D' h hZ hz₁ hz₁z hz₁2
          ⟨x, (Subgroup.mem_inf.mp x.2).1⟩).mp (Subgroup.mem_inf.mp x.2).2))
  have hψs : Function.Surjective ψ := by
    intro y
    let yA : ↥QA45.originalSubgroup := ⟨y, QP45_le_QA45 y.2⟩
    obtain ⟨x, hx⟩ := qH_surjective D' yA
    have hxC : (x : G) ∈ C := by
      change (x : G) ∈ Subgroup.centralizer ({z₁} : Set G)
      exact (mem_centralizer_z1_iff_qH_mem_QP45 (z := z) D' h hZ hz₁ hz₁z hz₁2 x).mpr
        (by rw [hx]; exact y.2)
    refine ⟨⟨x, x.2, hxC⟩, ?_⟩
    apply Subtype.ext
    exact (Subgroup.subgroupOfEquivOfLe_apply_coe QP45_le_QA45 _).trans
      (congrArg Subtype.val hx)
  have hkerψ : ψ.ker = K₁ := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hq : qH D' ⟨x, (Subgroup.mem_inf.mp x.2).1⟩ = 1 := by
        have h1 : (((qH D').comp (Subgroup.inclusion inf_le_left)).codRestrict
              (QP45.originalSubgroup.subgroupOf QA45.originalSubgroup) _ x) = 1 :=
          (MulEquiv.map_eq_one_iff (Subgroup.subgroupOfEquivOfLe QP45_le_QA45)).mp hx
        exact congrArg Subtype.val h1
      have hxJ : (x : G) ∈ J z :=
        Subgroup.mem_subgroupOf.mp ((J_mem_iff D' ⟨x, (Subgroup.mem_inf.mp x.2).1⟩).mpr hq)
      exact Subgroup.mem_comap.mpr hxJ
    · intro hx
      have hxJ : (x : G) ∈ J z := Subgroup.mem_comap.mp hx
      have hq : qH D' ⟨x, (Subgroup.mem_inf.mp x.2).1⟩ = 1 :=
        (J_mem_iff D' ⟨x, (Subgroup.mem_inf.mp x.2).1⟩).mp (Subgroup.mem_subgroupOf.mpr hxJ)
      change (Subgroup.subgroupOfEquivOfLe QP45_le_QA45)
        (((qH D').comp (Subgroup.inclusion inf_le_left)).codRestrict
          (QP45.originalSubgroup.subgroupOf QA45.originalSubgroup) _ x) = 1
      rw [MulEquiv.map_eq_one_iff]
      refine Subtype.ext ?_
      exact hq
  let Φ : ↥H₁ →* (↥(H (quotW hzC)) ⧸ (J (quotW hzC)).subgroupOf (H (quotW hzC))) :=
    (QuotientGroup.mk' ((J (quotW hzC)).subgroupOf (H (quotW hzC)))).comp
      (quotHH₁ h hZ hz₁ hz₁z hz₁2 hzC)
  have hΦs : Function.Surjective Φ := by
    intro a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨x, hx⟩ := quotHH₁_surjective h hZ hz₁ hz₁z hz₁2 hzC b
    exact ⟨x, by simp [Φ, hx]⟩
  have hkerΦ : Φ.ker = K₁ := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      obtain ⟨y, hyJ, hqy⟩ :=
        (mem_J_quotW_iff_of_ne h hZ hz₁ hz₁z hz₁2 hzC (quotH₁ z z₁ x)).mp hx
      let xH : ↥H₁ := ⟨y, (Subgroup.mem_inf.mp (hJH₁ hyJ)).1, y.2⟩
      have hq : quotH₁ z z₁ xH = quotH₁ z z₁ x := hqy
      have hmem : xH⁻¹ * x ∈ (quotH₁ z z₁).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hq, inv_mul_cancel]
      have hzp : ((xH⁻¹ * x : ↥H₁) : G) ∈ Subgroup.zpowers z₁ :=
        (mem_ker_quotH₁_iff _).mp hmem
      have hJ : ((xH⁻¹ * x : ↥H₁) : G) ∈ J z :=
        zpowers_le_J_of_mem_centerIn hz₁ hzp
      have hx_eq : (x : G) = (y : G) * ((xH⁻¹ * x : ↥H₁) : G) := by
        show (x : G) = (y : G) * ((y : G)⁻¹ * (x : G))
        group
      rw [Subgroup.mem_comap]
      change (x : G) ∈ J z
      rw [hx_eq]
      exact (J z).mul_mem hyJ hJ
    · intro hx
      have hxJ : (x : G) ∈ J z := Subgroup.mem_comap.mp hx
      exact (mem_J_quotW_iff_of_ne h hZ hz₁ hz₁z hz₁2 hzC (quotH₁ z z₁ x)).mpr
        ⟨⟨x, (Subgroup.mem_inf.mp x.2).2⟩, hxJ, rfl⟩
  exact ⟨{ X := ↥QP45.originalSubgroup
           instX := inferInstance
           lie := CFSG.Sporadic.Co2Smith.lieModel_QP45
           iso := (QuotientGroup.quotientKerEquivOfSurjective Φ hΦs).symm.trans
             ((QuotientGroup.quotientMulEquivOfEq (hkerΦ.trans hkerψ.symm)).trans
               (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)) }⟩

end CFSG.RankThree.GF2n.Parrott
