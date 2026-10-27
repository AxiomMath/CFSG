module

public import CFSG.RankThree.GF2n.Parrott.Section4QuotientHypA
public import CFSG.RankThree.GF2n.Parrott.Section5Lemma52
public import CFSG.GroupTheory.PCore.PCoreOfNormalEq

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z z₁ : G}

theorem not_isConj_z_mul_z1_of_ne (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2) :
    ¬ IsConj z (z * z₁) := by
  intro hconj
  obtain ⟨x, hxH, hxC⟩ := exists_mem_H_not_mem_centralizer_z1 h hZ hz₁ hz₁z hz₁2
  have hx : x * z₁ * x⁻¹ = z * z₁ :=
    conj_z1_eq_of_not_mem_centralizer h hz₁ hz₁z hz₁2 hxH hxC
  exact not_isConj_z_z1 h hZ hz₁ hz₁z hz₁2
    (hconj.trans (isConj_iff.mpr ⟨x, hx⟩).symm)

theorem centralizer_quotW_eq_map_of_ne (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) :
    Subgroup.centralizer ({quotW hzC} : Set (QuotC z₁)) =
      ((H z).subgroupOf (Subgroup.centralizer ({z₁} : Set G))).map (quotMk z₁) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    have h1 : (QuotientGroup.mk (x * ⟨z, hzC⟩) : QuotC z₁) =
        QuotientGroup.mk (⟨z, hzC⟩ * x) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact hy
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
    have h2 : z⁻¹ * (x : G)⁻¹ * z * (x : G) ∈ Subgroup.zpowers z₁ := by
      have e : (((x * ⟨z, hzC⟩)⁻¹ * (⟨z, hzC⟩ * x) :
          ↥(Subgroup.centralizer ({z₁} : Set G))) : G) =
          z⁻¹ * (x : G)⁻¹ * z * (x : G) := by
        show ((x : G) * z)⁻¹ * (z * (x : G)) = _
        group
      rwa [e] at h1
    refine Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    show (x : G) ∈ H z
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hz₁2 h2 with h3 | h3
    · rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
      have e : (x : G) * z * (z⁻¹ * (x : G)⁻¹ * z * (x : G)) = z * (x : G) := by
        group
      rw [h3, mul_one] at e
      exact e
    · exfalso
      apply not_isConj_z_mul_z1_of_ne h hZ hz₁ hz₁z hz₁2
      refine isConj_iff.mpr ⟨(x : G)⁻¹, ?_⟩
      have e : z * (z⁻¹ * (x : G)⁻¹ * z * (x : G)) =
          (x : G)⁻¹ * z * ((x : G)⁻¹)⁻¹ := by group
      rw [← e, h3]
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxz : (x : G) * z = z * (x : G) := by
      have := Subgroup.mem_subgroupOf.mp hx
      rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at this
      exact this
    show quotMk z₁ x * quotW hzC = quotW hzC * quotMk z₁ x
    rw [quotMk, quotW, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hxz

@[expose] noncomputable def quotH₁ (z z₁ : G) :
    ↥(H z ⊓ Subgroup.centralizer ({z₁} : Set G)) →* QuotC z₁ :=
  (quotMk z₁).comp (Subgroup.inclusion inf_le_right)

omit [Finite G] in
theorem mem_ker_quotH₁_iff (x : ↥(H z ⊓ Subgroup.centralizer ({z₁} : Set G))) :
    x ∈ (quotH₁ z z₁).ker ↔ (x : G) ∈ Subgroup.zpowers z₁ := by
  rw [MonoidHom.mem_ker, quotH₁, MonoidHom.comp_apply, quotMk, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  rfl

theorem quotH₁_mem_H_of_ne (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z))
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G))
    (x : ↥(H z ⊓ Subgroup.centralizer ({z₁} : Set G))) :
    quotH₁ z z₁ x ∈ H (quotW hzC) := by
  rw [H_eq_centralizer, centralizer_quotW_eq_map_of_ne h hZ hz₁ hz₁z hz₁2 hzC]
  exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion inf_le_right x,
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp x.2).1, rfl⟩

@[expose] noncomputable def quotHH₁ (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) :
    ↥(H z ⊓ Subgroup.centralizer ({z₁} : Set G)) →* ↥(H (quotW hzC)) :=
  (quotH₁ z z₁).codRestrict (H (quotW hzC)) (quotH₁_mem_H_of_ne h hZ hz₁ hz₁z hz₁2 hzC)

theorem quotHH₁_surjective (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z))
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) :
    Function.Surjective (quotHH₁ h hZ hz₁ hz₁z hz₁2 hzC) := by
  intro y
  have hy : (y : QuotC z₁) ∈ Subgroup.centralizer ({quotW hzC} : Set (QuotC z₁)) := y.2
  rw [centralizer_quotW_eq_map_of_ne h hZ hz₁ hz₁z hz₁2 hzC] at hy
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
  refine ⟨⟨(x : G), Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hx, x.2⟩⟩, ?_⟩
  apply Subtype.ext
  rw [← hxy]
  rfl

theorem isPGroup_ker_quotHH₁ (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z))
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) :
    IsPGroup 2 (quotHH₁ h hZ hz₁ hz₁z hz₁2 hzC).ker := by
  have hkerHH : (quotHH₁ h hZ hz₁ hz₁z hz₁2 hzC).ker = (quotH₁ z z₁).ker :=
    MonoidHom.ker_codRestrict _ _ _
  rw [hkerHH]
  have hker : (quotH₁ z z₁).ker =
      (Subgroup.zpowers z₁).subgroupOf (H z ⊓ Subgroup.centralizer ({z₁} : Set G)) :=
    Subgroup.ext (mem_ker_quotH₁_iff (z := z) (z₁ := z₁))
  rw [hker]
  have h2 : IsPGroup 2 (Subgroup.zpowers z₁) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz₁2]; norm_num)
  exact h2.comap_subtype

theorem J_le_inf_centralizer_z1 (hz₁ : z₁ ∈ centerIn (J z)) :
    J z ≤ H z ⊓ Subgroup.centralizer ({z₁} : Set G) := by
  intro j hj
  exact Subgroup.mem_inf.mpr ⟨J_le_H hj,
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hz₁.2 j hj)⟩

theorem pCoreOf_inf_centralizer_z1 (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2) :
    pCoreOf 2 (H z ⊓ Subgroup.centralizer ({z₁} : Set G)) = J z := by
  have hN : ((H z ⊓ Subgroup.centralizer ({z₁} : Set G)).subgroupOf (H z)).Normal :=
    Subgroup.normal_of_index_eq_two (relIndex_inf_centralizer_z1 h hZ hz₁ hz₁z hz₁2)
  exact pCoreOf_eq_of_le_of_normal 2 inf_le_left hN (J_le_inf_centralizer_z1 hz₁)

theorem J_quotW_eq_of_ne (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z))
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) :
    J (quotW hzC) =
      ((J z).subgroupOf (Subgroup.centralizer ({z₁} : Set G))).map (quotMk z₁) := by
  have h1 := map_pCore_eq_of_surjective_of_isPGroup_ker (p := 2)
    (quotHH₁ h hZ hz₁ hz₁z hz₁2 hzC) (quotHH₁_surjective h hZ hz₁ hz₁z hz₁2 hzC)
    (isPGroup_ker_quotHH₁ h hZ hz₁ hz₁z hz₁2 hzC)
  have hcomp : (H (quotW hzC)).subtype.comp (quotHH₁ h hZ hz₁ hz₁z hz₁2 hzC) =
      (quotMk z₁).comp (Subgroup.inclusion inf_le_right) :=
    MonoidHom.ext fun _ => rfl
  have h2 : (pCore 2 ↥(H z ⊓ Subgroup.centralizer ({z₁} : Set G))).map
      (Subgroup.inclusion inf_le_right) =
      (J z).subgroupOf (Subgroup.centralizer ({z₁} : Set G)) := by
    apply Subgroup.map_injective (Subgroup.centralizer ({z₁} : Set G)).subtype_injective
    rw [Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le ((J_le_inf_centralizer_z1 hz₁).trans inf_le_right)]
    rw [Subgroup.subtype_comp_inclusion]
    change pCoreOf 2 (H z ⊓ Subgroup.centralizer ({z₁} : Set G)) = J z
    exact pCoreOf_inf_centralizer_z1 h hZ hz₁ hz₁z hz₁2
  show (pCore 2 ↥(H (quotW hzC))).map (H (quotW hzC)).subtype = _
  rw [← h1, Subgroup.map_map, hcomp, ← Subgroup.map_map, h2]

theorem mem_J_quotW_iff_of_ne (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z))
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) (y : QuotC z₁) :
    y ∈ J (quotW hzC) ↔
      ∃ x : ↥(Subgroup.centralizer ({z₁} : Set G)), (x : G) ∈ J z ∧ quotMk z₁ x = y := by
  rw [J_quotW_eq_of_ne h hZ hz₁ hz₁z hz₁2 hzC, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

theorem exists_conj_quotW_ne_of_ne (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G))
    (hfuse : ∃ g ∈ Subgroup.centralizer ({z₁} : Set G),
      g * z * g⁻¹ ∈ H z ⊓ Subgroup.centralizer ({z₁} : Set G) ∧ g * z * g⁻¹ ≠ z) :
    ∃ g : QuotC z₁, (g * quotW hzC * g⁻¹) * quotW hzC = quotW hzC * (g * quotW hzC * g⁻¹) ∧
      g * quotW hzC * g⁻¹ ≠ quotW hzC := by
  obtain ⟨g, hg, hgH, hne⟩ := hfuse
  have hyconj : quotMk z₁ ⟨g, hg⟩ * quotW hzC * (quotMk z₁ ⟨g, hg⟩)⁻¹ =
      quotMk z₁ ⟨g * z * g⁻¹, hgH.2⟩ := by
    rw [show quotW hzC = quotMk z₁ ⟨z, hzC⟩ from rfl, ← map_inv, ← map_mul, ← map_mul]
    exact congrArg (quotMk z₁) (Subtype.ext rfl)
  have hcomm : quotMk z₁ ⟨g * z * g⁻¹, hgH.2⟩ * quotW hzC =
      quotW hzC * quotMk z₁ ⟨g * z * g⁻¹, hgH.2⟩ := by
    have ha : (g * z * g⁻¹) * z = z * (g * z * g⁻¹) := by
      have hHa : g * z * g⁻¹ ∈ H z := hgH.1
      rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at hHa
      exact hHa
    rw [show quotW hzC = quotMk z₁ ⟨z, hzC⟩ from rfl, ← map_mul, ← map_mul]
    exact congrArg (quotMk z₁) (Subtype.ext ha)
  refine ⟨quotMk z₁ ⟨g, hg⟩, ?_, ?_⟩
  · rw [hyconj]
    exact hcomm
  · intro heq
    have hq : quotMk z₁ ⟨g * z * g⁻¹, hgH.2⟩ = quotW hzC := by
      rw [← hyconj]
      exact heq
    rw [quotMk, quotW, QuotientGroup.mk'_apply] at hq
    have hker := QuotientGroup.eq.mp hq
    rw [Subgroup.mem_subgroupOf] at hker
    have h3 : (g * z * g⁻¹)⁻¹ * z ∈ Subgroup.zpowers z₁ := by
      rwa [show (((⟨g * z * g⁻¹, hgH.2⟩ :
          ↥(Subgroup.centralizer ({z₁} : Set G)))⁻¹ * ⟨z, hzC⟩ :
          ↥(Subgroup.centralizer ({z₁} : Set G))) : G) =
          (g * z * g⁻¹)⁻¹ * z from rfl] at hker
    have hz₁sq : z₁ * z₁ = 1 := by
      have := pow_orderOf_eq_one z₁
      rwa [hz₁2, pow_two] at this
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hz₁2 h3 with h4 | h4
    · apply hne
      have h5 : z = g * z * g⁻¹ := by
        calc z = (g * z * g⁻¹) * ((g * z * g⁻¹)⁻¹ * z) := by group
          _ = (g * z * g⁻¹) * 1 := by rw [h4]
          _ = g * z * g⁻¹ := mul_one _
      exact h5.symm
    · apply not_isConj_z_mul_z1_of_ne h hZ hz₁ hz₁z hz₁2
      refine isConj_iff.mpr ⟨g, ?_⟩
      have h6 : z = (g * z * g⁻¹) * z₁ := by
        calc z = (g * z * g⁻¹) * ((g * z * g⁻¹)⁻¹ * z) := by group
          _ = (g * z * g⁻¹) * z₁ := by rw [h4]
      have h7 : z * z₁ = g * z * g⁻¹ := by
        nth_rewrite 1 [h6]
        simp only [mul_assoc, hz₁sq, mul_one]
      exact h7.symm

end CFSG.RankThree.GF2n.Parrott
