module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairCore

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G]

@[expose] def minimalLocalFailureProperPairClassCommutators (H : Subgroup G)
    (z : G) : Subgroup G :=
  Subgroup.closure {c : G | ∃ a ∈ conjugacyWithin H z,
    ∃ b ∈ conjugacyWithin H z, a⁻¹ * b⁻¹ * a * b = c}

theorem minimalLocalFailureProperPairClassCommutators_le_point
    (H : Subgroup G) {z : G} (hz : z ∈ H) :
    minimalLocalFailureProperPairClassCommutators H z ≤ H := by
  apply (Subgroup.closure_le _).mpr
  rintro c ⟨a, ⟨g, rfl⟩, b, ⟨k, rfl⟩, rfl⟩
  have haH : (g : G)⁻¹ * z * g ∈ H :=
    H.mul_mem (H.mul_mem (H.inv_mem g.property) hz) g.property
  have hbH : (k : G)⁻¹ * z * k ∈ H :=
    H.mul_mem (H.mul_mem (H.inv_mem k.property) hz) k.property
  exact H.mul_mem (H.mul_mem (H.mul_mem (H.inv_mem haH) (H.inv_mem hbH)) haH) hbH

private theorem conjugacyWithin_conj_mem (H : Subgroup G) (z : G)
    {a g : G} (ha : a ∈ conjugacyWithin H z) (hg : g ∈ H) :
    g * a * g⁻¹ ∈ conjugacyWithin H z := by
  obtain ⟨k, rfl⟩ := ha
  refine ⟨k * (⟨g, hg⟩ : H)⁻¹, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
  group

private theorem classCommutators_conj_le (H : Subgroup G) (z : G)
    {g : G} (hg : g ∈ H) :
    (minimalLocalFailureProperPairClassCommutators H z).map
      (MulAut.conj g).toMonoidHom ≤ minimalLocalFailureProperPairClassCommutators H z := by
  rw [minimalLocalFailureProperPairClassCommutators,
    (MulAut.conj g).toMonoidHom.map_closure]
  apply (Subgroup.closure_le _).mpr
  rintro c ⟨d, ⟨a, ha, b, hb, rfl⟩, rfl⟩
  apply Subgroup.subset_closure
  refine ⟨g * a * g⁻¹, conjugacyWithin_conj_mem H z ha hg,
    g * b * g⁻¹, conjugacyWithin_conj_mem H z hb hg, ?_⟩
  change (g * a * g⁻¹)⁻¹ * (g * b * g⁻¹)⁻¹ *
    (g * a * g⁻¹) * (g * b * g⁻¹) = g * (a⁻¹ * b⁻¹ * a * b) * g⁻¹
  group

theorem minimalLocalFailureProperPairClassCommutators_normal_in_point
    (H : Subgroup G) {z : G} (hz : z ∈ H) :
    ((minimalLocalFailureProperPairClassCommutators H z).subgroupOf H).Normal := by
  let W := minimalLocalFailureProperPairClassCommutators H z
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (minimalLocalFailureProperPairClassCommutators_le_point H hz)).mpr
  intro g hg
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  apply le_antisymm (classCommutators_conj_le H z hg)
  intro w hw
  have hginv : g⁻¹ ∈ H := H.inv_mem hg
  have hback : g⁻¹ * w * g ∈ W := by
    have hmem := classCommutators_conj_le H z hginv
      (Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hw)
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hmem
  refine Subgroup.mem_map.mpr ⟨g⁻¹ * w * g, hback, ?_⟩
  change g * (g⁻¹ * w * g) * g⁻¹ = w
  group

theorem minimalLocalFailureProperPairClassCommutators_le_hull_oddCore [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hcomm : ∀ a b : minimalLocalFailureProperPairHull H z beta t,
      a ∈ H.subgroupOf (minimalLocalFailureProperPairHull H z beta t) → orderOf a = 2 →
      b ∈ H.subgroupOf (minimalLocalFailureProperPairHull H z beta t) → orderOf b = 2 →
      Commute
        (QuotientGroup.mk a : minimalLocalFailureProperPairHull H z beta t ⧸
          oddCore (minimalLocalFailureProperPairHull H z beta t))
        (QuotientGroup.mk b : minimalLocalFailureProperPairHull H z beta t ⧸
          oddCore (minimalLocalFailureProperPairHull H z beta t))) :
    minimalLocalFailureProperPairClassCommutators H z ≤
      minimalLocalFailureProperPairOddCore H z beta t := by
  let K := minimalLocalFailureProperPairHull H z beta t
  have hclass := minimalLocalFailureProperPair_class_subset
    h.local_datum h.central_sylow hbeta ht
  apply (Subgroup.closure_le _).mpr
  rintro c ⟨a, ha, b, hb, rfl⟩
  let aK : K := ⟨a, (hclass ha).2⟩
  let bK : K := ⟨b, (hclass hb).2⟩
  have haambient : a ∈ involutionPointClass z := by
    obtain ⟨g, hg⟩ := ha
    exact ⟨g, hg⟩
  have hbambient : b ∈ involutionPointClass z := by
    obtain ⟨g, hg⟩ := hb
    exact ⟨g, hg⟩
  have haorder : orderOf aK = 2 := (Subgroup.orderOf_coe aK).symm.trans
    (order_two_of_mem_pointClass h.local_datum.distinguished_order haambient)
  have hborder : orderOf bK = 2 := (Subgroup.orderOf_coe bK).symm.trans
    (order_two_of_mem_pointClass h.local_datum.distinguished_order hbambient)
  have hquotcomm := hcomm aK bK (hclass ha).1 haorder (hclass hb).1 hborder
  have hkernel : aK⁻¹ * bK⁻¹ * aK * bK ∈ oddCore K := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (oddCore K)) (aK⁻¹ * bK⁻¹ * aK * bK) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    calc
      (QuotientGroup.mk aK : K ⧸ oddCore K)⁻¹ * (QuotientGroup.mk bK)⁻¹ *
          QuotientGroup.mk aK * QuotientGroup.mk bK =
          (QuotientGroup.mk aK)⁻¹ *
            ((QuotientGroup.mk bK)⁻¹ * QuotientGroup.mk aK) * QuotientGroup.mk bK := by group
      _ = (QuotientGroup.mk aK)⁻¹ *
            (QuotientGroup.mk aK * (QuotientGroup.mk bK)⁻¹) * QuotientGroup.mk bK := by
        rw [hquotcomm.symm.inv_left.eq]
      _ = 1 := by group
  exact Subgroup.mem_map_of_mem K.subtype hkernel

theorem minimalLocalFailureProperPairClassCommutators_normal_and_le_pair_oddCore [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hcomm : ∀ a b : minimalLocalFailureProperPairHull H z beta t,
      a ∈ H.subgroupOf (minimalLocalFailureProperPairHull H z beta t) → orderOf a = 2 →
      b ∈ H.subgroupOf (minimalLocalFailureProperPairHull H z beta t) → orderOf b = 2 →
      Commute
        (QuotientGroup.mk a : minimalLocalFailureProperPairHull H z beta t ⧸
          oddCore (minimalLocalFailureProperPairHull H z beta t))
        (QuotientGroup.mk b : minimalLocalFailureProperPairHull H z beta t ⧸
          oddCore (minimalLocalFailureProperPairHull H z beta t))) :
    ((minimalLocalFailureProperPairClassCommutators H z).subgroupOf H).Normal ∧
      minimalLocalFailureProperPairClassCommutators H z ≤ pairOddCore H beta := by
  let W := minimalLocalFailureProperPairClassCommutators H z
  let N := minimalLocalFailureProperPairOddCore H z beta t
  let B := pairPointStabilizer H beta
  have hWH := minimalLocalFailureProperPairClassCommutators_le_point H
    h.local_datum.distinguished_mem
  have hnormal := minimalLocalFailureProperPairClassCommutators_normal_in_point H
    h.local_datum.distinguished_mem
  have hWN : W ≤ N :=
    minimalLocalFailureProperPairClassCommutators_le_hull_oddCore h hbeta ht hcomm
  have hNB : N ≤ B :=
    minimalLocalFailureProperPairOddCore_le_pair_stabilizer h hbeta ht hproper
  have hWB : W ≤ B := hWN.trans hNB
  have hBH : B ≤ H := pairPointStabilizer_le_point H beta
  have hnormalB : (W.subgroupOf B).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hWB).mpr
    exact hBH.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hWH).mp hnormal)
  have hWodd : Odd (Nat.card W) :=
    (minimalLocalFailureProperPairOddCore_odd H z beta t).of_dvd_nat
      (Subgroup.card_dvd_of_le hWN)
  have hWBodd : Odd (Nat.card (W.subgroupOf B)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWB).toEquiv]
    exact hWodd
  have hcore : W.subgroupOf B ≤ oddCore B :=
    CFSG.ComponentClassification.OddCore.maximal B _ hnormalB hWBodd
  have hmap := Subgroup.map_mono (f := B.subtype) hcore
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hWB] at hmap
  exact ⟨hnormal, hmap⟩

end CFSG.ShultStronglyClosedTI
