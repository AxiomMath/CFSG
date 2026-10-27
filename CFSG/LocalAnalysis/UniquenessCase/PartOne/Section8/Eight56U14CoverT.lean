module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56U14CoverDefs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ExtraspecialBasic
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ExtraspecialTransport
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.GroupTheory.PRankMapOfKerPrimeNotDvd
import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups (IsExtraspecialExpP)

abbrev pPrimeBarImage {Γ : Type} [Group Γ] [Finite Γ] (H : Subgroup Γ) :
    Subgroup (Γ ⧸ CFSG.pPrimeCore 3 Γ) :=
  H.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ))

private theorem covtbar_not_dvd_card (Γ : Type) [Group Γ] [Finite Γ] :
    ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 Γ) :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card

private theorem covtbar_rank {Γ : Type} [Group Γ] [Finite Γ]
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup Γ) ≤ 3) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (Γ ⧸ CFSG.pPrimeCore 3 Γ)) ≤ 3 := by
  have hker : ¬ 3 ∣ Nat.card ↥(MonoidHom.ker (QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ))) := by
    rw [QuotientGroup.ker_mk']
    exact covtbar_not_dvd_card Γ
  have h := CFSG.pRank_map_eq_of_not_dvd_card_ker (QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ))
    (QuotientGroup.mk'_surjective _) Nat.prime_three hker ⊤
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
  exact h.le.trans hr

theorem coverBarGroup_of_isKGroup {Γ : Type} [Group Γ] [Finite Γ] (hK : CFSG.Open.IsKGroup Γ)
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup Γ) ≤ 3) :
    CFSG.Open.IsKGroup (Γ ⧸ CFSG.pPrimeCore 3 Γ) ∧
      CFSG.pPrimeCore 3 (Γ ⧸ CFSG.pPrimeCore 3 Γ) = ⊥ ∧
      CFSG.Open.pRank 3 (⊤ : Subgroup (Γ ⧸ CFSG.pPrimeCore 3 Γ)) ≤ 3 :=
  ⟨CFSG.Open.IsKGroup.quotient hK _, CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three,
    covtbar_rank hr⟩

private theorem covtbar_inj {Γ : Type} [Group Γ] [Finite Γ] {A : Subgroup Γ} (hA : IsPGroup 3 A) :
    Function.Injective ((QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ)).comp A.subtype) :=
  CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype (covtbar_not_dvd_card Γ) hA

private theorem covtbar_eq_of_mk_eq {Γ : Type} [Group Γ] [Finite Γ] {A : Subgroup Γ}
    (hA : IsPGroup 3 A) {x y : Γ} (hx : x ∈ A) (hy : y ∈ A)
    (hxy : QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ) x = QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ) y) :
    x = y :=
  congrArg Subtype.val (covtbar_inj hA (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)

private theorem covtbar_equiv {Γ : Type} [Group Γ] [Finite Γ] {A : Subgroup Γ}
    (hA : IsPGroup 3 A) : Nonempty (↥A ≃* ↥(pPrimeBarImage A)) := by
  refine ⟨(MonoidHom.ofInjective (covtbar_inj hA)).trans (MulEquiv.subgroupCongr ?_)⟩
  rw [MonoidHom.range_comp, Subgroup.range_subtype]

private theorem covtbar_card {Γ : Type} [Group Γ] [Finite Γ] {A : Subgroup Γ}
    (hA : IsPGroup 3 A) : Nat.card ↥(pPrimeBarImage A) = Nat.card ↥A := by
  obtain ⟨e⟩ := covtbar_equiv hA
  exact (Nat.card_congr e.toEquiv).symm

private theorem covtbar_zOf {Γ : Type} [Group Γ] [Finite Γ] {Q : Subgroup Γ}
    (hQ : IsPGroup 3 Q) : pPrimeBarImage (ZOf Q) = ZOf (pPrimeBarImage Q) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxQ, hxc⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map_of_mem _ hxQ, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    have hqx := Subgroup.mem_centralizer_iff.1 hxc q hq
    rw [← map_mul, ← map_mul, hqx]
  · intro y hy
    obtain ⟨hyQ, hyc⟩ := Subgroup.mem_inf.1 hy
    obtain ⟨q, hq, rfl⟩ := hyQ
    refine ⟨q, Subgroup.mem_inf.2 ⟨hq, Subgroup.mem_centralizer_iff.2 fun q' hq' => ?_⟩, rfl⟩
    have hc := Subgroup.mem_centralizer_iff.1 hyc (QuotientGroup.mk' _ q')
      (Subgroup.mem_map_of_mem _ hq')
    exact covtbar_eq_of_mk_eq hQ (Subgroup.mul_mem _ hq' hq) (Subgroup.mul_mem _ hq hq')
      (by rw [map_mul, map_mul]; exact hc)

theorem coverBarSylowPart_of_coverCore {Γ : Type} [Group Γ] [Finite Γ] {Z Q L N : Subgroup Γ}
    (h : CoverCore Z Q L N) :
    Nat.card (pPrimeBarImage Z) = 3 ∧ pPrimeBarImage Z = ZOf (pPrimeBarImage Q) ∧
      IsExtraspecialExpP 3 1 ↥(pPrimeBarImage Q) ∧ pPrimeBarImage Q ≤ pPrimeBarImage L ∧
      pPrimeBarImage L ≤ centralizer ((pPrimeBarImage Z : Subgroup (Γ ⧸ CFSG.pPrimeCore 3 Γ)) :
        Set (Γ ⧸ CFSG.pPrimeCore 3 Γ)) := by
  have hQ : IsPGroup 3 Q := isPGroup_of_isExtraspecialExpP h.qext
  have hZQ : Z ≤ Q := by
    rw [h.zq]
    exact inf_le_left
  have hZ : IsPGroup 3 Z := hQ.to_le hZQ
  refine ⟨?_, ?_, ?_, Subgroup.map_mono h.ql, ?_⟩
  · rw [covtbar_card hZ, h.zcard]
  · rw [h.zq]
    exact covtbar_zOf hQ
  · obtain ⟨e⟩ := covtbar_equiv hQ
    exact isExtraspecialExpP_of_mulEquiv e.symm h.qext
  · intro y hy
    obtain ⟨l, hl, rfl⟩ := hy
    refine Subgroup.mem_centralizer_iff.2 ?_
    rintro _ ⟨z, hz, rfl⟩
    have hzl := Subgroup.mem_centralizer_iff.1 (h.lcz hl) z hz
    rw [← map_mul, ← map_mul, hzl]

private theorem covtquasi_not_dvd_card (Γ : Type) [Group Γ] [Finite Γ] :
    ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 Γ) :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card

private theorem covtquasi_zle {Γ : Type} [Group Γ] [Finite Γ] {Z Q L N : Subgroup Γ}
    (h : CoverCore Z Q L N) : Z ≤ L := by
  have hZQ : Z ≤ Q := by
    rw [h.zq]
    exact inf_le_left
  exact hZQ.trans h.ql

private theorem covtquasi_not_le_ker {Γ : Type} [Group Γ] [Finite Γ] {Z Q L N : Subgroup Γ}
    (h : CoverCore Z Q L N) : ¬ L ≤ (QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ)).ker := by
  intro hL
  rw [QuotientGroup.ker_mk'] at hL
  have h3 : Nat.card ↥Z ∣ Nat.card ↥(CFSG.pPrimeCore 3 Γ) :=
    Subgroup.card_dvd_of_le ((covtquasi_zle h).trans hL)
  rw [h.zcard] at h3
  exact covtquasi_not_dvd_card Γ h3

private theorem covtquasi_ker_le_center {Γ : Type} [Group Γ] [Finite Γ] {Z Q L N : Subgroup Γ}
    (h : CoverCore Z Q L N) :
    ((QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ)).subgroupMap L).ker ≤ center ↥L := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups h.lq
    ((QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ)).subgroupMap L).normal_ker with hk | hk
  · refine absurd (fun x hx => ?_) (covtquasi_not_le_ker h)
    have hx' : (⟨x, hx⟩ : ↥L) ∈
        ((QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ)).subgroupMap L).ker := by
      rw [hk]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at hx' ⊢
    exact congrArg Subtype.val hx'
  · exact hk

private theorem covtquasi_equiv {Γ : Type} [Group Γ] [Finite Γ] {Z Q L N : Subgroup Γ}
    (h : CoverCore Z Q L N) :
    Nonempty (↥L ⧸ center ↥L ≃* ↥(pPrimeBarImage L) ⧸ center ↥(pPrimeBarImage L)) := by
  have hφ := MonoidHom.subgroupMap_surjective (QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ)) L
  have hc : center ↥L = ((QuotientGroup.mk' (center ↥(pPrimeBarImage L))).comp
      ((QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ)).subgroupMap L)).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      CFSG.LocalCores.comap_center_eq_of_perfect h.lq.1 _ hφ (covtquasi_ker_le_center h)]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hφ))⟩

private theorem covtquasi_shape {X Y : Type} [Group X] [Group Y]
    (e : X ⧸ center X ≃* Y ⧸ center Y) (hX : IsCoverShape X) (hY : IsQuasisimple Y)
    (h3 : 3 ∣ Nat.card (center Y)) : IsCoverShape Y := by
  obtain ⟨-, -, hs⟩ := hX
  refine ⟨hY, h3, ?_⟩
  rcases hs with ha | ha | ha
  · obtain ⟨a⟩ := ha
    exact Or.inl ⟨e.symm.trans a⟩
  · obtain ⟨a⟩ := ha
    exact Or.inr (Or.inl ⟨e.symm.trans a⟩)
  · obtain ⟨a⟩ := ha
    exact Or.inr (Or.inr ⟨e.symm.trans a⟩)

private theorem covtquasi_card {Γ : Type} [Group Γ] [Finite Γ] {A : Subgroup Γ}
    (hA : IsPGroup 3 A) : Nat.card ↥(pPrimeBarImage A) = Nat.card ↥A := by
  have hinj := CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype
    (covtquasi_not_dvd_card Γ) hA
  refine (Nat.card_congr
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr ?_)).toEquiv).symm
  rw [MonoidHom.range_comp, Subgroup.range_subtype]

private theorem covtquasi_dvd {Γ : Type} [Group Γ] [Finite Γ] {Z Q L N : Subgroup Γ}
    (h : CoverCore Z Q L N) : 3 ∣ Nat.card ↥(center ↥(pPrimeBarImage L)) := by
  have hZQ : Z ≤ Q := by
    rw [h.zq]
    exact inf_le_left
  have hZ : IsPGroup 3 Z := (isPGroup_of_isExtraspecialExpP h.qext).to_le hZQ
  have hZL : pPrimeBarImage Z ≤ pPrimeBarImage L := Subgroup.map_mono (covtquasi_zle h)
  have hle : (pPrimeBarImage Z).subgroupOf (pPrimeBarImage L) ≤ center ↥(pPrimeBarImage L) := by
    rintro ⟨y, hyL⟩ hyZ
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_subgroupOf.1 hyZ
    rw [Subgroup.mem_center_iff]
    rintro ⟨_, l, hl, rfl⟩
    refine Subtype.ext ?_
    have hzl := Subgroup.mem_centralizer_iff.1 (h.lcz hl) z hz
    show QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ) l * QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ) z =
      QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ) z * QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ) l
    rw [← map_mul, ← map_mul, hzl]
  have h3 : Nat.card ↥((pPrimeBarImage Z).subgroupOf (pPrimeBarImage L)) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZL).toEquiv, covtquasi_card hZ, h.zcard]
  have hdvd := Subgroup.card_dvd_of_le hle
  rwa [h3] at hdvd

theorem coverBarQuasi_of_coverCore {Γ : Type} [Group Γ] [Finite Γ] {Z Q L N : Subgroup Γ}
    (h : CoverCore Z Q L N) :
    IsQuasisimple ↥(pPrimeBarImage L) ∧ IsCoverShape ↥(pPrimeBarImage L) := by
  have hq : IsQuasisimple ↥(pPrimeBarImage L) :=
    CFSG.LocalCores.isQuasisimple_map h.lq _ (covtquasi_not_le_ker h)
  obtain ⟨e⟩ := covtquasi_equiv h
  exact ⟨hq, covtquasi_shape e h.lcov hq (covtquasi_dvd h)⟩

private theorem covtlocal_not_dvd_card (Γ : Type) [Group Γ] [Finite Γ] :
    ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 Γ) :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card

private theorem covtlocal_isPGroup_z {Γ : Type} [Group Γ] [Finite Γ] {Z Q L N : Subgroup Γ}
    (h : CoverCore Z Q L N) : IsPGroup 3 Z := by
  have hZQ : Z ≤ Q := by
    rw [h.zq]
    exact inf_le_left
  exact (isPGroup_of_isExtraspecialExpP h.qext).to_le hZQ

private theorem covtlocal_le_centralizer {Γ : Type} [Group Γ] [Finite Γ] {Z Q L N : Subgroup Γ}
    (h : CoverCore Z Q L N) :
    pPrimeBarImage L ≤ centralizer ((pPrimeBarImage Z : Subgroup (Γ ⧸ CFSG.pPrimeCore 3 Γ)) :
      Set (Γ ⧸ CFSG.pPrimeCore 3 Γ)) := by
  rw [(CFSG.GroupTheory.SteinbergBS.prime_to_p_quotient_normalizer_centralizer_lifting
    (covtlocal_not_dvd_card Γ) (covtlocal_isPGroup_z h)).2.2]
  exact Subgroup.map_mono h.lcz

private theorem covtlocal_lnorm {Γ : Type} [Group Γ] [Finite Γ] {Z Q L N : Subgroup Γ}
    (h : CoverCore Z Q L N) :
    ((pPrimeBarImage L).subgroupOf (centralizer ((pPrimeBarImage Z :
      Subgroup (Γ ⧸ CFSG.pPrimeCore 3 Γ)) : Set (Γ ⧸ CFSG.pPrimeCore 3 Γ)))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (covtlocal_le_centralizer h),
    (CFSG.GroupTheory.SteinbergBS.prime_to_p_quotient_normalizer_centralizer_lifting
      (covtlocal_not_dvd_card Γ) (covtlocal_isPGroup_z h)).2.2]
  exact (Subgroup.map_mono
    ((Subgroup.normal_subgroupOf_iff_le_normalizer h.lcz).1 h.lnorm)).trans
    (Subgroup.le_normalizer_map _)

private theorem covtlocal_nq {Γ : Type} [Group Γ] [Finite Γ] {Z Q L N : Subgroup Γ}
    (h : CoverCore Z Q L N) (A : Subgroup (Γ ⧸ CFSG.pPrimeCore 3 Γ))
    (hAQ : A ≤ pPrimeBarImage Q) (hA : A ≠ ⊥) :
    normalizer (A : Set (Γ ⧸ CFSG.pPrimeCore 3 Γ)) ≤ pPrimeBarImage N := by
  obtain ⟨A₀, hA₀Q, hmap⟩ : ∃ A₀ : Subgroup Γ, A₀ ≤ Q ∧
      A₀.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ)) = A := by
    refine ⟨Q ⊓ A.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ)), inf_le_left,
      le_antisymm (Subgroup.map_le_iff_le_comap.2 inf_le_right) fun a ha => ?_⟩
    obtain ⟨q, hq, rfl⟩ := hAQ ha
    exact ⟨q, ⟨hq, ha⟩, rfl⟩
  have hA₀ne : A₀ ≠ ⊥ := by
    rintro rfl
    exact hA (by rw [← hmap, Subgroup.map_bot])
  have hlift := (CFSG.GroupTheory.SteinbergBS.prime_to_p_quotient_normalizer_centralizer_lifting
    (covtlocal_not_dvd_card Γ)
    ((isPGroup_of_isExtraspecialExpP h.qext).to_le hA₀Q)).2.1
  rw [hmap] at hlift
  rw [hlift]
  exact Subgroup.map_mono (h.nq A₀ hA₀Q hA₀ne)

private theorem covtlocal_kn {Γ : Type} [Group Γ] [Finite Γ] {Z Q L N : Subgroup Γ}
    (h : CoverCore Z Q L N) :
    ¬ normalClosure ((pPrimeBarImage Z : Subgroup (Γ ⧸ CFSG.pPrimeCore 3 Γ)) :
      Set (Γ ⧸ CFSG.pPrimeCore 3 Γ)) ≤ pPrimeBarImage N := by
  intro hle
  rw [Subgroup.coe_map, ← Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _)] at hle
  have h2 := Subgroup.map_le_iff_le_comap.1 hle
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2
  exact h.kn h2

theorem coverBarLocal_of_coverCore {Γ : Type} [Group Γ] [Finite Γ] {Z Q L N : Subgroup Γ}
    (h : CoverCore Z Q L N) :
    CoverBarLocal (pPrimeBarImage Z) (pPrimeBarImage Q) (pPrimeBarImage L) (pPrimeBarImage N) :=
  ⟨covtlocal_lnorm h, covtlocal_nq h, covtlocal_kn h⟩

theorem coverBar_of_coverCore {Γ : Type} [Group Γ] [Finite Γ] {Z Q L N : Subgroup Γ}
    (h : CoverCore Z Q L N) :
    CoverBar (pPrimeBarImage Z) (pPrimeBarImage Q) (pPrimeBarImage L) (pPrimeBarImage N) := by
  obtain ⟨hk, ho, hr⟩ := coverBarGroup_of_isKGroup h.kgroup h.rank
  obtain ⟨hz, hzq, hq, hql, hlz⟩ := coverBarSylowPart_of_coverCore h
  obtain ⟨hlq, hlcov⟩ := coverBarQuasi_of_coverCore h
  have hloc := coverBarLocal_of_coverCore h
  exact
    { kgroup := hk, o3 := ho, rank := hr, zcard := hz, zq := hzq, qext := hq, ql := hql,
      lq := hlq, lcov := hlcov, lcz := hlz, lnorm := hloc.lnorm, nq := hloc.nq, kn := hloc.kn }

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
