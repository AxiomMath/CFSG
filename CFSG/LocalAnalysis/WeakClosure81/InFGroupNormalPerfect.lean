module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.Quasithin.Background.A3Structure312Defs
import CFSG.LocalAnalysis.WeakClosure81.InFGroupNormalQuasisimple
import CFSG.Walter.AStar.Subnormal
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10LayerS6
import CFSG.RankThree.PartOne.S12.Sec125Moved
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

private theorem le_normalizer_pCoreOf_of_normal {G : Type} [Group G] {J K : Subgroup G}
    (hJK : J ≤ K) (hJn : (J.subgroupOf K).Normal) :
    K ≤ Subgroup.normalizer (pCoreOf 2 J : Set G) := by
  have hKJ : K ≤ Subgroup.normalizer (J : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJK).mp hJn
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact CFSG.Walter.conj_mem_map_of_characteristic (D := CFSG.pCore 2 ↥J) (hKJ hk) hx
  · intro hx
    have hk' : k⁻¹ ∈ Subgroup.normalizer (J : Set G) := inv_mem (hKJ hk)
    have h := CFSG.Walter.conj_mem_map_of_characteristic (D := CFSG.pCore 2 ↥J) hk' hx
    rwa [show k⁻¹ * (k * x * k⁻¹) * (k⁻¹)⁻¹ = x from by group] at h

private theorem le_normalizer_map_solvableRadical {G : Type} [Group G] {K : Subgroup G} :
    K ≤ Subgroup.normalizer ((CFSG.solvableRadical ↥K).map K.subtype : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨⟨k, hk⟩ * r * ⟨k, hk⟩⁻¹,
      (inferInstance : (CFSG.solvableRadical ↥K).Normal).conj_mem r hr ⟨k, hk⟩, rfl⟩
  · rintro ⟨r, hr, hx⟩
    have hconj : ⟨k, hk⟩⁻¹ * r * ⟨k, hk⟩ ∈ CFSG.solvableRadical ↥K := by
      simpa using
        (inferInstance : (CFSG.solvableRadical ↥K).Normal).conj_mem r hr ⟨k, hk⟩⁻¹
    refine ⟨⟨k, hk⟩⁻¹ * r * ⟨k, hk⟩, hconj, ?_⟩
    rw [map_mul, map_mul, map_inv, hx]
    show k⁻¹ * (k * x * k⁻¹) * k = x
    group

private theorem pCoreOf_le_map_solvableRadical {G : Type} [Group G] [Finite G]
    {K J : Subgroup G} (hJK : J ≤ K) (hJn : (J.subgroupOf K).Normal) :
    pCoreOf 2 J ≤ (CFSG.solvableRadical ↥K).map K.subtype := by
  have hQK : pCoreOf 2 J ≤ K := (CFSG.LieType.BorelTits.pCoreOf_le 2 J).trans hJK
  have hKnorm : K ≤ Subgroup.normalizer (pCoreOf 2 J : Set G) :=
    le_normalizer_pCoreOf_of_normal hJK hJn
  have hNn : ((pCoreOf 2 J).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQK).mpr hKnorm
  have hNs : Group.IsSolvable ↥((pCoreOf 2 J).subgroupOf K) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Group.IsSolvable ↥(pCoreOf 2 J) := by
      haveI := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J).isNilpotent
      exact IsNilpotent.to_isSolvable
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe hQK).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hQK).symm.surjective
  have hle : (pCoreOf 2 J).subgroupOf K ≤ CFSG.solvableRadical ↥K :=
    A3.le_solvableRadical hNn hNs
  have hmap := Subgroup.map_mono (f := K.subtype) hle
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQK] at hmap

private theorem inf_map_solvableRadical_le_pCoreOf {G : Type} [Group G] [Finite G]
    {K J : Subgroup G} (hJK : J ≤ K) (hJn : (J.subgroupOf K).Normal)
    (hJperf : ⁅J, J⁆ = J) (hJs : IsSimpleGroup (ModO2 J)) :
    (CFSG.solvableRadical ↥K).map K.subtype ⊓ J ≤ pCoreOf 2 J := by
  have hJnormR : J ≤ Subgroup.normalizer
      ((CFSG.solvableRadical ↥K).map K.subtype : Set G) :=
    hJK.trans (le_normalizer_map_solvableRadical (K := K))
  set N : Subgroup G := (CFSG.solvableRadical ↥K).map K.subtype ⊓ J
  set M : Subgroup ↥J := N.subgroupOf J
  have hMnorm : M.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr fun j hj => by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [Subgroup.mem_inf, Subgroup.mem_inf]
      constructor
      · rintro ⟨hxR, hxJ⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp (hJnormR hj) x).mp hxR,
          (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hj) x).mp hxJ⟩
      · rintro ⟨hxR, hxJ⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp (hJnormR hj) x).mpr hxR,
          (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hj) x).mpr hxJ⟩
  have hMsolv : Group.IsSolvable ↥M := by
    haveI : Group.IsSolvable ↥(CFSG.solvableRadical ↥K) := A3.solvableRadical_isSolvable
    have hRsolv : Group.IsSolvable ↥((CFSG.solvableRadical ↥K).map K.subtype) :=
      Group.isSolvable_of_surjective
        (f := (Subgroup.equivMapOfInjective (CFSG.solvableRadical ↥K) K.subtype
          K.subtype_injective).toMonoidHom)
        (Subgroup.equivMapOfInjective (CFSG.solvableRadical ↥K) K.subtype
          K.subtype_injective).surjective
    haveI := hRsolv
    have hNsolv : Group.IsSolvable ↥N :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion inf_le_left)
        (Subgroup.inclusion_injective inf_le_left)
    haveI := hNsolv
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe inf_le_right).symm.toMonoidHom)
      (by simpa using (Subgroup.subgroupOfEquivOfLe inf_le_right).symm.surjective)
  haveI : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJperf
  haveI : Group.IsPerfect (ModO2 J) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥J))
      (QuotientGroup.mk'_surjective _)
  let q : ↥J →* ModO2 J := QuotientGroup.mk' (CFSG.pCore 2 ↥J)
  have hqMn : (M.map q).Normal := hMnorm.map q (QuotientGroup.mk'_surjective _)
  haveI : (M.map q).Normal := hqMn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.map q) with hbot | htop
  · have hle : M ≤ CFSG.pCore 2 ↥J := by
      rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥J)]
      exact (Subgroup.map_eq_bot_iff M).mp hbot
    have hmap : N ≤ pCoreOf 2 J := by
      have h := Subgroup.map_mono (f := J.subtype) hle
      rwa [Subgroup.map_subgroupOf_eq_of_le inf_le_right] at h
    simpa [N] using hmap
  · exfalso
    have hsurj : Function.Surjective (q.comp M.subtype) := by
      intro y
      have hy : y ∈ M.map q := htop ▸ Subgroup.mem_top y
      rw [Subgroup.mem_map] at hy
      obtain ⟨x, hx, hqx⟩ := hy
      exact ⟨⟨x, hx⟩, hqx⟩
    haveI : Group.IsSolvable (ModO2 J) :=
      Group.isSolvable_of_surjective (f := q.comp M.subtype) hsurj
    exact Group.IsPerfect.not_isSolvable (ModO2 J) inferInstance

private theorem isPGroup_solvableRadical_of_simple {G : Type} [Group G] [Finite G]
    {K J : Subgroup G} (hK2 : ∀ x ∈ K, ∃ k : ℕ, x ^ 2 ^ k ∈ J)
    (hInter : (CFSG.solvableRadical ↥K).map K.subtype ⊓ J = pCoreOf 2 J) :
    IsPGroup 2 ↥(CFSG.solvableRadical ↥K) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro r
  obtain ⟨k, hk⟩ := hK2 (r : ↥K).1 (r : ↥K).2
  have hmem : K.subtype ((r : ↥K) ^ 2 ^ k) ∈ pCoreOf 2 J := by
    rw [← hInter]
    exact ⟨Subgroup.mem_map.mpr
      ⟨(r : ↥K) ^ 2 ^ k, (CFSG.solvableRadical ↥K).pow_mem r.2 _, rfl⟩, hk⟩
  obtain ⟨m, hm⟩ := (isPGroup_iff_pow_pow_eq_one.mp
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J))
    ⟨K.subtype ((r : ↥K) ^ 2 ^ k), hmem⟩
  have hm' : (K.subtype ((r : ↥K) ^ 2 ^ k)) ^ 2 ^ m = 1 := by
    simpa using congrArg (Subtype.val) hm
  refine ⟨k + m, ?_⟩
  apply Subgroup.subtype_injective (CFSG.solvableRadical ↥K)
  rw [map_pow, map_one]
  apply K.subtype_injective
  rw [map_pow, map_one, pow_add, pow_mul]
  rw [map_pow] at hm'
  exact hm'

private theorem isSimpleGroup_map_solvableRadical {G : Type} [Group G] [Finite G]
    {K J : Subgroup G} (hJK : J ≤ K) (hJn : (J.subgroupOf K).Normal)
    (hJperf : ⁅J, J⁆ = J) (hJs : IsSimpleGroup (ModO2 J))
    (hInter : (CFSG.solvableRadical ↥K).map K.subtype ⊓ J = pCoreOf 2 J) :
    IsSimpleGroup ((J.subgroupOf K).map (QuotientGroup.mk' (CFSG.solvableRadical ↥K))) ∧
      ∃ a b : (J.subgroupOf K).map (QuotientGroup.mk' (CFSG.solvableRadical ↥K)),
        a * b ≠ b * a := by
  have hperf : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJperf
  let π : ↥K →* (↥K ⧸ CFSG.solvableRadical ↥K) :=
    QuotientGroup.mk' (CFSG.solvableRadical ↥K)
  let φ : ↥J →* (↥K ⧸ CFSG.solvableRadical ↥K) := π.comp (Subgroup.inclusion hJK)
  have hQsub : (pCoreOf 2 J).subgroupOf J = CFSG.pCore 2 ↥J := by
    unfold pCoreOf Subgroup.subgroupOf
    exact Subgroup.comap_map_eq_self_of_injective J.subtype_injective _
  have hker : φ.ker = CFSG.pCore 2 ↥J := by
    ext x
    rw [MonoidHom.mem_ker]
    show QuotientGroup.mk' (CFSG.solvableRadical ↥K) (Subgroup.inclusion hJK x) = 1 ↔
      x ∈ CFSG.pCore 2 ↥J
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← hQsub, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hmem : (x : G) ∈ (CFSG.solvableRadical ↥K).map K.subtype ⊓ J :=
        ⟨Subgroup.mem_map.mpr ⟨Subgroup.inclusion hJK x, hx, rfl⟩, x.2⟩
      rwa [hInter] at hmem
    · intro hx
      have hmem : (x : G) ∈ (CFSG.solvableRadical ↥K).map K.subtype ⊓ J := by
        rw [hInter]
        exact hx
      obtain ⟨r, hr, hrx⟩ := hmem.1
      have hEq : Subgroup.inclusion hJK x = r := by
        apply K.subtype_injective
        simpa using hrx.symm
      rwa [hEq]
  have hrange : φ.range = (J.subgroupOf K).map π := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  haveI : IsSimpleGroup (ModO2 J) := hJs
  haveI : IsSimpleGroup (↥J ⧸ φ.ker) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).symm.isSimpleGroup
  haveI : IsSimpleGroup ↥φ.range :=
    (QuotientGroup.quotientKerEquivRange φ).symm.isSimpleGroup
  have hsimple : IsSimpleGroup ((J.subgroupOf K).map π) :=
    (MulEquiv.subgroupCongr hrange).symm.isSimpleGroup
  refine ⟨hsimple, ?_⟩
  have hnonabMod : ∃ a b : ModO2 J, a * b ≠ b * a := by
    have h := Group.IsPerfect.not_isMulCommutative (ModO2 J)
    rw [isMulCommutative_iff, not_forall] at h
    obtain ⟨a, ha⟩ := h
    rw [not_forall] at ha
    exact ⟨a, ha⟩
  let e : ModO2 J ≃* ((J.subgroupOf K).map π) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))
  obtain ⟨a, b, hab⟩ := hnonabMod
  refine ⟨e a, e b, fun h => hab (e.injective ?_)⟩
  rw [map_mul, map_mul]
  exact h

private theorem layer_eq_iSup_map_conj {G : Type} [Group G] {T A K : Subgroup G}
    {Q : Type} [Group Q] {π : ↥K →* Q} {L : Subgroup Q}
    (hLn : L.Normal) (hlayer : CFSG.layer Q = L) :
    CFSG.layer Q =
      ⨆ t ∈ ((tA T A).subgroupOf K).map π, L.map (MulAut.conj t).toMonoidHom := by
  rw [hlayer]
  refine le_antisymm ?_ (iSup₂_le fun t _ => ?_)
  · refine le_iSup₂_of_le (1 : Q) ?_ ?_
    · exact Subgroup.mem_map.mpr ⟨1, Subgroup.one_mem _, map_one π⟩
    · exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp (by
        rw [Subgroup.normalizer_eq_top_iff.mpr hLn]; exact Subgroup.mem_top _)).ge
  · exact le_of_eq (Subgroup.mem_normalizer_iff_map_conj_eq.mp (by
      rw [Subgroup.normalizer_eq_top_iff.mpr hLn]; exact Subgroup.mem_top t))

theorem eCaseII_of_normal_perfect {G : Type} [Group G] [Finite G] {T A K J : Subgroup G}
    (hJK : J ≤ K) (hJn : (J.subgroupOf K).Normal) (hJperf : ⁅J, J⁆ = J)
    (hJs : IsSimpleGroup (ModO2 J)) (hK2 : ∀ x ∈ K, ∃ k : ℕ, x ^ 2 ^ k ∈ J) (hAK : A ≤ K)
    (hAJ : ∃ a ∈ A, ∃ x ∈ J, ⁅a, x⁆ ∉ pCoreOf 2 J) : ECaseII T A K := by
  set R : Subgroup ↥K := CFSG.solvableRadical ↥K with hRdef
  set J' : Subgroup ↥K := J.subgroupOf K with hJ'def
  set π : ↥K →* (↥K ⧸ R) := QuotientGroup.mk' R with hπdef
  set L : Subgroup (↥K ⧸ R) := J'.map π with hLdef
  have hJ'2 : ∀ x : ↥K, ∃ k : ℕ, x ^ 2 ^ k ∈ J' := by
    intro x
    obtain ⟨k, hk⟩ := hK2 x.1 x.2
    exact ⟨k, Subgroup.mem_subgroupOf.mpr hk⟩
  have hInter : R.map K.subtype ⊓ J = pCoreOf 2 J :=
    le_antisymm (inf_map_solvableRadical_le_pCoreOf hJK hJn hJperf hJs)
      (le_inf (pCoreOf_le_map_solvableRadical hJK hJn)
        (CFSG.LieType.BorelTits.pCoreOf_le 2 J))
  have hR2 : IsPGroup 2 ↥R := isPGroup_solvableRadical_of_simple hK2 hInter
  have hR2cl : E1.IsTwoClosed R :=
    ⟨R, ⟨le_rfl, hR2, by rw [Subgroup.relIndex_self]; norm_num⟩,
      by rw [Subgroup.subgroupOf_self]; infer_instance⟩
  obtain ⟨hLsimple, hLnonab⟩ := isSimpleGroup_map_solvableRadical hJK hJn hJperf hJs hInter
  haveI : IsSimpleGroup L := hLsimple
  have hLq : CFSG.IsQuasisimple L :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hLnonab).1
  have hLn : L.Normal := Subgroup.Normal.map hJn π (QuotientGroup.mk'_surjective R)
  haveI : L.Normal := hLn
  have hJ'perf : ⁅J', J'⁆ = J' := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJK, hJperf]
  have hsolv_quot : Group.IsSolvable ((↥K ⧸ R) ⧸ L) :=
    isSolvable_quotient_map_solvableRadical hK2
  have hlayer : CFSG.layer (↥K ⧸ R) = L :=
    CFSG.OddStandard.SmallF3.Omega.LayerS6.layer_eq_of_normal_quasisimple L hLq hsolv_quot
  have hsup : CFSG.layer (↥K ⧸ R) =
      ⨆ t ∈ ((tA T A).subgroupOf K).map π, L.map (MulAut.conj t).toMonoidHom :=
    layer_eq_iSup_map_conj (Q := ↥K ⧸ R) hLn hlayer
  have hAJ' : ∃ a ∈ A, ∃ x ∈ J, ⁅a, x⁆ ∉ R.map K.subtype := by
    obtain ⟨a, ha, x, hx, hne⟩ := hAJ
    refine ⟨a, ha, x, hx, fun hmem => hne ?_⟩
    have hKJ : K ≤ Subgroup.normalizer (J : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hJK).mp hJn
    have hcomm : ⁅a, x⁆ ∈ J := by
      have hconj : a * x * a⁻¹ ∈ J :=
        (Subgroup.mem_normalizer_iff.mp (hKJ (hAK ha)) x).mp hx
      rw [commutatorElement_def]
      exact J.mul_mem hconj (J.inv_mem hx)
    rw [← hInter]
    exact ⟨hmem, hcomm⟩
  have hcomm_ne : ⁅L, E1.barRad ↥K (A.subgroupOf K)⁆ ≠ ⊥ :=
    commutator_barRad_ne_bot hJK hAK hAJ'
  have halt : L = ⁅L, E1.barRad ↥K (A.subgroupOf K)⁆ :=
    (CFSG.RankThree.PartOne.Sec125.commutator_eq_of_ne_bot hLq
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hLn]; exact le_top) hcomm_ne).symm
  have hres_eq : twoResidual (⊤ : Subgroup ↥K) = perfectCore (⊤ : Subgroup ↥K) :=
    twoResidual_eq_perfectCore_of_forall_pow_mem hJn hJ'perf hJ'2
  have hJ'le : J' ≤ oInftyE ↥K := by
    intro j hj
    show j ∈ (CFSG.layer (↥K ⧸ R)).comap π
    rw [hlayer]
    exact Subgroup.mem_comap.mpr (Subgroup.mem_map.mpr ⟨j, hj, rfl⟩)
  refine ⟨hR2cl, pCore_oInftyE_eq_top_of_le hJ'2 hJ'le, hres_eq, L,
    ⟨hLq, hLn.isSubnormal⟩, hsup, Or.inl halt⟩

end CFSG.LocalAnalysis.WeakClosure81
