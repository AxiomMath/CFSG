module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofStar
import CFSG.RankThree.GroupTheory.SteinbergCEThetaSubnormalDichotomy
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.CGT.PushingUp.TwoLocals
import CFSG.Quasithin.Background.RonanD33
import CFSG.Quasithin.Background.C2Basic
import CFSG.RankThree.PartTwo.Sec16.Item166ThetaDich
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.RankThree.PartTwo.Sec16.Ctr166

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ X J : Subgroup G}

structure Conf166A5 (A : Subgroup G) (c : G) (L Y₀ X J : Subgroup G) : Prop where
  std : Sec17Std G A c L Y₀
  j2 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)
  mem_y3Star : X ∈ scriptY3Star A (lB A)
  not_solvable : ¬ Group.IsSolvable ↥X
  solvable_core : Group.IsSolvable ↥(pPrimeCoreOf 3 X)
  residual_ne_bot : oPrimeResidualOf 3 X ≠ ⊥
  mem_theta : J ∈ thetaComponentsIn (Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G))
  mem_y0 : J ∈ scriptY0 A (lB A)
  quot_a5 : Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5))
  not_le : ¬ X ≤ Subgroup.normalizer (Y₀ : Set G)

theorem ctr166A5_of_forall_not (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hno : ∀ X J : Subgroup G, ¬ Conf166A5 A c L Y₀ X J) : Ctr166A5 A Y₀ := by
  intro X hX hns hsc hres X' hX' hX'X J hJth hJy0 hX'J hA5
  by_contra hnotle
  exact hno X J ⟨h, hJ, hX, hns, hsc, hres, hJth, hJy0, hA5, hnotle⟩

namespace Conf166A5

theorem eq_delta_normalizer (hC : Conf166A5 A c L Y₀ X J) :
    X = delta A (lB A) (Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G)) :=
  Proof15Res8Star.eq_delta_normalizer_of_mem_scriptY3Star hC.std.toSec14Std hC.mem_y3Star

theorem le_X (hC : Conf166A5 A c L Y₀ X J) : J ≤ X := by
  have hJΔ : J = delta A (lB A) J := hC.mem_y0.1.2.2.1
  have hJN : J ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    le_of_mem_thetaComponentsIn hC.mem_theta
  calc J = delta A (lB A) J := hJΔ
    _ ≤ delta A (lB A) (Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G)) := delta_mono hJN
    _ = X := (eq_delta_normalizer hC).symm

theorem le_y0 (hC : Conf166A5 A c L Y₀ X J) : J ≤ Y₀ := by
  obtain ⟨K, hJK, hKmax⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptY0 A (lB A))) hC.mem_y0
  rw [hC.std.eq_of_mem_y0Star hKmax] at hJK
  exact hJK

private theorem pCore_le_theta (hC : Conf166A5 A c L Y₀ X J) :
    CFSG.pCore 2 ↥J ≤ aschbacherSolvableCore 3 ↥J := by
  have hchar := solvable_prime_complement_core_characterization Nat.prime_three (H := ↥J)
  refine hchar.2.2.2.1 (CFSG.pCore 2 ↥J) (CFSG.pCore_normal (p := 2) (G := ↥J)) ?_ ?_
  · haveI : Group.IsNilpotent (CFSG.pCore 2 ↥J) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥J)).isNilpotent
    infer_instance
  · obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥J)).exists_card_eq
    rw [hk]
    intro h3
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h3
    obtain ⟨t, ht⟩ := h32
    omega

private theorem theta_le_pCore (hC : Conf166A5 A c L Y₀ X J) :
    aschbacherSolvableCore 3 ↥J ≤ CFSG.pCore 2 ↥J := by
  obtain ⟨e⟩ := hC.quot_a5
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  set θ := aschbacherSolvableCore 3 ↥J
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥J)
  have hθsol : Group.IsSolvable ↥θ :=
    (solvable_prime_complement_core_characterization Nat.prime_three (H := ↥J)).1
  set N : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J) := θ.map π
  have hNn : N.Normal :=
    Subgroup.Normal.map (inferInstance : θ.Normal) π (QuotientGroup.mk'_surjective _)
  have hNsol : Group.IsSolvable ↥N := by
    have := hθsol
    exact Group.isSolvable_of_surjective (f := π.subgroupMap θ) (π.subgroupMap_surjective θ)
  haveI : (N.map e.toMonoidHom).Normal := hNn.map e.toMonoidHom e.surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map e.toMonoidHom) with hbot | htop
  · have hNbot : N = ⊥ := by
      rwa [Subgroup.map_eq_bot_iff_of_injective _ e.injective] at hbot
    rw [show N = Subgroup.map π θ from rfl, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk'] at hNbot
    exact hNbot
  · exfalso
    haveI : Group.IsPerfect ↥(alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (α := Fin 5) (by simp)⟩
    have hA5sol : Group.IsSolvable ↥(alternatingGroup (Fin 5)) := by
      have := hNsol
      refine Group.isSolvable_of_surjective (f := e.toMonoidHom.comp N.subtype) ?_
      intro y
      have hy : y ∈ N.map e.toMonoidHom := by rw [htop]; exact Subgroup.mem_top y
      obtain ⟨x, hx, hxe⟩ := hy
      exact ⟨⟨x, hx⟩, hxe⟩
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)) hA5sol

theorem theta_eq (hC : Conf166A5 A c L Y₀ X J) :
    aschbacherSolvableCore 3 ↥J = CFSG.pCore 2 ↥J :=
  le_antisymm (theta_le_pCore hC) (pCore_le_theta hC)

private theorem mem_thetaComponentsIn_of_le_of_le {H : Subgroup G} {J X : Subgroup G}
    (hJ : J ∈ thetaComponentsIn H) (hJX : J ≤ X) (hXH : X ≤ H) :
    J ∈ thetaComponentsIn X := by
  have hJH : J ≤ H := le_of_mem_thetaComponentsIn hJ
  have hJ'H : J.subgroupOf H ∈ thetaComponents 3 H := (mem_thetaComponentsIn_iff.mp hJ).2
  have hsubH : CFSG.Assembly.IsSubnormal J H :=
    (CFSG.Assembly.IsSubnormal.iff_subgroupOf hJH).mpr hJ'H.2.1
  have hsubX : CFSG.Open.IsSubnormal J X := by
    have h := CFSG.Assembly.isSubnormal_iff_open.mp
      (CFSG.Assembly.IsSubnormal.inf_of_le hsubH hXH)
    rwa [inf_eq_left.mpr hJX] at h
  have hperfJ : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hJ
  have hε := Subgroup.subgroupOfEquivOfLe hJX
  have hperf : Group.IsPerfect ↥(J.subgroupOf X) := by
    have := hperfJ
    exact Group.IsPerfect.ofSurjective (f := hε.symm.toMonoidHom) hε.symm.surjective
  have hqJ : CFSG.IsQuasisimple (↥J ⧸ aschbacherSolvableCore 3 ↥J) :=
    LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr (aschbacherSolvableCore 3 ↥(J.subgroupOf H))
        (aschbacherSolvableCore 3 ↥J) (Subgroup.subgroupOfEquivOfLe hJH)
        (aschbacherSolvableCore_map_mulEquiv Nat.prime_three
          (Subgroup.subgroupOfEquivOfLe hJH)))
      hJ'H.2.2
  have hquot : CFSG.IsQuasisimple
      (↥(J.subgroupOf X) ⧸ aschbacherSolvableCore 3 ↥(J.subgroupOf X)) :=
    LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr (aschbacherSolvableCore 3 ↥J)
        (aschbacherSolvableCore 3 ↥(J.subgroupOf X)) hε.symm
        (aschbacherSolvableCore_map_mulEquiv Nat.prime_three hε.symm))
      hqJ
  exact mem_thetaComponentsIn_iff.mpr ⟨hJX, hperf, CFSG.Open.IsSubnormal.subgroupOf hsubX,
    hquot⟩

theorem mem_comp3In (hC : Conf166A5 A c L Y₀ X J) : J ∈ Sec15.comp3In X := by
  refine ⟨mem_thetaComponentsIn_of_le_of_le hC.mem_theta (le_X hC)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X), hC.mem_y0.1.2.1⟩

theorem inf_pCoreOf_le (hC : Conf166A5 A c L Y₀ X J) :
    J ⊓ CFSG.Open.pCoreOf 2 Y₀ ≤ CFSG.Open.pCoreOf 2 J := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ?_
  · intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, (hC.le_y0.trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀)) hx⟩
  · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀).to_le inf_le_right

private theorem mem_scriptY0_of_mem_comp3In (hC : Conf166A5 A c L Y₀ X J)
    (hRead : Sec15.Y4CoreReadR) (hMem : Sec15.Y4CoreMemR) {K : Subgroup G}
    (hK : K ∈ Sec15.comp3In X) : K ∈ scriptY0 A (lB A) := by
  obtain ⟨J₁, J₂, hS⟩ := (hRead G A c L hC.std.toSec15R X hC.mem_y3Star.prop.1.1
    hC.mem_y3Star.prop.2).1
  have hA2 : A ≤ Subgroup.normalizer (X : Set G) := hC.mem_y3Star.prop.1.1.2
  have hAK : A ≤ Subgroup.normalizer (K : Set G) :=
    Sec15.Y4Core.le_normalizer_of_isElemAbelian hS hC.std.isE27.1 hA2 hK
  have hN2 : Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) ∈ scriptY2 A :=
    normalizer_pCoreOf_mem_scriptY2 hC.std.isSimpleGroup hC.std.nonabelian hC.mem_y3Star.prop.1
  have hFN : generalizedFitting ↥(Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G)) =
      CFSG.pCore 2 ↥(Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G)) :=
    (isCharacteristicP_iff_generalizedFitting_eq_pCore _ 2).mp
      (CFSG.CGT.PushingUp.isCharacteristicP_of_isPLocal hC.std.charTwoType
        (CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X) hC.mem_y3Star.prop.1.2))
  have hK'c : K ∈ Sec15.comp3In (delta A (lB A)
      (Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G))) := by
    rw [← eq_delta_normalizer hC]
    exact hK
  exact hMem G A c L hC.std.toSec15R _ hN2 hFN K hK'c hAK

private theorem le_y0_of_mem_scriptY0 (hC : Conf166A5 A c L Y₀ X J) {K : Subgroup G}
    (hK : K ∈ scriptY0 A (lB A)) : K ≤ Y₀ := by
  obtain ⟨K', hKK', hK'max⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY0 A (lB A))) hK
  rw [hC.std.eq_of_mem_y0Star hK'max] at hKK'
  exact hKK'

private theorem eq_of_le_of_mem_comp3In (hC : Conf166A5 A c L Y₀ X J) {K : Subgroup G}
    (hK : K ∈ Sec15.comp3In X) (hJK : J ≤ K) : K = J := by
  have hJX : J ≤ X := le_X hC
  have hKX : K ≤ X := Sec15.Y4Core.le_of_mem_comp3In hK
  have hneJ : J ≠ ⊥ := Sec15.Y4Core.ne_bot (mem_comp3In hC)
  have hJ' : J.subgroupOf X ∈ thetaComponents 3 ↥X :=
    (mem_thetaComponentsIn_iff.mp (mem_comp3In hC).1).2
  have hK' : K.subgroupOf X ∈ thetaComponents 3 ↥X :=
    (mem_thetaComponentsIn_iff.mp hK.1).2
  have hne' : J.subgroupOf X ≠ ⊥ := by
    intro h0
    refine hneJ ?_
    rw [← Subgroup.map_subgroupOf_eq_of_le hJX, h0, Subgroup.map_bot]
  have hle' : J.subgroupOf X ≤ K.subgroupOf X := fun x hx => hJK hx
  have heq := CFSG.RankThree.theta_component_eq_of_perfect_le Nat.prime_three hJ' hK'
    hne' hJ'.1 le_rfl hle'
  calc K = (K.subgroupOf X).map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hKX).symm
    _ = (J.subgroupOf X).map X.subtype := by rw [heq]
    _ = J := Subgroup.map_subgroupOf_eq_of_le hJX

private theorem ker_comp_inclusion_mk' {K : Subgroup G} (hKY : K ≤ Y₀) :
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)).comp (Subgroup.inclusion hKY)).ker =
      (K ⊓ CFSG.Open.pCoreOf 2 Y₀).subgroupOf K := by
  ext k
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro h
    have h1 := (QuotientGroup.eq_one_iff (Subgroup.inclusion hKY k)).mp h
    have h2 : Y₀.subtype (Subgroup.inclusion hKY k) ∈
        (CFSG.pCore 2 ↥Y₀).map Y₀.subtype :=
      (Subgroup.mem_map_iff_mem Y₀.subtype_injective).mpr h1
    refine ⟨k.2, ?_⟩
    rw [show CFSG.Open.pCoreOf 2 Y₀ = (CFSG.pCore 2 ↥Y₀).map Y₀.subtype from rfl]
    exact h2
  · rintro ⟨-, hq⟩
    have h2 : Y₀.subtype (Subgroup.inclusion hKY k) ∈
        (CFSG.pCore 2 ↥Y₀).map Y₀.subtype := by
      rw [show CFSG.Open.pCoreOf 2 Y₀ = (CFSG.pCore 2 ↥Y₀).map Y₀.subtype from rfl] at hq
      simpa using hq
    exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hKY k)).mpr
      ((Subgroup.mem_map_iff_mem Y₀.subtype_injective).mp h2)

private theorem range_comp_inclusion_le_centralizer {K : Subgroup G} (hKY : K ≤ Y₀)
    (hJKQ : ⁅J, K⁆ ≤ CFSG.Open.pCoreOf 2 Y₀) :
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)).comp (Subgroup.inclusion hKY)).range ≤
      Subgroup.centralizer
        ((((J.subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)) :
          Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))) : Set (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) := by
  intro x hx
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hy
  have hmem : (j * Subgroup.inclusion hKY k * j⁻¹ * (Subgroup.inclusion hKY k)⁻¹ :
      ↥Y₀) ∈ CFSG.pCore 2 ↥Y₀ := by
    have hG : ((j : ↥Y₀) : G) * (k : G) * ((j : ↥Y₀) : G)⁻¹ * (k : G)⁻¹ ∈
        CFSG.Open.pCoreOf 2 Y₀ := by
      have h1 := (Subgroup.commutator_le.mp hJKQ) (j : G) (Subgroup.mem_subgroupOf.mp hj)
        (k : G) k.2
      simpa [commutatorElement_def] using h1
    exact (Subgroup.mem_map_iff_mem Y₀.subtype_injective).mp hG
  change ((j * Subgroup.inclusion hKY k : ↥Y₀) : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) =
    ((Subgroup.inclusion hKY k * j : ↥Y₀) : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)
  rw [QuotientGroup.eq_iff_div_mem]
  simpa [div_eq_mul_inv, mul_assoc] using hmem

private theorem isSolvable_of_commutator_le_pCoreOf {K : Subgroup G} (hKY : K ≤ Y₀)
    (hJKQ : ⁅J, K⁆ ≤ CFSG.Open.pCoreOf 2 Y₀)
    (hcent : Group.IsSolvable ↥(Subgroup.centralizer
      ((((J.subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)) :
        Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))) : Set (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)))) :
    Group.IsSolvable ↥K := by
  set φ : ↥K →* (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)).comp (Subgroup.inclusion hKY) with hφ
  have hker : φ.ker = (K ⊓ CFSG.Open.pCoreOf 2 Y₀).subgroupOf K := by
    rw [hφ]
    exact ker_comp_inclusion_mk' hKY
  have hle : φ.range ≤ Subgroup.centralizer
      ((((J.subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)) :
        Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))) : Set (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) := by
    rw [hφ]
    exact range_comp_inclusion_le_centralizer hKY hJKQ
  haveI : Group.IsSolvable ↥(Subgroup.centralizer
      ((((J.subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)) :
        Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))) : Set (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))) := hcent
  haveI : Group.IsSolvable ↥φ.range :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  haveI : Group.IsSolvable ↥φ.ker := by
    rw [hker]
    have h2 : IsPGroup 2 ↥((K ⊓ CFSG.Open.pCoreOf 2 Y₀).subgroupOf K) :=
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀).to_le
        (inf_le_right : K ⊓ CFSG.Open.pCoreOf 2 Y₀ ≤ CFSG.Open.pCoreOf 2 Y₀)).of_equiv
        (Subgroup.subgroupOfEquivOfLe (inf_le_left : K ⊓ CFSG.Open.pCoreOf 2 Y₀ ≤ K)).symm
    haveI : Group.IsNilpotent ↥((K ⊓ CFSG.Open.pCoreOf 2 Y₀).subgroupOf K) := h2.isNilpotent
    infer_instance
  haveI : Group.IsSolvable (↥K ⧸ φ.ker) :=
    Group.isSolvable_of_surjective
      (f := (QuotientGroup.quotientKerEquivRange φ).symm.toMonoidHom)
      (QuotientGroup.quotientKerEquivRange φ).symm.surjective
  exact Group.isSolvable_of_subgroup_quotient φ.ker

private theorem false_of_commutator_le_theta (hC : Conf166A5 A c L Y₀ X J)
    (hJQ : CFSG.Open.pCoreOf 2 J ≤ CFSG.Open.pCoreOf 2 Y₀)
    (hCJ : Group.IsSolvable ↥(Subgroup.centralizer
      ((((J.subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)) :
        Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))) : Set (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))))
    {K : Subgroup G} (hK : K ∈ Sec15.comp3In X) (hKY : K ≤ Y₀)
    (hcommJK : ⁅J, K⁆ ≤ inSubgroup (aschbacherSolvableCore 3) J) : False := by
  have hKX : K ≤ X := Sec15.Y4Core.le_of_mem_comp3In hK
  have hJKθ : ⁅J, K⁆ ≤ CFSG.Open.pCoreOf 2 J := by
    have hθJ : inSubgroup (aschbacherSolvableCore 3) J = CFSG.Open.pCoreOf 2 J := by
      rw [inSubgroup, theta_eq hC]
      rfl
    rwa [hθJ] at hcommJK
  have hKsol : Group.IsSolvable ↥K :=
    isSolvable_of_commutator_le_pCoreOf hKY (hJKθ.trans hJQ) hCJ
  have hKperf : Group.IsPerfect ↥K := by
    haveI : Group.IsPerfect ↥(K.subgroupOf X) := (mem_thetaComponentsIn_iff.mp hK.1).2.1
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hKX).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKX).surjective
  exact Sec15.Y4Core.ne_bot hK
    (CFSG.RankThree.GroupTheory.eq_bot_of_isPerfect_of_isSolvable hKperf hKsol)

theorem comp3In_eq (hC : Conf166A5 A c L Y₀ X J) (hRead : Sec15.Y4CoreReadR)
    (hMem : Sec15.Y4CoreMemR) (hJQ : CFSG.Open.pCoreOf 2 J ≤ CFSG.Open.pCoreOf 2 Y₀)
    (hCJ : Group.IsSolvable ↥(Subgroup.centralizer
      ((((J.subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)) :
        Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))) : Set (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)))) :
    Sec15.comp3In X = {J} := by
  classical
  have hJθ : J ∈ thetaComponentsIn X := (mem_comp3In hC).1
  ext K
  constructor
  · intro hK
    rw [Set.mem_singleton_iff]
    by_contra hKne
    have hKY : K ≤ Y₀ :=
      le_y0_of_mem_scriptY0 hC (mem_scriptY0_of_mem_comp3In hC hRead hMem hK)
    rcases dichotomy_of_mem_thetaComponentsIn hJθ hK.1 with hle | ⟨-, hcommJK⟩
    · exact hKne (eq_of_le_of_mem_comp3In hC hK hle)
    · exact false_of_commutator_le_theta hC hJQ hCJ hK hKY hcommJK
  · intro hK
    rw [Set.mem_singleton_iff] at hK
    rw [hK]
    exact mem_comp3In hC

theorem le_normalizer (hC : Conf166A5 A c L Y₀ X J) (hU : Sec15.comp3In X = {J}) :
    X ≤ Subgroup.normalizer (J : Set G) := by
  intro x hx
  have hJ : J ∈ Sec15.comp3In X := mem_comp3In hC
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  have hmem := Sec15.Y4Core.map_conj_mem (Y := X) (Subgroup.le_normalizer hx) hJ
  rw [hU] at hmem
  exact Set.mem_singleton_iff.mp hmem

theorem commutator_pPrimeCore_le (hC : Conf166A5 A c L Y₀ X J) :
    ⁅J, pPrimeCoreOf 3 X⁆ ≤ CFSG.Open.pCoreOf 2 J := by
  have hJ : J ∈ Sec15.comp3In X := mem_comp3In hC
  have hRN : pPrimeCoreOf 3 X ≤ Subgroup.normalizer (J : Set G) :=
    Sec15.Y4Core.pPrimeCoreOf_le_normalizer hJ
  have hJR : J ≤ Subgroup.normalizer (pPrimeCoreOf 3 X : Set G) :=
    (le_X hC).trans (Sec14.le_normalizer_pPrimeCoreOf 3 X)
  have hinf : J ⊓ pPrimeCoreOf 3 X ≤ CFSG.Open.pCoreOf 2 J := by
    have hchar := solvable_prime_complement_core_characterization Nat.prime_three (H := ↥J)
    have hNJ : J ≤ Subgroup.normalizer ((J ⊓ pPrimeCoreOf 3 X : Subgroup G) : Set G) :=
      fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hx, hJR hx⟩
    have hnormal : ((J ⊓ pPrimeCoreOf 3 X).subgroupOf J).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hNJ
    have hsol : Group.IsSolvable ↥((J ⊓ pPrimeCoreOf 3 X).subgroupOf J) := by
      have hNsol : Group.IsSolvable ↥(J ⊓ pPrimeCoreOf 3 X) := by
        haveI := hC.solvable_core
        exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective inf_le_right)
      have := hNsol
      exact Group.isSolvable_of_surjective
        (f := (Subgroup.subgroupOfEquivOfLe (inf_le_left : J ⊓ pPrimeCoreOf 3 X ≤ J)).symm
          |>.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe (inf_le_left : J ⊓ pPrimeCoreOf 3 X ≤ J)).symm.surjective
    have hcop : ¬ 3 ∣ Nat.card ((J ⊓ pPrimeCoreOf 3 X).subgroupOf J) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : J ⊓ pPrimeCoreOf 3 X ≤ J)).toEquiv]
      refine fun hd => ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (coprime_card_pPrimeCoreOf 3 X)) (hd.trans (Subgroup.card_dvd_of_le inf_le_right))
    have hleθ : (J ⊓ pPrimeCoreOf 3 X).subgroupOf J ≤ aschbacherSolvableCore 3 ↥J :=
      hchar.2.2.2.1 _ hnormal hsol hcop
    calc J ⊓ pPrimeCoreOf 3 X
        = ((J ⊓ pPrimeCoreOf 3 X).subgroupOf J).map J.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le inf_le_left).symm
      _ ≤ (aschbacherSolvableCore 3 ↥J).map J.subtype := Subgroup.map_mono hleθ
      _ = (CFSG.pCore 2 ↥J).map J.subtype := by rw [theta_eq hC]
      _ = CFSG.Open.pCoreOf 2 J := rfl
  rw [Subgroup.commutator_le]
  intro j hj r hr
  refine hinf ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    have h : r * j⁻¹ * r⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hRN hr) j⁻¹).mp (J.inv_mem hj)
    simpa [mul_assoc] using J.mul_mem hj h
  · rw [commutatorElement_def]
    have h : j * r * j⁻¹ ∈ pPrimeCoreOf 3 X :=
      (Subgroup.mem_normalizer_iff.mp (hJR hj) r).mp hr
    simpa [mul_assoc] using (pPrimeCoreOf 3 X).mul_mem h ((pPrimeCoreOf 3 X).inv_mem hr)

theorem deltaZero_le (hC : Conf166A5 A c L Y₀ X J) (hRead : Sec15.Y4CoreReadR)
    (hU : Sec15.comp3In X = {J}) :
    deltaZero A (lB A) X ≤ J ⊔ pPrimeCoreOf 3 X := by
  have hcov := (hRead G A c L hC.std.toSec15R X hC.mem_y3Star.prop.1.1
    hC.mem_y3Star.prop.2).2
  rwa [hU, sSup_singleton] at hcov

theorem pCoreOf_le_pPrimeCore (hC : Conf166A5 A c L Y₀ X J) :
    CFSG.Open.pCoreOf 2 J ≤ pPrimeCoreOf 3 X := by
  have hJX : J ≤ X := le_X hC
  have hJX' : J ≤ X := hJX
  have hJsub : (J.subgroupOf X).IsSubnormal :=
    (mem_thetaComponentsIn_iff.mp (mem_comp3In hC).1).2.2.1
  have hsub : CFSG.Open.IsSubnormal J X :=
    CFSG.Assembly.isSubnormal_iff_open.mp
      ((CFSG.Assembly.IsSubnormal.iff_subgroupOf hJX').mpr hJsub)
  have h1 : CFSG.Open.pCoreOf 2 J ≤ CFSG.Open.pCoreOf 2 X :=
    Quasithin.RonanD33.pCoreOf_le_of_isSubnormal hsub
  refine h1.trans (Sec14.le_pPrimeCoreOf (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X) ?_)
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_right k (by norm_num)

private theorem mem_pCoreOf_of_centralizes_quot_a5 {J : Subgroup G} {j : G} (hj : j ∈ J)
    (hquot : Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5)))
    (hcomm : ∀ y ∈ J, ⁅y, j⁆ ∈ CFSG.Open.pCoreOf 2 J) : j ∈ CFSG.Open.pCoreOf 2 J := by
  obtain ⟨e⟩ := hquot
  have hZ : Subgroup.center ↥(alternatingGroup (Fin 5)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  set j' : ↥J := ⟨j, hj⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥J)
  have hcent : π j' ∈ Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥J) g
    have hmem : z * j' * z⁻¹ * j'⁻¹ ∈ CFSG.pCore 2 ↥J := by
      have hG : ((z : G) * j * (z : G)⁻¹ * j⁻¹) ∈ CFSG.Open.pCoreOf 2 J := by
        have h1 := hcomm (z : G) z.2
        rwa [commutatorElement_def] at h1
      rw [show CFSG.Open.pCoreOf 2 J = (CFSG.pCore 2 ↥J).map J.subtype from rfl] at hG
      exact (Subgroup.mem_map_iff_mem J.subtype_injective).mp hG
    change ((z * j' : ↥J) : ↥J ⧸ CFSG.pCore 2 ↥J) = ((j' * z : ↥J) : ↥J ⧸ CFSG.pCore 2 ↥J)
    rw [QuotientGroup.eq_iff_div_mem]
    simpa [div_eq_mul_inv, mul_assoc] using hmem
  have h1 : e (π j') ∈ Subgroup.center ↥(alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro a
    obtain ⟨b, rfl⟩ := e.surjective a
    have h := (Subgroup.mem_center_iff.mp hcent) b
    calc e b * e (π j') = e (b * π j') := (map_mul e b (π j')).symm
      _ = e (π j' * b) := by rw [h]
      _ = e (π j') * e b := map_mul e (π j') b
  have h2 : e (π j') = 1 := by
    have hmem : e (π j') ∈ (⊥ : Subgroup ↥(alternatingGroup (Fin 5))) := by
      rw [← hZ]
      exact h1
    simpa using hmem
  have h3 : π j' = 1 := e.injective (by rw [h2, map_one])
  have h4 : j' ∈ CFSG.pCore 2 ↥J := (QuotientGroup.eq_one_iff j').mp h3
  exact (Subgroup.mem_map_iff_mem J.subtype_injective).mpr h4

private theorem le_normalizer_deltaZero (hC : Conf166A5 A c L Y₀ X J) (hbot : Item145BotS17) :
    X ≤ Subgroup.normalizer (deltaZero A (lB A) X : Set G) := by
  obtain ⟨-, -, h145n⟩ := rank3II_14_5_lB hC.std.isE27 (hbot G A c L Y₀ hC.std)
    hC.mem_y3Star.prop.1.1.2
  calc X = delta A (lB A) X := hC.mem_y3Star.prop.2
    _ ≤ Subgroup.normalizer (deltaZero A (lB A) X : Set G) := h145n

private theorem coprime_card_quotient_deltaZero (hC : Conf166A5 A c L Y₀ X J)
    (hbot : Item145BotS17) :
    Nat.Coprime 3 (Nat.card (↥X ⧸ (deltaZero A (lB A) X).subgroupOf X)) := by
  obtain ⟨h145, -, h145n⟩ := rank3II_14_5_lB hC.std.isE27 (hbot G A c L Y₀ hC.std)
    hC.mem_y3Star.prop.1.1.2
  set D := deltaZero A (lB A) X
  set C₀ := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ X
  have hDX : D ≤ X := Sec14.deltaZero_le X
  have hXeq : X = D ⊔ C₀ := by rw [hC.mem_y3Star.prop.2, h145]
  have hXND : X ≤ Subgroup.normalizer (D : Set G) := le_normalizer_deltaZero hC hbot
  haveI : (D.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDX).mpr hXND
  have hC0ND : C₀ ≤ Subgroup.normalizer (D : Set G) :=
    (inf_le_right : C₀ ≤ X).trans hXND
  have hsup : Nat.card ↥X ∣ Nat.card C₀ * Nat.card D := by
    rw [hXeq, sup_comm]
    exact Sec14.card_sup_dvd_card_mul hC0ND
  have hquot : Nat.card ↥X =
      Nat.card (↥X ⧸ D.subgroupOf X) * Nat.card ↥(D.subgroupOf X) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hsub : Nat.card ↥(D.subgroupOf X) = Nat.card ↥D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDX).toEquiv
  rw [hquot, hsub] at hsup
  have hdvd : Nat.card (↥X ⧸ D.subgroupOf X) ∣ Nat.card C₀ :=
    Nat.dvd_of_mul_dvd_mul_right (Nat.card_pos (α := ↥D)) hsup
  have hC0cop : Nat.Coprime 3 (Nat.card C₀) := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => ?_
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (coprime_card_pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))))
      (h3.trans (Subgroup.card_dvd_of_le (inf_le_left : C₀ ≤ _)))
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 =>
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hC0cop) (h3.trans hdvd)

private theorem inf_sup_le_pPrimeCore (hC : Conf166A5 A c L Y₀ X J)
    (hU : Sec15.comp3In X = {J}) {y : G}
    (hyC : y ∈ CFSG.Quasithin.centralizerSection X J (CFSG.Open.pCoreOf 2 J))
    (hyJR : y ∈ J ⊔ pPrimeCoreOf 3 X) : y ∈ pPrimeCoreOf 3 X := by
  classical
  obtain ⟨-, -, -, hycomm⟩ := CFSG.Quasithin.mem_centralizerSection.mp hyC
  have hJR : J ≤ Subgroup.normalizer (pPrimeCoreOf 3 X : Set G) :=
    (le_X hC).trans (Sec14.le_normalizer_pPrimeCoreOf 3 X)
  have hy' : y ∈ (J : Set G) * (pPrimeCoreOf 3 X : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right J _ hJR]
    exact hyJR
  obtain ⟨j, hj, r, hr, hjr⟩ := hy'
  have hjNQ : j ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 J : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J hj
  have hJr : ∀ u ∈ J, ⁅u, r⁆ ∈ CFSG.Open.pCoreOf 2 J := fun u hu =>
    (Subgroup.commutator_le.mp (commutator_pPrimeCore_le hC)) u hu r hr
  have hjcomm : ∀ u ∈ J, ⁅u, j⁆ ∈ CFSG.Open.pCoreOf 2 J := by
    intro u hu
    have hyc : ⁅u, y⁆ ∈ CFSG.Open.pCoreOf 2 J := hycomm u hu
    have hmid : j * ⁅u, r⁆ * j⁻¹ ∈ CFSG.Open.pCoreOf 2 J :=
      (Subgroup.mem_normalizer_iff.mp hjNQ ⁅u, r⁆).mp (hJr u hu)
    have hsplit : ⁅u, y⁆ = ⁅u, j⁆ * (j * ⁅u, r⁆ * j⁻¹) := by
      rw [← hjr, commutatorElement_mul_right_eq_mul_conj]
      group
    have hkey : ⁅u, j⁆ = ⁅u, y⁆ * (j * ⁅u, r⁆ * j⁻¹)⁻¹ := by
      rw [hsplit]
      group
    rw [hkey]
    exact (CFSG.Open.pCoreOf 2 J).mul_mem hyc ((CFSG.Open.pCoreOf 2 J).inv_mem hmid)
  have hjQ : j ∈ CFSG.Open.pCoreOf 2 J :=
    mem_pCoreOf_of_centralizes_quot_a5 hj hC.quot_a5 hjcomm
  rw [← hjr]
  exact (pPrimeCoreOf 3 X).mul_mem ((pCoreOf_le_pPrimeCore hC) hjQ) hr

private theorem coprime_card_centralizerSection (hC : Conf166A5 A c L Y₀ X J)
    (hbot : Item145BotS17) (hRead : Sec15.Y4CoreReadR) (hU : Sec15.comp3In X = {J}) :
    Nat.Coprime 3 (Nat.card ↥(CFSG.Quasithin.centralizerSection X J
      (CFSG.Open.pCoreOf 2 J))) := by
  classical
  set Q := CFSG.Open.pCoreOf 2 J
  set R := pPrimeCoreOf 3 X
  set D := deltaZero A (lB A) X
  set C := CFSG.Quasithin.centralizerSection X J Q
  have hCX : C ≤ X := CFSG.Quasithin.centralizerSection_le_left X J Q
  have hDR : D ≤ J ⊔ R := deltaZero_le hC hRead hU
  have hDX : D ≤ X := Sec14.deltaZero_le X
  have hXND : X ≤ Subgroup.normalizer (D : Set G) := le_normalizer_deltaZero hC hbot
  haveI : (D.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDX).mpr hXND
  have hCD : C ⊓ D ≤ R := fun y hy => inf_sup_le_pPrimeCore hC hU hy.1 (hDR hy.2)
  let φ : ↥C →* (↥X ⧸ D.subgroupOf X) :=
    (QuotientGroup.mk' (D.subgroupOf X)).comp (Subgroup.inclusion hCX)
  have hker : φ.ker = (C ⊓ D).subgroupOf C := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      refine ⟨c.2, ?_⟩
      have h' := (QuotientGroup.eq_one_iff (Subgroup.inclusion hCX c)).mp h
      rwa [Subgroup.mem_subgroupOf] at h'
    · rintro ⟨-, h⟩
      exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hCX c)).mpr
        (by rwa [Subgroup.mem_subgroupOf])
  have hdvd : Nat.card (↥C ⧸ (C ⊓ D).subgroupOf C) ∣
      Nat.card (↥X ⧸ D.subgroupOf X) := by
    rw [← hker, Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv,
      ← Subgroup.card_top (G := ↥X ⧸ D.subgroupOf X)]
    exact Subgroup.card_dvd_of_le (le_top : φ.range ≤ ⊤)
  have hcopquot : Nat.Coprime 3 (Nat.card (↥C ⧸ (C ⊓ D).subgroupOf C)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 =>
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (coprime_card_quotient_deltaZero hC hbot)) (h3.trans hdvd)
  have hcopker : Nat.Coprime 3 (Nat.card ((C ⊓ D).subgroupOf C)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : C ⊓ D ≤ C)).toEquiv]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 =>
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (coprime_card_pPrimeCoreOf 3 X)) (h3.trans (Subgroup.card_dvd_of_le hCD))
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ((C ⊓ D).subgroupOf C)]
  exact hcopquot.mul_right hcopker

private theorem centralizerSection_le_pPrimeCore (hC : Conf166A5 A c L Y₀ X J)
    (hbot : Item145BotS17) (hRead : Sec15.Y4CoreReadR) (hU : Sec15.comp3In X = {J}) :
    CFSG.Quasithin.centralizerSection X J (CFSG.Open.pCoreOf 2 J) ≤ pPrimeCoreOf 3 X :=
  Sec14.le_pPrimeCoreOf (CFSG.Quasithin.centralizerSection_le_left X J _)
    (CFSG.Quasithin.centralizerSection_normal (le_normalizer hC hU))
    (coprime_card_centralizerSection hC hbot hRead hU)

theorem le_pPrimeCore_of_commutator_le (hC : Conf166A5 A c L Y₀ X J)
    (hbot : Item145BotS17) (hRead : Sec15.Y4CoreReadR) (hU : Sec15.comp3In X = {J})
    {U : Subgroup G} (hUX : U ≤ X) (hUJ : ⁅U, J⁆ ≤ CFSG.Open.pCoreOf 2 J) :
    U ≤ pPrimeCoreOf 3 X := by
  refine (CFSG.Quasithin.le_centralizerSection_iff (M := X) (X := J)
    (Z := CFSG.Open.pCoreOf 2 J) (S := U) (CFSG.LieType.BorelTits.pCoreOf_le 2 J)).mpr
    ⟨hUX, ?_⟩ |>.trans (centralizerSection_le_pPrimeCore hC hbot hRead hU)
  rw [Subgroup.commutator_comm]
  exact hUJ

theorem commutatorElement_mem_pPrimeCore (hC : Conf166A5 A c L Y₀ X J)
    (h1523 : Item1523R) : ∀ j ∈ J, ⁅j, c⁆ ∈ pPrimeCoreOf 3 X := by
  obtain ⟨hY0eq, -⟩ := h1523 G A c L hC.std.toSec15R hC.j2 Y₀ hC.std.mem_y0Star
  rw [inf_eq_right.mpr hC.std.le_y0] at hY0eq
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp hC.std.zpowers_mem_omegaA).1
  have hQ0N : L ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y₀ : Set G) :=
    hC.std.le_y0.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀)
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec14.le_centralizer_of_mem_thetaComponentsAt (mem_lA_iff.mp hC.std.mem_lA).1
  have hAQ0 : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y₀ : Set G) :=
    (Subgroup.le_normalizer.trans hC.std.normalizer_le).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀)
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) := hC.mem_y0.1.1.2
  intro j hj
  have hjY : j ∈ Y₀ := hC.le_y0 hj
  rw [hY0eq] at hjY
  have hjm : j ∈ (L : Set G) * (CFSG.Open.pCoreOf 2 Y₀ : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right L _ hQ0N]
    exact hjY
  obtain ⟨l, hl, q, hq, hlq⟩ := hjm
  have hlc : ⁅l, c⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLc hl)
  have hjcQ : ⁅j, c⁆ ∈ CFSG.Open.pCoreOf 2 Y₀ := by
    rw [← hlq, commutatorElement_mul_left_eq_conj_mul, hlc, mul_one]
    have hq1 : ⁅q, c⁆ ∈ CFSG.Open.pCoreOf 2 Y₀ := by
      rw [commutatorElement_def]
      have h1 : c * q⁻¹ * c⁻¹ ∈ CFSG.Open.pCoreOf 2 Y₀ :=
        (Subgroup.mem_normalizer_iff.mp (hAQ0 hcA) q⁻¹).mp
          ((CFSG.Open.pCoreOf 2 Y₀).inv_mem hq)
      simpa [mul_assoc] using (CFSG.Open.pCoreOf 2 Y₀).mul_mem hq h1
    exact (Subgroup.mem_normalizer_iff.mp (hQ0N hl) ⁅q, c⁆).mp hq1
  have hjcJ : ⁅j, c⁆ ∈ J := by
    rw [commutatorElement_def]
    have h1 : c * j⁻¹ * c⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hAJ hcA) j⁻¹).mp (J.inv_mem hj)
    simpa [mul_assoc] using J.mul_mem hj h1
  exact pCoreOf_le_pPrimeCore hC (inf_pCoreOf_le hC ⟨hjcJ, hjcQ⟩)

end Conf166A5

end CFSG.RankThree.PartTwo.Sec16.Ctr166
