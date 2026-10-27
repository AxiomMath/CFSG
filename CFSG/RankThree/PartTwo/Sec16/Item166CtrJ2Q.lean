module

public import CFSG.RankThree.PartTwo.Sec16.Item166CtrStar
public import CFSG.Quasithin.SteinbergBSResidualCentralizer
import CFSG.GH74.Uniqueness.Section7Lemma711Aux
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
import CFSG.GroupTheory.SteinbergCBFTPSolvable

public section

namespace CFSG.RankThree.PartTwo.Sec16.Ctr166

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ J S : Subgroup G}

theorem pCoreOf_y0_eq_inf_and_quotientCentralizer_eq
    (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h1523 : Item1523R) (hS2 : IsPGroup 2 S) (hSM : S ≤ Subgroup.normalizer (Y₀ : Set G))
    (hQS : CFSG.Open.pCoreOf 2 (Y₀ ⊔ S) ≤ S) :
    CFSG.Open.pCoreOf 2 Y₀ = CFSG.Open.pCoreOf 2 (Y₀ ⊔ S) ⊓ Y₀ ∧
      CFSG.Quasithin.SteinbergBS.quotientCentralizer (Y₀ ⊔ S) Y₀ (CFSG.pCore 2 ↥Y₀) =
        CFSG.Open.pCoreOf 2 (Y₀ ⊔ S) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
    have h1 := (h1523 G A c L h.toSec15R hJ Y₀ h.mem_y0Star).1
    rwa [inf_of_le_right h.le_y0] at h1
  have hYJ : Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃*
      CFSG.Blueprint.NativeSporadic.J2) :=
    CFSG.RankThree.PartTwo.Sec17.PropU.nonempty_quotient_J2 h hJ hY
  have hcenter : Subgroup.center (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) = ⊥ := by
    obtain ⟨e⟩ := hYJ
    haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 :=
      CFSG.Sporadic.J2.isSimpleGroup_J2
    have hZJ : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥ := by
      haveI : Group.IsPerfect CFSG.Blueprint.NativeSporadic.J2 :=
        CFSG.RankThree.PartTwo.Sec17.PropU.isPerfect_J2
      have hnc : ¬ IsMulCommutative CFSG.Blueprint.NativeSporadic.J2 :=
        Group.IsPerfect.not_isMulCommutative CFSG.Blueprint.NativeSporadic.J2
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.center CFSG.Blueprint.NativeSporadic.J2) with hz | hz
      · exact hz
      · exact absurd (Subgroup.center_eq_top_iff.mp hz) hnc
    rw [eq_bot_iff]
    intro z hz
    have hz' : e z ∈ Subgroup.center CFSG.Blueprint.NativeSporadic.J2 := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro w
      obtain ⟨w', rfl⟩ := e.surjective w
      rw [← map_mul, ← map_mul, hz w']
    rw [hZJ, Subgroup.mem_bot] at hz'
    exact e.injective (by rw [hz', map_one])
  haveI : (Y₀.subgroupOf (Y₀ ⊔ S)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer hSM)
  have hquot : IsPGroup 2 (↥(Y₀ ⊔ S) ⧸ Y₀.subgroupOf (Y₀ ⊔ S)) :=
    CFSG.GH74.Uniqueness.isPGroup_quotient_sup_of_le_normalizer Y₀ S hS2
  have hSS : CFSG.ABGLocalTools.IsSylowOf 2 S S := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_rfl, hS2,
      by rw [Subgroup.relIndex_eq_one.mpr le_rfl]; norm_num⟩
  obtain ⟨h1, h2, -⟩ :=
    CFSG.Quasithin.SteinbergBS.centerless_two_residual_has_original_two_core_centralizer
      (E := Y₀ ⊔ S) (L := Y₀) (B := S) (T := S) le_sup_left hquot le_sup_right hSS
      hQS hcenter hSM
  exact ⟨h1, h2⟩

private theorem comap_pCore_inclusion_eq {H K : Subgroup G} (hHK : H ≤ K)
    (hQ : CFSG.Open.pCoreOf 2 H = CFSG.Open.pCoreOf 2 K ⊓ H) :
    (CFSG.pCore 2 ↥K).comap (Subgroup.inclusion hHK) = CFSG.pCore 2 ↥H := by
  ext x
  have h1 : x ∈ (CFSG.pCore 2 ↥K).comap (Subgroup.inclusion hHK) ↔
      (x : G) ∈ CFSG.Open.pCoreOf 2 K := by
    rw [Subgroup.mem_comap]
    constructor
    · intro hx
      exact Subgroup.mem_map_of_mem K.subtype hx
    · intro hx
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx
      have hzx' : z = Subgroup.inclusion hHK x := by
        apply Subtype.ext
        exact hzx
      rwa [hzx'] at hz
  have h2 : x ∈ CFSG.pCore 2 ↥H ↔ (x : G) ∈ CFSG.Open.pCoreOf 2 K := by
    constructor
    · intro hx
      have hx' : (x : G) ∈ CFSG.Open.pCoreOf 2 H := Subgroup.mem_map_of_mem H.subtype hx
      rw [hQ] at hx'
      exact hx'.1
    · intro hx
      have hx' : (x : G) ∈ CFSG.Open.pCoreOf 2 K ⊓ H := ⟨hx, x.2⟩
      rw [← hQ] at hx'
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx'
      have hzx' : z = x := Subtype.ext hzx
      rwa [hzx'] at hz
  exact h1.trans h2.symm

private theorem commutator_mem_pCore_of_mem {a j : G} (ha : a ∈ S) (hj : j ∈ J)
    (hY : a * j * a⁻¹ * j⁻¹ ∈ Y₀)
    (hSJ : ⁅S, J⁆ ≤ CFSG.Open.pCoreOf 2 Y₀) :
    (⟨a * j * a⁻¹ * j⁻¹, hY⟩ : ↥Y₀) ∈ CFSG.pCore 2 ↥Y₀ := by
  have hmem : ⁅a, j⁆ ∈ ⁅S, J⁆ := Subgroup.commutator_mem_commutator ha hj
  obtain ⟨q, hq, hqval⟩ := Subgroup.mem_map.mp (hSJ hmem)
  have hqj : q = ⟨a * j * a⁻¹ * j⁻¹, hY⟩ := by
    apply Subtype.ext
    show (q : G) = a * j * a⁻¹ * j⁻¹
    exact hqval.trans (commutatorElement_def _ _)
  rwa [hqj] at hq

private theorem conjQuotientHom_star_apply_eq {s : G} (hs : s ∈ S)
    (hSM : S ≤ Subgroup.normalizer (Y₀ : Set G))
    (hSJ : ⁅S, J⁆ ≤ CFSG.Open.pCoreOf 2 Y₀) :
    ∀ k ∈ (J.subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)),
      CFSG.Quasithin.SteinbergBS.conjQuotientHom Y₀ (CFSG.pCore 2 ↥Y₀) ⟨s, hSM hs⟩ k = k := by
  intro k hk
  obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hk
  have hj' : (j : G) ∈ J := Subgroup.mem_subgroupOf.mp hj
  have hY : s * (j : G) * s⁻¹ * (j : G)⁻¹ ∈ Y₀ := by
    refine Y₀.mul_mem ?_ (Y₀.inv_mem j.2)
    exact (Subgroup.mem_normalizer_iff.mp (hSM hs) (j : G)).mp j.2
  have hd : (⟨s * (j : G) * s⁻¹ * (j : G)⁻¹, hY⟩ : ↥Y₀) ∈ CFSG.pCore 2 ↥Y₀ :=
    commutator_mem_pCore_of_mem hs hj' hY hSJ
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)
      (Subgroup.normalizerMonoidHom Y₀ ⟨s, hSM hs⟩ j) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) j := by
    have e : Subgroup.normalizerMonoidHom Y₀ ⟨s, hSM hs⟩ j * j⁻¹ =
        (⟨s * (j : G) * s⁻¹ * (j : G)⁻¹, hY⟩ : ↥Y₀) := by
      apply Subtype.ext
      simp [div_eq_mul_inv, Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hmem : Subgroup.normalizerMonoidHom Y₀ ⟨s, hSM hs⟩ j * j⁻¹ ∈
        CFSG.pCore 2 ↥Y₀ := e ▸ hd
    have hAj : QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)
        (Subgroup.normalizerMonoidHom Y₀ ⟨s, hSM hs⟩ j * j⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmem
    rw [map_mul, map_inv] at hAj
    exact mul_inv_eq_one.mp hAj
  calc CFSG.Quasithin.SteinbergBS.conjQuotientHom Y₀ (CFSG.pCore 2 ↥Y₀) ⟨s, hSM hs⟩
        (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) j)
      = QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)
          (Subgroup.normalizerMonoidHom Y₀ ⟨s, hSM hs⟩ j) :=
        rfl
    _ = QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) j := h1

private theorem inv_mul_mem_quotientCentralizer {s : G} (hs : s ∈ S) {yv : ↥Y₀}
    (hSM : S ≤ Subgroup.normalizer (Y₀ : Set G))
    (hα : CFSG.Quasithin.SteinbergBS.conjQuotientHom Y₀ (CFSG.pCore 2 ↥Y₀) ⟨s, hSM hs⟩ =
      MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) yv)) :
    (yv : G)⁻¹ * s ∈ CFSG.Quasithin.SteinbergBS.quotientCentralizer (Y₀ ⊔ S) Y₀
      (CFSG.pCore 2 ↥Y₀) := by
  rw [CFSG.Quasithin.SteinbergBS.mem_quotientCentralizer_iff]
  refine ⟨?_, ?_, ?_⟩
  · exact mul_mem (Subgroup.mem_sup_left (Y₀.inv_mem yv.2)) (Subgroup.mem_sup_right hs)
  · exact mul_mem (Subgroup.le_normalizer (Y₀.inv_mem yv.2)) (hSM hs)
  · intro l hl
    let l' : ↥Y₀ := ⟨l, hl⟩
    have hαl : CFSG.Quasithin.SteinbergBS.conjQuotientHom Y₀ (CFSG.pCore 2 ↥Y₀) ⟨s, hSM hs⟩
        (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) l') =
        QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)
          (Subgroup.normalizerMonoidHom Y₀ ⟨s, hSM hs⟩ l') :=
      rfl
    have hconjmk : MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) yv)
          (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) l') =
        QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)
          (Subgroup.normalizerMonoidHom Y₀ ⟨(yv : G), Subgroup.le_normalizer yv.2⟩ l') := by
      rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
      congr 1
    have hdiff : Subgroup.normalizerMonoidHom Y₀ ⟨s, hSM hs⟩ l' /
        Subgroup.normalizerMonoidHom Y₀ ⟨(yv : G), Subgroup.le_normalizer yv.2⟩ l' ∈
        CFSG.pCore 2 ↥Y₀ := by
      have h := congrArg (fun f : MulAut (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) =>
        f (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) l')) hα
      rw [hαl, hconjmk] at h
      exact QuotientGroup.eq_iff_div_mem.mp h
    have hconjmem : yv⁻¹ * (Subgroup.normalizerMonoidHom Y₀ ⟨s, hSM hs⟩ l' /
        Subgroup.normalizerMonoidHom Y₀ ⟨(yv : G), Subgroup.le_normalizer yv.2⟩ l') *
        (yv⁻¹)⁻¹ ∈ CFSG.pCore 2 ↥Y₀ :=
      (CFSG.pCore_normal (p := 2) (G := ↥Y₀)).conj_mem _ hdiff yv⁻¹
    have hl' : ((l' : ↥Y₀) : G) = l := rfl
    refine Subgroup.mem_map.mpr ⟨_, hconjmem, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, div_eq_mul_inv, hl',
      Subgroup.normalizerMonoidHom_apply_apply_coe]
    group

theorem exists_mem_inf_inv_mul_mem
    (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h1523 : Item1523R) (hK : KFacts.KS166J2A5) (hJY : J ≤ Y₀)
    (hJperf : Group.IsPerfect ↥J)
    (hJA5 : Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5)))
    (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hSM : S ≤ Subgroup.normalizer (Y₀ : Set G)) (hQS : CFSG.Open.pCoreOf 2 (Y₀ ⊔ S) ≤ S)
    (hSJ : ⁅S, J⁆ ≤ CFSG.Open.pCoreOf 2 Y₀)
    (hC : CFSG.Quasithin.SteinbergBS.quotientCentralizer (Y₀ ⊔ S) Y₀ (CFSG.pCore 2 ↥Y₀) =
      CFSG.Open.pCoreOf 2 (Y₀ ⊔ S)) :
    ∀ s ∈ S, ∃ y ∈ S ⊓ Y₀, y⁻¹ * s ∈ CFSG.Open.pCoreOf 2 (Y₀ ⊔ S) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKstar := ks166J2A5_at_star h hJ h1523 hK hJY hJperf hJA5 hAJ
  intro s hs
  obtain ⟨g, -, hα⟩ := hKstar.2.2.1 _ (conjQuotientHom_star_apply_eq hs hSM hSJ)
  obtain ⟨yv, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y₀) g
  have hx := inv_mul_mem_quotientCentralizer hs hSM hα
  rw [hC] at hx
  refine ⟨(yv : G), ⟨?_, yv.2⟩, hx⟩
  have hy : (yv : G) = s * ((yv : G)⁻¹ * s)⁻¹ := by group
  rw [hy]
  exact S.mul_mem hs (S.inv_mem (hQS hx))

theorem exists_quotient_mulEquiv_y0 (hSM : S ≤ Subgroup.normalizer (Y₀ : Set G))
    (hQY : CFSG.Open.pCoreOf 2 Y₀ = CFSG.Open.pCoreOf 2 (Y₀ ⊔ S) ⊓ Y₀)
    (hcov : ∀ s ∈ S, ∃ y ∈ S ⊓ Y₀, y⁻¹ * s ∈ CFSG.Open.pCoreOf 2 (Y₀ ⊔ S)) :
    ∃ ψ : (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) ≃* (↥(Y₀ ⊔ S) ⧸ CFSG.pCore 2 ↥(Y₀ ⊔ S)),
      ∀ y : ↥Y₀, ψ (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) y) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥(Y₀ ⊔ S)) (Subgroup.inclusion le_sup_left y) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Qy : Subgroup ↥Y₀ := CFSG.pCore 2 ↥Y₀
  let Qg : Subgroup ↥(Y₀ ⊔ S) := CFSG.pCore 2 ↥(Y₀ ⊔ S)
  let φ : ↥Y₀ →* ↥(Y₀ ⊔ S) ⧸ Qg :=
    (QuotientGroup.mk' Qg).comp (Subgroup.inclusion le_sup_left)
  have hker : φ.ker = Qy := by
    rw [show φ = (QuotientGroup.mk' Qg).comp (Subgroup.inclusion le_sup_left) from rfl,
      ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact comap_pCore_inclusion_eq le_sup_left hQY
  have hsurj : Function.Surjective φ := by
    intro z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
    have hg : (g : G) ∈ (Y₀ : Set G) * (S : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Y₀ S hSM]
      exact g.2
    obtain ⟨y₁, hy₁, s, hs, hys⟩ := hg
    obtain ⟨y₂, hy₂, hy₂s⟩ := hcov s hs
    let w : ↥Y₀ := ⟨y₁ * y₂, Y₀.mul_mem hy₁ (Subgroup.mem_inf.mp hy₂).2⟩
    refine ⟨w, ?_⟩
    show QuotientGroup.mk' Qg (Subgroup.inclusion le_sup_left w) = QuotientGroup.mk' Qg g
    rw [QuotientGroup.mk'_eq_mk']
    refine ⟨(Subgroup.inclusion le_sup_left w : ↥(Y₀ ⊔ S))⁻¹ * g, ?_, ?_⟩
    · have hval : (((Subgroup.inclusion le_sup_left w :
          ↥(Y₀ ⊔ S))⁻¹ * g : ↥(Y₀ ⊔ S)) : G) = y₂⁻¹ * s := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        show (y₁ * y₂)⁻¹ * (g : G) = y₂⁻¹ * s
        rw [show (g : G) = y₁ * s from hys.symm]
        group
      have hG : (((Subgroup.inclusion le_sup_left w : ↥(Y₀ ⊔ S))⁻¹ * g :
          ↥(Y₀ ⊔ S)) : G) ∈ CFSG.Open.pCoreOf 2 (Y₀ ⊔ S) := by
        rw [hval]
        exact hy₂s
      obtain ⟨q, hq, hqz⟩ := Subgroup.mem_map.mp hG
      have hqeq : q = (Subgroup.inclusion le_sup_left w : ↥(Y₀ ⊔ S))⁻¹ * g :=
        Subtype.ext hqz
      rw [hqeq] at hq
      exact hq
    · group
  refine ⟨QuotientGroup.liftEquiv Qy hsurj hker.symm, ?_⟩
  intro y
  exact QuotientGroup.liftEquiv_mk _ _ _ _

theorem map_star_inf_eq
    (hcov : ∀ s ∈ S, ∃ y ∈ S ⊓ Y₀, y⁻¹ * s ∈ CFSG.Open.pCoreOf 2 (Y₀ ⊔ S))
    (ψ : (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) ≃* (↥(Y₀ ⊔ S) ⧸ CFSG.pCore 2 ↥(Y₀ ⊔ S)))
    (hψ : ∀ y : ↥Y₀, ψ (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) y) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥(Y₀ ⊔ S)) (Subgroup.inclusion le_sup_left y)) :
    (((S ⊓ Y₀).subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀))).map ψ.toMonoidHom =
      (S.subgroupOf (Y₀ ⊔ S)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(Y₀ ⊔ S))) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
    change ψ (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) b) ∈
      (S.subgroupOf (Y₀ ⊔ S)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(Y₀ ⊔ S)))
    rw [hψ b]
    exact Subgroup.mem_map_of_mem _
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hb).1)
  · intro hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y, hy, hyq⟩ := hcov (g : G) hg
    have hmemY : QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) ⟨y, (Subgroup.mem_inf.mp hy).2⟩ ∈
        ((S ⊓ Y₀).subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hy)
    have hmemG := Subgroup.mem_map_of_mem ψ.toMonoidHom hmemY
    have hgy : QuotientGroup.mk' (CFSG.pCore 2 ↥(Y₀ ⊔ S)) g =
        ψ (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) ⟨y, (Subgroup.mem_inf.mp hy).2⟩) := by
      rw [hψ ⟨y, (Subgroup.mem_inf.mp hy).2⟩, QuotientGroup.mk'_eq_mk']
      have hinv : ((Subgroup.inclusion le_sup_left
          ⟨y, (Subgroup.mem_inf.mp hy).2⟩ : ↥(Y₀ ⊔ S))⁻¹ * g) ∈
          CFSG.pCore 2 ↥(Y₀ ⊔ S) := by
        obtain ⟨q, hq, hqval⟩ := Subgroup.mem_map.mp hyq
        have hq' : ((Subgroup.inclusion le_sup_left
            ⟨y, (Subgroup.mem_inf.mp hy).2⟩ : ↥(Y₀ ⊔ S))⁻¹ * g : ↥(Y₀ ⊔ S)) = q := by
          apply Subtype.ext
          rw [Subgroup.coe_mul, Subgroup.coe_inv]
          show (y : G)⁻¹ * (g : G) = (q : G)
          exact hqval.symm
        rwa [hq']
      refine ⟨g⁻¹ * (Subgroup.inclusion le_sup_left
        ⟨y, (Subgroup.mem_inf.mp hy).2⟩ : ↥(Y₀ ⊔ S)), ?_, ?_⟩
      · convert (CFSG.pCore 2 ↥(Y₀ ⊔ S)).inv_mem hinv using 1
        group
      · group
    rwa [hgy]

private theorem map_inf_le_centralizer_star (hSJ : ⁅S, J⁆ ≤ CFSG.Open.pCoreOf 2 Y₀) :
    ((S ⊓ Y₀).subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)) ≤
      Subgroup.centralizer
        (((J.subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)) :
          Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) : Set (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hy
  have ha' : (a : G) ∈ S := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ha)).1
  have hj' : (j : G) ∈ J := Subgroup.mem_subgroupOf.mp hj
  have hd : a * j * a⁻¹ * j⁻¹ ∈ CFSG.pCore 2 ↥Y₀ := by
    have hcomm : ⁅(a : G), (j : G)⁆ ∈ ⁅S, J⁆ := Subgroup.commutator_mem_commutator ha' hj'
    obtain ⟨q, hq, hqval⟩ := Subgroup.mem_map.mp (hSJ hcomm)
    have hqj : q = a * j * a⁻¹ * j⁻¹ := by
      apply Subtype.ext
      show (q : G) = a * j * a⁻¹ * j⁻¹
      exact hqval.trans (commutatorElement_def _ _)
    rwa [hqj] at hq
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) (a * j * a⁻¹ * j⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hd
  calc QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) j * QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) a
      = QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) (j * a) := by rw [map_mul]
    _ = QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) (a * j) := by
        have hd' : (a * j * a⁻¹ * j⁻¹)⁻¹ ∈ CFSG.pCore 2 ↥Y₀ :=
          (CFSG.pCore 2 ↥Y₀).inv_mem hd
        have hkey : (j * a) / (a * j) = (a * j * a⁻¹ * j⁻¹)⁻¹ := by
          rw [div_eq_mul_inv]
          group
        have hmem : (j * a) / (a * j) ∈ CFSG.pCore 2 ↥Y₀ := by rw [hkey]; exact hd'
        exact QuotientGroup.eq_iff_div_mem.mpr hmem
    _ = QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) a * QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) j := by
        rw [map_mul]

private theorem isPGroup_map_inf_star (hS2 : IsPGroup 2 S) :
    IsPGroup 2 (((S ⊓ Y₀).subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀))) := by
  have h2 : IsPGroup 2 ((S ⊓ Y₀).subgroupOf Y₀) :=
    IsPGroup.of_equiv hS2.to_inf_left (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  exact IsPGroup.map h2 (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀))

private theorem inf_le_pCoreOf_of_map_inf_eq_bot
    (hbot : ((S ⊓ Y₀).subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)) = ⊥) :
    S ⊓ Y₀ ≤ CFSG.Open.pCoreOf 2 Y₀ := by
  have hle : (S ⊓ Y₀).subgroupOf Y₀ ≤ CFSG.pCore 2 ↥Y₀ := by
    have h := (Subgroup.map_eq_bot_iff ((S ⊓ Y₀).subgroupOf Y₀)).mp hbot
    rwa [QuotientGroup.ker_mk'] at h
  intro x hx
  exact Subgroup.mem_map.mpr ⟨⟨x, (Subgroup.mem_inf.mp hx).2⟩,
    hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem inf_le_pCoreOf_or_nonempty
    (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h1523 : Item1523R) (hK : KFacts.KS166J2A5) (hJY : J ≤ Y₀)
    (hJperf : Group.IsPerfect ↥J)
    (hJA5 : Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5)))
    (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hS2 : IsPGroup 2 S) (hAS : A ≤ Subgroup.normalizer (S : Set G))
    (hSJ : ⁅S, J⁆ ≤ CFSG.Open.pCoreOf 2 Y₀)
    (ψ : (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) ≃* (↥(Y₀ ⊔ S) ⧸ CFSG.pCore 2 ↥(Y₀ ⊔ S)))
    (himg : (((S ⊓ Y₀).subgroupOf Y₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀))).map
        ψ.toMonoidHom =
      (S.subgroupOf (Y₀ ⊔ S)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(Y₀ ⊔ S)))) :
    S ⊓ Y₀ ≤ CFSG.Open.pCoreOf 2 Y₀ ∨
      (Nonempty ((S.subgroupOf (Y₀ ⊔ S)).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥(Y₀ ⊔ S))) ≃*
          Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
        Nonempty (Subgroup.centralizer
            (((S.subgroupOf (Y₀ ⊔ S)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(Y₀ ⊔ S))) :
              Subgroup (↥(Y₀ ⊔ S) ⧸ CFSG.pCore 2 ↥(Y₀ ⊔ S))) :
              Set (↥(Y₀ ⊔ S) ⧸ CFSG.pCore 2 ↥(Y₀ ⊔ S))) ≃*
          (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) × alternatingGroup (Fin 5))) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Qy : Subgroup ↥Y₀ := CFSG.pCore 2 ↥Y₀
  let Qg : Subgroup ↥(Y₀ ⊔ S) := CFSG.pCore 2 ↥(Y₀ ⊔ S)
  let Jstar : Subgroup (↥Y₀ ⧸ Qy) := (J.subgroupOf Y₀).map (QuotientGroup.mk' Qy)
  let E : Subgroup (↥Y₀ ⧸ Qy) := ((A ⊓ L).subgroupOf Y₀).map (QuotientGroup.mk' Qy)
  let Sstar : Subgroup (↥Y₀ ⧸ Qy) := ((S ⊓ Y₀).subgroupOf Y₀).map (QuotientGroup.mk' Qy)
  let Rstar : Subgroup (↥Y₀ ⧸ Qy) :=
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer (Jstar : Set (↥Y₀ ⧸ Qy)))
  let SstarG : Subgroup (↥(Y₀ ⊔ S) ⧸ Qg) := (S.subgroupOf (Y₀ ⊔ S)).map (QuotientGroup.mk' Qg)
  have hEnorm : E ≤ Subgroup.normalizer (Sstar : Set (↥Y₀ ⧸ Qy)) :=
    map_inf_le_normalizer_star (J := S ⊓ Y₀) inf_le_right
      (CFSG.GroupTheory.FT63ChII.le_normalizer_inf_of_le hAS h.mem_y0Star.prop.1.1.2)
  have hKstar := ks166J2A5_at_star h hJ h1523 hK hJY hJperf hJA5 hAJ
  have h4 := hKstar.2.2.2.1 Sstar (map_inf_le_centralizer_star hSJ) (isPGroup_map_inf_star hS2)
    hEnorm
  obtain ⟨h5⟩ := hKstar.2.2.2.2.1
  obtain ⟨h6⟩ := hKstar.2.2.2.2.2
  rcases h4 with hbot | hR
  · exact Or.inl (inf_le_pCoreOf_of_map_inf_eq_bot hbot)
  · right
    have hCeq : Subgroup.centralizer (Sstar : Set (↥Y₀ ⧸ Qy)) =
        Subgroup.centralizer (Rstar : Set (↥Y₀ ⧸ Qy)) := by rw [hR]
    constructor
    · have h : Nonempty (↥(Sstar.map ψ.toMonoidHom) ≃*
          Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
        ⟨(Subgroup.equivMapOfInjective Sstar ψ.toMonoidHom ψ.injective).symm.trans
          ((MulEquiv.subgroupCongr hR).trans h5)⟩
      rw [himg] at h
      exact h
    · have h : Nonempty (↥(Subgroup.centralizer
          ((Sstar.map ψ.toMonoidHom : Subgroup (↥(Y₀ ⊔ S) ⧸ Qg)) : Set
            (↥(Y₀ ⊔ S) ⧸ Qg))) ≃*
          (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) × alternatingGroup (Fin 5)) := by
        rw [CFSG.StandardSubgroupAPI.centralizer_map_mulEquiv ψ Sstar]
        exact ⟨(Subgroup.equivMapOfInjective
          (Subgroup.centralizer (Sstar : Set (↥Y₀ ⧸ Qy))) ψ.toMonoidHom ψ.injective).symm.trans
          ((MulEquiv.subgroupCongr hCeq).trans h6)⟩
      rw [himg] at h
      exact h

end CFSG.RankThree.PartTwo.Sec16.Ctr166
