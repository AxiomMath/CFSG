module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight106KFact
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NTrans
import CFSG.LocalAnalysis.RankThreeTheoremC.LayerNormal
public import CFSG.Quasithin.Background.AutOnBasics
import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4A318
import CFSG.GroupTheory.Commutator.SubgroupOf
import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem dvd_card_of_isL2 {K : Subgroup G} {n p : ℕ} (hn : n ≠ 0) (hL2 : IsL2 (Bar2 K) (2 * n))
    (hpn : p ∣ 2 ^ n + 1) : p ∣ Nat.card K := by
  have hcard : Nat.card (Bar2 K) = 2 ^ (2 * n) * ((2 ^ (2 * n)) ^ 2 - 1) :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two
      (hL2.statedClassicalModel (by decide))
  have h1 : 2 ^ n + 1 ∣ 2 ^ (2 * n) - 1 := by
    have h := Nat.sq_sub_sq (2 ^ n) 1
    rw [one_pow, ← pow_mul, show n * 2 = 2 * n by omega] at h
    rw [h]
    exact dvd_mul_of_dvd_left (dvd_refl _) _
  have h2 : 2 ^ (2 * n) - 1 ∣ (2 ^ (2 * n)) ^ 2 - 1 := by
    have h := Nat.sq_sub_sq (2 ^ (2 * n)) 1
    rw [one_pow] at h
    rw [h]
    exact dvd_mul_of_dvd_right (dvd_refl _) _
  have h3 : p ∣ Nat.card (Bar2 K) := by
    rw [hcard]
    exact hpn.trans (h1.trans (dvd_mul_of_dvd_right h2 _))
  exact h3.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥K))

private theorem eq_bot_of_isComponentOf_of_isComponentOf_of_ne {X Y Y' K : Subgroup G}
    (hY : CFSG.Open.IsComponentOf Y X) (hY' : CFSG.Open.IsComponentOf Y' X) (hne : Y ≠ Y')
    (hKY : K ≤ Y) (hKY' : K ≤ Y') (hK : ⁅K, K⁆ = K) : K = ⊥ := by
  have hcomm : ⁅Y, Y'⁆ = ⊥ :=
    (CFSG.LocalAnalysis.GLTheoremA.I142N.isComponent_commute_or_eq hY hY').resolve_left hne
  rw [eq_bot_iff]
  calc K = ⁅K, K⁆ := hK.symm
    _ ≤ ⁅Y, Y'⁆ := Subgroup.commutator_mono hKY hKY'
    _ = ⊥ := hcomm

theorem le_normalizer_of_le_isComponentOf {X Y K V : Subgroup G}
    (hY : CFSG.Open.IsComponentOf Y X) (hKY : K ≤ Y) (hK : ⁅K, K⁆ = K) (hK1 : K ≠ ⊥)
    (hVX : V ≤ X) (hVK : V ≤ normalizer (K : Set G)) : V ≤ normalizer (Y : Set G) := by
  intro v hv
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  have hY' : CFSG.Open.IsComponentOf (Y.map (MulAut.conj v).toMonoidHom) X :=
    CFSG.LocalAnalysis.RankThreeTheoremC.IsComponentOf.map_conj hY (hVX hv)
  have hKmap : K.map (MulAut.conj v).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hVK hv)
  have hKle : K ≤ Y.map (MulAut.conj v).toMonoidHom := by
    rw [← hKmap]
    exact Subgroup.map_mono hKY
  exact hK1 (eq_bot_of_isComponentOf_of_isComponentOf_of_ne hY hY'
    (fun h => hne h.symm) hKY hKle hK)

private theorem isL2_bar2_subgroupOf {Y K : Subgroup G} {n : ℕ} (hKY : K ≤ Y)
    (hL2 : IsL2 (Bar2 K) (2 * n)) : IsL2 (Bar2 (K.subgroupOf Y)) (2 * n) := by
  obtain ⟨e⟩ := CFSG.Quasithin.H13.Ch4.L436.quotPCore_subgroupOf_mulEquiv hKY
  exact CFSG.Blueprint.LieModel.of_mulEquiv e.symm hL2

private theorem isStronglyPEmbedded_normalizer_subgroupOf {Y K M : Subgroup G} {p : ℕ}
    [Fact p.Prime] (hM : IsStronglyPEmbedded p M) (hKY : K ≤ Y) (hKM : K ≤ M) (hYM : ¬ Y ≤ M)
    (hYMK : Y ⊓ M ≤ normalizer (K : Set G)) (hNKM : normalizer (K : Set G) ≤ M)
    (hpK : p ∣ Nat.card K) :
    IsStronglyPEmbedded p (Subgroup.normalizer (K.subgroupOf Y : Set ↥Y)) := by
  have hnorm : Subgroup.normalizer (K.subgroupOf Y : Set ↥Y) = (Y ⊓ M).subgroupOf Y := by
    rw [← Subgroup.subgroupOf_normalizer_eq hKY]
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      exact Subgroup.mem_subgroupOf.mpr ⟨x.2, hNKM hx⟩
    · intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      exact Subgroup.mem_subgroupOf.mpr (hYMK hx)
  have hdvd : p ∣ Nat.card (Y ⊓ M : Subgroup G) :=
    hpK.trans (Subgroup.card_dvd_of_le (le_inf hKY hKM))
  rw [hnorm]
  exact hM.subgroupOf hYM hdvd

private theorem autOn_map_subgroupOf_eq_self {Y K V : Subgroup G} (hKY : K ≤ Y)
    (hVK : V ≤ normalizer (K : Set G)) :
    ∀ α ∈ CFSG.Quasithin.autOn V Y,
      (K.subgroupOf Y).map α.toMonoidHom = K.subgroupOf Y := by
  intro α hα
  obtain ⟨n, hn, rfl⟩ := CFSG.Quasithin.AutOn.mem_autOn_iff.mp hα
  have hmap : (((K.subgroupOf Y).map (CFSG.Quasithin.conjAct Y n).toMonoidHom).map Y.subtype) =
      K.map (MulAut.conj (n : G)) := by
    ext z
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨w, Subgroup.mem_subgroupOf.mp hw, by
        simp [CFSG.Quasithin.AutOn.coe_conjAct_apply, MulAut.conj_apply]⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨_, ⟨⟨w, hKY hw⟩, Subgroup.mem_subgroupOf.mpr hw, rfl⟩, by
        simp [CFSG.Quasithin.AutOn.coe_conjAct_apply, MulAut.conj_apply]⟩
  apply Subgroup.map_injective Y.subtype_injective
  rw [hmap, Subgroup.mem_normalizer_iff_map_conj_eq.mp (hVK hn),
    Subgroup.map_subgroupOf_eq_of_le hKY]

private theorem mulAut_conj_mem_autOn {Y K V M : Subgroup G} (hKY : K ≤ Y)
    (hVY : V ≤ normalizer (Y : Set G)) (hYMV : Y ⊓ M ≤ normalizer (V : Set G))
    (hNKM : normalizer (K : Set G) ≤ M) :
    ∀ y ∈ Subgroup.normalizer (K.subgroupOf Y : Set ↥Y), ∀ α ∈ CFSG.Quasithin.autOn V Y,
      MulAut.conj y * α * (MulAut.conj y)⁻¹ ∈ CFSG.Quasithin.autOn V Y := by
  intro y hy α hα
  obtain ⟨v, hv, rfl⟩ := CFSG.Quasithin.AutOn.mem_autOn_iff.mp hα
  have hyN : (y : G) ∈ Subgroup.normalizer (K : Set G) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hKY] at hy
    exact Subgroup.mem_subgroupOf.mp hy
  have hyM : (y : G) ∈ Y ⊓ M := ⟨y.2, hNKM hyN⟩
  have hv' : (y : G) * (v : G) * (y : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (hYMV hyM) (v : G)).mp hv
  refine CFSG.Quasithin.AutOn.mem_autOn_iff.mpr ⟨⟨_, hVY hv'⟩, hv', ?_⟩
  ext z
  simp [CFSG.Quasithin.AutOn.coe_conjAct_apply, CFSG.Quasithin.conjAct, MulAut.conj_apply,
    mul_assoc]

theorem false_of_kComp8106 (hKC : KComp8106) {Y K V M : Subgroup G} {n p : ℕ} [Fact p.Prime]
    (hYk : CFSG.Open.IsKGroup ↥Y) (hYq : CFSG.Open.IsQuasisimple ↥Y)
    (hZ : Odd (Nat.card (center ↥Y))) (hY3 : pRank 3 Y ≤ 1) (hn2 : 2 ≤ n) (hne : Even n)
    (hpn : p ∣ 2 ^ n + 1) (hKY : K ≤ Y) (hK : ⁅K, K⁆ = K) (hL2 : IsL2 (Bar2 K) (2 * n))
    (hM : IsStronglyPEmbedded p M) (hYM : ¬ Y ≤ M) (hpK : p ∣ Nat.card K) (hKM : K ≤ M)
    (hYMK : Y ⊓ M ≤ normalizer (K : Set G)) (hNKM : normalizer (K : Set G) ≤ M)
    (hV2 : IsPGroup 2 V) (hVY : V ≤ normalizer (Y : Set G)) (hVK : V ≤ normalizer (K : Set G))
    (hYMV : Y ⊓ M ≤ normalizer (V : Set G)) (hVc : ¬ V ≤ centralizer (Y : Set G)) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hprank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥Y) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥Y]
    exact hY3
  have hterm : ⁅K.subgroupOf Y, K.subgroupOf Y⁆ = K.subgroupOf Y := by
    rw [CFSG.GroupTheory.commutator_subgroupOf_eq hKY hKY, hK]
  have hbot : CFSG.Quasithin.autOn V Y = ⊥ :=
    hKC ↥Y hYk hYq hZ hprank n p hn2 hne (Fact.out : p.Prime) hpn (K.subgroupOf Y)
      hterm (isL2_bar2_subgroupOf hKY hL2)
      (isStronglyPEmbedded_normalizer_subgroupOf hM hKY hKM hYM hYMK hNKM hpK)
      (CFSG.Quasithin.autOn V Y) (CFSG.Quasithin.AutOn.isPGroup_autOn hV2)
      (autOn_map_subgroupOf_eq_self hKY hVK) (mulAut_conj_mem_autOn hKY hVY hYMV hNKM)
  exact (CFSG.Quasithin.AutOn.autOn_ne_bot_of_not_le_centralizer hVY hVc) hbot

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
