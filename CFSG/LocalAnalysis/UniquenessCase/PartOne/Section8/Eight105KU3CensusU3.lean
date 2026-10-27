module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KU3CensusL2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KU3CensusSub

import CFSG.LocalAnalysis.EvenBN.GMSK.U3Perfect
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQSL2U3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def KU3SU3L2Fix : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (f m : ℕ), Nat.card F = (2 ^ f) ^ 2 → 2 ≤ f → 2 ≤ m →
    ∀ L : Subgroup (StatedSU 3 (2 ^ f) F), IsL2 L m →
      ∃ J : Subgroup (StatedSU 3 (2 ^ f) F), IsL2 J f ∧ L ≤ J

private lemma two_le_of_even_of_lieModel_PSU {X : Type} [Group X] {f : ℕ}
    (hL : LieModel X .PSU 3 2 f) (hf : Even f) : 2 ≤ f := by
  obtain ⟨k, rfl⟩ := hf
  have h1 : 1 ≤ k + k := (LieModel.admissible hL).2.1
  omega

private lemma pCore_two_eq_bot_of_isPerfect_of_lieModel_PSU3 {X : Type} [Group X] [Finite X]
    {f : ℕ} (hL : LieModel X .PSU 3 2 f) {K : Subgroup X} (hperfect : ⁅K, K⁆ = K)
    (hKne : K ≠ ⊥) : CFSG.pCore 2 ↥K = ⊥ := by
  by_contra hne
  let D : Subgroup X := (CFSG.pCore 2 ↥K).map K.subtype
  have hDle : D ≤ K := Subgroup.map_subtype_le (CFSG.pCore 2 ↥K)
  have hDsub : D.subgroupOf K = CFSG.pCore 2 ↥K := by
    rw [Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective K)]
  have hDnorm : (D.subgroupOf K).Normal := hDsub ▸ CFSG.pCore_normal
  have hKD : K ≤ Subgroup.normalizer (D : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDle).mp hDnorm
  have hDp : IsPGroup 2 ↥D :=
    IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) K.subtype
  have hDne : D ≠ ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (CFSG.pCore 2 ↥K)
      (Subgroup.subtype_injective K)).not.mpr hne
  exact hKne
    (CFSG.LocalAnalysis.EvenBN.GMSK.eq_bot_of_isPerfect_of_le_normalizer_of_lieModel_PSU3
      hL hDp hDne (Subgroup.isPerfect_iff.mpr hperfect) hKD)

private lemma exists_isL2_le_of_fix {X F : Type} [Group X] [Field F] [Finite F]
    (hFix : KU3SU3L2Fix) {f n : ℕ} (hFcard : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f)
    (hn : 2 ≤ n) (e : X ≃* StatedSU 3 (2 ^ f) F) {K : Subgroup X}
    (hK : IsL2 ↥K (2 * n)) : ∃ J : Subgroup X, IsL2 ↥J f ∧ K ≤ J := by
  let L : Subgroup (StatedSU 3 (2 ^ f) F) := K.map e.toMonoidHom
  have hL : IsL2 ↥L (2 * n) :=
    LieModel.of_mulEquiv (Subgroup.equivMapOfInjective K e.toMonoidHom e.injective) hK
  obtain ⟨J, hJ, hLJ⟩ := hFix F f (2 * n) hFcard hf (by omega) L hL
  have hmap : (J.comap e.toMonoidHom).map e.toMonoidHom = J :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective J
  have hJ' : IsL2 ↥(J.comap e.toMonoidHom) f :=
    LieModel.of_mulEquiv
      ((Subgroup.equivMapOfInjective (J.comap e.toMonoidHom) e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hmap)).symm hJ
  refine ⟨J.comap e.toMonoidHom, hJ', ?_⟩
  intro x hx
  rw [Subgroup.mem_comap]
  exact hLJ (Subgroup.mem_map_of_mem e.toMonoidHom hx)

private lemma strictMono_two_pow_mul_two_pow_sq_sub_one :
    StrictMono (fun m : ℕ => 2 ^ m * ((2 ^ m) ^ 2 - 1)) := by
  refine strictMono_nat_of_lt_succ fun m => ?_
  have h1 : 2 ^ m < 2 ^ (m + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h2 : (2 ^ m) ^ 2 - 1 < (2 ^ (m + 1)) ^ 2 - 1 := by
    have h3 : (2 ^ m) ^ 2 < (2 ^ (m + 1)) ^ 2 := by
      rw [← pow_mul, ← pow_mul]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hpos : 0 < (2 ^ m) ^ 2 := by positivity
    exact Nat.sub_lt_sub_right (by omega) h3
  exact Nat.mul_lt_mul'' h1 h2

private lemma eq_of_isL2_of_isL2_two_mul {X : Type} [Group X] {f n : ℕ}
    (h1 : IsL2 X f) (h2 : IsL2 X (2 * n)) : f = 2 * n := by
  have hcard1 := CFSG.SeitzReduction.RankOne.card_of_lieModel_PSL_two_two h1
  have hcard2 := CFSG.SeitzReduction.RankOne.card_of_lieModel_PSL_two_two h2
  have hord : ordA 1 (2 ^ f) = ordA 1 (2 ^ (2 * n)) := hcard1.symm.trans hcard2
  have hf1 : 1 ≤ f := (LieModel.admissible h1).2.1
  have h2n1 : 1 ≤ 2 * n := (LieModel.admissible h2).2.1
  rw [CFSG.RankThree.PartOne.S12K.ordA_one_eq hf1,
    CFSG.RankThree.PartOne.S12K.ordA_one_eq h2n1] at hord
  exact StrictMono.injective strictMono_two_pow_mul_two_pow_sq_sub_one hord

theorem kU3CensusU3_of_fix (hFix : KU3SU3L2Fix) : KU3CensusU3 := by
  intro X _ _ f hf hL K D₀ n p h
  obtain ⟨hperfect, hL2, hn, hnEven, hp, hpdiv, hD₀K, hD₀p, hcent, -⟩ := h
  obtain ⟨F, hF, hFin, hFcard, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS.exists_mulEquiv_statedSU_of_isU3
      hL hf
  have hf2 : 2 ≤ f := two_le_of_even_of_lieModel_PSU hL hf
  have hp1 : 1 < p := hp.one_lt
  have hD₀ne : D₀ ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hD₀p
    omega
  have hKne : K ≠ ⊥ := by
    intro hbot
    exact hD₀ne (le_bot_iff.mp (hbot ▸ hD₀K))
  have hpCore : CFSG.pCore 2 ↥K = ⊥ :=
    pCore_two_eq_bot_of_isPerfect_of_lieModel_PSU3 hL hperfect hKne
  have hK2n : IsL2 ↥K (2 * n) :=
    LieModel.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hpCore).trans QuotientGroup.quotientBot) hL2
  obtain ⟨J, hJ, hKJ⟩ := exists_isL2_le_of_fix hFix hFcard hf2 hn e hK2n
  have hKJeq : K = J := by
    by_contra hne
    have hcensus := kU3CensusHyp_subgroupOf (X := J) hKJ hperfect hL2 hn hnEven hp hpdiv
      hD₀K hD₀p (inf_le_right.trans hcent) (fun h => hne h.symm)
    exact kU3CensusL2_holds (X := ↥J) f hJ (K.subgroupOf J) (D₀.subgroupOf J) n p hcensus
  rw [← hKJeq] at hJ
  exact eq_of_isL2_of_isL2_two_mul hJ hK2n

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
