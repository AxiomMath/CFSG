module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporK105In
public import CFSG.Monster.B.Cbar.GenData
import CFSG.Monster.B.Cbar.SylowTwo
import CFSG.Monster.B.Co2Catalog
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo2
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporOdd
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporK105InThompson
import CFSG.Monster.AxisCount.BabySetup
import CFSG.Monster.B.Final.PinnedBOrder
import CFSG.GroupTheory.ElementaryAbelianTransport
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3027
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3118
public import Certificates.Certificate6001
public import Certificates.Certificate6002
public import Certificates.Certificate6003
public import Certificates.Certificate6004
public import Certificates.Certificate6005
public import Certificates.Certificate6007
public import Certificates.Certificate10503
public import Certificates.Certificate16026
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.Monster.AxisCount.BabyCount
public import CFSG.Monster.AxisCount.BabyCover
public import CFSG.Monster.AxisCount.BabyCoverCheck
public import CFSG.Monster.AxisCount.BabyCoverSpec
public import CFSG.Monster.AxisCount.BabyIdentCheck
public import CFSG.Monster.AxisCount.BabyInvCheck
public import CFSG.Monster.Visible.SignCompat
public import CFSG.Open.MonsterY443Defs
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.Co1Base
public import CFSG.Sporadic.Th.F2Spec
import CFSG.Certificates.InvariantMerge

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

namespace BK

open Subgroup CFSG.Monster.B
open CFSG.QuasithinUnique (IsSylowTwoOf)

private theorem subgroupOf_isSylowTwoOf {T : Subgroup Cbar} (hT : IsSylowTwoOf T ⊤)
    (hTJ : T ≤ Jbar) :
    IsPGroup 2 (T.subgroupOf Jbar) ∧ ¬ 2 ∣ (T.subgroupOf Jbar).index := by
  have hT2 : IsPGroup 2 (T.subgroupOf Jbar) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTJ).symm
  have hTnot : ¬ 2 ∣ T.relIndex ⊤ := hT.2.2
  rw [Subgroup.relIndex_top_right] at hTnot
  exact ⟨hT2, fun h2 => hTnot (h2.trans (Subgroup.relIndex_dvd_index_of_le hTJ))⟩

theorem ebar_le {T : Subgroup Cbar} (hT : IsSylowTwoOf T ⊤) (hTJ : T ≤ Jbar) : Ebar ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hT2, hTindex⟩ := subgroupOf_isSylowTwoOf hT hTJ
  let P : Sylow 2 Jbar := hT2.toSylow hTindex
  have hPcoe : (P : Subgroup Jbar) = T.subgroupOf Jbar := IsPGroup.toSylow_coe hT2 hTindex
  have hE2 : IsPGroup 2 (Ebar.subgroupOf Jbar) :=
    Ebar_extraspecial.1.1.of_equiv (Subgroup.subgroupOfEquivOfLe Ebar_le_Jbar).symm
  have hEP : Ebar.subgroupOf Jbar ≤ (P : Subgroup Jbar) :=
    IsPGroup.le_sylow_of_normal hE2 P
  intro e he
  have hmem : (⟨e, Ebar_le_Jbar he⟩ : ↥Jbar) ∈ Ebar.subgroupOf Jbar :=
    Subgroup.mem_subgroupOf.mpr he
  have hPmem := hEP hmem
  rw [hPcoe] at hPmem
  exact Subgroup.mem_subgroupOf.mp hPmem

theorem xbar_mem_quasithinOmegaOneCenter {T : Subgroup Cbar} (hT : IsSylowTwoOf T ⊤)
    (hTJ : T ≤ Jbar) : xbar ∈ CFSG.Open.quasithinOmegaOneCenter T := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · refine ⟨ebar_le hT hTJ xbar_mem_Ebar, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro t ht
    exact Subgroup.mem_centralizer_singleton_iff.mp (Jbar_le_centralizer_xbar (hTJ ht))
  · rw [pow_two, xbar_mul_self]

theorem k105In_centralizer_xbar
    (T : Subgroup CFSG.Monster.B.Cbar) (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤)
    (hTJ : T ≤ CFSG.Monster.B.Jbar) :
    K105In (Subgroup.centralizer {CFSG.Monster.B.xbar}) T := by
  rw [centralizer_xbar]
  refine k105In_of_quotient hT hTJ (Ebar.subgroupOf Jbar) ?_ (MulEquiv.refl _)
    (k105SporAt_Co2 _ ⟨Co2Catalog.jbarQuotEquiv⟩)
  rw [Subgroup.subgroupOf_map_subtype]
  exact inf_le_left.trans (ebar_le hT hTJ)

theorem eq_one_or_eq_xbar_of_central {T : Subgroup Cbar} (hT : IsSylowTwoOf T ⊤)
    (hTJ : T ≤ Jbar) {t : Cbar} (ht : t ∈ T) (hts : ∀ s ∈ T, s * t = t * s) :
    t = 1 ∨ t = xbar := by
  have hE : Ebar ≤ T := ebar_le hT hTJ
  have hcent : t ∈ Jbar ⊓ Subgroup.centralizer (Ebar : Set Cbar) := by
    refine Subgroup.mem_inf.2 ⟨hTJ ht, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    exact fun e he => hts e (hE he)
  rw [centralizer_Ebar] at hcent
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hcent
  have hk2 : xbar ^ (k % (orderOf xbar : ℤ)) = xbar ^ k := zpow_mod_orderOf xbar k
  rw [orderOf_xbar, Nat.cast_ofNat, hk] at hk2
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [h, zpow_zero] at hk2
    exact hk2.symm
  · right
    rw [h, zpow_one] at hk2
    exact hk2.symm

theorem b_oddLocal
    {T : Subgroup Cbar} (hT : IsSylowTwoOf T ⊤) (hTJ : T ≤ Jbar) (p : ℕ) (hp : p.Prime)
    (hp5 : 5 ≤ p) (A : Subgroup Cbar) (hA : CFSG.Open.IsElemAbelian p A) (hA1 : A ≠ ⊥)
    (hTA : T ≤ normalizer (A : Set Cbar)) : A ⊓ centralizer {xbar} ≠ ⊥ := by
  intro hAz
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := (CFSG.Open.IsElemAbelian.isPGroup hA).exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hA1 (Subgroup.card_eq_one.1 (by rw [hn, pow_zero]))
  have hzT : xbar ∈ T := ebar_le hT hTJ xbar_mem_Ebar
  have hdvd := card_dvd_card_GL_of_inf_centralizer_eq_bot hp (by omega) hT.2.1 hzT xbar_mul_self
    (fun t ht hts => eq_one_or_eq_xbar_of_central hT hTJ ht hts) hA hn hA1 hTA hAz
  have hdef : CFSG.Open.monsterBabyOrder =
      2 ^ 41 * (3 ^ 13 * (5 ^ 6 * (7 ^ 2 * (11 * (13 * (17 * (19 * (23 * (31 * 47))))))))) := by
    have h : CFSG.Open.monsterBabyOrder =
        2 ^ 41 * 3 ^ 13 * 5 ^ 6 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 31 * 47 := rfl
    rw [h]
    ring
  have hpn : p ^ n ∣
      2 ^ 41 * (3 ^ 13 * (5 ^ 6 * (7 ^ 2 * (11 * (13 * (17 * (19 * (23 * (31 * 47))))))))) := by
    rw [← hdef, ← hn, ← CFSG.Monster.AxisCount.Baby.natCard_Cbar_eq_monsterBabyOrder]
    exact Subgroup.card_subgroup_dvd_card A
  have h241T : 2 ^ 41 ∣ Nat.card T := by
    have hmul : Nat.card T * T.index = CFSG.Open.monsterBabyOrder := by
      rw [← CFSG.Monster.AxisCount.Baby.natCard_Cbar_eq_monsterBabyOrder]
      exact Subgroup.card_mul_index T
    have hTidx : ¬ 2 ∣ T.index := by
      have h := hT.2.2
      rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at h
    have hcop : Nat.Coprime (2 ^ 41) T.index :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hTidx).pow_left 41
    have h : 2 ^ 41 ∣ Nat.card T * T.index := by
      rw [hmul, hdef]
      exact dvd_mul_right _ _
    exact hcop.dvd_of_dvd_mul_right h
  have h241 : 2 ^ 41 ∣ Nat.card (GL (Fin n) (ZMod p)) := h241T.trans hdvd
  have hpM : p ∣
      2 ^ 41 * (3 ^ 13 * (5 ^ 6 * (7 ^ 2 * (11 * (13 * (17 * (19 * (23 * (31 * 47))))))))) :=
    (dvd_pow_self p hn0).trans hpn
  have hfac : ([2 ^ 41, 3 ^ 13, 5 ^ 6, 7 ^ 2, 11, 13, 17, 19, 23, 31, 47] : List ℕ).prod =
      2 ^ 41 * (3 ^ 13 * (5 ^ 6 * (7 ^ 2 * (11 * (13 * (17 * (19 * (23 * (31 * 47))))))))) := rfl
  have hpL : p ∣ ([2 ^ 41, 3 ^ 13, 5 ^ 6, 7 ^ 2, 11, 13, 17, 19, 23, 31, 47] : List ℕ).prod := by
    rw [hfac]
    exact hpM
  obtain ⟨a, ha, hpa⟩ := hp.prime.dvd_prod_iff.1 hpL
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  have hcases : p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 31 ∨
      p = 47 := by
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hpa))
        (by omega)
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow hpa))
        (by omega)
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (hp.dvd_of_dvd_pow hpa))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1
        (hp.dvd_of_dvd_pow hpa)))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hpa)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hpa))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hpa)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hpa))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hpa)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hpa))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hpa))))))))
  have hn6 : n ≤ 6 := by
    by_contra h
    have h7 : p ^ 7 ∣
        2 ^ 41 * (3 ^ 13 * (5 ^ 6 * (7 ^ 2 * (11 * (13 * (17 * (19 * (23 * (31 * 47))))))))) :=
      (pow_dvd_pow p (by omega)).trans hpn
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at h7
  have hn7 : p = 7 → n ≤ 2 := by
    rintro rfl
    by_contra h
    have h3 : 7 ^ 3 ∣
        2 ^ 41 * (3 ^ 13 * (5 ^ 6 * (7 ^ 2 * (11 * (13 * (17 * (19 * (23 * (31 * 47))))))))) :=
      (pow_dvd_pow 7 (by omega)).trans hpn
    norm_num at h3
  have hn1 : p ≠ 5 → p ≠ 7 → n = 1 := by
    intro h5 h7
    by_contra hn1
    have hn2 : 2 ≤ n := by omega
    have h2 : p ^ 2 ∣
        2 ^ 41 * (3 ^ 13 * (5 ^ 6 * (7 ^ 2 * (11 * (13 * (17 * (19 * (23 * (31 * 47))))))))) :=
      (pow_dvd_pow p hn2).trans hpn
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h5 rfl
    · exact h7 rfl
    · norm_num at h2
    · norm_num at h2
    · norm_num at h2
    · norm_num at h2
    · norm_num at h2
    · norm_num at h2
    · norm_num at h2
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · interval_cases n <;> rw [Matrix.card_GL_field] at h241 <;>
      norm_num [ZMod.card, Fin.prod_univ_succ] at h241
  · have hn2 : n ≤ 2 := hn7 rfl
    interval_cases n <;> rw [Matrix.card_GL_field] at h241 <;>
      norm_num [ZMod.card, Fin.prod_univ_succ] at h241
  all_goals
    have hn : n = 1 := hn1 (by norm_num) (by norm_num)
    subst n
    rw [Matrix.card_GL_field] at h241
    norm_num [ZMod.card, Fin.prod_univ_succ] at h241

theorem k105SporAt_B_of_thompsonJ
    (hJ : ∃ T : Subgroup Cbar, IsSylowTwoOf T ⊤ ∧ T ≤ Jbar ∧
      K105In (normalizer (CFSG.Quasithin.thompsonJ T : Set Cbar)) T) :
    K105SporAt .B := by
  obtain ⟨T, hT, hTJ, hJT⟩ := hJ
  obtain ⟨e, -⟩ := pinned_B_explicit_native_isomorphism_simplicity_and_order.2.1
  exact k105SporAt_of_k105In (s := .B) hT
    (k105In_top_of_thompson hT (xbar_mem_quasithinOmegaOneCenter hT hTJ)
      (k105In_centralizer_xbar T hT hTJ) hJT (b_oddLocal hT hTJ))
    (e.trans (MulEquiv.inv' Cbar).symm)

end BK

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
