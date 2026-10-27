module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsFive
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFifteen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFifteenRank
import CFSG.GroupTheory.SquarefreeOrder
import CFSG.LocalAnalysis.UniquenessCase.UC1K462Basic
import CFSG.LocalAnalysis.UniquenessCase.UC22P21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup CFSG.GroupTheory
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Data G} {Ch : Choice2011 G}

theorem Ctx215.le_ncard_conjSetOf (e : Ctx215 D Ch) :
    orderOf e.a ≤ (conjSetOf D.M e.L).ncard := by
  classical
  have haM : e.a ∈ D.M := e.hBM (e.hle e.haB)
  have hmaps : Set.MapsTo (conjugatePower e.a e.L) (Set.Iio (orderOf e.a))
      (conjSetOf D.M e.L) := fun i _ =>
    ⟨e.a ^ i, D.M.pow_mem haM i, rfl⟩
  have hinj : Set.InjOn (conjugatePower e.a e.L) (Set.Iio (orderOf e.a)) :=
    conjugatePower_injOn e.ha_prime e.ha_not_mem
  have h := Set.ncard_le_ncard_of_injOn (conjugatePower e.a e.L) hmaps hinj
  rwa [Set.ncard_Iio_nat] at h

theorem Ctx215.five_le_pRank_of_dvd (e : Ctx215 D Ch) (hZ : Subgroup.center (Bar2 e.L) = ⊥)
    (hr5 : 5 ≤ orderOf e.a) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpL : p ∣ Nat.card (Bar2 e.L)) : 5 ≤ CFSG.Open.pRank p D.M := by
  have hZ' : ¬ p ∣ Nat.card (Subgroup.center (Bar2 e.L)) := by
    rw [hZ, Subgroup.card_bot]
    exact hp.not_dvd_one
  have hrank := ncard_conjSetOf_le_pRank e.hL hp hp2 hZ' hpL
  exact le_trans hr5 (le_trans (Ctx215.le_ncard_conjSetOf e) hrank)

theorem Ctx215.isStronglyPEmbedded_of_dvd (e : Ctx215 D Ch)
    (hσ : UC6S846.SigmaStd D) (hZ : Subgroup.center (Bar2 e.L) = ⊥)
    (hr5 : 5 ≤ orderOf e.a) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpL : p ∣ Nat.card (Bar2 e.L)) : IsStronglyPEmbedded p D.M := by
  have h5 := e.five_le_pRank_of_dvd hZ hr5 hp hp2 hpL
  by_contra hnot
  have h3 := s21_15_pRank_le_three hσ hp hp2 e.hL hnot
  omega

theorem Ctx215.not_dvd_card_bar2 (e : Ctx215 D Ch) (hσ : UC6S846.SigmaStd D)
    (hNM : ¬ Subgroup.normalizer (Subgroup.zpowers e.a : Set G) ≤ D.M)
    (hZ : Subgroup.center (Bar2 e.L) = ⊥) (hr5 : 5 ≤ orderOf e.a) :
    ¬ orderOf e.a ∣ Nat.card (Bar2 e.L) := by
  intro hdvd
  have hsp : IsStronglyPEmbedded (orderOf e.a) D.M :=
    Ctx215.isStronglyPEmbedded_of_dvd e hσ hZ hr5 e.ha_prime e.ha_ne_two hdvd
  have haM : e.a ∈ D.M := e.hBM (e.hle e.haB)
  have hAM : Subgroup.zpowers e.a ≤ D.M := Subgroup.zpowers_le.mpr haM
  have hcard : Nat.card ↥(Subgroup.zpowers e.a) = orderOf e.a := Nat.card_zpowers e.a
  have hAne : Subgroup.zpowers e.a ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(Subgroup.zpowers e.a) = 1 := by rw [hbot, Subgroup.card_bot]
    exact e.ha_prime.ne_one (hcard ▸ h1)
  have hAp : IsPGroup (orderOf e.a) ↥(Subgroup.zpowers e.a) :=
    IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])
  have hU : Subgroup.zpowers e.a ∈ uniqueSet D.M :=
    mem_uniqueSet_of_isStronglyPEmbedded e.ha_prime hsp hAM hAne hAp
  exact hNM (normalizer_le_of_mem_uniqueSet D.maxLocal hU)

theorem Ctx215.isStronglyPEmbedded_three (e : Ctx215 D Ch) (hσ : UC6S846.SigmaStd D)
    (hZ : Subgroup.center (Bar2 e.L) = ⊥) (hr5 : 5 ≤ orderOf e.a)
    (h3 : 3 ∣ Nat.card (Bar2 e.L)) : IsStronglyPEmbedded 3 D.M :=
  Ctx215.isStronglyPEmbedded_of_dvd e hσ hZ hr5 (by norm_num) (by norm_num) h3

theorem Ctx215.odd_n (e : Ctx215 D Ch) (h1930 : H1930 D)
    (hM3 : IsStronglyPEmbedded 3 D.M) : Odd e.n := by
  by_contra hodd
  have hev : Even e.n := Nat.not_odd_iff_even.mp hodd
  have h3eta : 3 ∈ etaSet e.n :=
    ⟨by norm_num, CFSG.LocalAnalysis.UniquenessCase.UCK.UC46.three_dvd_two_pow_sub_one hev⟩
  have h3pi : 3 ∈ piSet e.B0 := by rw [e.hpi]; exact h3eta
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨b, hbo⟩ := exists_prime_orderOf_dvd_card' (G := ↥e.B0) 3 h3pi.2
  have hbG : orderOf (b : G) = 3 := by rw [Subgroup.orderOf_coe, hbo]
  let A₃ : Subgroup G := Subgroup.zpowers (b : G)
  have hA3card : Nat.card ↥A₃ = 3 := by
    change Nat.card ↥(Subgroup.zpowers (b : G)) = 3
    rw [Nat.card_zpowers, hbG]
  have hA3B : A₃ ≤ e.B0 := Subgroup.zpowers_le.mpr b.2
  have hA3M : A₃ ≤ D.M := hA3B.trans e.hBM
  have hA3ne : A₃ ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥A₃ = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  have hA3p : IsPGroup 3 ↥A₃ := IsPGroup.of_card (n := 1) (by rw [hA3card, pow_one])
  have hU : A₃ ∈ uniqueSet D.M :=
    mem_uniqueSet_of_isStronglyPEmbedded (by norm_num) hM3 hA3M hA3ne hA3p
  have hNle : Subgroup.normalizer (A₃ : Set G) ≤ D.M :=
    normalizer_le_of_mem_uniqueSet D.maxLocal hU
  let c₀ : Ctx21 D Ch := { e.toCtx21 with B := e.B0, hB := e.hB0, hle := le_rfl }
  exact (s21_2 D Ch h1930 c₀ A₃ hA3B) hNle

theorem Ctx21.B0_le_normalizer (c : Ctx21 D Ch) (hodd : Odd c.n) :
    c.B0 ≤ Subgroup.normalizer (D.T : Set G) := by
  have hα := c.hα 0 c.n hodd (by simp)
  have hle : c.B0 ≤ oPi (etaSet c.n) c.B0 := by
    refine le_iSup₂_of_le c.B0 ⟨le_rfl, ?_, c.hpi.subset⟩ le_rfl
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.normal_top
  exact hle.trans (by simpa [etaSet] using hα)

theorem Ctx215.a_mem_normalizer (e : Ctx215 D Ch) (hodd : Odd e.n) :
    e.a ∈ Subgroup.normalizer (D.T : Set G) :=
  Ctx21.B0_le_normalizer e.toCtx21 hodd (e.hle e.haB)
