module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

theorem isCyclic_of_pRank_le_one {X : Type} [Group X] [Finite X]
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1) {R : Subgroup X} (hR : IsPGroup 3 R) :
    IsCyclic R := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (IsPGroup 3 R) := ⟨hR⟩
  by_contra hnc
  obtain ⟨E, -, hcard, hel⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hnc
  have hE : CFSG.Open.IsElemAbelian 3 E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).mp hel
  have hE' : CFSG.Open.IsElemAbelian 3 (E.map R.subtype) :=
    CFSG.SectionRank.isElemAbelian_map hE R.subtype
  have hcard' : Nat.card (E.map R.subtype) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective R.subtype_injective, hcard]
  have h2 := CFSG.SectionRank.le_pRank (p := 3) (by norm_num)
    (le_top : E.map R.subtype ≤ ⊤) hE' hcard'
  omega

theorem exists_zpowers_eq {S : Type} [Group S] {P : Subgroup S} [IsCyclic P] :
    ∃ g ∈ P, Subgroup.zpowers g = P := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := P)
  refine ⟨(g : S), g.2, le_antisymm (Subgroup.zpowers_le.mpr g.2) ?_⟩
  intro y hy
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
  exact Subgroup.mem_zpowers_iff.mpr ⟨i, by simpa using congrArg Subtype.val hi⟩

theorem three_pow_dvd_add_one {k : ℕ} {a : ℤ} (h1 : (3 : ℤ) ^ k ∣ (a - 1) * (a + 1))
    (h2 : ¬ (3 : ℤ) ^ k ∣ a - 1) : (3 : ℤ) ^ k ∣ a + 1 := by
  by_cases h3 : (3 : ℤ) ∣ a + 1
  · have h4 : ¬ (3 : ℤ) ∣ a - 1 := by omega
    have hcop : IsCoprime ((3 : ℤ) ^ k) (a - 1) :=
      IsCoprime.pow_left (Int.prime_three.coprime_iff_not_dvd.2 h4)
    exact hcop.dvd_of_dvd_mul_left h1
  · have hcop : IsCoprime ((3 : ℤ) ^ k) (a + 1) :=
      IsCoprime.pow_left (Int.prime_three.coprime_iff_not_dvd.2 h3)
    exact absurd (hcop.dvd_of_dvd_mul_right h1) h2

theorem conj_eq_inv_of_sq_eq {G : Type*} [Group G] {g x : G} {k : ℕ}
    (hord : orderOf g = 3 ^ k) {a : ℤ} (ha : g ^ a = x * g * x⁻¹)
    (h2 : x * (x * g * x⁻¹) * x⁻¹ = g) (hne : x * g * x⁻¹ ≠ g) :
    x * g * x⁻¹ = g⁻¹ := by
  have hsq : g ^ (a * a) = g := by
    calc g ^ (a * a) = (g ^ a) ^ a := zpow_mul g a a
      _ = (x * g * x⁻¹) ^ a := by rw [ha]
      _ = x * g ^ a * x⁻¹ := conj_zpow
      _ = x * (x * g * x⁻¹) * x⁻¹ := by rw [ha]
      _ = g := h2
  have hord' : (orderOf g : ℤ) = 3 ^ k := by rw [hord]; norm_num
  have hdvd1 : (orderOf g : ℤ) ∣ a * a - 1 := by
    rw [orderOf_dvd_iff_zpow_eq_one, zpow_sub, hsq, zpow_one, mul_inv_cancel]
  have hdvd2 : ¬ (3 : ℤ) ^ k ∣ a - 1 := by
    rw [← hord']
    intro hd
    apply hne
    have h1 : g ^ (a - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.mp hd
    rw [zpow_sub, zpow_one, mul_inv_eq_one] at h1
    rw [← ha, h1]
  have hprod : (3 : ℤ) ^ k ∣ (a - 1) * (a + 1) := by
    have e : (a - 1) * (a + 1) = a * a - 1 := by ring
    rw [e, ← hord']
    exact hdvd1
  have hdvd3 : (3 : ℤ) ^ k ∣ a + 1 := three_pow_dvd_add_one hprod hdvd2
  have hg1 : g ^ (a + 1) = 1 :=
    orderOf_dvd_iff_zpow_eq_one.mp (by rw [hord']; exact hdvd3)
  rw [zpow_add_one] at hg1
  rw [← ha]
  exact eq_inv_of_mul_eq_one_left hg1

theorem sq_mem_centralizer {S : Type} [Group S] [Finite S] (H : Subgroup S) [IsCyclic H]
    (hH : IsPGroup 3 H) (hcop : Nat.Coprime 3 H.index) {n : S}
    (hn : n ∈ Subgroup.normalizer (H : Set S)) :
    n ^ 2 ∈ Subgroup.centralizer (H : Set S) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let ψ : Subgroup.normalizer (H : Set S) →* MulAut H := Subgroup.normalizerMonoidHom H
  let C : Subgroup S := Subgroup.centralizer (H : Set S)
  have hker : ψ.ker = C.subgroupOf (Subgroup.normalizer (H : Set S)) :=
    Subgroup.normalizerMonoidHom_ker H
  have hrel : ψ.ker.index = C.relIndex (Subgroup.normalizer (H : Set S)) :=
    congrArg Subgroup.index hker
  have hHC : H ≤ C := Subgroup.le_centralizer H
  have hcop_r : Nat.Coprime ψ.ker.index 3 := by
    rw [hrel]
    refine Nat.Coprime.coprime_dvd_left ?_ hcop.symm
    exact (Subgroup.relIndex_dvd_of_le_left (L := Subgroup.normalizer (H : Set S)) hHC).trans
      (Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer)
  have hr_tot : ψ.ker.index ∣ Nat.totient (Nat.card H) := by
    rw [Subgroup.index_ker, ← IsCyclic.card_mulAut]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hH
  have hr2 : ψ.ker.index ∣ 2 := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hk0, pow_zero] at hk
      rw [hk, Nat.totient_one] at hr_tot
      exact hr_tot.trans (one_dvd 2)
    · rw [hk, Nat.totient_prime_pow Nat.prime_three hk0] at hr_tot
      have hc : Nat.Coprime ψ.ker.index (3 ^ (k - 1)) := Nat.Coprime.pow_right _ hcop_r
      exact hc.dvd_of_dvd_mul_left hr_tot
  have hpow : (⟨n, hn⟩ : Subgroup.normalizer (H : Set S)) ^ ψ.ker.index ∈
      C.subgroupOf (Subgroup.normalizer (H : Set S)) := by
    rw [← hker]
    exact Subgroup.pow_index_mem ψ.ker _
  have hnr : n ^ ψ.ker.index ∈ C := by
    simpa using Subgroup.mem_subgroupOf.mp hpow
  obtain ⟨t, ht⟩ := hr2
  have e : n ^ 2 = (n ^ ψ.ker.index) ^ t := by
    rw [← pow_mul, ← ht]
  rw [e]
  exact Subgroup.pow_mem C hnr t

theorem exists_normalizer_not_centralizer {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (P : Sylow 3 S) [IsCyclic (P : Subgroup S)]
    (hP1 : (P : Subgroup S) ≠ ⊥) :
    ∃ n ∈ Subgroup.normalizer (P : Set S), n ∉ Subgroup.centralizer (P : Set S) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (Sylow 3 S) := P.finite_of_finiteIndex
  by_contra hcon
  push Not at hcon
  have hle : Subgroup.normalizer (P : Set S) ≤ Subgroup.centralizer (P : Set S) :=
    fun n hn => hcon n hn
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hle
  obtain ⟨g, hgP, hgz⟩ := exists_zpowers_eq (P := (P : Subgroup S))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.transferSylow P hle).ker with
    hK | hK
  · have hPtop : (P : Subgroup S) = ⊤ := by
      have h := hcomp.sup_eq_top
      rw [hK, bot_sup_eq] at h
      exact h
    obtain ⟨a, b, hab⟩ := hna
    apply hab
    have ha : a ∈ Subgroup.zpowers g := by rw [hgz, hPtop]; exact Subgroup.mem_top a
    have hb : b ∈ Subgroup.zpowers g := by rw [hgz, hPtop]; exact Subgroup.mem_top b
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow_self g i j).eq
  · have h := hcomp.disjoint
    rw [hK, top_disjoint] at h
    exact hP1 h

theorem exists_inv_of_pRank_one {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup S) = 1)
    {b : S} (hb : orderOf b = 3) : ∃ t : S, t * b * t⁻¹ = b⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbP : IsPGroup 3 (Subgroup.zpowers b) :=
    IsPGroup.of_card (show Nat.card (Subgroup.zpowers b) = 3 ^ 1 by
      rw [Nat.card_zpowers, hb, pow_one])
  obtain ⟨P, hble⟩ := hbP.exists_le_sylow
  have hcyc : IsCyclic (P : Subgroup S) := isCyclic_of_pRank_le_one hrk.le P.isPGroup'
  haveI := hcyc
  have hbP' : b ∈ (P : Subgroup S) := hble (Subgroup.mem_zpowers b)
  have hP1 : (P : Subgroup S) ≠ ⊥ := by
    intro h
    have hb1 : b = 1 := Subgroup.mem_bot.mp (h ▸ hbP')
    rw [hb1, orderOf_one] at hb
    norm_num at hb
  obtain ⟨n, hnN, hnC⟩ := exists_normalizer_not_centralizer hna P hP1
  obtain ⟨g, hgP, hgz⟩ := exists_zpowers_eq (P := (P : Subgroup S))
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp P.isPGroup'
  have hord : orderOf g = 3 ^ k := by
    rw [← Nat.card_zpowers, hgz]
    exact hk
  have hcop : Nat.Coprime 3 (P : Subgroup S).index :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 P.not_dvd_index
  have hsq : n ^ 2 ∈ Subgroup.centralizer (P : Set S) :=
    sq_mem_centralizer (P : Subgroup S) P.isPGroup' hcop hnN
  have hng : n * g * n⁻¹ ∈ (P : Subgroup S) :=
    (Subgroup.mem_normalizer_iff.mp hnN g).mp hgP
  obtain ⟨a, ha⟩ : ∃ a : ℤ, g ^ a = n * g * n⁻¹ := by
    rw [← hgz] at hng
    exact Subgroup.mem_zpowers_iff.mp hng
  have hne : n * g * n⁻¹ ≠ g := by
    intro h
    apply hnC
    have hcomm : Commute g n := by
      show g * n = n * g
      calc g * n = (n * g * n⁻¹) * n := by rw [h]
        _ = n * g := inv_mul_cancel_right (n * g) n
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y ∈ Subgroup.zpowers g := by rw [hgz]; exact hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
    exact (Commute.zpow_left hcomm i).eq
  have hsq2 : n * (n * g * n⁻¹) * n⁻¹ = g := by
    have hc : g * n ^ 2 = n ^ 2 * g := Subgroup.mem_centralizer_iff.mp hsq g hgP
    calc n * (n * g * n⁻¹) * n⁻¹ = n ^ 2 * g * (n ^ 2)⁻¹ := by rw [pow_two]; group
      _ = g := by rw [← hc, mul_inv_cancel_right]
  have hconj : n * g * n⁻¹ = g⁻¹ := conj_eq_inv_of_sq_eq hord ha hsq2 hne
  have hbg : b ∈ Subgroup.zpowers g := by rw [hgz]; exact hbP'
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hbg
  refine ⟨n, ?_⟩
  rw [← hi, ← conj_zpow, hconj, inv_zpow]

end CFSG.RankThree.PartTwo.Sec4.RonanK432
