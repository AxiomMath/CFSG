module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P21e
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rs
import CFSG.LocalAnalysis.UniquenessCase.UC6K42h
import CFSG.RankThree.PartTwo.Sec18.Item182
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rq

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22ine229_s21_1Hyp {D : Data G} {X : Subgroup G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hXr : Nat.card X = r) (hXT : X ≤ normalizer (D.T : Set G)) (hXU : X ∈ uniqueSet D.M) :
    S21_1Hyp D X := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hT := D.sylowM.isPGroup
  obtain ⟨k, hk⟩ := hT.exists_card_eq
  have hcard : Nat.card ↥(X ⊔ D.T) = 2 ^ k * r := by
    rw [sup_comm, UC6.card_sup_uc6 hr hr2 hXr hT hXT, hk, hXr]
  haveI : IsCyclic ↥X := isCyclic_of_prime_card hXr
  refine ⟨hXr ▸ hr, hXr ▸ hr2,
    CFSG.RankThree.PartTwo.Sec18.isSolvable_sup_of_le_normalizer IsCyclic.isMulCommutative hT hXT,
    ⟨X, ⟨le_sup_left, hXr ▸ hr.odd_of_ne_two hr2, k, ?_⟩, IsCyclic.isMulCommutative⟩, ?_, hXU⟩
  · have h := uc22p22r_card_eq_mul_index (le_sup_left : X ≤ X ⊔ D.T)
    rw [hcard, hXr, mul_comm] at h
    exact (Nat.eq_of_mul_eq_mul_left hr.pos h).symm
  · intro p hp hp2
    haveI : Fact p.Prime := ⟨hp.1⟩
    have hcop : Nat.Coprime p (2 ^ k) :=
      Nat.Coprime.pow_right k ((Nat.coprime_primes hp.1 Nat.prime_two).2 hp2)
    refine (CFSG.SectionRank.pRank_le (k := 1) hp.1.one_lt fun E hEY hE => ?_).trans one_le_two
    obtain ⟨j, hj⟩ := hE.isPGroup.exists_card_eq
    have hdvd : p ^ j ∣ r := by
      have h := Subgroup.card_dvd_of_le hEY
      rw [hj, hcard] at h
      exact (hcop.pow_left j).dvd_of_dvd_mul_left h
    rw [hj, pow_one]
    rcases (Nat.dvd_prime hr).1 hdvd with h1 | h1
    · rw [h1]; exact hp.1.one_lt.le
    · rw [h1, ((Nat.Prime.pow_eq_iff hr).1 h1).1]

theorem uc22ine229_not_sp_of_le_normalizer {D : Data G} {Ch : Choice2011 G} (h211 : S21_1 D Ch)
    (h1930 : H1930 D) (c : Ctx21 D Ch) {X : Subgroup G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hXr : Nat.card X = r) (hXT : X ≤ normalizer (D.T : Set G)) :
    ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M := by
  intro hsp
  have hXp : IsPGroup r X := IsPGroup.of_card (n := 1) (by rw [hXr, pow_one])
  have hX1 : X ≠ ⊥ := fun h => hr.one_lt.ne' (by rw [← hXr, h, Subgroup.card_bot])
  have hXU := uc22p22r_mem_uniqueSet_of_sp D hr hsp (hXT.trans D.normalizer_le) hXp hX1
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := uc22ine229_s21_1Hyp hr hr2 hXr hXT hXU
  exact (h211 h1930 c X h1 h2 h3 h4 h5 h6).2 hXT

theorem uc22ine229_not_sp_of_mem_normalizer {D : Data G} {Ch : Choice2011 G} (h211 : S21_1 D Ch)
    (h1930 : H1930 D) (c : Ctx21 D Ch) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {x : G}
    (hxT : x ∈ normalizer (D.T : Set G)) (hxo : orderOf x = r) :
    ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M :=
  uc22ine229_not_sp_of_le_normalizer h211 h1930 c hr hr2 (by rw [Nat.card_zpowers, hxo])
    (zpowers_le.2 hxT)

theorem uc22ine229_not_mem_sig_of_mem_normalizer {D : Data G} {Ch : Choice2011 G}
    (h211 : S21_1 D Ch) (hSg : UC6S846.SigmaStd D) (hns : ¬ Group.IsSolvable ↥D.M)
    (h1930 : H1930 D) (c : Ctx21 D Ch) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {x : G}
    (hxT : x ∈ normalizer (D.T : Set G)) (hxo : orderOf x = r) : r ∉ D.sig := fun hrs =>
  uc22ine229_not_sp_of_mem_normalizer h211 h1930 c hr hr2 hxT hxo
    (UC6S846.sp_of_mem_sig hSg hns hrs)

end CFSG.LocalAnalysis.UniquenessCase.UC22
