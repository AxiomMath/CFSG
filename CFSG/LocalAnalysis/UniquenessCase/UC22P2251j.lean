module

import CFSG.LocalAnalysis.UniquenessCase.UC22P22rs
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ui
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1
import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Alt
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

namespace P2251j

theorem le_of_calNOf {M X H : Subgroup G} (hN : calNOf X = {M}) (hXH : X ≤ H) (hH : H ≠ ⊤) : H ≤ M := by
  rcases eq_top_or_exists_le_coatom H with h | ⟨N, hN', hHN⟩
  · exact absurd h hH
  · have hmem : N ∈ calNOf X := ⟨hN', hXH.trans hHN⟩
    rw [hN, Set.mem_singleton_iff] at hmem
    exact hmem ▸ hHN

theorem calMOf_eq_of_card (D : Data G) (Ch : Choice2011 G) (h211 : S21_1 D Ch) (hH : H1930 D) (c : Ctx21 D Ch)
    {X : Subgroup G} {r a : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hXr : Nat.card X = r)
    (hcard : Nat.card ↥(X ⊔ D.T) = 2 ^ a * r) (hXU : X ∈ uniqueSet D.M) : calMOf (X ⊔ D.T) = {D.M} := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hsol : IsSolvable ↥(X ⊔ D.T) := by
    haveI := Fintype.ofFinite ↥(X ⊔ D.T)
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := a) (b := 1)
      Nat.prime_two hr (Ne.symm hr2) (by rw [← Nat.card_eq_fintype_card, hcard, pow_one])
  have hhall : IsHallOddIn X (X ⊔ D.T) := by
    refine ⟨le_sup_left, by rw [hXr]; exact hr.odd_of_ne_two hr2, a, ?_⟩
    have h1 := relIndex_mul_card X (X ⊔ D.T)
    rw [inf_eq_left.2 (le_sup_left : X ≤ X ⊔ D.T), hcard, hXr] at h1
    exact Nat.eq_of_mul_eq_mul_right hr.pos h1
  have hrank : ∀ q ∈ piSet (X ⊔ D.T), q ≠ 2 → CFSG.Open.pRank q (X ⊔ D.T) ≤ 2 := by
    intro q hq hq2
    obtain ⟨hqp, hqd⟩ := hq
    rw [hcard] at hqd
    have hqr : q = r := by
      rcases (Nat.Prime.dvd_mul hqp).1 hqd with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).1 (hqp.dvd_of_dvd_pow h)) hq2
      · exact (Nat.prime_dvd_prime_iff_eq hqp hr).1 h
    rw [hqr]
    refine CFSG.SectionRank.pRank_le hr.one_lt fun F hF hFel => ?_
    obtain ⟨j, hj⟩ := (PartTwo.isPGroup_of_isElemAbelian hr hFel).exists_card_eq
    have h1 : Nat.card F ∣ 2 ^ a * r := by
      rw [← hcard]
      exact card_dvd_of_le hF
    have h2 : Nat.Coprime (Nat.card F) (2 ^ a) := by
      rw [hj]
      exact Nat.Coprime.pow j a ((Nat.coprime_primes hr Nat.prime_two).2 hr2)
    exact (Nat.le_of_dvd hr.pos (h2.dvd_of_dvd_mul_left h1)).trans (Nat.le_self_pow (by norm_num) r)
  haveI : IsCyclic X := isCyclic_of_prime_card hXr
  exact (h211 hH c X (by rw [hXr]; exact hr) (by rw [hXr]; exact hr2) hsol ⟨X, hhall, inferInstance⟩ hrank
    hXU).1

end P2251j

theorem uc22p2251j_sylow_mem (D : Data G) (hk : D.k = 1) {K : Subgroup G} (hKM : K ≤ D.M)
    (h3 : 3 ∣ Nat.card (Bar2 K)) {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P K) :
    P ∈ uniqueSet D.M := by
  refine uc22p22r_mem_uniqueSet_of_sp D Nat.prime_three (uc22p2251h_isStronglyPEmbedded D hk)
    (hP.le.trans hKM) hP.isPGroup fun hP1 => ?_
  have hf := Nat.Prime.factorization_pos_of_dvd Nat.prime_three (Nat.card_pos (α := ↥K)).ne'
    (h3.trans (card_quotient_dvd_card _))
  have hc := hP.card_eq
  rw [hP1, card_bot] at hc
  have h3le := Nat.le_self_pow hf.ne' 3
  omega

theorem uc22p2251j_uniqueMax (D : Data G) (Ch : Choice2011 G) (h211 : S21_1 D Ch) (hH : H1930 D)
    (c : Ctx21 D Ch) (hk : D.k = 1) {K : Subgroup G} (hKM : K ≤ D.M) (hKN : D.M ≤ normalizer (K : Set G))
    (e : Bar2 K ≃* alternatingGroup (Fin 5)) : UniqueMax D.M (K ⊔ D.T) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨X, hXB, hX3, hXS, hsup⟩ := CFSG.Quasithin.FA5.exists_cartan_three (L := K) (S := D.T)
    (CFSG.ABGLocalTools.isSylowOf_iff.1 (D.sylowM.inf_of_le_normalizer hKM hKN)) e
  have hBK := CFSG.Quasithin.F1.borelOf_le K D.T
  have hBN := CFSG.Quasithin.F1.borelOf_le_normalizer K D.T
  have hSB := CFSG.Quasithin.F1.sylow_le_borelOf K D.T
  have hTB := CFSG.Quasithin.F1.le_normalizer_borelOf (D.sylowM.le.trans hKN)
  generalize CFSG.Quasithin.borelOf K D.T = B at hXB hsup hBK hBN hSB hTB
  have hcardB : Nat.card B = Nat.card ↥(D.T ⊓ K) * 3 := by
    rw [← hsup, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer (D.T ⊓ K) X
      (hXB.trans hBN) (disjoint_iff.2 (by rw [inf_comm]; exact hXS)), hX3]
  have hBT : B ⊓ D.T = D.T ⊓ K :=
    le_antisymm (le_inf inf_le_right (inf_le_left.trans hBK)) (le_inf hSB inf_le_left)
  have h1 := relIndex_mul_card B D.T
  have h2 := relIndex_mul_card B (D.T ⊔ B)
  rw [hBT] at h1
  rw [inf_eq_left.2 (le_sup_right : B ≤ D.T ⊔ B), CFSG.Quasithin.F1.relIndex_sup_eq_of_le_normalizer hTB,
    hcardB] at h2
  have hXT : X ⊔ D.T = D.T ⊔ B :=
    le_antisymm (sup_le (hXB.trans le_sup_right) le_sup_left)
      (sup_le le_sup_right (hsup.symm.le.trans (sup_le (inf_le_left.trans le_sup_right) le_sup_left)))
  obtain ⟨a, ha⟩ := D.sylowM.isPGroup.exists_card_eq
  have hcard : Nat.card ↥(X ⊔ D.T) = 2 ^ a * 3 := by
    rw [hXT, ← h2, ← ha, ← h1]
    ring
  have hXK : X ≤ K := hXB.trans hBK
  have hX1 : X ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hX3
    omega
  have hXU := uc22p22r_mem_uniqueSet_of_sp D Nat.prime_three (uc22p2251h_isStronglyPEmbedded D hk)
    (hXK.trans hKM) (IsPGroup.of_card (n := 1) (by rw [hX3, pow_one])) hX1
  exact uc22p22u_uniqueMax_mono D (sup_le_sup_right hXK D.T) (sup_le hKM D.sylowM.le)
    (P2251j.calMOf_eq_of_card D Ch h211 hH c Nat.prime_three (by norm_num) hX3 hcard hXU)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
