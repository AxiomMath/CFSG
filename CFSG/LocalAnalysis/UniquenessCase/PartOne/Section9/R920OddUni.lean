module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddUniNorm
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddJ1
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddJ1Cent
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddLstar
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddSigPi
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddUniFlag
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddUniKer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

theorem sq_dvd_card_of_lieModel {Λ : Type} [Group Λ] {q f : ℕ}
    (h : (LieModel Λ .PSL 2 q f ∧ 2 ≤ f) ∨ LieModel Λ .PSL 3 q f ∨ LieModel Λ .PSU 3 q f) :
    q ^ 2 ∣ Nat.card Λ := by
  rcases h with ⟨h, hf⟩ | h | h
  · have h1 : q ^ f ∣ ordA 1 (q ^ f) := by
      simpa using CFSG.EvenSmallLie.CatalogOrders.pow_dvd_ordA (n := 2) le_rfl (q ^ f)
    rw [h.card_eq_lieOrd (by norm_num)]
    exact (pow_dvd_pow q hf).trans h1
  · have hf : 1 ≤ f := h.admissible.2.1
    have h1 : (q ^ f) ^ 3 ∣ ordA 2 (q ^ f) := by
      simpa using CFSG.EvenSmallLie.CatalogOrders.pow_dvd_ordA (n := 3) (by norm_num) (q ^ f)
    have h2 : q ^ 2 ∣ (q ^ f) ^ 3 := by
      rw [← pow_mul]
      exact pow_dvd_pow q (by omega)
    rw [h.card_eq_lieOrd (by norm_num)]
    exact h2.trans h1
  · have hf : 1 ≤ f := h.admissible.2.1
    have h1 : (q ^ f) ^ 3 ∣ ordTwistedA 2 (q ^ f) := by
      simpa using
        CFSG.EvenSmallLie.CatalogOrders.pow_dvd_ordTwistedA (n := 3) (by norm_num) (q ^ f)
    have h2 : q ^ 2 ∣ (q ^ f) ^ 3 := by
      rw [← pow_mul]
      exact pow_dvd_pow q (by omega)
    rw [h.card_eq_lieOrd (by norm_num)]
    exact h2.trans h1

variable {G : Type} [Group G] [Finite G]

namespace Slice

variable {D : Data G} {L D₃ Y H : Subgroup G} {q : ℕ}

theorem not_dvd_card_center_barImage_L9_of_lieModel (S : Slice D L D₃ Y H q) {E : Subgroup G}
    (hyp : F09.Hyp91 D Y H E) (hI : F09.I9 H ≤ D.M) (hGA : CFSG.Open.GriessAllModelsStatement)
    {t : StatedLieTag} {n f : ℕ} (ht : t = .PSL ∨ t = .PSU) (hnq : n < q)
    (hmod : LieModel (F09.Lbar9 Y H) t n q f) :
    ¬ q ∣ Nat.card (center ↥(barImage H (F09.L9 Y H))) := by
  intro hdvd
  obtain ⟨e⟩ := S.nonempty_lbar9_mulEquiv hyp hI
  have hd := CFSG.RankThree.PartOne.card_center_dvd_of_model hGA
    (CFSG.Quasithin.A3.isQuasisimple_iff_open.2 (S.isQuasisimple_barImage_L9 hyp hI))
    ((CFSG.Blueprint.LieModel.of_mulEquiv e hmod).statedClassicalModel
      (by rcases ht with rfl | rfl <;> decide))
  have hn : 2 ≤ n := by
    obtain ⟨-, -, hn⟩ := hmod.admissible
    rcases ht with rfl | rfl
    · exact hn.1
    · have := hn.1
      omega
  have hq3 : 3 < q := by have := S.gt; omega
  rcases CFSG.RankThree.PartOne.prime_dvd_table S.prime hq3 (hdvd.trans hd) with
    ⟨-, hqn, -⟩ | ⟨-, hqn, -⟩
  · exact absurd (Nat.le_of_dvd (by omega) hqn) (by omega)
  · exact absurd (Nat.le_of_dvd (by omega) hqn) (by omega)

theorem false_of_lieChar (S : Slice D L D₃ Y H q) (hq : 7 < q)
    (hN : ∀ A : Subgroup G, A ≤ Y → (Nat.card A).Prime → Odd (Nat.card A) →
      normalizer (A : Set G) ≤ D.M)
    {E : Subgroup G} (hyp : F09.Hyp91 D Y H E) (hI : F09.I9 H ≤ D.M)
    (hchev : ∃ f : ℕ, LieModel (F09.Lbar9 Y H) .PSL 2 q f ∨
        (q ^ f % 3 = 2 ∧ LieModel (F09.Lbar9 Y H) .PSL 3 q f) ∨
        (q ^ f % 3 = 1 ∧ LieModel (F09.Lbar9 Y H) .PSU 3 q f))
    (hGA : CFSG.Open.GriessAllModelsStatement) : False := by
  obtain ⟨f, hf⟩ := hchev
  have hq2 : q ≠ 2 := by omega
  have hq3 : q ≠ 3 := by omega
  haveI : Fact q.Prime := ⟨S.prime⟩
  have hmodel : LieModel (F09.Lbar9 Y H) .PSL 2 q f ∨ LieModel (F09.Lbar9 Y H) .PSL 3 q f ∨
      LieModel (F09.Lbar9 Y H) .PSU 3 q f :=
    hf.imp id (Or.imp And.right And.right)
  have hZ : ¬ q ∣ Nat.card (center ↥(barImage H (F09.L9 Y H))) := by
    rcases hmodel with h | h | h
    · exact S.not_dvd_card_center_barImage_L9_of_lieModel hyp hI hGA (Or.inl rfl) (by omega) h
    · exact S.not_dvd_card_center_barImage_L9_of_lieModel hyp hI hGA (Or.inl rfl) (by omega) h
    · exact S.not_dvd_card_center_barImage_L9_of_lieModel hyp hI hGA (Or.inr rfl) (by omega) h
  have hNW := S.normalizer_le_wbar9_of_not_dvd hN hI S.prime hq2
    (S.not_dvd_card_L9_inf_I9_of_center hI S.prime hq2 hZ)
  have hqX : q ∣ Nat.card (Bar2 (Opp 3 Y)) := by
    have h2 := two_mul_card_of_isL2Odd S.prime hq2 S.shape_opp
    exact Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes S.prime Nat.prime_two).2 hq2)
      (h2 ▸ dvd_mul_right q _)
  by_cases hsq : q ^ 2 ∣ Nat.card (F09.Lbar9 Y H)
  · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := xbar9 Y H) q
      (hqX.trans S.card_bar2_opp_dvd_card_xbar9)
    have hA : Nat.card (zpowers (x : F09.Lbar9 Y H)) = q := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
    have hAX : zpowers (x : F09.Lbar9 Y H) ≤ xbar9 Y H := (zpowers_le).mpr x.2
    obtain ⟨Q, hQ, hAQ⟩ := Sylow.exists_subgroup_card_pow_succ (p := q) (n := 1) hsq
      (by rw [hA, pow_one])
    have hQc := (IsPGroup.isMulCommutative_of_card_eq_prime_sq hQ).is_comm.comm
    have hQN : Q ≤ normalizer (zpowers (x : F09.Lbar9 Y H) : Set (F09.Lbar9 Y H)) := fun k hk =>
      Subgroup.mem_normalizer_fintype fun a ha => by
        have hka : k * a = a * k := congrArg Subtype.val (hQc ⟨k, hk⟩ ⟨a, hAQ ha⟩)
        rw [hka, mul_inv_cancel_right]
        exact ha
    obtain ⟨u, -, hu, hns⟩ := exists_mem_orderOf_eq_not_isSolvable_inf S.prime S.gt
      S.isL2Odd_bar2_tbar9 (IsPGroup.of_card hQ)
      ((hQN.trans (hNW _ hAX hA)).trans (S.wbar9_le_normalizer_tbar9 hyp)) (dvd_of_eq hQ.symm)
    haveI := isSolvable_centralizer_of_lieModel S.prime hq3 hmodel hu
    exact hns (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective inf_le_left))
  · have h1 : LieModel (F09.Lbar9 Y H) .PSL 2 q 1 := by
      rcases hf with h | ⟨-, h⟩ | ⟨-, h⟩
      · obtain rfl : f = 1 := by
          have hf1 : 1 ≤ f := h.admissible.2.1
          by_contra hne
          exact hsq (sq_dvd_card_of_lieModel (Or.inl ⟨h, by omega⟩))
        exact h
      · exact absurd (sq_dvd_card_of_lieModel (Or.inr (Or.inl h))) hsq
      · exact absurd (sq_dvd_card_of_lieModel (Or.inr (Or.inr h))) hsq
    have hcard : Nat.card (F09.Lbar9 Y H) = Nat.card (Bar2 (Opp 3 Y)) := by
      rw [h1.card_eq_lieOrd (by norm_num), S.shape_opp.card_eq_lieOrd (by norm_num)]
    have htop : xbar9 Y H = ⊤ := Subgroup.eq_top_of_card_eq _ (Nat.dvd_antisymm
      (Subgroup.card_subgroup_dvd_card _) (by rw [hcard]; exact S.card_bar2_opp_dvd_card_xbar9))
    have hXM : Opp 3 Y ≤ H ⊓ D.M :=
      le_inf ((opp_le 3 Y).trans S.Y_le_H) ((opp_le 3 Y).trans S.Y_le_M)
    have hle : F09.img9 H (Opp 3 Y) ≤ F09.img9 H (H ⊓ D.M) :=
      Subgroup.map_mono fun y hy => hXM hy
    have hXW : xbar9 Y H ≤ wbar9 D Y H := fun z hz =>
      Subgroup.mem_subgroupOf.2 (hle (Subgroup.mem_subgroupOf.1 hz))
    exact S.false_of_wbar9_eq_top hyp hI (top_le_iff.1 (by rw [← htop]; exact hXW))

end Slice

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
