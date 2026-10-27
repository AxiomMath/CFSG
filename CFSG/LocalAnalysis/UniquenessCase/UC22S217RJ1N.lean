module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920J1Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
import CFSG.LocalAnalysis.UniquenessCase.UC22S217VJ1
import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.JankoOne
import CFSG.GroupTheory.CoprimeSupPCore
import CFSG.RankThree.PartTwo.Sec17.Item17Res3ProofMeet

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22s217rj_normalizer_le (D : Data G) (h920 : PartOne.Section9.R920J1 D)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hJ1 : IsJ1 (Bar2 L)) {D₃ : Subgroup G}
    (hD₃L : D₃ ≤ L) (hD₃ : Nat.card D₃ = 3) (hD₃U : D₃ ∈ uniqueSet D.M) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) {Z : Subgroup G} (hZr : IsPGroup r Z) (hZ1 : Z ≠ ⊥)
    (hZM : Z ≤ D.M) (hZL : ⁅Z, L⁆ ≤ pCoreOf 2 L) : normalizer (Z : Set G) ≤ D.M := by
  by_contra hHM
  have hYL : L ⊓ centralizer (Z : Set G) ≤ L := inf_le_left
  have hsup : L = (L ⊓ centralizer (Z : Set G)) ⊔ pCoreOf 2 L :=
    (CFSG.GroupTheory.inf_centralizer_sup_pCoreOf_eq_of_commutator_le hr hr2 hZr hZL).symm
  have hHt : normalizer (Z : Set G) ≠ ⊤ := by
    intro htop
    haveI : IsSimpleGroup G := D.standing.simple
    haveI : Z.Normal := Subgroup.normalizer_eq_top_iff.1 htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Z with h | h
    · exact hZ1 h
    · rw [h] at hZM
      exact hHM (le_top.trans hZM)
  have hc : PartTwo.Hyp919c D L D₃ (L ⊓ centralizer (Z : Set G)) (normalizer (Z : Set G)) := by
    refine ⟨hL, hD₃L, hD₃, hD₃U, hYL.trans hL.1.le, ?_, ?_, ⟨0, ?_⟩, hHt,
      (inf_le_right : L ⊓ centralizer (Z : Set G) ≤ centralizer (Z : Set G)).trans
        (Subgroup.centralizer_le_normalizer _), hHM⟩
    · rw [inf_eq_right.mpr hYL]
      exact hsup
    · rw [inf_eq_right.mpr hYL, Subgroup.subgroupOf_self]
      exact inferInstance
    · rw [inf_eq_right.mpr hYL, Subgroup.subgroupOf_self, Subgroup.index_top, pow_zero]
  obtain ⟨e⟩ :=
    CFSG.RankThree.PartTwo.Sec17.Proof17Res3.nonempty_quotient_pCore_two_equiv hYL hsup
  obtain ⟨φ⟩ := hJ1
  exact h920 L D₃ _ _ hc hYL ⟨e.symm.trans φ⟩

theorem uc22s217rj_normalizer_le_of_ne (D : Data G) (h8107 : F08.R8107 D)
    (h920 : PartOne.Section9.R920J1 D) {L K : Subgroup G} (hL : L ∈ calC D.M)
    (hK : K ∈ calC D.M) (hLK : L ≠ K) (hJL : IsJ1 (Bar2 L)) (hJK : IsJ1 (Bar2 K)) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) {Z : Subgroup G} (hZr : IsPGroup r Z) (hZ1 : Z ≠ ⊥)
    (hZM : Z ≤ D.M) (hZL : ⁅Z, L⁆ ≤ pCoreOf 2 L) : normalizer (Z : Set G) ≤ D.M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3L : 3 ∣ Nat.card L :=
    (show 3 ∣ Nat.card (Bar2 L) by rw [(kJ1_holds _ hJL).1]; norm_num).trans
      (Subgroup.card_quotient_dvd_card _)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3 h3L
  have hD₃ : Nat.card (zpowers (x : G)) = 3 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  exact uc22s217rj_normalizer_le D h920 hL hJL (zpowers_le.2 x.2) hD₃
    (uc22s217v_mem_uniqueSet D h8107 hL hK hLK hJL hJK (zpowers_le.2 x.2) hD₃) hr hr2 hZr hZ1
    hZM hZL

theorem uc22s217rj_false_of_commutator_le (D : Data G) (Ch : Choice2011 G)
    (h8107 : F08.R8107 D) (h920 : PartOne.Section9.R920J1 D) (hH : H1930 D) (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hnN : ¬ (L.subgroupOf D.M).Normal)
    (hJ1 : IsJ1 (Bar2 L)) {b : G} (hb : b ∈ c.B0) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hbr : orderOf b = r) (hbL : ⁅zpowers b, L⁆ ≤ pCoreOf 2 L) : False := by
  let c₀ : Ctx21 D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  obtain ⟨K, hK, hKL⟩ := uc22s217v_exists_ne hL hnN
  exact s21_2 D Ch hH c₀ (zpowers b) (zpowers_le.2 hb)
    (uc22s217rj_normalizer_le_of_ne D h8107 h920 hL (uc22p2214_calC_of_mem_conjSetOf hL hK)
      hKL.symm hJ1 (uc22s217v_isJ1_of_mem hJ1 hK) hr hr2
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbr, pow_one]))
      (zpowers_ne_bot.2 fun h => by rw [h, orderOf_one] at hbr; exact hr.one_lt.ne hbr)
      (zpowers_le.2 (c.hBM hb)) hbL)

end CFSG.LocalAnalysis.UniquenessCase.UC22
