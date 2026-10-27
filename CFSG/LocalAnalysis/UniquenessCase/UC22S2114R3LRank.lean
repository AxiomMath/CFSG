module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20x
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Center
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Rank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.S15 (rkLin rkSp rkOmMinus eS)
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114r3l_card_center_eq_one (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {f : ℕ}
    (hf : LieModel (BarInf L) .PSL 4 2 f ∨ LieModel (BarInf L) .PSp 3 2 f ∨
      IsOmega8m (BarInf L) f) :
    Nat.card (center (Bar2 L)) = 1 := by
  refine Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 3
    (Nat.coprime_two_right.2 (uc22p20p_odd_center_bar2 ↥L))) ?_
  have key : ∀ {t : StatedLieTag} {n : ℕ}, LieModel (BarInf L) t n 2 f →
      t ∈ CFSG.Blueprint.classicalTags →
      (genericOrders t n 2 f).1 * (genericOrders t n 2 f).2 * ((exceptionalOrders t n 2 f).1 *
        (exceptionalOrders t n 2 f).2) ∣ 2 ^ 3 → Nat.card (center (Bar2 L)) ∣ 2 ^ 3 :=
    fun hX ht hP => (card_center_bar2_dvd_of_row hL (Nat.pos_of_dvd_of_pos hP (by norm_num))
      (griessRow_of_lieModel_classical hGA hX ht)).trans hP
  have h8 : ∀ a b c d : ℕ, a ∣ 4 → b = 1 → c * d ∣ 2 → a * b * (c * d) ∣ 2 ^ 3 :=
    fun a b c d ha hb hcd => by
      subst hb
      exact (Nat.mul_dvd_mul (Nat.mul_dvd_mul ha (dvd_refl 1)) hcd).trans (by norm_num)
  rcases hf with hX | hX | hX
  · refine key hX (by decide) (h8 _ _ _ _ (Nat.gcd_dvd_left 4 _) rfl ?_)
    rcases f with _ | _ | f
    · decide
    · decide
    · show (1 : ℕ) * 1 ∣ 2
      norm_num
  · refine key hX (by decide)
      (h8 _ _ _ _ ((Nat.gcd_dvd_left 2 _).trans (by norm_num)) rfl ?_)
    rcases f with _ | _ | f
    · decide
    · decide
    · show (1 : ℕ) * 1 ∣ 2
      norm_num
  · have hX' : LieModel (BarInf L) .POmegaMinus 4 2 f := hX
    refine key hX' (by decide) (h8 _ _ _ _ (Nat.gcd_dvd_left 4 _) rfl ?_)
    show (1 : ℕ) * 1 ∣ 2
    norm_num

theorem uc22s2114r3l_nonempty_mulEquiv_alt_eight (hGA : GriessAllModelsStatement)
    {M L : Subgroup G} (hL : L ∈ calC M) (hX : LieModel (BarInf L) .PSL 4 2 1) :
    Nonempty (Bar2 L ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_center_bot hL.2.2
    (Subgroup.card_eq_one.1 (uc22s2114r3l_card_center_eq_one hGA hL (Or.inl hX)))
  obtain ⟨eA⟩ := CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel hX
  exact ⟨e.symm.trans eA⟩

section Rank


theorem uc22s2114r3l_pRank_eq_rkLin (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {f : ℕ} (hf : 2 ≤ f) (hX : LieModel (BarInf L) .PSL 4 2 f) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p L = rkLin 4 true (2 ^ f) p (Nat.card (center (Bar2 L))) := by
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
  rw [← pRank_bar2_eq_of_odd hp hp2]
  have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨q, hv, hqp, hqc, ⟨e'⟩⟩ := uc22p20w_index_psl
    (LieModel.statedClassicalModel (LieModel.of_mulEquiv e hX) (by decide))
    (by rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩) <;> omega)
  rw [uc22p20x_lieOddRankChev hGA (Bar2 L) hL.2.2 ⟨.A (4 - 1) q, hv⟩ hqp ⟨e'⟩ p hp hp2]
  show rkLin 4 true q.card p _ = _
  rw [hqc]

theorem uc22s2114r3l_pRank_eq_rkSp (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {f : ℕ} (hX : LieModel (BarInf L) .PSp 3 2 f) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : CFSG.Open.pRank p L = rkSp 3 (2 ^ f) p := by
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
  rw [← pRank_bar2_eq_of_odd hp hp2]
  exact uc22p20w_pRank_psp (uc22p20x_lieOddRankChev hGA) hL.2.2
    (LieModel.statedClassicalModel (LieModel.of_mulEquiv e hX) (by decide)) hp hp2

theorem uc22s2114r3l_pRank_eq_rkOmMinus (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {f : ℕ} (hX : IsOmega8m (BarInf L) f) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : CFSG.Open.pRank p L = rkOmMinus 4 (2 ^ f) p := by
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hX' : LieModel (BarInf L) .POmegaMinus 4 2 f := hX
  rw [← pRank_bar2_eq_of_odd hp hp2]
  exact uc22p20w_pRank_pomegaMinus (uc22p20x_lieOddRankChev hGA) hL.2.2
    (LieModel.statedClassicalModel (LieModel.of_mulEquiv e hX') (by decide)) hp hp2

theorem uc22s2114r3l_three_le_pRank_three (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {f : ℕ}
    (hf : (LieModel (BarInf L) .PSL 4 2 f ∧ Even f) ∨ LieModel (BarInf L) .PSp 3 2 f ∨
      IsOmega8m (BarInf L) f) :
    3 ≤ CFSG.Open.pRank 3 L := by
  rcases hf with ⟨hX, hev⟩ | hX | hX
  · have hf2 : 2 ≤ f := by
      have := (LieModel.admissible hX).2.1
      obtain ⟨k, hk⟩ := hev
      omega
    have h1 := uc22s2114r3l_pRank_eq_rkLin hGA hL hf2 hX Nat.prime_three (by norm_num)
    have h2 := uc22p20v_rkLin_true_one_of_not_dvd (m := 4) (z := Nat.card (center (Bar2 L)))
      (by rw [uc22p20v_eP_three, if_pos hev]) (by norm_num)
    omega
  · have h1 := uc22s2114r3l_pRank_eq_rkSp hGA hL hX Nat.prime_three (by norm_num)
    have h2 := uc22p20v_rkSp_of_eS (l := 3) (uc22p20v_eS_three f)
    omega
  · have h1 := uc22s2114r3l_pRank_eq_rkOmMinus hGA hL hX Nat.prime_three (by norm_num)
    have h2 := uc22p20v_rkOmMinus_ge (l := 4) (uc22p20v_eS_three f)
    omega

theorem uc22s2114r3l_two_le_pRank_three (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {f : ℕ}
    (hf : LieModel (BarInf L) .PSL 4 2 f ∨ LieModel (BarInf L) .PSp 3 2 f ∨
      IsOmega8m (BarInf L) f) :
    2 ≤ CFSG.Open.pRank 3 L := by
  rcases hf with hX | hX | hX
  · rcases (show f = 1 ∨ 2 ≤ f by have := (LieModel.admissible hX).2.1; omega) with rfl | hf2
    · obtain ⟨e⟩ := uc22s2114r3l_nonempty_mulEquiv_alt_eight hGA hL hX
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      rw [← pRank_bar2_eq_of_odd Nat.prime_three (by norm_num)]
      refine CFSG.Quasithin.H13.Ch4.T425C27.two_le_pRank_of_surjective (K := ⊤)
        (e.toMonoidHom.comp (Subgroup.topEquiv (G := Bar2 L)).toMonoidHom) (fun y => ?_)
        (by norm_num) CFSG.Quasithin.H13.Rank8.two_le_pRank_alternating_eight
      exact ⟨⟨e.symm y, Subgroup.mem_top _⟩, by simp⟩
    · rw [uc22s2114r3l_pRank_eq_rkLin hGA hL hf2 hX Nat.prime_three (by norm_num)]
      exact uc22p20v_two_le_rkLin_four_true (uc22p20v_eP_three_cases f)
  · have := uc22s2114r3l_three_le_pRank_three hGA hL (Or.inr (Or.inl hX))
    omega
  · have := uc22s2114r3l_three_le_pRank_three hGA hL (Or.inr (Or.inr hX))
    omega

theorem uc22s2114r3l_three_le_pRank (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {f : ℕ}
    (hf : LieModel (BarInf L) .PSL 4 2 f ∨ LieModel (BarInf L) .PSp 3 2 f ∨
      IsOmega8m (BarInf L) f) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrq : r ∣ 2 ^ f - 1) :
    3 ≤ CFSG.Open.pRank r L := by
  have heS : eS (2 ^ f) r = 1 := by
    unfold eS
    rw [uc22p20v_cast_eq_one hrq, one_pow, orderOf_one]
  rcases hf with hX | hX | hX
  · have hf2 : 2 ≤ f := by
      by_contra h
      have h1 := (LieModel.admissible hX).2.1
      obtain rfl : f = 1 := by omega
      exact hr.one_lt.ne' (Nat.dvd_one.1 hrq)
    have h1 := uc22s2114r3l_pRank_eq_rkLin hGA hL hf2 hX hr hr2
    have hr4 : ¬ r ∣ 4 := fun h => hr2
      ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow (show r ∣ 2 ^ 2 from h)))
    have h2 := uc22p20v_rkLin_true_one_of_not_dvd (m := 4) (z := Nat.card (center (Bar2 L)))
      (uc22p20v_eP_of_dvd hrq) hr4
    omega
  · have h1 := uc22s2114r3l_pRank_eq_rkSp hGA hL hX hr hr2
    have h2 := uc22p20v_rkSp_of_eS (l := 3) heS
    omega
  · have h1 := uc22s2114r3l_pRank_eq_rkOmMinus hGA hL hX hr hr2
    have h2 := uc22p20v_rkOmMinus_ge (l := 4) heS
    omega

end Rank

end CFSG.LocalAnalysis.UniquenessCase.UC22
