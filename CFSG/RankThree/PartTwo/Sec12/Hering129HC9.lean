module

public import CFSG.RankThree.PartTwo.Sec12.Item128Bar125

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item125BarC9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec12StdBar G A c L →
    (Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22) →
    ∀ E : Subgroup G, Late.IsE27 E → E ≤ lcBar c L → c ∈ E →
      Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 9 →
      Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)

theorem item125BarC9_of (h45 : Sec4.Item4_5) (hK2 : KFacts.KS12NormalizerMoves)
    (hK9 : KFacts.KS12OrderNine) (hG1 : Gap125NonCentralBar) : Item125BarC9 := by
  intro G _ _ A c L h hty E hE hEL hcE hB9
  have hL := h.mem_thetaComponentsAt
  have hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3 := by
    rcases hty with hSL | hA6 | hA7 | hM22
    · exact card_center_eq_three_of_isSLThreePi hSL
    · exact hA6.1
    · exact hA7.1
    · exact hM22.1
  have hcEL : c ∈ E ⊓ L := ⟨hcE, h.mem_L⟩
  have hdvd : ∀ S : Subgroup G, S ≤ E → Nat.card S ∣ 3 ^ 3 := fun S hS => by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE.2]
    exact Subgroup.card_dvd_of_le hS
  obtain ⟨j, hj3, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (hdvd (E ⊓ L) inf_le_left)
  interval_cases j
  · rw [pow_zero, Subgroup.card_eq_one] at hj
    exact absurd (hj ▸ hcEL) (by simpa using h.ne_one)
  · exact (false_of_card_inf_L_eq_three hK9 h.partTwoF_eq hL h.mem_L h.ne_one hty hE hEL hcE
      hB9 (by rw [hj, pow_one])).elim
  · have hEL9 : Nat.card (E ⊓ L : Subgroup G) = 9 := by
      rw [hj]
      norm_num
    by_contra hU
    obtain ⟨P, hP, hPB⟩ := hG1 G A c L h hty E hE hEL hcE hB9 hEL9 hU
    have hbar : Sec12StdBar G E c L :=
      { toPartTwoStanding := h.toPartTwoStanding
        partTwoF_eq := h.partTwoF_eq
        isE27 := hE
        mem_A := hcE
        ne_one := h.ne_one
        mem_thetaComponentsAt := hL
        mem_L := h.mem_L
        card_B := hB9
        sup_eq := sup_eq_of_card_inf_nine hE hZ hB9 hEL9
        exists_sylow := ⟨P, hP, hPB⟩ }
    exact hU (normalizer_le_of_sec12StdBar_of_list h45 hK2 hbar hty)
  · exfalso
    have hEL' : E ⊓ L = E := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hj, hE.2]; norm_num)
    have hB3 : IsPGroup 3 (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) := fun x =>
      ⟨1, Subtype.ext (by simpa using hE.1.2 x x.2.1)⟩
    have h1 := card_inf_le_card_center_of_le_thetaQuotCentralizer hB3 inf_le_right (L := L)
    have h2 : E ⊓ Sec4.thetaQuotCentralizer L ⊓ L = E ⊓ Sec4.thetaQuotCentralizer L :=
      inf_eq_left.mpr (inf_le_left.trans (hEL' ▸ inf_le_right))
    rw [h2, hB9, hZ] at h1
    norm_num at h1

end CFSG.RankThree.PartTwo.Sec12
