module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R1613gCount
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7Proof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SixteenOrd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NatRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

theorem r1613g_not_nontrivial_quot_center {Q : Type*} [Group Q] (hc : ∀ a b : Q, a * b = b * a) :
    ¬ Nontrivial (Q ⧸ Subgroup.center Q) := by
  intro hn
  obtain ⟨a, b, hab⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [QuotientGroup.eq]
  exact Subgroup.mem_center_iff.2 fun g => hc _ _

theorem r1613g_not_isQuasisimple_of_comm {Q : Type*} [Group Q] (hc : ∀ a b : Q, a * b = b * a) :
    ¬ CFSG.Open.IsQuasisimple Q := fun h =>
  r1613g_not_nontrivial_quot_center hc h.2.toNontrivial

theorem r1613g_not_isPOnePlusTwo_of_comm {Q : Type*} [Group Q] (hc : ∀ a b : Q, a * b = b * a)
    (h : IsPOnePlusTwo 3 Q) : False := by
  haveI := h.1
  exact r1613g_not_nontrivial_quot_center hc (CFSG.IsExtraspecial.quotient_nontrivial 3 Q)

private theorem r1613g_pow_three_ne {c n : ℕ} (hn : n = 5 ∨ n = 7) : 3 ^ c ≠ n := by
  intro h
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · omega
  · have h3 : 3 ∣ 3 ^ c := dvd_pow_self 3 hc.ne'
    rw [h] at h3
    omega

variable {G : Type} [Group G] [Finite G]

theorem r1613g_case153_3_summary (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hconc : Conc4_136 D V₀ V hV L) (h3 : Case153_3 D V₀ V hV L) :
    Nat.card ↥(lBar V₀ V hV L) = 3 ∧ rk ↥(wTil V₀ V hV L) ≤ 2 := by
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  obtain ⟨⟨K₀, -, hcyc, hdir, hnat⟩, -⟩ := h3
  have hK3 : Nat.card ↥(barSub V₀ V hV K₀) = 3 := hcyc.2
  have hKabel : IsElemAbelian 3 (barSub V₀ V hV K₀) := s15_T7_isElemAbelian_of_cyclicOrd hcyc
  have hXabel : IsElemAbelian 3 (lBar V₀ V hV L) := s15_T7_isElemAbelian_of_directProd hKabel hdir
  have hXcomm : ∀ a b : ↥(lBar V₀ V hV L), a * b = b * a := by
    haveI := hXabel.1
    exact fun a b => mul_comm' a b
  have hKrk : rk ↥(commSub ⊤ (barSub V₀ V hV K₀)) = 2 :=
    s16c1610_rk_of_card_two_pow (s16c1610_card_alternatingNatural_odd (by decide) hnat)
  have hc1 := r1613g_card_directProd_of_conj hdir hK3
  have hc2 := r1613g_rk_commSub_directProd_le hdir (le_of_eq hKrk)
  set c := (conjSet (barSub V₀ V hV K₀)
    (Mbar D.M V₀ V hV ⊓ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _))).ncard with hc
  change Nat.card ↥(lBar V₀ V hV L) = 3 ^ c at hc1
  change rk ↥(commSub ⊤ (lBar V₀ V hV L)) ≤ c * 2 at hc2
  change Nat.card ↥(lBar V₀ V hV L) = 3 ∧ rk ↥(commSub ⊤ (lBar V₀ V hV L)) ≤ 2
  have h3pow : ∀ {a b : ℕ}, 3 ^ a = 3 ^ b → a = b := fun h =>
    Nat.pow_right_injective (by norm_num) h
  obtain ⟨t, -, -, -, -, -, -, halt⟩ := hconc
  rcases halt with ⟨p, hp, -, -, -, hcases⟩ | ⟨K', hK', g, -, -, hLK, -⟩ | ⟨hcomp, -⟩ |
    ⟨-, -, hcomp, -⟩
  · haveI : NeZero p := ⟨hp.ne_zero⟩
    rcases hcases with ⟨hcyc3, -⟩ | ⟨hcyc5, -⟩ | ⟨hP, -⟩ | ⟨hE, hrk8, -⟩ | ⟨hcyc7, -⟩ |
      ⟨r, m, hpm, hr2, hE, hrkr, -⟩ | ⟨hE, hrk6, -⟩
    · have h1 : c = 1 := h3pow (by rw [← hc1, hcyc3.2]; simp)
      exact ⟨hcyc3.2, by rw [h1] at hc2; omega⟩
    · exact absurd (hc1.symm.trans hcyc5.2) (r1613g_pow_three_ne (Or.inl rfl))
    · exact (r1613g_not_isPOnePlusTwo_of_comm hXcomm hP).elim
    · have h9 := s16c167_card_isElemAbelianOfRank hE
      have h1 : c = 2 := h3pow (by rw [← hc1, h9])
      omega
    · exact absurd (hc1.symm.trans hcyc7.2) (r1613g_pow_three_ne (Or.inr rfl))
    · rcases hpm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have h9 := s16c167_card_isElemAbelianOfRank hE
        have h1 : c = r := h3pow (by rw [← hc1, h9])
        omega
      · have h9 := s16c167_card_isElemAbelianOfRank hE
        have h7 : 7 ∣ 3 ^ c := by
          rw [← hc1, h9]
          exact dvd_pow_self 7 (by omega)
        have := Nat.Prime.dvd_of_dvd_pow (by norm_num) h7
        omega
    · have h9 := s16c167_card_isElemAbelianOfRank hE
      have h1 : c = 2 := h3pow (by rw [← hc1, h9])
      omega
  · have hle : K' ≤ lBar V₀ V hV L := le_sup_left.trans hLK.ge
    refine (r1613g_not_isQuasisimple_of_comm (fun a b => ?_) hK'.2.2).elim
    have h2 := congrArg Subtype.val (hXcomm ⟨(a : MulAut (Vtil V₀ V hV)), hle a.2⟩
      ⟨(b : MulAut (Vtil V₀ V hV)), hle b.2⟩)
    exact Subtype.ext h2
  · exact (r1613g_not_isQuasisimple_of_comm hXcomm hcomp.2.2).elim
  · exact (r1613g_not_isQuasisimple_of_comm hXcomm hcomp.2.2).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
