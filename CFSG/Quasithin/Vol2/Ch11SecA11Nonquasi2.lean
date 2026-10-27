module

public import CFSG.Quasithin.Vol2.Ch11SecA11Nonquasi
public import CFSG.Quasithin.Background.A3Structure314
public import CFSG.Quasithin.Vol2.Ch11SecA11Concl
public import CFSG.Quasithin.Vol2.Ch11SecA11Ord

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.QuasithinUnique

variable {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q} {n : ℕ}

theorem BarData.isSL2_of_imgOdd (hD : BarData B n) (hBL : B ≤ L) {r : ℕ} (hr : r.Prime)
    (hr5 : 5 ≤ r) (hM : IsSL2 r ↥(A313.imgOdd (B.subgroupOf L))) : IsSL2 r ↥B := by
  let eB : ↥(B.subgroupOf L) ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBL
  let e : (↥(B.subgroupOf L) ⧸ CFSG.oddCore ↥(B.subgroupOf L)) ≃* (↥B ⧸ CFSG.oddCore ↥B) :=
    QuotientGroup.congr _ _ eB (A313.oddCore_map_mulEquiv eB)
  have h1 := IsSL2.of_mulEquiv e (A314.isSL2_quotient_oddCore hr hr5 hM)
  have hO : CFSG.oddCore ↥B = ⊥ := hD.odd _ inferInstance (A37.odd_card_oddCore _)
  exact IsSL2.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot)
    h1

theorem concl_of_nonquasi (hD : BarData B n) (hBL : B ≤ L) (h36 : A36Strong L)
    (h : A312Nonquasi B L) : Concl1111 ↥L n := by
  have hnq := A312.not_quasisimple_of_nonquasi h
  obtain ⟨p₀, hp₀, hp₀3, hΛ⟩ := A312.exists_isSL2_oddCore h36 hnq
  have hr5₀ : 5 ≤ p₀ := A313.five_le_of_prime hp₀ hp₀3
  obtain ⟨hconc, hcom, -⟩ := h36
  have hF : CFSG.fittingSubgroup ↥L = CFSG.oddCore ↥L := hcom.1
  have hcase3 : ∀ p : ℕ, NaturalSL2Action p ↥L (CFSG.fittingSubgroup ↥L) →
      IsSL2 p (↥L ⧸ CFSG.oddCore ↥L) := fun p hN =>
    IsSL2.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hF) (isSL2_of_naturalSL2Action hN)
  unfold A312Nonquasi at h
  dsimp only at h
  rcases h with ⟨-, hLB, -⟩ | ⟨-, ⟨p₂, hp₂, hp₂5, hp₂8, hpSL₂⟩, N, hNn, hNeq, hN5⟩
  · have htop : A313.imgOdd (B.subgroupOf L) = ⊤ := (A313.imgOdd_eq_top_iff hBL).mpr hLB
    have hM : IsSL2 p₀ ↥(A313.imgOdd (B.subgroupOf L)) :=
      IsSL2.of_mulEquiv ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).symm hΛ
    have hB := hD.isSL2_of_imgOdd hBL hp₀ hr5₀ hM
    obtain ⟨a, ha⟩ := hD.card
    obtain ⟨rfl, hn⟩ := eq_five_of_sl2 hp₀ (by omega) hD.two_le (b := a + n) (by omega)
      (by rw [← card_of_isSL2 hp₀ hB, ha])
    refine Or.inr ⟨hn, ?_⟩
    rcases hconc with ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨p, hp, -, hFF, hE, hN⟩ | h4
    · exact absurd hc.1 hnq
    · exact absurd hc.1 hnq
    · have h1 : p * (p ^ 2 - 1) = 120 :=
        (card_of_isSL2 hp (hcase3 p hN)).symm.trans (card_of_isSL2 hp₀ hΛ)
      have hp5 := A314.p_eq_five_of_mul hp h1
      subst hp5
      exact three_case4 (a36Case4_of_case3_five hFF hE hN)
    · exact three_case4 h4
  · subst hNeq
    have hM : IsSL2 5 ↥(A313.imgOdd (B.subgroupOf L)) :=
      IsSL2.of_mulEquiv (A312.quotEquivImage hBL) hN5
    have hB := hD.isSL2_of_imgOdd hBL Nat.prime_five le_rfl hM
    obtain ⟨a, ha⟩ := hD.card
    obtain ⟨-, hn⟩ := eq_five_of_sl2 Nat.prime_five (by norm_num) hD.two_le (b := a + n)
      (by omega) (by rw [← card_of_isSL2 Nat.prime_five hB, ha])
    refine Or.inr ⟨hn, ?_⟩
    rcases hconc with ⟨hc, -⟩ | ⟨hc, -⟩ | ⟨p, hp, -, hFF, hE, hN⟩ | h4
    · exact absurd hc.1 hnq
    · exact absurd hc.1 hnq
    · have hpp : p = p₂ := eq_of_mul_sq_sub_one hp.one_lt.le hp₂.one_lt.le
        ((card_of_isSL2 hp (hcase3 p hN)).symm.trans (card_of_isSL2 hp₂ hpSL₂))
      subst hpp
      iterate 14 right
      exact ⟨p, hp, mod_five_of_sq hp₂5, hp₂8, hFF, hE, hN⟩
    · exact three_case4 h4

end CFSG.Quasithin.Vol2.Ch11.SecA
