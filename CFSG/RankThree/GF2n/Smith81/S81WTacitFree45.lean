module

public import CFSG.RankThree.GF2n.Smith81.S81WNotVI45
public import CFSG.RankThree.GF2n.Smith81.S81WTacitE4

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G]

theorem noA2All_of_inCaseE4 [Finite G] {M Q Z B : Subgroup G} (hc : Cfg M Q Z B)
    (h4 : InCaseE4 M Q Z B) : NoA2All M Q Z := by
  obtain ⟨t, ht, hE⟩ := id h4
  have hQ := hE.1
  have hq4 : 4 ≤ Nat.card Z := hc.ctx.hyp.q4
  have hq2 : 2 ≤ Nat.card Z := le_trans (by norm_num) hq4
  obtain ⟨h1, -⟩ := hc.conclusion
  rcases h1 with ⟨n, hqn, hL3⟩ | ⟨hQ5, -⟩ | ⟨hQ9, -, -⟩ | ⟨-, hA | hVI⟩
  · exfalso
    obtain ⟨e⟩ := hL3
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hqn
      omega
    have hQ3 : Nat.card Q = Nat.card Z ^ 3 := by
      rw [Nat.card_congr e.toEquiv, Tim79.card_ut3, GaloisField.card 2 n hn0, hqn]
    have h := Nat.pow_right_injective hq2 (hQ3.symm.trans hQ)
    omega
  · exfalso
    have h := Nat.pow_right_injective hq2 (hQ5.symm.trans hQ)
    omega
  · exfalso
    have h := Nat.pow_right_injective hq2 (hQ9.symm.trans hQ)
    omega
  · exact hA.1
  · exact (MS80NoA2.not_caseVI_of_caseE4 hc ht hE hVI).elim

theorem noA2All_of_inCaseE5 [Finite G] {M Q Z B : Subgroup G} (hc : Cfg M Q Z B)
    (h5 : InCaseE5 M Q Z B) : NoA2All M Q Z := by
  obtain ⟨t, ht, hE⟩ := id h5
  have hQ := hE.1
  have hq4 : 4 ≤ Nat.card Z := hc.ctx.hyp.q4
  have hq2 : 2 ≤ Nat.card Z := le_trans (by norm_num) hq4
  obtain ⟨h1, -⟩ := hc.conclusion
  rcases h1 with ⟨n, hqn, hL3⟩ | ⟨hQ5, -⟩ | ⟨hQ9, -, -⟩ | ⟨-, hA | hVI⟩
  · exfalso
    obtain ⟨e⟩ := hL3
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hqn
      omega
    have hQ3 : Nat.card Q = Nat.card Z ^ 3 := by
      rw [Nat.card_congr e.toEquiv, Tim79.card_ut3, GaloisField.card 2 n hn0, hqn]
    have h := Nat.pow_right_injective hq2 (hQ3.symm.trans hQ)
    omega
  · exfalso
    have h := Nat.pow_right_injective hq2 (hQ5.symm.trans hQ)
    omega
  · exfalso
    have h := Nat.pow_right_injective hq2 (hQ9.symm.trans hQ)
    omega
  · exact hA.1
  · exact (MS80NoA2.not_caseVI_of_caseE5 hc ht hE hVI).elim

theorem eTacitE4_of_genByB (hGen : StrothGenByBStatement) : ETacitE4Statement := by
  intro G _ _ M Q Z B _ hc h4 B' hB'
  have hno : NoA2 Q Z (LB M Q B') :=
    noA2All_of_inCaseE4 hc.toCfg h4 B' hB'.conj hB'.le hB'.ne
  obtain ⟨-, -, hQ, -⟩ := h4
  have hw : Width Q Z 16 := by simpa [Width] using hQ
  exact ⟨hno, hGen G M Q Z B' hB' 16 hw (by norm_num) hno⟩

theorem eTacitE5_of_genByB (hGen : StrothGenByBStatement) : ETacitE5Statement := by
  intro G _ _ M Q Z B _ hc h5 B' hB'
  have hno : NoA2 Q Z (LB M Q B') :=
    noA2All_of_inCaseE5 hc.toCfg h5 B' hB'.conj hB'.le hB'.ne
  obtain ⟨-, -, hQ, -⟩ := h5
  have hw : Width Q Z 28 := by simpa [Width] using hQ
  exact ⟨hno, hGen G M Q Z B' hB' 28 hw (by norm_num) hno⟩

end CFSG.RankThree.GF2n.Smith81
