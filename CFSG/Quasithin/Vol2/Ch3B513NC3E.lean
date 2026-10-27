module

public import CFSG.Quasithin.Vol2.Ch3B513NC3D
public import CFSG.Quasithin.Vol2.Ch3B513NC3B

public section

namespace CFSG.Quasithin.B513N

open CFSG.Assembly.LowTwoRank

variable {W : Type} [CommGroup W] [Finite W]

theorem card_le_four_of_realizes {L D : Subgroup (MulAut W)} (hDL : D ≤ L) {M : FFModel}
    (hM : M.Faithful) {U Z : Subgroup W} {π : M.Gam →* ↥L} (hr : M.RealizesVia L U Z π)
    (hX : ∀ E : Subgroup M.Gam, (∀ x ∈ E, x ^ 2 = 1) → Nat.card E ≤ 4)
    (hD2 : ∀ d ∈ D, d ^ 2 = 1) : Nat.card D ≤ 4 :=
  card_le_of_equiv hDL (MulEquiv.ofBijective π ⟨FFC.injective_of_faithful_sec hM hr, hr.1⟩).symm
    hX hD2

theorem hasGood_of_piece (hW : ∀ w : W, w ^ 2 = 1) {G L D : Subgroup (MulAut W)}
    (hD : IsFFStarMin G D) (hDL : D ≤ L) {Wi C : Subgroup W} (hC : C ≤ fixV L)
    (hsupW : Wi ⊔ fixV L = ⊤) (hP : B56Piece L Wi C) : HasGood G := by
  have hD2 : ∀ d ∈ D, d ^ 2 = 1 := hD.1.2.2.1.2
  have hinvU : ∀ h : ↥L, ∀ u ∈ commV L, (h : MulAut W) u ∈ commV L := fun h u hu =>
    FFC.commV_invariant_self L h h.2 u hu
  rcases hP with ⟨hWi, hSL2 | hS5 | hSL3⟩ | ⟨hWi, m, K, _, _, hK, hds⟩ | ⟨⟨e⟩, -, -, -, -⟩
  ·
    obtain ⟨n, K, _, _, hK, π, hr⟩ := hSL2
    rcases Nat.lt_or_ge n 3 with hn | hn
    · exact hasGood_of_card_le_four hW hD (card_le_four_of_realizes hDL (FFModel.nat_faithful _)
        hr (card_le_four_sl2 hK (by omega)) hD2)
    · have hcomm := commOf_commV_eq hC hWi hsupW
      have hr' := FFC.realizesVia_restrict hr hWi.symm hinvU
      have hZ := card_le_of_sl2_cover hW L (commV L) (fun x hx v hv => hinvU ⟨x, hx⟩ v hv) hcomm
        (inf_le_left.trans hC) inf_le_right (by omega) hK ⟨π, hr'⟩
      refine hasGood_of_nat_cent_of hW hD hDL hr' (by norm_num) ?_
      rw [hK]
      calc Nat.card ↥(C ⊓ commV L) * (2 ^ n) ^ (2 - 1) ≤ 2 ^ n * (2 ^ n) ^ (2 - 1) :=
            Nat.mul_le_mul_right _ hZ
        _ = (2 ^ n) ^ 2 := by ring
  ·
    obtain ⟨π, hr⟩ := hS5
    exact hasGood_of_card_le_four hW hD (card_le_four_of_realizes hDL
      (FFC.symDn_faithful (by norm_num)) hr (fun E hE => card_le_four_perm5 E hE) hD2)
  ·
    obtain ⟨m, K, _, _, hK, π, hr⟩ := hSL3
    rcases Nat.lt_or_ge m 2 with hm | hm
    · have hK2 : Nat.card K = 2 := by
        interval_cases m
        · have : 1 < Nat.card K := Finite.one_lt_card
          simp at hK
          omega
        · simpa using hK
      exact hasGood_of_card_le_four hW hD (card_le_four_of_realizes hDL (FFModel.nat_faithful _)
        hr (card_le_four_sl3 hK2) hD2)
    · have hcomm := commOf_commV_eq hC hWi hsupW
      have hr' := FFC.realizesVia_restrict hr hWi.symm hinvU
      have hZ := eq_bot_of_sl3_cover hW (fun x hx v hv => hinvU ⟨x, hx⟩ v hv) hcomm
        (inf_le_left.trans hC) inf_le_right (by omega) hK ⟨π, hr'⟩
      refine hasGood_of_nat_cent_of hW hD hDL hr' (by norm_num) ?_
      rw [hZ, Subgroup.card_bot, one_mul]
  ·
    rcases Nat.lt_or_ge m 2 with hm | hm
    · have hK2 : Nat.card K = 2 := by
        interval_cases m
        · have : 1 < Nat.card K := Finite.one_lt_card
          simp at hK
          omega
        · simpa using hK
      obtain ⟨I, π, -, -, -, hreal⟩ := hds
      exact hasGood_of_card_le_four hW hD (card_le_four_of_realizes hDL (FFModel.nat_faithful _)
        (hreal 0) (card_le_four_sl3 hK2) hD2)
    · exact hasGood_of_two_nat hW hD hDL hC hsupW (by omega) hK hds
  ·
    exact hasGood_of_card_le_four hW hD (card_le_of_equiv hDL e
      (card_le_four_sl3 (Nat.card_zmod 2)) hD2)

end CFSG.Quasithin.B513N
