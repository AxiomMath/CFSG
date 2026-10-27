module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316H

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative

namespace L3316

variable {G : Type} [Group G] [Finite G]

theorem sp4_module
    {T M L D : Subgroup G} (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (h51 : AsB51) (h10 : Stmt3_3_10) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (e : ↥(autOn L (vPlus L T)) ≃* ↥(StatedSp 2 K)) :
    ∃ _ : IsMulCommutative ↥(vPlus L T), ∃ m : ℕ,
      BinaryNaturalSp4 (autOn L (vPlus L T)) (tildeComm L T L) (cvPlus L T) m := by
  have hML := Hyp331.mPlus_eq_of_le hTL
  have hK2 : Nat.card K = 2 ^ 2 := by rw [hK]; norm_num
  have hN : Nat.card ↥(autOn L (vPlus L T)) = 979200 := by
    rw [Nat.card_congr e.toEquiv, card_sp4 hK2]
    norm_num
  have hnL2 := (h10 G T M L D h).2.1
  rw [hML] at hnL2
  obtain ⟨hVc, hc⟩ := h.lemma_3_3_8_of_le h38 h39 h51 hTL
  refine ⟨hVc, ?_⟩
  rcases hc with h1 | h2 | h3 | h4 | h5 | h6 | h7
  · obtain ⟨t, ht, htN, -⟩ := h1
    exact absurd (hTL ht) htN
  · obtain ⟨m, -, hm, -⟩ := h2
    rw [hML] at hm
    exact absurd hm (hnL2 m)
  · rcases h3 with ⟨⟨e'⟩, -⟩ | ⟨⟨e'⟩, -⟩
    · rw [hML] at e'
      rw [Nat.card_congr e'.toEquiv, card_alt 5 (by norm_num)] at hN
      norm_num [Nat.factorial] at hN
    · rw [hML] at e'
      rw [Nat.card_congr e'.toEquiv, card_alt 7 (by norm_num)] at hN
      norm_num [Nat.factorial] at hN
  · rcases h4 with ⟨m, K', _, _, hK', ⟨e'⟩, -⟩ | ⟨m, K', _, _, hm, hK', ⟨-⟩, hmod⟩ | ⟨⟨e'⟩, -⟩ |
      ⟨m, K', _, _, hK', ⟨e'⟩, -⟩
    · rw [hML] at e'
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · have h1 := Finite.one_lt_card (α := K')
          rw [hK'] at h1
          norm_num at h1
        · exact hm
      rw [Nat.card_congr e'.toEquiv, card_sl3 hK'] at hN
      exact (sp4_ne_sl3 (n := 2) (m := m) (by norm_num) hm1 (Or.inl rfl)
        (by rw [one_mul]; norm_num; exact hN.symm)).elim
    · rw [hML] at hmod
      exact ⟨m, hmod⟩
    · rw [hML] at e'
      rw [Nat.card_congr e'.toEquiv, card_alt 6 (by norm_num)] at hN
      norm_num [Nat.factorial] at hN
    · rw [hML] at e'
      rcases Nat.lt_or_ge m 2 with hm | hm
      · have hle : Nat.card ↥⁅quasithinG2 K', quasithinG2 K'⁆ ≤ Nat.card ↥(quasithinG2 K') := by
          refine Subgroup.card_le_of_le ?_
          rw [Subgroup.commutator_le]
          intro a ha b hb
          exact (quasithinG2 K').mul_mem ((quasithinG2 K').mul_mem
            ((quasithinG2 K').mul_mem ha hb) ((quasithinG2 K').inv_mem ha))
            ((quasithinG2 K').inv_mem hb)
        interval_cases m
        · have h1 := Finite.one_lt_card (α := K')
          rw [hK'] at h1
          norm_num at h1
        · rw [card_g2 le_rfl hK', ← Nat.card_congr e'.toEquiv, hN] at hle
          norm_num at hle
      · rw [Obs3324.commutator_quasithinG2_eq hm hK'] at e'
        rw [Nat.card_congr e'.toEquiv, card_g2 (by omega) hK'] at hN
        have h6 : 4096 ≤ 2 ^ (m * 6) :=
          calc 4096 = 2 ^ 12 := by norm_num
            _ ≤ 2 ^ (m * 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 : 16 ≤ 2 ^ (m * 2) :=
          calc 16 = 2 ^ 4 := by norm_num
            _ ≤ 2 ^ (m * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hle : 4096 * (4095 * 15) ≤
            2 ^ (m * 6) * ((2 ^ (m * 6) - 1) * (2 ^ (m * 2) - 1)) :=
          Nat.mul_le_mul h6 (Nat.mul_le_mul (by omega) (by omega))
        omega
  · obtain ⟨⟨e'⟩, -⟩ := h5
    rw [hML] at e'
    rw [Nat.card_congr e'.toEquiv, card_alt 7 (by norm_num)] at hN
    norm_num [Nat.factorial] at hN
  · obtain ⟨-, hZ, ⟨e'⟩, -⟩ := h6
    rw [hML] at hZ e'
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center ↥(autOn L (vPlus L T)))
    rw [Nat.card_congr e'.toEquiv, card_alt 6 (by norm_num), hZ, hN] at hcard
    norm_num [Nat.factorial] at hcard
  · obtain ⟨m, hm, ⟨e'⟩, -⟩ := h7
    rw [hML] at e'
    have hc := Nat.card_congr e'.toEquiv
    rcases hm with rfl | rfl
    · rw [Matrix.card_SL_field, ZMod.card, hN] at hc
      simp [Fin.prod_univ_four] at hc
    · rw [Matrix.card_SL_field, ZMod.card, hN] at hc
      simp [Fin.prod_univ_five] at hc

end L3316

end CFSG.Quasithin.H13
