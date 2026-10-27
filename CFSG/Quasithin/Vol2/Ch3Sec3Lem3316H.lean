module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316A
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative

namespace L3316

theorem sl3_ne {n N : ℕ} (hn : 2 ≤ n) (h1 : 60480 < N) (h2 : N < 16482816) :
    2 ^ (n * 3) * ((2 ^ (n * 2) - 1) * (2 ^ (n * 3) - 1)) ≠ N := by
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · obtain rfl : n = 2 := by omega
    norm_num
    omega
  · have h9 : 512 ≤ 2 ^ (n * 3) :=
      calc 512 = 2 ^ 9 := by norm_num
        _ ≤ 2 ^ (n * 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h6 : 64 ≤ 2 ^ (n * 2) :=
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (n * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hle : 512 * (63 * 511) ≤ 2 ^ (n * 3) * ((2 ^ (n * 2) - 1) * (2 ^ (n * 3) - 1)) :=
      Nat.mul_le_mul h9 (Nat.mul_le_mul (by omega) (by omega))
    omega

theorem card_alt (m : ℕ) (hm : 2 ≤ m) :
    Nat.card (alternatingGroup (Fin m)) = m.factorial / 2 := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]

variable {G : Type} [Group G] [Finite G]

theorem sl3_module
    {T M L D : Subgroup G} (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (h51 : AsB51) (h10 : Stmt3_3_10) (hTL : T ≤ Subgroup.normalizer (L : Set G)) {n : ℕ}
    (hn : 1 < n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n)
    (e : ↥(autOn L (vPlus L T)) ≃* ↥(StatedSL 3 K)) :
    ∃ _ : IsMulCommutative ↥(vPlus L T), ∃ (m : ℕ) (K' : Type) (_ : Field K') (_ : Finite K'),
      Nat.card K' = 2 ^ m ∧
      (BinaryNaturalSL (autOn L (vPlus L T)) (tildeComm L T L) (cvPlus L T) 3 m ∨
        DirectSumOfCopies (autOn L (vPlus L T)) (tildeComm L T L) (cvPlus L T)
          (FFModel.nat (StatedSL 3 K')) 2) := by
  have hML := Hyp331.mPlus_eq_of_le hTL
  have hN : Nat.card ↥(autOn L (vPlus L T)) =
      2 ^ (n * 3) * ((2 ^ (n * 2) - 1) * (2 ^ (n * 3) - 1)) := by
    rw [Nat.card_congr e.toEquiv, card_sl3 hK]
  have hge := sl3_ge (n := n) (by omega)
  rw [← hN] at hge
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
      rw [Nat.card_congr e'.toEquiv, card_alt 5 (by norm_num)] at hge
      norm_num [Nat.factorial] at hge
    · rw [hML] at e'
      rw [Nat.card_congr e'.toEquiv, card_alt 7 (by norm_num)] at hge
      norm_num [Nat.factorial] at hge
  · rcases h4 with ⟨m, K', _, _, hK', ⟨-⟩, hmod⟩ | ⟨m, K', _, _, hm, hK', ⟨e'⟩, -⟩ | ⟨⟨e'⟩, -⟩ |
      ⟨m, K', _, _, hK', ⟨e'⟩, -⟩
    · rw [hML] at hmod
      exact ⟨m, K', inferInstance, inferInstance, hK', hmod⟩
    · rw [hML] at e'
      rw [Nat.card_congr e'.toEquiv, card_sp4 hK'] at hN
      exact (sp4_ne_sl3 (n := m) (m := n) (by omega) (by omega) (Or.inl rfl)
        (by rw [one_mul]; exact hN)).elim
    · rw [hML] at e'
      rw [Nat.card_congr e'.toEquiv, card_alt 6 (by norm_num)] at hge
      norm_num [Nat.factorial] at hge
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
        · rw [card_g2 le_rfl hK', ← Nat.card_congr e'.toEquiv] at hle
          norm_num at hle
          omega
      · rw [Obs3324.commutator_quasithinG2_eq hm hK'] at e'
        rw [Nat.card_congr e'.toEquiv, card_g2 (by omega) hK'] at hN
        exact (g2_ne_sl3 (n := m) (m := n) (by omega) (by omega) (Or.inl rfl)
          (by rw [one_mul]; exact hN)).elim
  · obtain ⟨⟨e'⟩, -⟩ := h5
    rw [hML] at e'
    rw [Nat.card_congr e'.toEquiv, card_alt 7 (by norm_num)] at hge
    norm_num [Nat.factorial] at hge
  · obtain ⟨-, hZ, ⟨e'⟩, -⟩ := h6
    rw [hML] at hZ e'
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center ↥(autOn L (vPlus L T)))
    rw [Nat.card_congr e'.toEquiv, card_alt 6 (by norm_num), hZ] at hcard
    norm_num [Nat.factorial] at hcard
    omega
  · obtain ⟨m, hm, ⟨e'⟩, -⟩ := h7
    rw [hML] at e'
    have hc := Nat.card_congr e'.toEquiv
    rcases hm with rfl | rfl
    · rw [Matrix.card_SL_field, ZMod.card] at hc
      simp [Fin.prod_univ_four] at hc
      omega
    · rw [Matrix.card_SL_field, ZMod.card] at hc
      simp [Fin.prod_univ_five] at hc
      exact (sl3_ne (n := n) (by omega) (by omega) (by omega) (hN.symm.trans hc)).elim

end L3316

end CFSG.Quasithin.H13
