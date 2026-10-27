module

public import CFSG.Quasithin.Vol2.Ch11SecO10T
public import CFSG.Quasithin.Vol2.Ch11SecO10R

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem lt_mul_of_four_le {q : ℕ} (hq : 4 ≤ q) {b c : ℕ} (hb : 2 ≤ b) (hc : 3 ≤ c) :
    40320 < q ^ c * ((q ^ c - 1) * (q ^ b - 1)) := by
  have h1 : 64 ≤ q ^ c := le_trans (by norm_num) (Nat.pow_le_pow_left hq 3) |>.trans
    (Nat.pow_le_pow_right (by omega) hc)
  have h2 : 15 ≤ q ^ b - 1 := by
    have : 16 ≤ q ^ b :=
      le_trans (by norm_num) ((Nat.pow_le_pow_left hq 2).trans (Nat.pow_le_pow_right (by omega) hb))
    omega
  have h3 : 63 ≤ q ^ c - 1 := by omega
  calc 40320 < 64 * (63 * 15) := by norm_num
    _ ≤ q ^ c * ((q ^ c - 1) * (q ^ b - 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul h3 h2)

theorem lt_card_autOn_L (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) :
    40320 < Nat.card ↥(autOn L (fsuV T I)) := by
  have hn : 2 ≤ n := h.one_lt
  have hq : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rcases SecA.kind_cases h1102 h with ⟨K, _, _, hK, ⟨e⟩⟩ | ⟨K, _, _, hK, ⟨e⟩⟩ |
      ⟨K, _, _, hK, ⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv, CFSG.BrauerLinearThree.card_SL_three, hK, mul_assoc]
    exact lt_mul_of_four_le hq (b := 2) (c := 3) le_rfl le_rfl
  · rw [Nat.card_congr e.toEquiv, LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp]
    have hI : Finset.Icc 1 2 = {1, 2} := by decide
    rw [hI, Finset.prod_pair (by norm_num), hK]
    have := lt_mul_of_four_le hq (b := 2) (c := 4) le_rfl (by norm_num)
    rw [show (2 * 1 : ℕ) = 2 by norm_num, show (2 * 2 : ℕ) = 4 by norm_num,
      show (2 : ℕ) ^ 2 = 4 by norm_num]
    calc 40320 < (2 ^ n) ^ 4 * (((2 ^ n) ^ 4 - 1) * ((2 ^ n) ^ 2 - 1)) := this
      _ = (2 ^ n) ^ 4 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) := by ring
  · rw [Nat.card_congr e.toEquiv, KGNat.factG2DerivedOrder_holds K n hn hK]
    exact lt_mul_of_four_le hq (b := 2) (c := 6) le_rfl (by norm_num)

theorem card_le_of_sp4_two {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {m : ℕ}
    (hm : BinaryNaturalSp4 H ⊤ ⊥ m) (hm1 : ¬ 1 < m) : Nat.card ↥H ≤ 720 := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := hm
  have hm' : m = 1 := by have := one_le_of_card_field hK; omega
  subst hm'
  have hc : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 K) = 720 := by
    rw [LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp]
    have hI : Finset.Icc 1 2 = {1, 2} := by decide
    rw [hI, Finset.prod_pair (by norm_num), hK]
    norm_num
  have : Finite ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 K) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have h1 : Nat.card ↥H ≤ Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 K) :=
    Nat.card_le_card_of_surjective π hπ.1
  rw [hc] at h1
  exact h1

theorem card_le_of_g2_two {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {m : ℕ}
    (hm : G2Natural H ⊤ ⊥ m) (hm1 : ¬ 1 < m) : Nat.card ↥H ≤ 12096 := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := hm
  have hm' : m = 1 := by have := one_le_of_card_field hK; omega
  subst hm'
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have hc : Nat.card ↥(quasithinG2 K) = 12096 := by
    rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
      KGNat.card_cayleyGroup, hK]
    norm_num
  have : Finite ↥(quasithinG2 K) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have h1 : Nat.card ↥H ≤ Nat.card ↥(quasithinG2 K) := Nat.card_le_card_of_surjective π hπ.1
  rw [hc] at h1
  exact h1

theorem card_le_of_symDn {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {m : ℕ}
    (hm : m = 5 ∨ m = 7) {π : Equiv.Perm (Fin m) →* ↥H}
    (hπ : (FFModel.symDn m).RealizesVia H ⊤ ⊥ π) : Nat.card ↥H ≤ 5040 := by
  have h1 := Nat.card_le_card_of_surjective π hπ.1
  rw [Nat.card_perm, Nat.card_fin] at h1
  rcases hm with rfl | rfl
  · exact h1.trans (by decide)
  · exact h1.trans (by decide)

theorem ffJ_eq_autOn (hB42 : AsB42) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    [IsMulCommutative ↥(fsuV T I)] {S : Subgroup (MulAut ↥(fsuV T I))}
    (hTS : autOn T (fsuV T I) ≤ S) (hsec : Sec328 (autOn L (fsuV T I)) S)
    (hB4 : B4Hyp (autOn L (fsuV T I) ⊔ S) (autOn L (fsuV T I))) {A : Subgroup G}
    (hA : IsMaxElemAbelian T A) (hAV : ¬ A ≤ Subgroup.centralizer (fsuV T I : Set G)) :
    ffJ (autOn L (fsuV T I) ⊔ S) = autOn L (fsuV T I) := by
  have hoff := isFFStarOffender_autOn h hTS hA hAV
  have hLJ := le_ffJ_of_offender h hTS hsec hA hAV
  have hbig := lt_card_autOn_L h1102 h
  have hLJc : Nat.card ↥(autOn L (fsuV T I)) ≤ Nat.card ↥(ffJ (autOn L (fsuV T I) ⊔ S)) :=
    Subgroup.card_le_of_le hLJ
  have hc := hB42 _ hsec.sq _ _ hB4 _ hoff
  rcases hc with ⟨hJ, -⟩ | ⟨hJ, -⟩ | ⟨⟨m, hm, hmJ⟩, -⟩ | ⟨⟨m, hm, -, hmJ⟩, -⟩ |
      ⟨⟨m, hm57, π, hπ, -⟩, -⟩ | ⟨hJ, -⟩ | ⟨-, hJ, -⟩ | ⟨hJ, -⟩ | ⟨hJ, -⟩ |
      ⟨-, ⟨-, hJ, -⟩ | ⟨hGJ, ⟨e⟩, -⟩⟩ | ⟨-, hJ, -⟩
  · exact hJ
  · exact hJ
  · by_cases hm1 : 1 < m
    · exact hmJ hm1
    · have := card_le_of_sp4_two hm hm1
      omega
  · by_cases hm1 : 1 < m
    · exact hmJ hm1
    · have := card_le_of_g2_two hm hm1
      omega
  · have := card_le_of_symDn hm57 hπ
    omega
  · exact hJ
  · exact hJ
  · exact hJ
  · exact hJ
  · exact hJ
  · exfalso
    have h8 : Nat.card ↥(autOn L (fsuV T I) ⊔ S) = 40320 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    have := Subgroup.card_le_of_le (le_sup_left : autOn L (fsuV T I) ≤ autOn L (fsuV T I) ⊔ S)
    omega
  · exact hJ

theorem autOn_le_of_isMaxElemAbelian (hB42 : AsB42) (h1102 : Stmt11_0_2)
    (h8 : Ch10.TmpL6_3_2_2_eight) (h : Hyp11 G T L I n)
    (hcV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) {A : Subgroup G}
    (hA : IsMaxElemAbelian T A) : autOn A (fsuV T I) ≤ autOn L (fsuV T I) := by
  obtain ⟨_, -⟩ := h1102 G T L I n h
  by_cases hAV : A ≤ Subgroup.centralizer (fsuV T I : Set G)
  · intro x hx
    obtain ⟨a, ha, haV, rfl⟩ := SecA.mem_autOn_iff.mp hx
    have h1 : SecA.conjV (fsuV T I) a haV = 1 := by
      ext v
      rw [SecA.conjV_apply_coe, ← Subgroup.mem_centralizer_iff.mp (hAV ha) v v.2,
        mul_inv_cancel_right]
      rfl
    rw [h1]
    exact Subgroup.one_mem _
  · obtain ⟨S, -, hTS, hsec, hB4⟩ := exists_b4Hyp h1102 h8 h hcV
    have hoff := isFFStarOffender_autOn h hTS hA hAV
    exact (B6.le_ffJ hoff).trans (ffJ_eq_autOn hB42 h1102 h hTS hsec hB4 hA hAV).le

end CFSG.Quasithin.Vol2.Ch11.O10
