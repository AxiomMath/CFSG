module

public import CFSG.Quasithin.Vol2.Ch11SecEFacts7
public import CFSG.Quasithin.Vol2.Ch11SecAKE4
public import CFSG.Quasithin.Vol2.Ch11SecA11SL2
public import CFSG.Quasithin.Vol2.KGNatVec
public import CFSG.Quasithin.EmptyFaithful.T1515M11

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL)

namespace C10KH

theorem le_of_two_pow_dvd {N k : ℕ} (hN : N = 10200960 ∨ N = 86775571046077562880)
    (h : 2 ^ k ∣ N) : k ≤ 21 := by
  by_contra hk
  have h22 : 2 ^ 22 ∣ N := (Nat.pow_dvd_pow 2 (by omega)).trans h
  rcases hN with rfl | rfl <;> norm_num at h22

theorem psl2_ne {N m : ℕ} (hN : N = 10200960 ∨ N = 86775571046077562880)
    (h : 2 ^ m * ((2 ^ m) ^ 2 - 1) = N) : False := by
  have hm := le_of_two_pow_dvd hN (k := m) ⟨_, h.symm⟩
  interval_cases m <;> rcases hN with rfl | rfl <;> norm_num at h

theorem sl3_ne {N m : ℕ} (hN : N = 10200960 ∨ N = 86775571046077562880)
    (h : (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) = N) : False := by
  have hm := le_of_two_pow_dvd hN (k := m * 3) ⟨_, by rw [pow_mul]; exact h.symm⟩
  have hm' : m ≤ 7 := by omega
  interval_cases m <;> rcases hN with rfl | rfl <;> norm_num at h

theorem sp4_ne {N m : ℕ} (hN : N = 10200960 ∨ N = 86775571046077562880)
    (h : (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) = N) : False := by
  have hm := le_of_two_pow_dvd hN (k := m * 4) ⟨_, by rw [pow_mul]; exact h.symm⟩
  have hm' : m ≤ 5 := by omega
  interval_cases m <;> rcases hN with rfl | rfl <;> norm_num at h

theorem g2_ne {N m : ℕ} (hN : N = 10200960 ∨ N = 86775571046077562880)
    (h : (2 ^ m) ^ 6 * (((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1)) = N) : False := by
  have hm := le_of_two_pow_dvd hN (k := m * 6) ⟨_, by rw [pow_mul]; exact h.symm⟩
  have hm' : m ≤ 3 := by omega
  interval_cases m <;> rcases hN with rfl | rfl <;> norm_num at h

theorem exists_ne_zero_ne_one {K : Type} [Field K] [Finite K] (hK : 2 < Nat.card K) :
    ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have := Fintype.ofFinite K
  have hle : Fintype.card K ≤ ({0, 1} : Finset K).card :=
    Finset.card_le_card fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [hcon x hx]
  have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
  rw [Nat.card_eq_fintype_card] at hK
  omega

section Core


theorem not_list701Excl {Y : Type} [Group Y] {N : ℕ}
    (hN : N = 10200960 ∨ N = 86775571046077562880) (hY : Nat.card Y = N) : ¬ List701Excl Y := by
  classical
  have hN1 : 12096 < N := by rcases hN with rfl | rfl <;> norm_num
  intro h
  rcases h with ⟨m, hm⟩ | ⟨K, _, _, m, hK, h⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨-, hZ, ⟨e⟩⟩ | ⟨⟨e⟩⟩ |
    ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  ·
    rcases hm with ⟨-, hm⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact psl2_ne hN ((SecA.C10KH.card_of_isPSL_two_two hm).2.symm.trans hY)
    all_goals exact absurd h0 (by norm_num)
  · have hm1 : 1 ≤ m := by
      have := Finite.one_lt_card (α := K)
      rw [hK] at this
      by_contra h0
      simp [show m = 0 by omega] at this
    have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hm1 hK
    have := Fintype.ofFinite K
    rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨π, hπ⟩
    ·
      refine sl3_ne hN (m := m) ?_
      rw [← hY, Nat.card_congr e.toEquiv,
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hK,
        show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
    ·
      refine sp4_ne hN (m := m) ?_
      rw [← hY, Nat.card_congr e.toEquiv,
        CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK,
        show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
      norm_num
    ·
      rw [Nat.card_congr e.toEquiv] at hY
      by_cases hm2 : 2 ≤ m
      · obtain ⟨c, hc0, hc1⟩ := C10KH.exists_ne_zero_ne_one (K := K) (by
          rw [hK]
          calc 2 < 2 ^ 2 := by norm_num
            _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2)
        refine g2_ne hN (m := m) ?_
        rw [← hY, KGNat.commutator_quasithinG2_eq hc0 hc1, KGNat.card_cayleyGroup, hK]
      · have hle := Subgroup.card_le_of_le (KGNat.commutator_quasithinG2_le (K := K))
        rw [KGNat.card_cayleyGroup, hK, hY, show m = 1 by omega] at hle
        norm_num at hle
        omega
    ·
      let π' := π.comp (specialLinearGroupEquivStatedSL 2 K).toMonoidHom
      have hπ' : Function.Surjective π' := hπ.comp (specialLinearGroupEquivStatedSL 2 K).surjective
      have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
        rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
      by_cases hm2 : 2 ≤ m
      · have := SecA.isSimpleGroup_SL2 hm2 hK
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π'.ker with hb | ht
        · have hc := Nat.card_eq_of_bijective π' ⟨(MonoidHom.ker_eq_bot_iff π').mp hb, hπ'⟩
          exact psl2_ne hN (hSL.symm.trans (hc.trans hY))
        · have h1 : ∀ y : Y, y = 1 := fun y => by
            obtain ⟨x, rfl⟩ := hπ' y
            exact (MonoidHom.mem_ker).mp (ht ▸ Subgroup.mem_top x)
          have : Subsingleton Y := ⟨fun a b => (h1 a).trans (h1 b).symm⟩
          rw [Nat.card_unique] at hY
          omega
      · have hle := Nat.card_le_card_of_surjective π' hπ'
        rw [hSL, hY, show m = 1 by omega] at hle
        norm_num at hle
        omega
  ·
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hY
    rcases hN with rfl | rfl <;> revert hY <;> decide
  ·
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hY
    rcases hN with rfl | rfl <;> revert hY <;> decide
  ·
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hY
    rcases hN with rfl | rfl <;> revert hY <;> decide
  ·
    rw [(Subgroup.center Y).card_eq_card_quotient_mul_card_subgroup, Nat.card_congr e.toEquiv,
      nat_card_alternatingGroup, Nat.card_fin, hZ] at hY
    rcases hN with rfl | rfl <;> revert hY <;> decide
  ·
    rw [Nat.card_congr e.toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), Nat.card_zmod]
      at hY
    rcases hN with rfl | rfl <;> revert hY <;> decide
  ·
    rw [Nat.card_congr e.toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), Nat.card_zmod]
      at hY
    rcases hN with rfl | rfl <;> revert hY <;> decide
  ·
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Mathieu.card_M24] at hY
    rcases hN with rfl | rfl <;> omega

end Core

end C10KH


theorem factM23J4_holds : FactM23J4 := by
  intro X _ h
  rcases h with h | h
  · obtain ⟨e⟩ := h
    obtain ⟨hfin, -, hs⟩ := CFSG.Sporadic.Mathieu.fam_m23_simplicity
    have : Finite (NativeSporadic.Carrier .M23) := hfin
    exact ⟨@MulEquiv.isSimpleGroup _ _ _ _ hs e, C10KH.not_list701Excl (Or.inl rfl)
      ((Nat.card_congr e.toEquiv).trans card_nativeM23_1522)⟩
  · obtain ⟨e⟩ := h
    obtain ⟨-, -, hs⟩ := CFSG.Sporadic.J4.fam_j4_simplicity
    exact ⟨@MulEquiv.isSimpleGroup _ _ _ _ hs e, C10KH.not_list701Excl (Or.inr rfl)
      ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J4.card_J4)⟩

end CFSG.Quasithin.Vol2.Ch11.SecE
