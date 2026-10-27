module

public import CFSG.Quasithin.EmptyFaithful.Gold14610CmpGen
public import CFSG.Quasithin.EmptyFaithful.S146F3
public import CFSG.Quasithin.Background.I4Recognition
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.Gold14610

open CFSG.Assembly.LowTwoRank

theorem exists_ne_one_of_card {A : Type} [Group A] [Finite A] (h : 1 < Nat.card A) :
    ∃ a : A, a ≠ 1 := by
  have := Finite.one_lt_card_iff_nontrivial.mp h
  exact exists_ne 1

theorem nonempty_sl3_equiv_psl27 :
    Nonempty (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) := by
  obtain ⟨e⟩ := I4.nonempty_psl3_two_equiv_psl2_seven
  let e₁ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq
      CFSG.LocalAnalysis.ComponentInitial.center_SL_three_zmod_two_eq_bot).trans
      QuotientGroup.quotientBot
  exact ⟨e₁.symm.trans e⟩

theorem g_ge_two {Q Y A F : Type} [Group Q] [Finite Q] [Group Y]
    [Group A] [Field F] [Fintype F] {n : ℕ} (hn : 2 ≤ n) (hq : CFSG.IsQuasisimple Q)
    (hY : F618Core Y) (hext : CentralExt3 Q Y) (π : Q →* A) (hπ : Function.Surjective π)
    (hF : Fintype.card F = 2 ^ n) (e : A ≃* ↥(StatedSL 3 F)) : False := by
  have hFc : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have hA : Nat.card A = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
    rw [Nat.card_congr e.toEquiv, A38c7.card_statedSL_three, hFc]
  have : Finite A := Finite.of_surjective π hπ
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hnt : ∃ a : A, a ≠ 1 := by
    refine exists_ne_one_of_card ?_
    rw [hA]
    have h1 : 64 ≤ (2 ^ n) ^ 3 := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left h4 3
    have h2 : 1 ≤ ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) :=
      Nat.mul_pos (by have := Nat.pow_le_pow_left h4 2; omega)
        (by have := Nat.pow_le_pow_left h4 3; omega)
    calc 1 < 64 := by norm_num
      _ ≤ (2 ^ n) ^ 3 * 1 := by omega
      _ ≤ _ := Nat.mul_le_mul_left _ h2
  refine false_of_surj hq hY hext π hπ hnt ?_
  by_cases h3 : 3 ≤ n
  · refine Or.inl ⟨3 * n, by omega, ?_⟩
    rw [hA, show 3 * n = n * 3 by ring, pow_mul]
    exact Dvd.intro _ rfl
  · obtain rfl : n = 2 := by omega
    right
    rw [hA]
    norm_num

theorem h_four {Q Y A : Type} [Group Q] [Finite Q] [Group Y]
    [Group A] (hq : CFSG.IsQuasisimple Q) (hY : F618Core Y) (hext : CentralExt3 Q Y)
    (π : Q →* A) (hπ : Function.Surjective π) (e : A ≃* ↥(StatedSL 4 (ZMod 2))) : False := by
  have hA : Nat.card A = 20160 := by
    rw [Nat.card_congr e.toEquiv, Vol2.Ch10.SecA.card_statedSL,
      Vol2.Ch10.SecA.card_SL_four_of_two (K := ZMod 2) (by simp)]
  have : Finite A := Finite.of_surjective π hπ
  refine false_of_surj hq hY hext π hπ (exists_ne_one_of_card (by omega)) ?_
  right
  rw [hA]
  norm_num

theorem h_five {Q Y A : Type} [Group Q] [Finite Q] [Group Y]
    [Group A] (hq : CFSG.IsQuasisimple Q) (hY : F618Core Y) (hext : CentralExt3 Q Y)
    (π : Q →* A) (hπ : Function.Surjective π) (e : A ≃* ↥(StatedSL 5 (ZMod 2))) : False := by
  have hA : Nat.card A = 9999360 := by
    rw [Nat.card_congr e.toEquiv, Vol2.Ch10.SecA.card_statedSL,
      Vol2.Ch10.SecA.card_SL_five_of_two (K := ZMod 2) (by simp)]
  have : Finite A := Finite.of_surjective π hπ
  refine false_of_surj hq hY hext π hπ (exists_ne_one_of_card (by omega)) ?_
  left
  exact ⟨10, by norm_num, by rw [hA]; norm_num⟩

theorem g_one {Q Y A F : Type} [Group Q] [Finite Q] [Group Y]
    [Group A] [Field F] [Fintype F] (hq : CFSG.IsQuasisimple Q) (hY : F618Core Y)
    (hext : CentralExt3 Q Y) (π : Q →* A) (hπ : Function.Surjective π)
    (hF : Fintype.card F = 2) (e : A ≃* ↥(StatedSL 3 F)) :
    Nat.card Q = 168 ∧ Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  have hFc : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hF]
  have hA : Nat.card A = 168 := by
    rw [Nat.card_congr e.toEquiv, A38c7.card_statedSL_three, hFc]
    norm_num
  have : Finite A := Finite.of_surjective π hπ
  let ε : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by rw [hF, ZMod.card])
  let eA : A ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    e.trans ((specialLinearGroupEquivStatedSL 3 F).symm.trans (slMulEquivOfRingEquiv ε 3))
  obtain ⟨eP⟩ := nonempty_sl3_equiv_psl27
  let φ : Q →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) :=
    (eA.trans eP).toMonoidHom.comp π
  have hφ : Function.Surjective φ := (eA.trans eP).surjective.comp hπ
  have hnt : ∃ k : Q, φ k ≠ 1 := by
    obtain ⟨a, ha⟩ := exists_ne_one_of_card (A := A) (by omega)
    obtain ⟨q, rfl⟩ := hπ a
    exact ⟨q, fun h => ha ((eA.trans eP).injective (h.trans (map_one _).symm))⟩
  have hZ : φ.ker ≤ Subgroup.center Q :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq hnt
  have : Group.IsPerfect Q := hq.1
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hle : Nat.card φ.ker ≤ 2 :=
    card_ker_le_two_psl_two_odd (p := 7) (f := 1) (by norm_num) le_rfl (by simp)
      (by norm_num) φ hφ hZ
  have hker : φ.ker = π.ker := MonoidHom.ker_comp_of_injective π _ (eA.trans eP).injective
  rw [hker] at hle
  have hcard := card_eq_ker_mul π hπ
  have hpos : 0 < Nat.card π.ker := Nat.card_pos
  have h1 : Nat.card π.ker = 1 := by
    by_contra hne
    have h2 : Nat.card π.ker = 2 := by omega
    exact false_of_card hY hext (N := 336) (by rw [← hcard, h2, hA]) excl_336
  have hbot : π.ker = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
  have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hbot
  exact ⟨by rw [← hcard, h1, hA], ⟨(MulEquiv.ofBijective π ⟨hinj, hπ⟩).trans eA⟩⟩

end CFSG.Quasithin.Gold14610
