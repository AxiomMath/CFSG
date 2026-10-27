module

public import CFSG.GroupTheory.WeirSylow.Orthogonal
public import CFSG.RankThree.PartOne.KF.F128Cls

public section

namespace CFSG.RankThree.PartOne.TCO

open Module QuadraticMap CFSG.LieType.Universal.Spin CFSG.GroupTheory.WeirSylow
open CFSG.Assembly.LowTwoRank (StatedSp)

theorem orthMinusFour_sylow_cyclic {K : Type} [Field K] [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : ¬ p ∣ Nat.card K) (hr : (Nat.card K : ZMod p) ^ 2 ≠ 1) :
    ∀ P : Sylow p (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c)), IsCyclic P := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let _ : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = Nat.card K := Nat.card_eq_fintype_card.symm
  intro P
  have hdim : finrank K (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) = 2 * 4 :=
    finrank_quadMinus_space (m := 4) (by norm_num)
  have hnd := nondegenerate_polarBilin_quadMinus_of_finite 4 K hirr
  obtain ⟨-, T, hT3, hTs⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (K := K) (n := 4)
    le_rfl hirr
  have hmin : IsMinusType (quadMinus 4 K b c) :=
    ⟨⟨T, by rw [hT3, hdim], hTs⟩, not_isPlusType_quadMinus (by norm_num) hirr⟩
  obtain ⟨h1, h2, -⟩ := sylow_orthogonal_even (hp.odd_of_ne_two hp2) (by rwa [hcardK])
    (n := 4) (by norm_num) hdim (quadMinus 4 K b c) hnd (ε := -1) (Or.inr ⟨rfl, hmin⟩) P
  set r : ZMod p := (Nat.card K : ZMod p) with hrdef
  have hr0 : r ≠ 0 := by
    rw [hrdef, Ne, ZMod.natCast_eq_zero_iff]
    exact hpK
  have hp1 : (1 : ZMod p) ≠ -1 := by
    have : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
    exact (ZMod.neg_one_ne_one).symm
  have hcastK : ((Fintype.card K : ℕ) : ZMod p) = r := by rw [hcardK, hrdef]
  have he : ¬ orderOf r ∣ 2 := by
    intro hd
    exact hr (orderOf_dvd_iff_pow_eq_one.1 hd)
  by_cases h4 : r ^ 4 = 1
  ·
    have hnd2 : ¬ (p : ℤ) ∣ (Fintype.card K : ℤ) ^ 4 - (-1) := by
      intro hd
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hd
      push_cast at hd
      rw [hcastK, h4] at hd
      exact hp1 (sub_eq_zero.mp hd)
    have he4 : orderOf r ∣ 4 := orderOf_dvd_iff_pow_eq_one.2 h4
    have he' : orderOf r = 4 := by
      have hle := Nat.le_of_dvd (by norm_num) he4
      have : orderOf r = 0 ∨ orderOf r = 1 ∨ orderOf r = 2 ∨ orderOf r = 3 ∨ orderOf r = 4 := by
        omega
      rcases this with h0 | h1 | h2 | h3 | h4'
      · rw [h0] at he4; exact absurd he4 (by decide)
      · rw [h1] at he; exact absurd (by decide) he
      · rw [h2] at he; exact absurd (by decide) he
      · rw [h3] at he4; exact absurd he4 (by decide)
      · exact h4'
    obtain ⟨P'⟩ : Nonempty (Sylow p (StatedSp (4 - 1) K)) := inferInstance
    have hcyc : ∀ Q' : Sylow p (StatedSp (4 - 1) K), IsCyclic Q' :=
      sylow_cyclic_Sp (n := 4 - 1) hp hp2 hpK (by
        rw [← hrdef, he']
        decide)
    obtain ⟨e'⟩ := h2 hnd2 P'
    exact (MulEquiv.isCyclic e').2 (hcyc P')
  ·
    have hnd1 : ¬ (p : ℤ) ∣ (Fintype.card K : ℤ) ^ 4 + (-1) := by
      intro hd
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hd
      push_cast at hd
      rw [hcastK] at hd
      exact h4 (by linear_combination hd)
    have he4 : ¬ orderOf r ∣ 4 := fun hd => h4 (orderOf_dvd_iff_pow_eq_one.1 hd)
    obtain ⟨P'⟩ : Nonempty (Sylow p (StatedSp 4 K)) := inferInstance
    have hcyc : ∀ Q' : Sylow p (StatedSp 4 K), IsCyclic Q' :=
      sylow_cyclic_Sp (n := 4) hp hp2 hpK (by
        rw [← hrdef]
        by_cases hle : orderOf r ≤ 4
        · have : orderOf r = 0 ∨ orderOf r = 1 ∨ orderOf r = 2 ∨ orderOf r = 3 ∨
              orderOf r = 4 := by omega
          rcases this with h0 | h1 | h2 | h3 | h4'
          · rw [h0]; simp
          · rw [h1] at he4; exact absurd (by decide) he4
          · rw [h2] at he4; exact absurd (by decide) he4
          · rw [h3]; decide
          · rw [h4'] at he4; exact absurd (by decide) he4
        · have : (if Even (orderOf r) then 2 * 4 else 4) < orderOf r * 2 := by
            split_ifs <;> omega
          have := Nat.div_lt_of_lt_mul this
          omega)
    obtain ⟨e'⟩ := h1 hnd1 P'
    exact (MulEquiv.isCyclic e').2 (hcyc P')

theorem pRank_le_one_orthMinusFour {K : Type} [Field K] [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : ¬ p ∣ Nat.card K) (hr : (Nat.card K : ZMod p) ^ 2 ≠ 1) {H : Type} [Group H] [Finite H]
    (ι : H →* TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c))
    (hι : Function.Injective ι) : CFSG.pRank p H ≤ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c)) := by
    have : Finite (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) := inferInstance
    exact Finite.of_injective (fun g : TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c) =>
      (g : (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) → (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K)))
      fun g₁ g₂ h => Subtype.ext (LinearEquiv.ext fun v => congrFun h v)
  exact pRank_le_one_of_injective ι hι (orthMinusFour_sylow_cyclic hirr hp hp2 hpK hr)

end CFSG.RankThree.PartOne.TCO
