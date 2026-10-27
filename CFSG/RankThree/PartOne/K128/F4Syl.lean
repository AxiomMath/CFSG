module

public import CFSG.RankThree.PartOne.K128.TitsShape
public import CFSG.RankThree.PartOne.K128.FixCenter
public import CFSG.RankThree.PartOne.KF.F128Syl
public import CFSG.RankThree.PartOne.S11d.PSLRank

public section

namespace CFSG.RankThree.PartOne.K128

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KEXC CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.LargeReeOrder
open CFSG.Assembly (evenRank)

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)


theorem ree_of_lieModel {T : Type} [Group T] {n f : ℕ} (hM : LieModel T .twistedF4 n 2 f) :
    n = 0 ∧ ReeTitsModel T .twistedF4 2 f :=
  CFSG.Blueprint.LieModel.reeTitsModel hM (by decide)

theorem tits_of_lieModel {T : Type} [Group T] {n f : ℕ} (hM : LieModel T .Tits n 2 f) :
    n = 0 ∧ ReeTitsModel T .Tits 2 f :=
  CFSG.Blueprint.LieModel.reeTitsModel hM (by decide)

section Main


theorem ree_class {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hrk : 2 ≤ CFSG.pRank p (ReeTag.F4.reeGamma K a)) :
    ∃ d, (d = 1 ∨ d = 2 ∨ d = 4) ∧ p ∣ phiF4 d (2 ^ (2 * a + 1)) := by
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hpΓ : p ∣ Nat.card (ReeTag.F4.reeGamma K a) := dvd_card_of_pRank_pos hp (by omega)
  rcases (large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK).2 p hp (by omega)
    hpΓ with h1 | h2 | h3 | h4 | h5
  · exact ⟨1, Or.inl rfl, h1⟩
  · exact ⟨2, Or.inr (Or.inl rfl), h2⟩
  · exact ⟨4, Or.inr (Or.inr rfl), h3⟩
  · exact absurd (pRank_le_one_ree_phi6 hK hp hp5 h4) (by omega)
  · exact absurd (pRank_le_one_ree_phi12 hK hp hp5 h5) (by omega)


theorem kf128SylTag_twistedF4_of : KF128SylTag .twistedF4 := by
  intro J _ _ hq he T _ _ π hπ hker p hp hp5 hZ hLR2 n f₀ hf₀ hM α hαp hinn hLRA hFix hF hrk
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hn0, hRee⟩ := ree_of_lieModel hM
  subst hn0
  obtain ⟨a, K, _, _, _, ha, hfa, hK, ⟨eT⟩⟩ := exists_gamma_of_model hRee
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hpr : 2 ≤ CFSG.pRank p (ReeTag.F4.reeGamma K a) := by
    have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
    have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
    rw [← pRank_eq_of_mulEquiv_of_one_lt hp.one_lt eT]
    exact hrk
  obtain ⟨d, hd, hpd⟩ := ree_class hK' hp hp5 hpr
  have hshT := sylowShape_ree hK' hd hp hp5 hpd
  have hq1' : 1 ≤ 2 ^ f₀ := Nat.one_le_two_pow
  have hq2' : 2 ≤ 2 ^ f₀ := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) hf₀
  have hpq' : ¬ p ∣ 2 ^ f₀ := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    omega
  have hQ : 2 ^ (2 * a + 1) = (2 ^ f₀) ^ p := by rw [← hfa, mul_comm, pow_mul]
  have hpdq : p ∣ phiF4 d (2 ^ f₀) := dvd_phiF4_of_dvd_pow hp hq1' hd (by rw [← hQ]; exact hpd)
  have hne : phiF4 d (2 ^ f₀) ≠ 0 := phiF4_ne_zero hd hq2'
  have hone : 1 ≤ (phiF4 d (2 ^ f₀)).factorization p :=
    (hp.dvd_iff_one_le_factorization hne).1 hpdq
  have hlte := factorization_phiF4_pow hp hp5 hq2' hpq' hd hpdq
  rw [← hQ] at hlte
  rcases hFix with hN | ⟨-, -, hf1, hTits⟩
  ·
    obtain ⟨-, hRee'⟩ := ree_of_lieModel hN
    obtain ⟨a', K', _, _, _, ha', hfa', hK'', ⟨e'⟩⟩ := exists_gamma_of_model hRee'
    have hK2 : Nat.card K' = 2 ^ (2 * a' + 1) := by rw [hK'', hfa']
    have eN : ↥(fixRes α) ≃* ReeTag.F4.reeGamma K' a' := (fixResEquivQuotient hF).trans e'
    have hpdq' : p ∣ phiF4 d (2 ^ (2 * a' + 1)) := by rw [← hfa']; exact hpdq
    have hshN := sylowShape_ree hK2 hd hp hp5 hpdq'
    rw [← hfa'] at hshN
    refine ⟨(phiF4 d (2 ^ (2 * a + 1))).factorization p, by omega,
      SylowShape.of_mulEquiv eT hshT, ?_⟩
    have he1 : (phiF4 d (2 ^ (2 * a + 1))).factorization p - 1 =
        (phiF4 d (2 ^ f₀)).factorization p := by omega
    rw [he1]
    exact SylowShape.of_mulEquiv eN hshN
  ·
    subst hf1
    obtain ⟨-, hRee'⟩ := tits_of_lieModel hTits
    have hd4 : d = 4 ∧ p = 5 := by
      rcases hd with rfl | rfl | rfl
      · simp only [phiF4] at hpdq
        have := Nat.le_of_dvd (by norm_num) hpdq
        omega
      · simp only [phiF4] at hpdq
        have := Nat.le_of_dvd (by norm_num) hpdq
        omega
      · simp only [phiF4] at hpdq
        have h5 : p ∣ 5 := by simpa using hpdq
        exact ⟨rfl, (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h5⟩
    obtain ⟨rfl, rfl⟩ := hd4
    have hshN : SylowShape 5 2 1 ↥(fixRes α) :=
      SylowShape.of_mulEquiv (fixResEquivQuotient hF) (sylowShape_five_of_tits_model hRee')
    have hv1 : (phiF4 4 (2 ^ 1)).factorization 5 = 1 := by
      have h5 : phiF4 4 (2 ^ 1) = 5 := by norm_num [phiF4]
      rw [h5]
      exact Nat.Prime.factorization_self (by norm_num)
    refine ⟨(phiF4 4 (2 ^ (2 * a + 1))).factorization 5, by omega,
      SylowShape.of_mulEquiv eT hshT, ?_⟩
    have he1 : (phiF4 4 (2 ^ (2 * a + 1))).factorization 5 - 1 = 1 := by omega
    rw [he1]
    exact hshN

end Main

set_option linter.unusedSectionVars false

theorem kf128SylTag_twistedF4 : KF128SylTag .twistedF4 := by
  exact kf128SylTag_twistedF4_of

end CFSG.RankThree.PartOne.K128
