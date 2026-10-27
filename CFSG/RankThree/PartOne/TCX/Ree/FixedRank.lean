module

public import CFSG.RankThree.PartOne.TCX.RankInterface
public import CFSG.RankThree.PartOne.K128.F4Syl
public import CFSG.RankThree.PartOne.S11d.FieldKFactsClosed
import CFSG.RankThree.PartOne.K128.SylowShapeRank
public import CFSG.RankThree.PartOne.KLC.PRankTwo
public import CFSG.RankThree.PartOne.TCX.Interface

public section

namespace CFSG.RankThree.PartOne.TCX.Ree

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix
  CFSG.RankThree.PartOne.K128 CFSG.RankThree.PartOne.KLC CFSG.RankThree.PartOne.KLR
  CFSG.RankThree.PartOne.KEXC CFSG.RankThree.LargeReeOrder CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.K1214
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

open CFSG.RankThree.PartOne.TCX

section Shape

theorem two_le_pRank_of_sylowShape {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) {X : Type*} [Group X]
    [Finite X] (h : SylowShape p 2 e X) : 2 ≤ CFSG.pRank p X :=
  CFSG.RankThree.PartOne.K1214.two_le_pRank_of_sylowShape_sq hp he h

end Shape

section Main


theorem fixedRankT_twistedF4 : FixedRankT .twistedF4 := by
  intro T _ _ p hp hp5 hLR hpr n f₀ hf₀ hM α hαp hαinn hLRA hX
  have : Fact p.Prime := ⟨hp⟩
  have hnd1 : ¬ (p : ℤ) ∣ 1 := fun h =>
    hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h)
  have hF : FixedFacts p α := tagFixedFacts_twistedF4 largeReeTitsNonLocalized T p hp hp5 hLR n f₀
    hf₀ hM α hαp hαinn hLRA hX α hαp hαinn hLRA ⟨1, hnd1, by simp [(innerAut T).one_mem]⟩
  obtain ⟨hn0, hRee⟩ := ree_of_lieModel hM
  subst hn0
  obtain ⟨a, K, _, _, _, ha, hfa, hK, ⟨eT⟩⟩ := exists_gamma_of_model hRee
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hpr' : 2 ≤ CFSG.pRank p (ReeTag.F4.reeGamma K a) := by
    have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
    have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
    rw [← pRank_eq_of_mulEquiv_of_one_lt hp.one_lt eT]
    exact hpr
  obtain ⟨d, hd, hpd⟩ := ree_class hK' hp hp5 hpr'
  have hq1' : 1 ≤ 2 ^ f₀ := Nat.one_le_two_pow
  have hq2' : 2 ≤ 2 ^ f₀ := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) hf₀
  have hQ : 2 ^ (2 * a + 1) = (2 ^ f₀) ^ p := by rw [← hfa, mul_comm, pow_mul]
  have hpdq : p ∣ phiF4 d (2 ^ f₀) := dvd_phiF4_of_dvd_pow hp hq1' hd (by rw [← hQ]; exact hpd)
  have hne : phiF4 d (2 ^ f₀) ≠ 0 := phiF4_ne_zero hd hq2'
  have hone : 1 ≤ (phiF4 d (2 ^ f₀)).factorization p :=
    (hp.dvd_iff_one_le_factorization hne).1 hpdq
  rcases hX with hN | ⟨-, -, hf1, hTits⟩
  ·
    obtain ⟨-, hRee'⟩ := ree_of_lieModel hN
    obtain ⟨a', K', _, _, _, ha', hfa', hK'', ⟨e'⟩⟩ := exists_gamma_of_model hRee'
    have hK2 : Nat.card K' = 2 ^ (2 * a' + 1) := by rw [hK'', hfa']
    have eN : ↥(fixRes α) ≃* ReeTag.F4.reeGamma K' a' := (fixResEquivQuotient hF).trans e'
    have hpdq' : p ∣ phiF4 d (2 ^ (2 * a' + 1)) := by rw [← hfa']; exact hpdq
    have hshN := sylowShape_ree hK2 hd hp hp5 hpdq'
    rw [← hfa'] at hshN
    rw [pRank_congr_mulEquiv eN hp.one_lt]
    have : Finite (ModGL ReeTag.F4.tag K') := finite_modGL
    have : Finite (ReeTag.F4.reeGamma K' a') := Subtype.finite
    exact two_le_pRank_of_sylowShape hp hone hshN
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
    exact two_le_pRank_of_sylowShape (by norm_num) le_rfl hshN

end Main

end CFSG.RankThree.PartOne.TCX.Ree
