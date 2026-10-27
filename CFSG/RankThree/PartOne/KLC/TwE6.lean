module

public import CFSG.RankThree.PartOne.KLC.EigTwE6
public import CFSG.RankThree.PartOne.KLC.Degenerate
public import CFSG.RankThree.PartOne.KLC.E6
public import CFSG.RankThree.PartOne.S11c.Sec66TModelsTw
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.RankThree.PartOne.KE.CTTwistedEight
public import CFSG.RankThree.PartOne.KE.CTTwistedTwelve
public import CFSG.RankThree.PartOne.KE.CTTwistedEighteen

public section

namespace CFSG.RankThree.PartOne.KLC

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix
open CFSG.Assembly.LowTwoRank (StatedLieTag)

open CFSG.RankThree.Chevalley (exhaustionPhi
  exact_E_type_and_triality_cross_prime_factor_exhaustion)


section Odd

theorem odd_twE6_twelve {q : ℕ} (hq : Even q) (hq2 : 2 ≤ q) :
    Odd ((q ^ 4 - q ^ 2 + 1) * (q ^ 2 - q + 1)) := by
  refine Nat.odd_mul.2 ⟨?_, ?_⟩
  · have h1 : 2 ∣ q := even_iff_two_dvd.1 hq
    have h2 : 2 ∣ q ^ 2 := dvd_pow h1 (by norm_num)
    have h4 : 2 ∣ q ^ 4 := dvd_pow h1 (by norm_num)
    have l : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    rw [Nat.odd_iff]
    omega
  · have h1 : 2 ∣ q := even_iff_two_dvd.1 hq
    have h2 : 2 ∣ q ^ 2 := dvd_pow h1 (by norm_num)
    have l : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
    rw [Nat.odd_iff]
    omega

theorem odd_twE6_eighteen {q : ℕ} (hq : Even q) (hq2 : 2 ≤ q) :
    Odd (q ^ 6 - q ^ 3 + 1) := by
  have h1 : 2 ∣ q := even_iff_two_dvd.1 hq
  have h3 : 2 ∣ q ^ 3 := dvd_pow h1 (by norm_num)
  have h6 : 2 ∣ q ^ 6 := dvd_pow h1 (by norm_num)
  have l : q ^ 3 ≤ q ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  rw [Nat.odd_iff]
  omega

end Odd

section Main


@[expose] def TwistedE6TenLayer : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (p : ℕ), p.Prime → 5 < p → LocalRankLeTwo p T →
    CFSG.pRank p T = 1 → ∀ f₀ : ℕ, 1 ≤ f₀ → LieModel T .twistedE6 0 2 (p * f₀) →
    ∀ α : MulAut T, α ^ p = 1 → α ∉ innerAut T → LocalRankAut p T α →
      FixModel .twistedE6 0 f₀ α →
      (p : ℤ) ∣ (exhaustionPhi 10).eval ((2 : ℤ) ^ (p * f₀)) →
      ∀ x : T, x ^ p = 1 → x ≠ 1 → α x = x →
        LayerConclusion p α (Subgroup.centralizer ({x} : Set T))

theorem lieGoodComponentFixT_twistedE6_of_layer (h10 : TwistedE6TenLayer) :
    LieGoodComponentFixT .twistedE6 := by
  intro T _ _ p hp hp5 hLR hpr n f₀ hf₀ hM α hαp hαinn hLRA hX x hxp hx1 hαx y hy2 hy1 hxy
  have : Fact p.Prime := ⟨hp⟩
  have hf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  obtain ⟨hn0, hCEM⟩ := lieModel_twistedE6_iff.mp hM
  subst hn0
  obtain ⟨K, hKf, hKfin, σ, hKcard, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .E6 Nat.prime_two hf hCEM.2
  have hK : Nat.card K = (2 ^ (p * f₀)) ^ 2 := hKcard
  have : Finite (twistedE6RootGroup K σ) := Finite.of_equiv T e.toEquiv
  have hdvd : p ∣ Nat.card T := by
    have := orderOf_dvd_natCard x
    rwa [orderOf_eq_prime hxp hx1] at this
  have hq1 : 1 ≤ 2 ^ (p * f₀) := Nat.one_le_two_pow
  have hq2 : 2 ≤ 2 ^ (p * f₀) := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (p * f₀) := Nat.pow_le_pow_right (by norm_num) hf
  have hQ2 : Even (2 ^ (p * f₀)) := Nat.even_pow.2 ⟨even_two, by omega⟩
  have hx' : orderOf (e x) = p := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hxp hx1
  have hy2' : (e y) ^ 2 = 1 := by rw [← map_pow, hy2, map_one]
  have hy1' : e y ≠ 1 := fun h => hy1 (e.injective (by rw [h, map_one]))
  have hxy' : e x * e y = e y * e x := by rw [← map_mul, ← map_mul, hxy]
  have hpr' : CFSG.pRank p (twistedE6RootGroup K σ) = 1 := by
    rw [← pRank_congr_mulEquiv e hp.one_lt]
    exact hpr
  obtain ⟨m, hm, hpm⟩ := ((exact_E_type_and_triality_cross_prime_factor_exhaustion hp (by omega)
    (by omega) hCEM).1 hdvd).2.2.2.1 rfl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  have hex : ∀ e' : ℕ, (e' = 1 ∨ e' = 2 ∨ e' = 3 ∨ e' = 4 ∨ e' = 6) →
      (p : ℤ) ∣ (exhaustionPhi e').eval ((2 ^ (p * f₀) : ℕ) : ℤ) → False := fun e' he' h => by
    have := two_le_pRank_twistedE6_of_sector Nat.prime_two hf K hK σ hσ hp hp5 (by omega) he' h
    omega
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hex 1 (by simp) hpm).elim
  · exact (hex 2 (by simp) hpm).elim
  · exact (hex 3 (by simp) hpm).elim
  · exact (hex 4 (by simp) hpm).elim
  · exact (hex 6 (by simp) hpm).elim
  ·
    exfalso
    obtain ⟨-, -, k, hc⟩ := twisted_E6_eight_cyclic_sylow Nat.prime_two hf K hK σ hσ hp (by omega)
      hpm
    exact not_commute_involution_of_cyclicSylow hc (odd_E6_eight hQ2 hq2) hx' hy2' hy1' hxy'
  ·
    by_cases hp5' : 5 < p
    · refine h10 T p hp hp5' hLR hpr f₀ hf₀ hM α hαp hαinn hLRA hX ?_ x hxp hx1 hαx
      simpa using hpm
    · exfalso
      obtain rfl : p = 5 := by omega
      have h5 : (5 : ℤ) ∣ (2 ^ (5 * f₀) : ℤ) + 1 := by
        refine dvd_add_one_of_dvd_phi_ten ?_
        simpa using hpm
      exact hex 2 (by simp) (by simpa [exhaustionPhi] using h5)
  ·
    exfalso
    obtain ⟨-, -, k, hc⟩ := twisted_E6_twelve_cyclic_sylow Nat.prime_two hf K hK σ hσ hp (by omega)
      hpm
    exact not_commute_involution_of_cyclicSylow hc (odd_twE6_twelve hQ2 hq2) hx' hy2' hy1' hxy'
  ·
    exfalso
    obtain ⟨-, -, k, hc⟩ := twisted_E6_eighteen_cyclic_sylow Nat.prime_two hf K hK σ hσ hp
      (by omega) hpm
    exact not_commute_involution_of_cyclicSylow hc (odd_twE6_eighteen hQ2 hq2) hx' hy2' hy1' hxy'

end Main

end CFSG.RankThree.PartOne.KLC
