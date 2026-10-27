module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveRootRankL2
import CFSG.LocalAnalysis.WeakClosure81.EightFiveRootRankDihedral
import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitSL2

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic

private theorem trace_ne_zero_of_orderOf_eq_card_add_one {F : Type} [Field F] [Finite F]
    [CharP F 2] {x : Matrix.SpecialLinearGroup (Fin 2) F} (hx : orderOf x = Nat.card F + 1) :
    (x : Matrix (Fin 2) (Fin 2) F) 0 0 + (x : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
  intro hτ
  have htr : Matrix.trace (x : Matrix (Fin 2) (Fin 2) F) = 0 := by
    rw [Matrix.trace_fin_two]
    exact hτ
  have hsq : x ^ 2 = 1 := by
    refine Subtype.ext ?_
    rw [CFSG.SeitzReduction.F4Pilot.sq_eq_trace_smul_sub_one, htr,
      Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CharTwo.neg_eq]
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  rw [hx] at hdvd
  have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

private theorem utriElt_mul_mul_utriElt_eq_inv {F : Type} [Field F] [CharP F 2]
    (x : Matrix.SpecialLinearGroup (Fin 2) F) {s : F}
    (hs : s * (x : Matrix (Fin 2) (Fin 2) F) 1 0 =
      (x : Matrix (Fin 2) (Fin 2) F) 0 0 + (x : Matrix (Fin 2) (Fin 2) F) 1 1) :
    CFSG.CGT.Timmesfeld75.utriElt s * x * CFSG.CGT.Timmesfeld75.utriElt s = x⁻¹ := by
  have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
  apply CFSG.CGT.Timmesfeld75.sl2_ext
  · simp only [CFSG.CGT.Timmesfeld75.mul_apply_00, CFSG.CGT.Timmesfeld75.mul_apply_01,
      CFSG.CGT.Timmesfeld75.mul_apply_10, CFSG.CGT.Timmesfeld75.mul_apply_11,
      CFSG.CGT.Timmesfeld75.utriElt_apply_00, CFSG.CGT.Timmesfeld75.utriElt_apply_01,
      CFSG.CGT.Timmesfeld75.utriElt_apply_10, CFSG.CGT.Timmesfeld75.utriElt_apply_11,
      CFSG.CGT.Timmesfeld75.inv_apply_00, one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero]
    linear_combination hs + (x : Matrix (Fin 2) (Fin 2) F) 0 0 * htwo
  · simp only [CFSG.CGT.Timmesfeld75.mul_apply_00, CFSG.CGT.Timmesfeld75.mul_apply_01,
      CFSG.CGT.Timmesfeld75.mul_apply_10, CFSG.CGT.Timmesfeld75.mul_apply_11,
      CFSG.CGT.Timmesfeld75.utriElt_apply_00, CFSG.CGT.Timmesfeld75.utriElt_apply_01,
      CFSG.CGT.Timmesfeld75.utriElt_apply_10, CFSG.CGT.Timmesfeld75.utriElt_apply_11,
      CFSG.CGT.Timmesfeld75.inv_apply_01, one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero]
    linear_combination s * hs +
      (s * ((x : Matrix (Fin 2) (Fin 2) F) 0 0 + (x : Matrix (Fin 2) (Fin 2) F) 1 1) +
        (x : Matrix (Fin 2) (Fin 2) F) 0 1) * htwo
  · simp only [CFSG.CGT.Timmesfeld75.mul_apply_00, CFSG.CGT.Timmesfeld75.mul_apply_01,
      CFSG.CGT.Timmesfeld75.mul_apply_10, CFSG.CGT.Timmesfeld75.mul_apply_11,
      CFSG.CGT.Timmesfeld75.utriElt_apply_00, CFSG.CGT.Timmesfeld75.utriElt_apply_01,
      CFSG.CGT.Timmesfeld75.utriElt_apply_10, CFSG.CGT.Timmesfeld75.utriElt_apply_11,
      CFSG.CGT.Timmesfeld75.inv_apply_10, one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero]
    rw [CharTwo.neg_eq]
  · simp only [CFSG.CGT.Timmesfeld75.mul_apply_00, CFSG.CGT.Timmesfeld75.mul_apply_01,
      CFSG.CGT.Timmesfeld75.mul_apply_10, CFSG.CGT.Timmesfeld75.mul_apply_11,
      CFSG.CGT.Timmesfeld75.utriElt_apply_00, CFSG.CGT.Timmesfeld75.utriElt_apply_01,
      CFSG.CGT.Timmesfeld75.utriElt_apply_10, CFSG.CGT.Timmesfeld75.utriElt_apply_11,
      CFSG.CGT.Timmesfeld75.inv_apply_11, one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero]
    linear_combination hs + (x : Matrix (Fin 2) (Fin 2) F) 1 1 * htwo

private theorem exists_involution_mul_mul_eq_inv {F : Type} [Field F] [CharP F 2]
    {x : Matrix.SpecialLinearGroup (Fin 2) F}
    (hc : (x : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0)
    (hτ : (x : Matrix (Fin 2) (Fin 2) F) 0 0 + (x : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0) :
    ∃ w : Matrix.SpecialLinearGroup (Fin 2) F, w * w = 1 ∧ w ≠ 1 ∧ w * x * w = x⁻¹ := by
  let s : F := ((x : Matrix (Fin 2) (Fin 2) F) 0 0 + (x : Matrix (Fin 2) (Fin 2) F) 1 1) /
    ((x : Matrix (Fin 2) (Fin 2) F) 1 0)
  have hs0 : s ≠ 0 := div_ne_zero hτ hc
  have hs : s * (x : Matrix (Fin 2) (Fin 2) F) 1 0 =
      (x : Matrix (Fin 2) (Fin 2) F) 0 0 + (x : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    dsimp only [s]
    exact div_mul_cancel₀ _ hc
  refine ⟨CFSG.CGT.Timmesfeld75.utriElt s, ?_, ?_, utriElt_mul_mul_utriElt_eq_inv x hs⟩
  · rw [← CFSG.CGT.Timmesfeld75.utriElt_add s s, CharTwo.add_self_eq_zero,
      CFSG.CGT.Timmesfeld75.utriElt_zero]
  · intro h
    have h01 : s = 0 := by
      have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
        (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
      simpa [CFSG.CGT.Timmesfeld75.utriElt_apply_01] using this
    exact hs0 h01

theorem exists_orderOf_eq_card_add_one_mul_mul_eq_inv {F : Type} [Field F] [Finite F]
    [CharP F 2] {t : Matrix.SpecialLinearGroup (Fin 2) F} (ht : t * t = 1) (ht1 : t ≠ 1) :
    ∃ y : Matrix.SpecialLinearGroup (Fin 2) F, orderOf y = Nat.card F + 1 ∧ t * y * t = y⁻¹ := by
  obtain ⟨x, hx⟩ := CFSG.SeitzReduction.F4Pilot.exists_orderOf_eq_natCard_add_one (K := F)
  have hc : (x : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 :=
    CFSG.SeitzReduction.F4Pilot.apply_one_zero_ne_zero_of_orderOf_eq hx
  have hτ : (x : Matrix (Fin 2) (Fin 2) F) 0 0 + (x : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 :=
    trace_ne_zero_of_orderOf_eq_card_add_one hx
  obtain ⟨w, hw2, hw1, hwxw⟩ := exists_involution_mul_mul_eq_inv hc hτ
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (CFSG.CGT.Timmesfeld75.isConj_of_mul_self_eq_one ht ht1 hw2 hw1).symm
  refine ⟨g * x * g⁻¹, ?_, ?_⟩
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hx]
  · rw [← hg]
    calc (g * w * g⁻¹) * (g * x * g⁻¹) * (g * w * g⁻¹)
        = g * (w * x * w) * g⁻¹ := by group
      _ = g * x⁻¹ * g⁻¹ := by rw [hwxw]
      _ = (g * x * g⁻¹)⁻¹ := by group

private theorem three_le_modCommRank_of_orderOf_eq_nine {Y : Type} [Group Y] {F : Type}
    [AddCommGroup F] [Module (ZMod 2) F] [Finite F] {σ : Y →* LGL 2 F}
    (hσinj : Function.Injective σ) {t y : Y} (ht : t * t = 1) (hyinv : t * y * t = y⁻¹)
    (hord9 : orderOf y = 9) : 3 ≤ modCommRank (σ t) := by
  have hσt2 : σ t * σ t = 1 := by rw [← map_mul, ht, map_one]
  have hσty : σ t * σ y * σ t = (σ y)⁻¹ := by
    rw [← map_mul, ← map_mul, ← map_inv, hyinv]
  have hy9 : y ^ 9 = 1 := by rw [← hord9]; exact pow_orderOf_eq_one y
  have hy3 : y ^ 3 ≠ 1 := by
    intro h3
    have hdvd : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    rw [hord9] at hdvd
    exact absurd hdvd (by norm_num)
  have hσy9 : (σ y) ^ 9 = 1 := by rw [← map_pow, hy9, map_one]
  have hσy3 : (σ y) ^ 3 ≠ 1 := by
    intro h3
    apply hy3
    apply hσinj
    simpa using h3
  exact three_le_modCommRank_of_pow_nine hσt2 hσty hσy9 hσy3

private theorem le_modCommRank_of_orderOf_eq_two_pow_add_one {Y : Type} [Group Y] {F : Type}
    [AddCommGroup F] [Module (ZMod 2) F] [Finite F] {σ : Y →* LGL 2 F}
    (hσinj : Function.Injective σ) {n : ℕ} (hn : 2 ≤ n) (hn3 : n ≠ 3) {t y : Y}
    (ht : t * t = 1) (hyinv : t * y * t = y⁻¹) (hyord : orderOf y = 2 ^ n + 1) :
    n ≤ modCommRank (σ t) := by
  obtain ⟨p, hpp⟩ :=
    CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 2 * n) (by omega) (by omega)
  haveI : Fact p.Prime := ⟨hpp.prime⟩
  have hp2 : p ≠ 2 := hpp.ne_two (by omega)
  have hpdvd : p ∣ 2 ^ n + 1 := by
    rw [hpp.dvd_add_one_iff (by omega) n]
    refine ⟨?_, ?_⟩
    · exact dvd_refl (2 * n)
    · intro hdiv
      have hle := Nat.le_of_dvd (by omega : 0 < n) hdiv
      omega
  have horder : orderOf (2 : ZMod p) = 2 * n := by
    refine (orderOf_eq_iff (by omega)).mpr ⟨?_, ?_⟩
    · exact (CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff (p := p) (2 * n)).mp hpp.dvd
    · intro m hm hpos hm1
      exact hpp.2.2 m hpos hm
        ((CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff (p := p) m).mpr hm1)
  have hp_dvd : p ∣ orderOf y := by rw [hyord]; exact hpdvd
  have hord0 : orderOf y ≠ 0 := by rw [hyord]; exact Nat.succ_ne_zero _
  let y₀ : Y := y ^ ((2 ^ n + 1) / p)
  have hy₀ord : orderOf y₀ = p := by
    have h := orderOf_pow_orderOf_div (x := y) (n := p) hord0 hp_dvd
    rwa [hyord] at h
  have hy₀p : y₀ ^ p = 1 := by rw [← hy₀ord]; exact pow_orderOf_eq_one y₀
  have hy₀1 : y₀ ≠ 1 := by
    intro h1
    have h2 : p = 1 := by rw [← hy₀ord, h1, orderOf_one]
    have := hpp.prime.two_le
    omega
  have hy₀inv : t * y₀ * t = y₀⁻¹ := by
    have hty : MulAut.conj t y = y⁻¹ := by
      rw [MulAut.conj_apply, inv_eq_of_mul_eq_one_right ht, hyinv]
    have h1 : MulAut.conj t (y ^ ((2 ^ n + 1) / p)) =
        (y ^ ((2 ^ n + 1) / p))⁻¹ := by
      rw [map_pow, hty, inv_pow]
    simpa [y₀, MulAut.conj_apply, inv_eq_of_mul_eq_one_right ht] using h1
  have hσt2 : σ t * σ t = 1 := by rw [← map_mul, ht, map_one]
  have hσy₀inv : σ t * σ y₀ * σ t = (σ y₀)⁻¹ := by
    rw [← map_mul, ← map_mul, ← map_inv, hy₀inv]
  have hσy₀p : (σ y₀) ^ p = 1 := by rw [← map_pow, hy₀p, map_one]
  have hσy₀1 : σ y₀ ≠ 1 := by
    intro h1
    exact hy₀1 (hσinj (by simpa using h1))
  have hA := orderOf_two_le_two_mul_modCommRank (F := F) (p := p) hp2
    (s := σ t) (y := σ y₀) hσt2 hσy₀inv hσy₀p hσy₀1
  rw [horder] at hA
  omega

theorem l2IrreducibleRank_holds : L2IrreducibleRank := by
  intro Y _ n hn hY F _ _ _ σ _ t ht hσt
  haveI : Finite Y := finite_of_isL2Gp hY
  haveI : IsSimpleGroup Y := isSimpleGroup_of_isL2Gp hn hY
  have hker : σ.ker = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (σ.ker) with h | h
    · exact h
    · exfalso
      apply hσt
      have hσ1 : σ = 1 := by
        refine MonoidHom.ext fun y => ?_
        exact MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top y)
      rw [hσ1]
      simp
  have hσinj : Function.Injective σ := MonoidHom.ker_eq_bot_iff σ |>.mp hker
  have ht1 : t ≠ 1 := fun h1 => hσt (by rw [h1, map_one])
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := hY
  haveI : CharP K 2 := by
    haveI : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := n) (by
      rw [← Nat.card_eq_fintype_card, hKcard])
  have het : e t * e t = 1 := by rw [← map_mul, ht, map_one]
  have het1 : e t ≠ 1 := fun h1 => ht1 (e.injective (by simpa using h1))
  obtain ⟨y', hy'ord, hy'inv⟩ := exists_orderOf_eq_card_add_one_mul_mul_eq_inv het het1
  let y : Y := e.symm y'
  have hyord : orderOf y = 2 ^ n + 1 := by
    change orderOf (e.symm y') = 2 ^ n + 1
    rw [MulEquiv.orderOf_eq, hy'ord, hKcard]
  have hyinv : t * y * t = y⁻¹ := by
    apply e.injective
    simpa [y, map_mul] using hy'inv
  by_cases hn3 : n = 3
  · subst hn3
    exact three_le_modCommRank_of_orderOf_eq_nine hσinj ht hyinv (by simpa using hyord)
  · exact le_modCommRank_of_orderOf_eq_two_pow_add_one hσinj hn hn3 ht hyinv hyord

end CFSG.LocalAnalysis.WeakClosure81

end
