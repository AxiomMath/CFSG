module

public import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms
import CFSG.LocalAnalysis.ComponentClassification.SolvableKernelContainment

public section

namespace CFSG.RankThree.PartTwo.Sec16.Res6Act

theorem fin_two_eq_one_or_eq_neg_one {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {M : Matrix (Fin 2) (Fin 2) K} (hM : M * M = 1) (hdet : M.det = 1) : M = 1 ∨ M = -1 := by
  have entry : ∀ i j, (M * M) i j = (1 : Matrix (Fin 2) (Fin 2) K) i j := fun i j => by rw [hM]
  have e00 := entry 0 0
  have e01 := entry 0 1
  have e10 := entry 1 0
  have e11 := entry 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e00 e01 e10 e11
  rw [Matrix.det_fin_two] at hdet
  have hs : M 0 0 + M 1 1 ≠ 0 := by
    intro h
    have h' : M 0 0 * (M 0 0 + M 1 1) = 2 := by linear_combination e00 + hdet
    rw [h, mul_zero] at h'
    exact h2 h'.symm
  have hb : M 0 1 = 0 := by
    have h' : M 0 1 * (M 0 0 + M 1 1) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp h').resolve_right hs
  have hc : M 1 0 = 0 := by
    have h' : M 1 0 * (M 0 0 + M 1 1) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp h').resolve_right hs
  rw [hb, hc] at e00 hdet
  have had : M 0 0 = M 1 1 := by linear_combination M 1 1 * e00 - M 0 0 * hdet
  have ha : M 0 0 * M 0 0 = 1 := by linear_combination e00
  rcases mul_self_eq_one_iff.mp ha with h1 | h1
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, h1, ← had]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, h1, ← had]

theorem fin_one_eq_one_or_eq_neg_one {K : Type*} [Field K] {M : Matrix (Fin 1) (Fin 1) K}
    (hM : M * M = 1) : M = 1 ∨ M = -1 := by
  have e00 : (M * M) 0 0 = (1 : Matrix (Fin 1) (Fin 1) K) 0 0 := by rw [hM]
  simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.one_apply_eq] at e00
  rcases mul_self_eq_one_iff.mp e00 with h1 | h1
  · left
    ext i j
    fin_cases i
    fin_cases j
    simp [h1]
  · right
    ext i j
    fin_cases i
    fin_cases j
    simp [h1]

theorem eq_one_or_eq_neg_one {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) (hdim : Module.finrank K V ≤ 2)
    {g : Module.End K V} (hg : g * g = 1) (hdet : LinearMap.det g = 1) : g = 1 ∨ g = -1 := by
  classical
  rcases (by omega : Module.finrank K V = 0 ∨ Module.finrank K V = 1 ∨
      Module.finrank K V = 2) with h0 | h1 | h2'
  · have : Subsingleton V := Module.finrank_zero_iff.mp h0
    left
    exact LinearMap.ext fun v => Subsingleton.elim _ _
  · set b := Module.finBasisOfFinrankEq K V h1
    have hM : LinearMap.toMatrix b b g * LinearMap.toMatrix b b g = 1 := by
      rw [← LinearMap.toMatrix_mul, hg, LinearMap.toMatrix_one]
    rcases fin_one_eq_one_or_eq_neg_one hM with h | h
    · left
      apply (LinearMap.toMatrix b b).injective
      rw [h, LinearMap.toMatrix_one]
    · right
      apply (LinearMap.toMatrix b b).injective
      rw [h, map_neg, LinearMap.toMatrix_one]
  · set b := Module.finBasisOfFinrankEq K V h2'
    have hM : LinearMap.toMatrix b b g * LinearMap.toMatrix b b g = 1 := by
      rw [← LinearMap.toMatrix_mul, hg, LinearMap.toMatrix_one]
    have hd : (LinearMap.toMatrix b b g).det = 1 := by rw [LinearMap.det_toMatrix, hdet]
    rcases fin_two_eq_one_or_eq_neg_one h2 hM hd with h | h
    · left
      apply (LinearMap.toMatrix b b).injective
      rw [h, LinearMap.toMatrix_one]
    · right
      apply (LinearMap.toMatrix b b).injective
      rw [h, map_neg, LinearMap.toMatrix_one]

theorem det_eq_one_of_isPerfect {S : Type*} [Group S] [Group.IsPerfect S] {K V : Type*}
    [Field K] [AddCommGroup V] [Module K V] (f : S →* (Module.End K V)ˣ) (s : S) :
    LinearMap.det (f s : Module.End K V) = 1 := by
  let d : S →* Kˣ := (Units.map (LinearMap.det : Module.End K V →* K)).comp f
  have h1 := CFSG.ComponentClassification.SolvableKernelContainment.hom_eq_one d
  have h2 : d s = 1 := by rw [h1]; rfl
  have h3 := congrArg Units.val h2
  simpa [d] using h3

theorem eq_bot_of_isPerfect_of_isPGroup {p : ℕ} [Fact p.Prime] {H : Type*} [Group H]
    {T : Subgroup H} [Finite T] (hTp : Group.IsPerfect ↥T) (hT : IsPGroup p T) : T = ⊥ := by
  have : Group.IsNilpotent T := hT.isNilpotent
  have := hTp
  have hsub : Subsingleton T :=
    CFSG.ComponentClassification.SolvableKernelContainment.perfect_solvable_subsingleton
  rw [eq_bot_iff]
  intro t ht
  have := Subsingleton.elim (⟨t, ht⟩ : T) 1
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)

theorem isPGroup_of_le_ker {p : ℕ} [hp : Fact p.Prime] {D : Type*} [Group D] [Finite D]
    (hD : IsPGroup p D) {T : Subgroup (MulAut D)}
    (hT : T ≤ (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
      (frattini D)).ker) : IsPGroup p T := by
  intro τ
  have hn0 : orderOf τ ≠ 0 := (orderOf_pos τ).ne'
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.out.ne_one
  by_cases hb1 : b = 1
  · refine ⟨a, ?_⟩
    rw [← orderOf_dvd_iff_pow_eq_one, hab, hb1, mul_one]
  exfalso
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hab
    exact hn0 hab
  set q := b.minFac with hq
  have hqp : q.Prime := Nat.minFac_prime hb1
  have : Fact q.Prime := ⟨hqp⟩
  have hqb : q ∣ b := Nat.minFac_dvd b
  have hqne : q ≠ p := fun h => hb (h ▸ hqb)
  obtain ⟨c, hc⟩ := hqb
  set τ' := τ ^ (p ^ a * c) with hτ'
  have hord : orderOf τ' = q := by
    rw [hτ', orderOf_pow_of_dvd]
    · rw [hab, hc]
      have hpc : p ^ a * c ≠ 0 := by
        refine mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) ?_
        rintro rfl
        rw [mul_zero] at hc
        exact hb0 hc
      rw [show p ^ a * (q * c) = q * (p ^ a * c) by ring,
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hpc)]
    · refine mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) ?_
      rintro rfl
      rw [mul_zero] at hc
      exact hb0 hc
    · rw [hab, hc]
      exact ⟨q, by ring⟩
  have hqD : ¬ q ∣ Nat.card D := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hD
    rw [hk]
    intro h
    exact hqne ((Nat.prime_dvd_prime_iff_eq hqp hp.out).mp (hqp.dvd_of_dvd_pow h))
  have hmem : (τ' : MulAut D) ∈ (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
      (frattini D)).ker := hT (pow_mem τ.2 _)
  have hτ1 := CFSG.OrderReductions.FrattiniAutomorphisms.prime_order_frattini_kernel_trivial q
    (τ' : MulAut D) (by rw [Subgroup.orderOf_coe, hord]) hqD hmem
  have h1 : τ' = 1 := Subtype.ext hτ1
  rw [h1, orderOf_one] at hord
  exact hqp.one_lt.ne hord

end CFSG.RankThree.PartTwo.Sec16.Res6Act
