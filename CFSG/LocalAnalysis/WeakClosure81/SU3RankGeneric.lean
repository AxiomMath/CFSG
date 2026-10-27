module

public import CFSG.LocalAnalysis.WeakClosure81.SU3RankDefs
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveRootRankMod
import CFSG.LocalAnalysis.WeakClosure81.SU3RankModel
import CFSG.LocalAnalysis.WeakClosure81.SU3RankRoots
import CFSG.LocalAnalysis.WeakClosure81.SU3RankTorusModel
import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.SignalizerFunctorTheorem.Quadratic

theorem two_mul_le_modCommRank_permSU_swap_of_ne_three {n : ℕ} {F₀ : Type} [Field F₀]
    [Finite F₀] [CharP F₀ 2] (hn : 2 ≤ n) (hn3 : n ≠ 3) (hcard : Nat.card F₀ = (2 ^ n) ^ 2)
    {F : Type} [AddCommGroup F] [Module (ZMod 2) F] [Finite F]
    (σ : ↥(StatedSU 3 (2 ^ n) F₀) →* LGL 2 F)
    (hσ : ∀ x, σ x = 1 → (x : GL (Fin 3) F₀) ∈ StatedScalars (Fin 3) F₀) :
    2 * n ≤ modCommRank (σ (permSU n F₀ (Equiv.swap 0 1))) := by
  have hk : 2 ≤ 2 * n := by omega
  have h6 : 2 * n ≠ 6 := by
    intro h
    exact hn3 (by omega)
  obtain ⟨p, hprim⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 2 * n) hk h6
  have hkpos : 0 < 2 * n := by omega
  have hnpos : 0 < n := by omega
  have hm : p ∣ 2 ^ n + 1 := by
    refine (hprim.dvd_add_one_iff hkpos n).mpr ⟨dvd_refl (2 * n), ?_⟩
    rintro ⟨c, hc⟩
    have hle : 2 * n ≤ n := Nat.le_of_dvd hnpos ⟨c, hc⟩
    omega
  have hp2 : p ≠ 2 := hprim.ne_two hkpos
  have hp3 : p ≠ 3 := by
    rintro rfl
    have h26 : 2 * n = 2 := hprim.eq_two_of_dvd_three hkpos (dvd_refl 3)
    omega
  have hord : orderOf (2 : ZMod (p ^ 1)) = 2 * n := by
    rw [Nat.pow_one]
    rw [orderOf_eq_iff (x := (2 : ZMod p)) (n := 2 * n) hkpos]
    refine ⟨(CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff (2 * n)).mp hprim.dvd, ?_⟩
    intro m hm_lt hm_pos hm1
    have hdvd : p ∣ 2 ^ m - 1 := (CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff m).mpr hm1
    have hdiv : 2 * n ∣ m := (hprim.dvd_sub_one_iff hkpos m).mp hdvd
    exact absurd (Nat.le_of_dvd hm_pos hdiv) (not_le.mpr hm_lt)
  obtain ⟨ν, hνp⟩ := exists_orderOf_eq_of_dvd_two_pow_add_one (n := n) (F₀ := F₀) hcard hm
  have hν : orderOf ν = p ^ 1 := by rw [Nat.pow_one]; exact hνp
  have hinj : ∀ a b : rootsOfUnity (2 ^ n + 1) F₀, a ^ p = 1 → b ^ p = 1 →
      σ (diagSU n F₀ (a, b)) = 1 → a = 1 ∧ b = 1 := by
    intro a b ha hb hab
    have hscal := hσ (diagSU n F₀ (a, b)) hab
    obtain ⟨hab_eq, ha3⟩ :=
      (diagSU_mem_statedScalars_iff (n := n) (F₀ := F₀) (a, b)).mp hscal
    have hcop : Nat.Coprime p 3 :=
      (hprim.prime.coprime_iff_not_dvd (n := 3)).mpr fun hdvd3 =>
        hp3 ((Nat.prime_dvd_prime_iff_eq hprim.prime Nat.prime_three).mp hdvd3)
    have ha1 : a = 1 := by
      have hgd : a ^ Nat.gcd p 3 = 1 :=
        (pow_gcd_eq_one (a := a) (m := p) (n := 3)).mpr ⟨ha, ha3⟩
      rw [hcop.gcd_eq_one] at hgd
      simpa using hgd
    have hab_eq' : a = b := hab_eq
    exact ⟨ha1, hab_eq' ▸ ha1⟩
  have hmain := orderOf_two_le_modCommRank_permSU_swap (n := n) (F₀ := F₀) (ℓ := p) (k := 1)
    hprim.prime hp2 le_rfl (ν := ν) hν σ hinj
  rw [hord] at hmain
  exact hmain

end CFSG.LocalAnalysis.WeakClosure81

end
