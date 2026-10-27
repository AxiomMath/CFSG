module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Crit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Fit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Min
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Module

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open scoped commutatorElement

theorem s16c1_G47_lemmaR {Hs F : Type} [Group Hs] [Finite Hs] [Group F] [Finite F]
    {Xs N : Subgroup Hs} (hXp : Group.IsPerfect Xs) (hN : N.Normal) (hodd : Odd (Nat.card N))
    (h3 : ¬ 3 ∣ Nat.card N)
    (hrk : ∀ q : ℕ, q.Prime → 3 < q → CFSG.Open.pRank q (⊤ : Subgroup Hs) ≤ 2)
    {u : Hs} (hu2 : u * u = 1) (hux : ∀ x ∈ Xs, u * x = x * u)
    (hnN : ∃ n ∈ N, u * n * u⁻¹ ≠ n)
    (hA9 : ∀ c : Hs, (∀ x ∈ Xs, c * x = x * c) → c * u = u * c)
    (hF : ∀ e : F, e * e = 1) (ρ : Hs →* MulAut F) (hD : ∃ e : F, ρ u e * e ≠ 1)
    (hTI : ∀ r : Hs, r * u * r⁻¹ ≠ u → ∀ e e' : F, ρ r (ρ u e * e) = ρ u e' * e' →
      ρ u e * e = 1)
    (hSc : ∀ c : Hs, ∀ q : ℕ, q.Prime → 5 ≤ q → orderOf c = q → c * u = u * c →
      (∀ x ∈ Xs, c * x = x * c) → ∀ e : F, ρ c (ρ u e * e) = ρ u e * e) : False := by
  classical
  obtain ⟨q, P, hq, hPN, hPn, hP, hPnt⟩ := s16c1_G47_fit hN hodd hu2 hnN
  haveI : Fact q.Prime := ⟨hq⟩
  have hPne : P ≠ ⊥ := by
    rintro rfl
    obtain ⟨n, hn, hne⟩ := hPnt
    rw [Subgroup.mem_bot] at hn
    subst hn
    simp at hne
  have hPcard : 1 < Nat.card P := (Subgroup.one_lt_card_iff_ne_bot P).2 hPne
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := q)).1 hP
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    omega
  have hqP : q ∣ Nat.card P := by
    rw [hk]
    exact dvd_pow_self q hk0
  have hqN : q ∣ Nat.card N := hqP.trans (Subgroup.card_dvd_of_le hPN)
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact hodd.not_two_dvd_nat hqN
  have hq5 : 5 ≤ q := by
    by_contra hlt
    have h2q := hq.two_le
    have : q = 2 ∨ q = 3 ∨ q = 4 := by omega
    rcases this with h | h | h
    · exact hq2 h
    · exact h3 (h ▸ hqN)
    · rw [h] at hq
      exact absurd hq (by norm_num)
  obtain ⟨D₀, hD₀P, hD₀n, hD₀q, hD₀cl, hD₀nt⟩ := s16c1_G47_crit hq hq2 hPn hP hu2 hPnt
  have hrq : CFSG.Open.pRank q (⊤ : Subgroup Hs) ≤ 2 := hrk q hq (by omega)
  obtain ⟨S, Z, hSD, hZS, hSu, -, hSZ, hZc, hcomm, hZu, hZX, hnc⟩ :=
    s16c1_G47_min hq hq2 hXp hu2 hux hA9 hD₀q hD₀cl
      (fun x _ d hd => hD₀n.conj_mem d hd x) (fun d hd => hD₀n.conj_mem d hd u) hD₀nt hrq
  have hSpg : IsPGroup q S := hP.to_le (hSD.trans hD₀P)
  have hZD : ∀ c ∈ Z, ∀ e : F, ρ c (ρ u e * e) = ρ u e * e := by
    intro c hc e
    have hcD : c ∈ D₀ := hSD (hZS hc)
    have hcq : c ^ q = 1 := hD₀q c hcD
    have hord : orderOf c ∣ q := orderOf_dvd_of_pow_eq_one hcq
    rcases (Nat.dvd_prime hq).1 hord with h1 | h1
    · rw [orderOf_eq_one_iff.1 h1]
      simp
    · exact hSc c q hq hq5 h1 (hZu c hc).symm (hZX c hc) e
  exact s16c1_G47_module hq hq2 hSpg hZS hu2 hSu hSZ hZc hcomm hnc hF ρ hD hTI hZD

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
