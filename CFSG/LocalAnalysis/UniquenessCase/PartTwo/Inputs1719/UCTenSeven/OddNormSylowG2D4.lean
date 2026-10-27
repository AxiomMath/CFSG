module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddAutSylow
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35Exc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup

theorem normSylowAt_of_odd_orderOf_dvd_three {X : Type} [Group X] [Finite X]
    (h : ∀ S : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ →
      ∀ y ∈ normalizer (S : Set X), Odd (orderOf y) → orderOf y ∣ 3)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : NormSylowAt X p := by
  intro S hS y hy hyp
  obtain ⟨a, b, hbodd, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have hy2aN : y ^ 2 ^ a ∈ normalizer (S : Set X) := Subgroup.pow_mem _ hy _
  have hb3 : b ∣ 3 := by
    have hb_eq : orderOf (y ^ 2 ^ a) = b := by
      rw [orderOf_pow_of_dvd (pow_ne_zero a (by norm_num))
        (by rw [hord]; exact dvd_mul_right _ _),
        hord, Nat.mul_div_cancel_left b (pow_pos (by norm_num) a)]
    have h3 := h S hS (y ^ 2 ^ a) hy2aN (by rw [hb_eq]; exact hbodd)
    rwa [hb_eq] at h3
  have hp_not_dvd_2a : ¬ p ∣ 2 ^ a := by
    intro hd
    have hp2dvd : p ∣ 2 := hp.dvd_of_dvd_pow hd
    have hle := Nat.le_of_dvd (by norm_num) hp2dvd
    omega
  have hp_not_dvd_b : ¬ p ∣ b := by
    intro hd
    have hp3 : p ∣ 3 := hd.trans hb3
    have hle := Nat.le_of_dvd (by norm_num) hp3
    omega
  have hp_not_dvd_y : ¬ p ∣ orderOf y := by
    rw [hord]
    intro hd
    exact (hp.dvd_mul.mp hd).elim hp_not_dvd_2a hp_not_dvd_b
  have hcop : Nat.Coprime p (orderOf y) :=
    (hp.coprime_iff_not_dvd).mpr hp_not_dvd_y
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := y) (n := p) hcop
  rw [← hm]
  exact (Subgroup.centralizer (S : Set X)).pow_mem hyp m

theorem normSylowAt_G2
    {X : Type} [Group X] [Finite X] {n r f : ℕ} (hr2 : r ≠ 2)
    (hadm : CFSG.Open.StatedLieAdmissible .G2 n r f) (hX : CFSG.Blueprint.LieModel X .G2 n r f)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : NormSylowAt X p := by
  have hn : n = 0 := hadm.2.2.1
  subst hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine normSylowAt_of_odd_orderOf_dvd_three ?_ hp hp5
  intro S hS y hy hodd
  have hSiff := (CFSG.ABGLocalTools.isSylowOf_iff (p := 2) (P := S) (K := ⊤)).mp hS
  let Q : Sylow 2 X := hSiff.2.1.toSylow
    (by simpa [Subgroup.relIndex_top_right] using hSiff.2.2)
  have hQcoe : (Q : Subgroup X) = S := IsPGroup.toSylow_coe _ _
  exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s2112r34q35_normSylow_G2_of_odd
    hadm.1 hr2 hX Q (by simpa [hQcoe] using hy) hodd

theorem normSylowAt_trialityD4
    {X : Type} [Group X] [Finite X] {n r f : ℕ} (hr2 : r ≠ 2)
    (hadm : CFSG.Open.StatedLieAdmissible .trialityD4 n r f)
    (hX : CFSG.Blueprint.LieModel X .trialityD4 n r f)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : NormSylowAt X p := by
  have hn : n = 0 := hadm.2.2
  subst hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine normSylowAt_of_odd_orderOf_dvd_three ?_ hp hp5
  intro S hS y hy hodd
  have hSiff := (CFSG.ABGLocalTools.isSylowOf_iff (p := 2) (P := S) (K := ⊤)).mp hS
  let Q : Sylow 2 X := hSiff.2.1.toSylow
    (by simpa [Subgroup.relIndex_top_right] using hSiff.2.2)
  have hQcoe : (Q : Subgroup X) = S := IsPGroup.toSylow_coe _ _
  exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s2112r34q35_normSylow_D4_of_odd
    hadm.1 hr2 hX Q (by simpa [hQcoe] using hy) hodd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
