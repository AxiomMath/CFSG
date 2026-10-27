module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3A5Split
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s1611e3_a5_triv {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L Z : Subgroup (MulAut W)} {U : Subgroup W} (hL : IsAlt ↥L 5)
    (hsum : SumOfNat (fun H V Z => AlternatingNatural H V Z 5) L U ⊥ 2)
    (hZ : Nat.card ↥Z = 3) (hZL : ∀ z ∈ Z, ∀ l ∈ L, z * l = l * z)
    (hZU : ∀ z ∈ Z, ∀ w ∈ U, z w ∈ U) (hZf : ∀ z ∈ Z, z ≠ 1 → ∃ w ∈ U, z w ≠ w)
    {J : Subgroup W} (hJU : J ≤ U) (hJ : AlternatingNatural L J ⊥ 5) {e : MulAut W}
    (heL : L.map (MulAut.conj e).toMonoidHom = L) (heU : U.map e.toMonoidHom = U)
    (hJe : ∀ j ∈ J, e j = j) :
    ((∀ z ∈ Z, e * z = z * e) → ∀ u ∈ U, e u = u) ∧
      ((∀ z ∈ Z, e * z * e⁻¹ ∈ Z) → ∀ u ∈ U, e u * u⁻¹ ∈ J) := by
  classical
  have hZne : Z ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥Z = 1 := by rw [hbot]; exact Subgroup.card_bot
    omega
  obtain ⟨⟨z, hzZ⟩, hz1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  have hz1 : z ≠ 1 := fun h => hz1' (Subtype.ext h)
  have hdvd : orderOf z ∣ 3 := by rw [← hZ]; exact Subgroup.orderOf_dvd_natCard Z hzZ
  have hord : orderOf z = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hz1
    · exact h
  have hz3 : z ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one z
  obtain ⟨-, -, hJsup, hquad⟩ :=
    s1611e3_a5_split hW hL hsum hZ hZL hZU hZf hJU hJ hzZ hz1
  have hZeq : Subgroup.zpowers z = Z := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem hzZ) ?_
    rw [Nat.card_zpowers, hord, hZ]
  have hclass : ∀ w ∈ Z, w = 1 ∨ w = z ∨ w = z * z := by
    intro w hw
    have hw' : w ∈ Subgroup.zpowers z := hZeq.symm ▸ hw
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw'
    have hk3 : z ^ k = z ^ (k % (3 : ℤ)) := by
      have h := (zpow_mod_orderOf z k).symm
      rwa [hord] at h
    have hm : z ^ (k % (3 : ℤ)) = w := hk3.symm.trans hk
    have h0 : 0 ≤ k % (3 : ℤ) := by
      have := Int.emod_nonneg k (show (3 : ℤ) ≠ 0 by norm_num)
      omega
    have hlt : k % (3 : ℤ) < 3 := Int.emod_lt_of_pos k (by norm_num)
    have hcases : k % (3 : ℤ) = 0 ∨ k % (3 : ℤ) = 1 ∨ k % (3 : ℤ) = 2 := by omega
    rcases hcases with h | h | h
    · left; rw [← hm, h, zpow_zero]
    · right; left; rw [← hm, h, zpow_one]
    · right; right
      rw [← hm, h, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two]
  constructor
  · intro hcen u hu
    rw [← hJsup] at hu
    obtain ⟨j₁, hj₁, j₂, hj₂, rfl⟩ := Subgroup.mem_sup.1 hu
    obtain ⟨j, hjJ, rfl⟩ := Subgroup.mem_map.1 hj₂
    have hezj : e (z j) = z j := by
      have h := congrArg (fun x : MulAut W => x j) (hcen z hzZ)
      simpa [MulAut.mul_apply, hJe j hjJ] using h
    show e (j₁ * z j) = j₁ * z j
    rw [map_mul, hJe j₁ hj₁, hezj]
  · intro hnorm u hu
    rw [← hJsup] at hu
    obtain ⟨j₁, hj₁, j₂, hj₂, rfl⟩ := Subgroup.mem_sup.1 hu
    obtain ⟨j, hjJ, rfl⟩ := Subgroup.mem_map.1 hj₂
    have heinj : e⁻¹ j = j := by
      have h := congrArg (fun x : W => e⁻¹ x) (hJe j hjJ)
      simpa [MulAut.inv_apply_self] using h.symm
    by_cases hez : e * z * e⁻¹ = z
    · have hconj : e * z = z * e := by
        have h := congrArg (fun x : MulAut W => x * e) hez
        rw [mul_assoc, inv_mul_cancel, mul_one] at h
        exact h
      have hezj : e (z j) = z j := by
        have h := congrArg (fun x : MulAut W => x j) hconj
        simpa [MulAut.mul_apply, hJe j hjJ] using h
      show e (j₁ * z j) * (j₁ * z j)⁻¹ ∈ J
      rw [map_mul, hJe j₁ hj₁, hezj, mul_inv_cancel]
      exact J.one_mem
    · have hwZ : e * z * e⁻¹ ∈ Z := hnorm z hzZ
      have hw1 : e * z * e⁻¹ ≠ 1 := by
        intro h
        have h1 : e * z = e := by
          have := congrArg (fun x : MulAut W => x * e) h
          rw [mul_assoc, inv_mul_cancel, mul_one, one_mul] at this
          exact this
        have h2 : z = 1 := by
          have := congrArg (fun x : MulAut W => e⁻¹ * x) h1
          rw [← mul_assoc, inv_mul_cancel, one_mul] at this
          exact this
        exact hz1 h2
      have hw2 : e * z * e⁻¹ = z * z := by
        rcases hclass (e * z * e⁻¹) hwZ with h | h | h
        · exact absurd h hw1
        · exact absurd h hez
        · exact h
      have hprod : e (z j) * (z j)⁻¹ = j := by
        have h1 : (e * z * e⁻¹) j = e (z j) := by
          simp only [MulAut.mul_apply, heinj]
        rw [← h1, hw2, MulAut.mul_apply, hquad j hjJ]
        group
      have hgoal : (j₁ * e (z j)) * (j₁ * z j)⁻¹ = j := by
        have h2 : (j₁ * e (z j)) * (j₁ * z j)⁻¹ =
            j₁ * (e (z j) * (z j)⁻¹) * j₁⁻¹ := by
          rw [mul_inv_rev]; group
        rw [h2, hprod, mul_comm j₁ j]
        group
      show e (j₁ * z j) * (j₁ * z j)⁻¹ ∈ J
      rw [map_mul, hJe j₁ hj₁, hgoal]
      exact hjJ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
