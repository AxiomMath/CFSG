module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.BinaryScalarInvariance
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.FrobeniusBilinear

public section

namespace CFSG.ShultStronglyClosedTI

universe u

open CFSG.BenderSuzuki.PFAppendixIII

theorem unitaryTorusOrder_not_dvd_one_add_two_pow (f k : ℕ)
    (hf : 2 ≤ f) (hk : k < 2 * f) :
    ¬ (2 ^ (2 * f) - 1) / Nat.gcd 3 (2 ^ f + 1) ∣ 1 + 2 ^ k := by
  have hdelta : Nat.gcd 3 (2 ^ f + 1) = 1 ∨ Nat.gcd 3 (2 ^ f + 1) = 3 :=
    Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ (Nat.gcd_dvd_left _ _)
  have hN16 : 16 ≤ 2 ^ (2 * f) := by
    have h := Nat.pow_le_pow_right (n := 2) (by decide : 0 < 2)
      (show 4 ≤ 2 * f by omega)
    norm_num at h ⊢
    exact h
  rcases hdelta with hd | hd
  · rw [hd, Nat.div_one]
    have hp : 2 ^ k ≤ 2 ^ (2 * f - 1) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    have hdouble : 2 ^ (2 * f) = 2 * 2 ^ (2 * f - 1) := by
      calc
        2 ^ (2 * f) = 2 ^ ((2 * f - 1) + 1) := by congr 1; omega
        _ = 2 * 2 ^ (2 * f - 1) := by rw [pow_succ, Nat.mul_comm]
    exact Nat.not_dvd_of_pos_of_lt (by positivity) (by omega)
  · rw [hd]
    have hf3 : 3 ≤ f := by
      by_contra h
      have hf2 : f = 2 := by omega
      norm_num [hf2] at hd
    have hN64 : 64 ≤ 2 ^ (2 * f) := by
      have h := Nat.pow_le_pow_right (n := 2) (by decide : 0 < 2)
        (show 6 ≤ 2 * f by omega)
      norm_num at h ⊢
      exact h
    by_cases hklow : k ≤ 2 * f - 2
    · have hp : 2 ^ k ≤ 2 ^ (2 * f - 2) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) hklow
      have hquad : 2 ^ (2 * f) = 4 * 2 ^ (2 * f - 2) := by
        calc
          2 ^ (2 * f) = 2 ^ ((2 * f - 2) + 2) := by congr 1; omega
          _ = 4 * 2 ^ (2 * f - 2) := by rw [pow_add]; norm_num; omega
      exact Nat.not_dvd_of_pos_of_lt (by positivity) (by omega)
    · have hkmax : k = 2 * f - 1 := by omega
      rw [hkmax]
      have hdouble : 2 ^ (2 * f) = 2 * 2 ^ (2 * f - 1) := by
        calc
          2 ^ (2 * f) = 2 ^ ((2 * f - 1) + 1) := by congr 1; omega
          _ = 2 * 2 ^ (2 * f - 1) := by rw [pow_succ, Nat.mul_comm]
      intro hdiv
      have heq := Nat.eq_of_dvd_of_lt_two_mul
        (show 1 + 2 ^ (2 * f - 1) ≠ 0 by positivity) hdiv (by omega)
      omega

theorem odd_not_dvd_two_pow_add_two_pow (m n : ℕ) (hm : Odd m)
    (hweights : ∀ k < n, ¬ m ∣ 1 + 2 ^ k) (i j : Fin n) :
    ¬ m ∣ 2 ^ (i : ℕ) + 2 ^ (j : ℕ) := by
  have hcop : Nat.Coprime m 2 := hm.coprime_two_right
  by_cases hij : (i : ℕ) ≤ j
  · have heq : 2 ^ (i : ℕ) + 2 ^ (j : ℕ) =
        2 ^ (i : ℕ) * (1 + 2 ^ ((j : ℕ) - i)) := by
      rw [mul_add, mul_one, ← pow_add, Nat.add_sub_of_le hij]
    rw [heq, (hcop.pow_right (i : ℕ)).dvd_mul_left]
    exact hweights _ (by omega)
  · have hji : (j : ℕ) ≤ i := by omega
    have heq : 2 ^ (i : ℕ) + 2 ^ (j : ℕ) =
        2 ^ (j : ℕ) * (1 + 2 ^ ((i : ℕ) - j)) := by
      rw [mul_add, mul_one, ← pow_add, Nat.add_sub_of_le hji, add_comm]
    rw [heq, (hcop.pow_right (j : ℕ)).dvd_mul_left]
    exact hweights _ (by omega)

theorem binaryGaloisScalarInvariantBiadditive_eq_zero_of_weights
    (n m : ℕ) (hn : 0 < n) (hm : Odd m)
    (hweights : ∀ k < n, ¬ m ∣ 1 + 2 ^ k)
    (h : GaloisField 2 n) (horder : orderOf h = m)
    (b : GaloisField 2 n → GaloisField 2 n → GaloisField 2 n)
    (hleft : ∀ x x' y, b (x + x') y = b x y + b x' y)
    (hright : ∀ x y y', b x (y + y') = b x y + b x y')
    (hinvariant : ∀ x y, b (h * x) (h * y) = b x y) :
    ∀ x y, b x y = 0 := by
  classical
  let F := GaloisField 2 n
  let inner (x : F) : F →ₗ[ZMod 2] F :=
    (AddMonoidHom.mk' (b x) (hright x)).toZModLinearMap 2
  let outer : F →+ (F →ₗ[ZMod 2] F) :=
    AddMonoidHom.mk' inner (by
      intro x x'
      ext y
      exact hleft x x' y)
  let B : F →ₗ[ZMod 2] F →ₗ[ZMod 2] F := outer.toZModLinearMap 2
  obtain ⟨coeff, hexpansion, hsupport⟩ :=
    frobeniusBilinear_expansion_with_support_of_equivariant
      n hn B h h 1 (by
        intro x y
        change b (h * x) (h * y) = 1 * b x y
        simpa only [one_mul] using hinvariant x y)
  have hcoeff (i j : Fin n) : coeff i j = 0 := by
    by_contra hij
    have hpow : h ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) = 1 := by
      rw [pow_add]
      exact hsupport i j hij
    have hdiv : m ∣ 2 ^ (i : ℕ) + 2 ^ (j : ℕ) := by
      rw [← horder]
      exact orderOf_dvd_iff_pow_eq_one.mpr hpow
    exact odd_not_dvd_two_pow_add_two_pow m n hm hweights i j hdiv
  intro x y
  calc
    b x y = B x y := rfl
    _ = ∑ i : Fin n, ∑ j : Fin n,
        coeff i j * x ^ (2 ^ (i : ℕ)) * y ^ (2 ^ (j : ℕ)) := hexpansion x y
    _ = 0 := by simp only [hcoeff, zero_mul, Finset.sum_const_zero]

theorem binaryUnitaryTorusInvariantBiadditive_eq_zero
    {K : Type u} [Field K] [Finite K] [CharP K 2]
    (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (M : Subgroup Kˣ)
    (hMcard : Nat.card M = ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1))
    (b : K → K → ZMod 2)
    (hleft : ∀ x x' y, b (x + x') y = b x y + b x' y)
    (hright : ∀ x y y', b x (y + y') = b x y + b x y')
    (hinvariant : ∀ h : M, ∀ x y : K,
      b (((h : Kˣ) : K) * x) (((h : Kˣ) : K) * y) = b x y) :
    ∀ x y, b x y = 0 := by
  classical
  have hn : 0 < 2 * f := by omega
  have hcard' : Nat.card K = 2 ^ (2 * f) := by
    simpa only [← pow_mul, Nat.mul_comm f 2] using hcard
  have hN16 : 16 ≤ 2 ^ (2 * f) := by
    have h := Nat.pow_le_pow_right (n := 2) (by decide : 0 < 2)
      (show 4 ≤ 2 * f by omega)
    norm_num at h ⊢
    exact h
  by_cases hdelta : Nat.gcd 3 (2 ^ f + 1) = 1
  · have htop : M = ⊤ := M.eq_top_of_card_eq (by
      rw [hMcard, hdelta, Nat.div_one, Nat.card_units, hcard])
    apply binaryScalarInvariantBiadditive_eq_zero
      (show 4 < Nat.card K by omega) b hleft hright
    intro a ha x y
    have hmem : Units.mk0 a ha ∈ M := by rw [htop]; trivial
    exact hinvariant ⟨Units.mk0 a ha, hmem⟩ x y
  · have hMcard' : Nat.card M =
        (2 ^ (2 * f) - 1) / Nat.gcd 3 (2 ^ f + 1) := by
      simpa only [← pow_mul, Nat.mul_comm f 2] using hMcard
    have hoddN : Odd (2 ^ (2 * f) - 1) :=
      Nat.Even.sub_odd (by omega)
        ((by decide : Even (2 : ℕ)).pow_of_ne_zero hn.ne')
        (by decide : Odd (1 : ℕ))
    have hMdiv : Nat.card M ∣ 2 ^ (2 * f) - 1 := by
      simpa only [Nat.card_units, hcard'] using M.card_subgroup_dvd_card
    have hm : Odd (Nat.card M) := hoddN.of_dvd_nat hMdiv
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := M)
    have hgorder : orderOf g = Nat.card M :=
      orderOf_eq_card_of_forall_mem_zpowers hg
    let F := GaloisField 2 (2 * f)
    let : Fintype K := Fintype.ofFinite K
    let : Fintype F := Fintype.ofFinite F
    let e : K ≃+* F := FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard',
        GaloisField.card 2 (2 * f) hn.ne'])
    let h : F := e ((g : Kˣ) : K)
    have horder : orderOf h = Nat.card M := by
      calc
        orderOf h = orderOf ((g : Kˣ) : K) := e.toMulEquiv.orderOf_eq _
        _ = orderOf (g : Kˣ) :=
          orderOf_injective (Units.coeHom K) Units.val_injective _
        _ = orderOf g := Subgroup.orderOf_coe g
        _ = Nat.card M := hgorder
    let c (x y : F) : F :=
      algebraMap (ZMod 2) F (b (e.symm x) (e.symm y))
    have hc_left : ∀ x x' y, c (x + x') y = c x y + c x' y := by
      intro x x' y
      simp only [c, map_add, hleft]
    have hc_right : ∀ x y y', c x (y + y') = c x y + c x y' := by
      intro x y y'
      simp only [c, map_add, hright]
    have hc_invariant : ∀ x y, c (h * x) (h * y) = c x y := by
      intro x y
      simp only [c, h, map_mul, RingEquiv.symm_apply_apply, hinvariant]
    have hweights : ∀ k < 2 * f, ¬ Nat.card M ∣ 1 + 2 ^ k := by
      intro k hk
      rw [hMcard']
      exact unitaryTorusOrder_not_dvd_one_add_two_pow f k hf hk
    have hc_zero := binaryGaloisScalarInvariantBiadditive_eq_zero_of_weights
      (2 * f) (Nat.card M) hn hm hweights h horder c hc_left hc_right hc_invariant
    intro x y
    apply (algebraMap (ZMod 2) F).injective
    simpa only [c, RingEquiv.symm_apply_apply, map_zero] using hc_zero (e x) (e y)

theorem binaryUnitaryTorusInvariantAddHom_eq_zero
    {K : Type u} [Field K] [Finite K] [CharP K 2]
    (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (M : Subgroup Kˣ)
    (hMcard : Nat.card M = ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1))
    (b : K →+ K →+ ZMod 2)
    (hinvariant : ∀ h : M, ∀ x y : K,
      b (((h : Kˣ) : K) * x) (((h : Kˣ) : K) * y) = b x y) :
    ∀ x y, b x y = 0 := by
  apply binaryUnitaryTorusInvariantBiadditive_eq_zero f hf hcard M hMcard
    (fun x y => b x y) ?_ ?_ hinvariant
  · intro x x' y
    simp only [map_add, AddMonoidHom.add_apply]
  · intro x y y'
    exact (b x).map_add y y'

end CFSG.ShultStronglyClosedTI
