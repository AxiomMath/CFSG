module

public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem exists_fixed_norm_one_order {K : Type} [Field K] {m n : ℕ} (h : UnitaryFieldData 2 n K)
    {φ : K ≃+* K} (hcard : Nat.card (semilinearFixedSubfield φ) = (2 ^ m) ^ 2)
    (hbar : ∀ x : K, φ x = x → h.bar x = x ^ 2 ^ m) {d : ℕ} (hd : d ∣ 2 ^ m + 1) :
    ∃ ζ : K, ζ ≠ 0 ∧ orderOf ζ = d ∧ φ ζ = ζ ∧ h.norm ζ = 1 := by
  classical
  have hfin : Finite K := h.finite
  set S := semilinearFixedSubfield φ with hS
  haveI : Finite S := Subtype.finite
  haveI : Fintype S := Fintype.ofFinite S
  have hunits : Nat.card Sˣ = (2 ^ m) ^ 2 - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hcard]
  have hdN : d ∣ Nat.card Sˣ := by
    rw [hunits]
    have e : (2 ^ m) ^ 2 - 1 = (2 ^ m + 1) * (2 ^ m - 1) := by
      have := Nat.sq_sub_sq (2 ^ m) 1
      simpa using this
    rw [e]
    exact Dvd.dvd.mul_right hd _
  have hNpos : 0 < Nat.card Sˣ := Nat.card_pos
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Sˣ)
  obtain ⟨k, hk⟩ := hdN
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    omega
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hk
    omega
  have hkdvd : k ∣ orderOf g := by rw [hg, hk]; exact Dvd.intro_left d rfl
  have hord : orderOf (g ^ k) = d := by
    rw [orderOf_pow_of_dvd hk0 hkdvd, hg, hk, mul_comm, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hk0)]
  set ζ : K := (((g ^ k : Sˣ) : S) : K) with hζ
  have hζ0 : ζ ≠ 0 := by
    intro h0
    have : (((g ^ k : Sˣ) : S) : S) = 0 := Subtype.ext h0
    exact (g ^ k).ne_zero this
  have hζord : orderOf ζ = d := by
    have hinj : Function.Injective
        ((S.subtype : S →+* K).toMonoidHom.comp (Units.coeHom S)) := by
      intro a b hab
      apply Units.ext
      exact Subtype.ext hab
    have := orderOf_injective _ hinj (g ^ k)
    rw [← hord]
    exact this
  have hφζ : φ ζ = ζ := by
    have hmem := ((g ^ k : Sˣ) : S).2
    exact RingHom.mem_eqLocusField.mp hmem
  refine ⟨ζ, hζ0, hζord, hφζ, ?_⟩
  have hpow : ζ ^ (2 ^ m + 1) = 1 := by
    have : orderOf ζ ∣ 2 ^ m + 1 := hζord ▸ hd
    exact orderOf_dvd_iff_pow_eq_one.1 this
  rw [UnitaryFieldData.norm, hbar ζ hφζ, ← pow_succ']
  exact hpow

end CFSG.LocalAnalysis.UniquenessCase.UCK
