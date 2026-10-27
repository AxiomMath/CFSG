module

public import CFSG.Sporadic.HNOddCore.InvDefs
public import CFSG.Sporadic.HNSchreier.AltCent

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier Equiv Equiv.Perm

theorem swap01_type : (swap (0 : Fin 12) 1).cycleType = Multiset.replicate 1 2 :=
  cycleType_of_sq (by rw [pow_two, swap_mul_self]) (by decide)

theorem card_centralizer_swap01 :
    Nat.card (Subgroup.centralizer {swap (0 : Fin 12) 1}) = 7257600 := by
  rw [Perm.nat_card_centralizer, swap01_type]
  decide

theorem card_centralizer_sig2 : Nat.card (Subgroup.centralizer {sig2}) = 322560 := by
  rw [Perm.nat_card_centralizer, sig2_type]
  decide

theorem card_centralizer_sig4 : Nat.card (Subgroup.centralizer {sig4}) = 9216 := by
  rw [Perm.nat_card_centralizer, sig4_type]
  decide

theorem card_centralizer_sig6 : Nat.card (Subgroup.centralizer {sig6}) = 46080 := by
  rw [Perm.nat_card_centralizer, sig6_type]
  decide

theorem card_alt_of_mem {K : Subgroup (Perm (Fin 12))} {a b : Fin 12} (hab : a ≠ b)
    (h : swap a b ∈ K) {c : ℕ} (hc : Nat.card K = 2 * c) :
    Nat.card (K ⊓ alternatingGroup (Fin 12) : Subgroup (Perm (Fin 12))) = c := by
  have := card_inf_alt_of_odd h (sign_swap hab)
  omega

theorem card_altCentralizer_swap01 :
    Nat.card (Subgroup.centralizer {swap (0 : Fin 12) 1} ⊓ alternatingGroup (Fin 12) :
      Subgroup (Perm (Fin 12))) = 3628800 :=
  card_alt_of_mem (by decide) (Subgroup.mem_centralizer_singleton_iff.2 rfl)
    (by rw [card_centralizer_swap01])

theorem card_altCentralizer_sig2 :
    Nat.card (Subgroup.centralizer {sig2} ⊓ alternatingGroup (Fin 12) :
      Subgroup (Perm (Fin 12))) = 161280 :=
  card_alt_of_mem (a := 0) (b := 1) (by decide)
    (Subgroup.mem_centralizer_singleton_iff.2 (by unfold sig2; decide))
    (by rw [card_centralizer_sig2])

theorem card_altCentralizer_sig4 :
    Nat.card (Subgroup.centralizer {sig4} ⊓ alternatingGroup (Fin 12) :
      Subgroup (Perm (Fin 12))) = 4608 :=
  card_alt_of_mem (a := 0) (b := 1) (by decide)
    (Subgroup.mem_centralizer_singleton_iff.2 (by unfold sig4; decide))
    (by rw [card_centralizer_sig4])

theorem card_altCentralizer_sig6 :
    Nat.card (Subgroup.centralizer {sig6} ⊓ alternatingGroup (Fin 12) :
      Subgroup (Perm (Fin 12))) = 23040 :=
  card_alt_of_mem (a := 0) (b := 6) (by decide)
    (Subgroup.mem_centralizer_singleton_iff.2 (by unfold sig6; decide))
    (by rw [card_centralizer_sig6])

@[expose] def shift2 : Fin 10 ≃ {i : Fin 12 // 2 ≤ i.val} where
  toFun j := ⟨⟨j.val + 2, by omega⟩, by simp⟩
  invFun i := ⟨i.1.val - 2, by have := i.1.isLt; omega⟩
  left_inv j := by ext; simp
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    have := i.2
    simp only
    omega

abbrev ext2 : Perm (Fin 10) →* Perm (Fin 12) := extendDomainHom shift2

theorem ext2_fix (π : Perm (Fin 10)) {i : Fin 12} (hi : i.val < 2) : ext2 π i = i := by
  rw [extendDomainHom_apply]
  exact extendDomain_apply_not_subtype π shift2 (by omega)

theorem ext2_commute (π : Perm (Fin 10)) : ext2 π * swap 0 1 = swap 0 1 * ext2 π := by
  ext i
  simp only [Perm.mul_apply]
  by_cases hi : i.val < 2
  · have hs : (swap (0 : Fin 12) 1 i).val < 2 := by
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> decide
    rw [ext2_fix π hs, ext2_fix π hi]
  · have hi' : 2 ≤ i.val := by omega
    have h1 : swap (0 : Fin 12) 1 i = i := swap_apply_of_ne_of_ne (by omega) (by omega)
    have h2 : 2 ≤ (ext2 π i).val := by
      rw [extendDomainHom_apply, extendDomain_apply_subtype π shift2 hi']
      exact (shift2 _).2
    rw [h1, swap_apply_of_ne_of_ne (by omega) (by omega)]

@[expose] def signTau (u : ℤˣ) : Perm (Fin 12) := if u = 1 then 1 else swap 0 1

theorem signTau_mul (u v : ℤˣ) : signTau (u * v) = signTau u * signTau v := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl <;>
    simp [signTau, swap_mul_self]

@[expose] def s10Hom : Perm (Fin 10) →* Perm (Fin 12) where
  toFun π := ext2 π * signTau (sign π)
  map_one' := by simp [signTau]
  map_mul' π ρ := by
    rw [map_mul, map_mul, signTau_mul]
    have hc : signTau (sign π) * ext2 ρ = ext2 ρ * signTau (sign π) := by
      unfold signTau
      split_ifs
      · rw [one_mul, mul_one]
      · exact (ext2_commute ρ).symm
    calc ext2 π * ext2 ρ * (signTau (sign π) * signTau (sign ρ))
        = ext2 π * (ext2 ρ * signTau (sign π)) * signTau (sign ρ) := by group
      _ = ext2 π * (signTau (sign π) * ext2 ρ) * signTau (sign ρ) := by rw [hc]
      _ = ext2 π * signTau (sign π) * (ext2 ρ * signTau (sign ρ)) := by group

theorem s10Hom_apply (π : Perm (Fin 10)) : s10Hom π = ext2 π * signTau (sign π) := rfl

theorem s10Hom_mem (π : Perm (Fin 10)) :
    s10Hom π ∈ Subgroup.centralizer {swap (0 : Fin 12) 1} ⊓ alternatingGroup (Fin 12) := by
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, ?_⟩
  · rw [s10Hom_apply]
    unfold signTau
    split_ifs
    · rw [mul_one]
      exact ext2_commute π
    · rw [mul_assoc, swap_mul_self, mul_one, ext2_commute π, ← mul_assoc, swap_mul_self, one_mul]
  · rw [mem_alternatingGroup, s10Hom_apply, map_mul, extendDomainHom_apply, sign_extendDomain]
    unfold signTau
    rcases Int.units_eq_one_or (sign π) with h | h
    · rw [h, ite_eq_left rfl, map_one, mul_one]
    · rw [h, ite_eq_right (by decide), sign_swap (by decide)]
      decide

theorem s10Hom_injective : Function.Injective s10Hom := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro π hπ
  rw [MonoidHom.mem_ker, s10Hom_apply] at hπ
  have h0 : sign π = 1 := by
    by_contra h
    have := congrArg (fun f : Perm (Fin 12) => f 0) hπ
    simp only [Perm.mul_apply, Perm.one_apply, signTau, ite_eq_right h] at this
    rw [swap_apply_left, ext2_fix π (by decide)] at this
    exact absurd this (by decide)
  rw [signTau, ite_eq_left h0, mul_one] at hπ
  exact (extendDomainHom_injective shift2) (hπ.trans (map_one _).symm)

abbrev Z01 : Subgroup (Perm (Fin 12)) :=
  Subgroup.centralizer {swap (0 : Fin 12) 1} ⊓ alternatingGroup (Fin 12)

theorem s10Hom_range : s10Hom.range = Z01 := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨π, rfl⟩
    exact s10Hom_mem π
  · rw [card_altCentralizer_swap01,
      ← Nat.card_congr (MonoidHom.ofInjective s10Hom_injective).toEquiv, Nat.card_perm,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    decide

@[expose] def s10Equiv : Perm (Fin 10) ≃* Z01 :=
  (MonoidHom.ofInjective s10Hom_injective).trans (MulEquiv.subgroupCongr s10Hom_range)

end CFSG.Sporadic.HNOddCore
