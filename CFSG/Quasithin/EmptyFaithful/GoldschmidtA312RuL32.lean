module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerOrder168
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedMain

public section

namespace CFSG.Quasithin.A312Ru

open Equiv CFSG.ProperTwoGeneratedCore.CosetNormalizer

theorem multiset_six {m : Multiset ℕ} (h2 : ∀ n ∈ m, 2 ≤ n) (hsum : m.sum ≤ 7)
    (hlcm : m.lcm = 6) (hpar : Even (m.sum + Multiset.card m)) : m = {2, 2, 3} := by
  have hcard : Multiset.card m * 2 ≤ m.sum := by
    have := Multiset.card_nsmul_le_sum h2
    simpa [smul_eq_mul] using this
  have hc3 : Multiset.card m ≤ 3 := by omega
  rcases Nat.lt_or_ge (Multiset.card m) 3 with hlt | hge
  · exfalso
    interval_cases hk : Multiset.card m
    · rw [Multiset.card_eq_zero] at hk
      subst hk
      simp at hlcm
    · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp hk
      simp at hlcm hpar
      subst hlcm
      exact absurd hpar (by decide)
    · obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp hk
      have ha := h2 a (by simp)
      have hb := h2 b (by simp)
      simp at hsum hlcm hpar
      have ha' : a ≤ 5 := by omega
      have hb' : b ≤ 5 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (revert hlcm hpar; decide)
  · have : Multiset.card m = 3 := by omega
    obtain ⟨a, b, c, rfl⟩ := Multiset.card_eq_three.mp this
    have ha := h2 a (by simp)
    have hb := h2 b (by simp)
    have hc := h2 c (by simp)
    simp at hsum hlcm hpar
    have ha' : a ≤ 3 := by omega
    have hb' : b ≤ 3 := by omega
    have hc' : c ≤ 3 := by omega
    interval_cases a <;> interval_cases b <;> interval_cases c <;>
      first | omega | (revert hlcm hpar; decide)

theorem cycleType_of_six (σ : Perm (Fin 7)) (h6 : orderOf σ = 6) (hs : Perm.sign σ = 1) :
    σ.cycleType = {2, 2, 3} := by
  apply multiset_six
  · exact fun n hn => Perm.two_le_of_mem_cycleType hn
  · simpa using Perm.sum_cycleType_le σ
  · rw [Perm.lcm_cycleType, h6]
  · have h := Perm.sign_of_cycleType σ
    rw [hs] at h
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    rw [hodd.neg_one_pow] at h
    exact absurd h (by decide)

def rho0 : Perm (Fin 7) := Equiv.swap 0 1 * Equiv.swap 2 3 * (Equiv.swap 4 5 * Equiv.swap 4 6)

theorem cycleType_rho0 : rho0.cycleType = {2, 2, 3} := by
  have h3 : (Equiv.swap (4 : Fin 7) 5 * Equiv.swap 4 6).IsThreeCycle :=
    Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  have d1 : Perm.Disjoint (Equiv.swap (0 : Fin 7) 1) (Equiv.swap 2 3) := by
    intro x; revert x; decide
  have d2 : Perm.Disjoint (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3)
      (Equiv.swap 4 5 * Equiv.swap 4 6) := by
    intro x; revert x; decide
  have s1 : (Equiv.swap (0 : Fin 7) 1).cycleType = {2} :=
    Perm.isSwap_iff_cycleType.mp ⟨0, 1, by decide, rfl⟩
  have s2 : (Equiv.swap (2 : Fin 7) 3).cycleType = {2} :=
    Perm.isSwap_iff_cycleType.mp ⟨2, 3, by decide, rfl⟩
  rw [rho0, d2.cycleType_mul, d1.cycleType_mul, h3, s1, s2]
  rfl

theorem rho0_sq : (rho0 ^ 2).IsThreeCycle :=
  card_support_eq_three_iff.mp (by decide)

theorem isThreeCycle_sq_of_six (σ : Perm (Fin 7)) (h6 : orderOf σ = 6)
    (hs : Perm.sign σ = 1) : (σ ^ 2).IsThreeCycle := by
  have hct := cycleType_of_six σ h6 hs
  have hconj : IsConj σ rho0 := Perm.isConj_iff_cycleType_eq.mpr (hct.trans cycleType_rho0.symm)
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have h1 : (σ ^ 2).cycleType = (rho0 ^ 2).cycleType := by
    have : rho0 ^ 2 = c * σ ^ 2 * c⁻¹ := by rw [← hc, conj_pow]
    rw [this, Perm.cycleType_conj]
  exact h1.trans rho0_sq

variable {H : Type} [Group H] [Finite H] [IsSimpleGroup H]

omit [Finite H] in
theorem orderOf_ne_six_of_perm_seven (hcard : Nat.card H = 168) (ι : H →* Perm (Fin 7))
    (hι : Function.Injective ι) (htr : ∀ i j : Fin 7, ∃ h : H, ι h i = j) (g : H) :
    orderOf g ≠ 6 := by
  intro h6
  have hsign : Perm.sign (ι g) = 1 := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Perm.sign : Perm (Fin 7) →* ℤˣ).comp ι).ker
      with h | h
    · exfalso
      have hinj : Function.Injective ((Perm.sign : Perm (Fin 7) →* ℤˣ).comp ι) :=
        (MonoidHom.ker_eq_bot_iff _).mp h
      have h1 := Nat.card_le_card_of_injective _ hinj
      have h2 : Nat.card ℤˣ = 2 := by
        rw [Nat.card_eq_fintype_card]; exact Fintype.card_units_int
      omega
    · have : g ∈ ((Perm.sign : Perm (Fin 7) →* ℤˣ).comp ι).ker := h ▸ Subgroup.mem_top g
      simpa using this
  have hσ6 : orderOf (ι g) = 6 := by rw [orderOf_injective ι hι g]; exact h6
  have h3c := isThreeCycle_sq_of_six (ι g) hσ6 hsign
  have hmem : ι g ^ 2 ∈ ι.range := ⟨g ^ 2, by simp⟩
  have : MulAction.IsPretransitive ι.range (Fin 7) := ⟨fun i j => by
    obtain ⟨h, hh⟩ := htr i j
    exact ⟨⟨ι h, h, rfl⟩, hh⟩⟩
  have hprime : (Nat.card (Fin 7)).Prime := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num
  have : MulAction.IsPreprimitive ι.range (Fin 7) :=
    MulAction.IsPreprimitive.of_prime_card hprime
  have hA := Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem this h3c hmem
  have hcardG : Nat.card ι.range = 168 := by
    rw [← hcard]; exact (Nat.card_congr (MonoidHom.ofInjective hι).toEquiv).symm
  have hcardA : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]; decide
  have := Subgroup.card_le_of_le hA
  omega

theorem isPSL_three_two_of_perm_seven (hcard : Nat.card H = 168) (ι : H →* Perm (Fin 7))
    (hι : Function.Injective ι) (htr : ∀ i j : Fin 7, ∃ h : H, ι h i = j) :
    CFSG.Quasithin.IsPSL 3 2 1 H := by
  have hnonab : ∃ a b : H, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have : IsMulCommutative H := ⟨⟨hcon⟩⟩
    have hp : (Nat.card H).Prime := Group.is_simple_iff_prime_card.mp inferInstance
    rw [hcard] at hp
    exact absurd hp (by norm_num)
  have hsix := orderOf_ne_six_of_perm_seven hcard ι hι htr
  obtain ⟨-, -, ℓ, φ, -, -, -, hmodel⟩ :=
    simple_order_168_without_six_projective_seven_recognition H hnonab hcard hsix
  exact CFSG.QuasithinUnique.Vol2Native.L239.statedClassicalModel_psl_three_two_of_psl_two_seven
    hmodel

end CFSG.Quasithin.A312Ru
