
module

public import CFSG.Sporadic.Schreier.J4SOuterBase1

public import CFSG.Sporadic.Schreier.J4SAut
public import CFSG.Sporadic.Schreier.J4SKernel
public import CFSG.GroupActions.SelfCentralizingCoreOuterPrimeBound
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SFive
public import CFSG.Sporadic.Schreier.J4SPointwise
public meta import CFSG.Sporadic.J4.PrimSpec
public import Certificates.Certificate2177
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.Schreier.J4SPrimes
public meta import CFSG.Sporadic.Schreier.J4SPrimes
public import CFSG.Sporadic.Schreier.J4SProfile
public meta import CFSG.Sporadic.Schreier.J4SProfile
public import CFSG.Sporadic.Schreier.J4SSylowData
public meta import CFSG.Sporadic.Schreier.J4SSylowData
public import CFSG.Sporadic.J4.Local

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms

theorem S0_le_H : S0 ≤ H := by
  rw [← N_sup_U]
  exact sup_le N_le_H (U_le_K.trans K_le_H)

theorem normalizer_N :
    Subgroup.normalizer (N : Set J) = H := by
  have := isSimpleGroup_J j4Facts
  rcases H_isCoatom.le_iff.1 H_le_normalizer with h | h
  · exfalso
    have hN : N.Normal := Subgroup.normalizer_eq_top_iff.1 h
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h1 | h1
    · have h2 := card_N
      rw [h1, Subgroup.card_bot] at h2
      norm_num at h2
    · have h2 := card_N
      rw [h1, Subgroup.card_top, card_J j4Facts] at h2
      norm_num at h2
  · exact h

theorem not_dvd_card_outer_J
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ∣ Nat.card (Outer J) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCp : ¬ p ∣ Nat.card (pointwiseFixingAut H) := by
    intro h
    rcases R3E_J4_pointwise_local_automorphism_kernel_no_large_primes.2 p hp h with h2 | h3 <;>
      omega
  have h := not_dvd_card_outer_of_sylow_bound (by omega : p ≠ 2) S0Sylow N H
    (by rw [S0Sylow_coe]; exact N_le_S0) (by rw [S0Sylow_coe]; exact S0_le_H) isPGroup_N
    normalizer_N QT_unique_J4_local_normal_module_irreducible.2.2.2.2.2.2.2.2.2.le hCp
    (R3E_J4_Sylow_two_automorphism_group_is_two_group S0Sylow).2
  exact h

theorem R3E_J4_outer_automorphism_group_no_large_primes
    {T : Type*} [Group T]
    (hT : Nonempty (T ≃* NativeSporadic.J4)) :
    (∀ p : ℕ, p.Prime → p ∣ Nat.card (Outer T) → p = 2 ∨ p = 3) ∧
      ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ A : Subgroup (MulAut T), IsPGroup p A → A ≤ inner T := by
  obtain ⟨e⟩ := hT
  have eJ : T ≃* J := e.trans (seedEquiv j4Facts.mat)
  have hcard : Nat.card (Outer T) = Nat.card (Outer J) := by
    have h := @card_outer_congr T J _ (Subgroup.toGroup J) eJ
    exact h
  have hno : ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ Nat.card (Outer T) := fun p hp hp5 => by
    rw [hcard]
    exact not_dvd_card_outer_J hp hp5
  refine ⟨fun p hp hdvd => ?_, fun p hp hp5 A hA => ?_⟩
  · by_contra hne
    have hp5 : 5 ≤ p := by
      rcases Nat.lt_or_ge p 5 with hlt | h
      · have h2 := hp.two_le
        interval_cases p
        · exact absurd (Or.inl rfl) hne
        · exact absurd (Or.inr rfl) hne
        · exact absurd hp (by norm_num)
      · exact h
    exact hno p hp hp5 hdvd
  · intro a ha
    have : Finite T := Finite.of_equiv _ e.toEquiv.symm
    have : Finite (MulAut T) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut T))
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := hA ⟨a, ha⟩
    have hak : a ^ p ^ k = 1 := by
      have := congrArg Subtype.val hk
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    have h1 : orderOf (QuotientGroup.mk' (inner T) a) ∣ p ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hak, map_one])
    have h2 : orderOf (QuotientGroup.mk' (inner T) a) ∣ Nat.card (Outer T) :=
      orderOf_dvd_natCard _
    have hcop : Nat.Coprime (p ^ k) (Nat.card (Outer T)) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 (hno p hp hp5))
    have h3 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
    exact h3

end CFSG.Sporadic.J4Schreier
