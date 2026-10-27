module

public import CFSG.LocalAnalysis.UniquenessCase.UCK461b
public import CFSG.LocalAnalysis.UniquenessCase.UC6K42j
public import CFSG.LocalAnalysis.UniquenessCase.UC1K462Basic
import CFSG.Quasithin.Vol2.Ch5Sec1L34OddAbel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup

section TwoModule

variable {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem pCore_two_eq_bot (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    [ρ.IsIrreducible] : CFSG.pCore 2 G = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra (ZMod 2) G) ρ.asModule
  have hfix : fixV ρ (CFSG.pCore 2 G) ≠ ⊥ := UC46.fixV_ne_bot_of_pGroup (ρ := ρ) (CFSG.pCore_isPGroup)
  let R : Subrepresentation ρ :=
    ⟨fixV ρ (CFSG.pCore 2 G), fun g v hv n hn => by
      have hn' : g⁻¹ * n * g ∈ CFSG.pCore 2 G := by
        have := (CFSG.pCore_normal (p := 2) (G := G)).conj_mem n hn g⁻¹
        simpa using this
      have h1 : ρ n (ρ g v) = ρ g (ρ (g⁻¹ * n * g) v) := by
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
        congr 2
        group
      rw [h1, hv _ hn']⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top R with hbot | htop
  · exact absurd (congrArg Subrepresentation.toSubmodule hbot) (by
      intro h0
      exact hfix h0)
  · have htop' : fixV ρ (CFSG.pCore 2 G) = ⊤ := congrArg Subrepresentation.toSubmodule htop
    rw [eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    apply hρ
    rw [map_one]
    ext v
    have hv : v ∈ fixV ρ (CFSG.pCore 2 G) := by rw [htop']; trivial
    exact hv n hn

theorem odd_card_center_of_irreducible_two (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) [ρ.IsIrreducible] : Odd (Nat.card (Subgroup.center G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have h2 : 2 ∣ Nat.card (Subgroup.center G) := by
    rw [Nat.not_odd_iff_even] at hodd
    exact even_iff_two_dvd.1 hodd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center G) 2 h2
  have hz2 : (z : G) ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this
  have := central_involution_false_uc6 ρ hρ z.2 hz2
  have h1 : z = 1 := Subtype.ext this
  rw [h1, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem commutator_eq_bot_of_normalizes_two (hK : CFSG.Open.IsKGroup G) (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) {D : Subgroup G} (hD : Nat.card D = 3) (hfix : fixV ρ D = ⊥) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) {Q : Subgroup G} (hQ : IsPGroup q Q)
    (hDQ : D ≤ normalizer (Q : Set G)) : ⁅D, Q⁆ = ⊥ := by
  by_contra hne
  haveI : Fact q.Prime := ⟨hq⟩
  set R : Subgroup G := ⁅D, Q⁆ with hR
  have hRQ : R ≤ Q := Subgroup.le_normalizer_iff_commutator_le_right.1 hDQ
  have hRp : IsPGroup q R := hQ.to_le hRQ
  have hDR : D ≤ normalizer (R : Set G) := Subgroup.normalizer_commutator_ge_left D Q
  have hcop : Nat.Coprime (Nat.card D) (Nat.card Q) := by
    obtain ⟨k, hk⟩ := hQ.exists_card_eq
    rw [hD, hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_three hq).2 (Ne.symm hq3))
  have hRR : ⁅D, R⁆ = R := by
    have h1 := CFSG.Quasithin.H13.coprime_commutator_commutator_eq hDQ hcop
    calc ⁅D, R⁆ = ⁅R, D⁆ := Subgroup.commutator_comm _ _
      _ = ⁅⁅Q, D⁆, D⁆ := by rw [hR, Subgroup.commutator_comm D Q]
      _ = ⁅Q, D⁆ := h1
      _ = R := (Subgroup.commutator_comm Q D).trans (hR ▸ rfl)
  exact hq2 (UC6.k42_uc6 2 Nat.prime_two G hK V ρ hρ q 3 hq Nat.prime_three hq2 (by norm_num) hq3 D hD hfix
    R hRp hne hDR hRR).2.1

end TwoModule

end CFSG.LocalAnalysis.UniquenessCase.UCK
