module

public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOB

open Subgroup

theorem eq_one_of_inner_of_noR {Y : Type} [Group Y] [Finite Y] (hZ : Subgroup.center Y = ⊥)
    (S : Sylow 2 Y) {r : ℕ} (hN : ∀ b ∈ Subgroup.normalizer ((S : Subgroup Y) : Set Y), b ^ r = 1 → b = 1)
    {θ : MulAut Y} (hin : θ ∈ (MulAut.conj : Y →* MulAut Y).range) (hθ : θ ^ r = 1)
    (hS : ∀ x ∈ (S : Subgroup Y), θ x ∈ (S : Subgroup Y)) : θ = 1 := by
  obtain ⟨x, rfl⟩ := hin
  have hle : (S : Subgroup Y).map (MulAut.conj x).toMonoidHom ≤ (S : Subgroup Y) := by
    rintro _ ⟨s, hs, rfl⟩
    exact hS s hs
  have heq : (S : Subgroup Y).map (MulAut.conj x).toMonoidHom = (S : Subgroup Y) := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
  have hxN : x ∈ Subgroup.normalizer ((S : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hS h hh, fun hh => ?_⟩
    rw [← heq] at hh
    obtain ⟨s, hs, hsh⟩ := hh
    have : s = h := (MulAut.conj x).injective hsh
    rwa [← this]
  have hpow : MulAut.conj (x ^ r) = 1 := by
    rw [map_pow]
    exact hθ
  have hxr : x ^ r ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut Y => φ g) hpow
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  rw [hZ, Subgroup.mem_bot] at hxr
  have hx1 : x = 1 := hN x hxN hxr
  subst hx1
  simp

theorem noR_of_not_dvd_card {Y : Type} [Group Y] [Finite Y] {r : ℕ} (hr : r.Prime) (S : Sylow 2 Y)
    (h : ¬ r ∣ Nat.card (Subgroup.normalizer ((S : Subgroup Y) : Set Y))) :
    ∀ b ∈ Subgroup.normalizer ((S : Subgroup Y) : Set Y), b ^ r = 1 → b = 1 := by
  intro b hb hbr
  rcases (Nat.dvd_prime hr).1 (orderOf_dvd_of_pow_eq_one hbr) with h2 | h2
  · exact orderOf_eq_one_iff.1 h2
  · exfalso
    apply h
    have h3 : orderOf (⟨b, hb⟩ : Subgroup.normalizer ((S : Subgroup Y) : Set Y)) ∣
        Nat.card (Subgroup.normalizer ((S : Subgroup Y) : Set Y)) := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk, h2] at h3

theorem noR_of_pow_mem {Y : Type} [Group Y] [Finite Y] {r e : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hre : Nat.Coprime r e) (S : Sylow 2 Y)
    (h : ∀ b ∈ Subgroup.normalizer ((S : Subgroup Y) : Set Y), b ^ e ∈ (S : Subgroup Y)) :
    ∀ b ∈ Subgroup.normalizer ((S : Subgroup Y) : Set Y), b ^ r = 1 → b = 1 := by
  intro b hb hbr
  have hcr : (b ^ e) ^ r = 1 := by rw [← pow_mul, mul_comm, pow_mul, hbr, one_pow]
  obtain ⟨k, hk⟩ := S.isPGroup' (⟨b ^ e, h b hb⟩ : (S : Subgroup Y))
  have hk' : (b ^ e) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have hcop : Nat.Coprime r (2 ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hr Nat.prime_two).2 hr2)
  have hbe : b ^ e = 1 := by
    have := (pow_gcd_eq_one (a := b ^ e)).2 ⟨hcr, hk'⟩
    rwa [hcop, pow_one] at this
  have := (pow_gcd_eq_one (a := b)).2 ⟨hbr, hbe⟩
  rwa [hre, pow_one] at this

theorem center_quotient_eq_bot {X : Type} [Group X] (hX : CFSG.Open.IsQuasisimple X) :
    Subgroup.center (X ⧸ Subgroup.center X) = ⊥ := by
  obtain ⟨hcomm, hs⟩ := hX
  haveI : Group.IsPerfect X := (Group.isPerfect_def).2 hcomm
  have hp : Group.IsPerfect (X ⧸ Subgroup.center X) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center X))
      (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (X ⧸ Subgroup.center X))
    with h | h
  · exact h
  · exfalso
    have hbot : commutator (X ⧸ Subgroup.center X) = ⊥ := by
      rw [commutator_def, commutator_eq_bot_iff_le_centralizer]
      intro a _
      rw [Subgroup.mem_centralizer_iff]
      intro b _
      exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a)) b
    have htop : (⊤ : Subgroup (X ⧸ Subgroup.center X)) = ⊥ := by
      rw [← (Group.isPerfect_def).1 hp, hbot]
    obtain ⟨a, b, hab⟩ := hs.exists_pair_ne
    exact hab ((Subgroup.mem_bot.mp (htop ▸ Subgroup.mem_top a)).trans
      (Subgroup.mem_bot.mp (htop ▸ Subgroup.mem_top b)).symm)

theorem eq_one_of_bar {X : Type} [Group X] [Finite X] (hX : CFSG.Open.IsQuasisimple X) {r : ℕ}
    (hbar : ∀ (σ : MulAut (X ⧸ Subgroup.center X)) (T : Sylow 2 (X ⧸ Subgroup.center X)),
      σ ^ r = 1 → (∀ y ∈ (T : Subgroup (X ⧸ Subgroup.center X)),
        σ y ∈ (T : Subgroup (X ⧸ Subgroup.center X))) → σ = 1)
    (S : Sylow 2 X) {θ : MulAut X} (hθ : θ ^ r = 1)
    (hS : ∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) : θ = 1 := by
  haveI : Group.IsPerfect X := (Group.isPerfect_def).2 hX.1
  refine CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_eq_one_imp θ
    (hbar (CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient θ)
      (Sylow.mapSurjective (f := QuotientGroup.mk' (Subgroup.center X))
        (QuotientGroup.mk'_surjective _) S) ?_ ?_)
  · have h1 := congrArg (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom X) hθ
    rwa [map_pow, map_one] at h1
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk]
    exact ⟨θ x, hS x hx, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOB

end
