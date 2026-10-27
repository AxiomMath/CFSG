module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.StandardType

@[expose] def IsAlternatingEightCover (J : Type*) [Group J] : Prop :=
  commutator J = ⊤ ∧ Nonempty ((J ⧸ Subgroup.center J) ≃* alternatingGroup (Fin 8)) ∧
    IsPGroup 2 (Subgroup.center J)

section Lift

theorem exists_orderOf_prime_conj_sq_of_quotient {J : Type*} [Group J] [Finite J]
    (hZ : IsPGroup 2 (Subgroup.center J)) {A : Type*} [Group A]
    (e : (J ⧸ Subgroup.center J) ≃* A) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a b : A}
    (ha : orderOf a = p) (hab : b * a * b⁻¹ = a ^ 2) :
    ∃ x y : J, orderOf x = p ∧ y * x * y⁻¹ = x ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  let Z := Subgroup.center J
  let π : J →* A := e.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hker : π.ker = Z := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' Z x) = 1 ↔ x ∈ Z
    rw [← map_one e, e.injective.eq_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hZ
  have hZkill : ∀ z : Z, z ^ (2 ^ m) = 1 := by
    intro z
    rw [← hm]
    exact pow_card_eq_one'
  have hcop : Nat.Coprime p (2 ^ m) :=
    (Nat.coprime_primes hp Nat.prime_two).mpr hp2 |>.pow_right m
  obtain ⟨t, ht1, ht2⟩ := Nat.chineseRemainder hcop 1 0
  have htmod : t % p = 1 := by
    have h := ht1
    rw [Nat.ModEq] at h
    rwa [Nat.mod_eq_of_lt hp.one_lt] at h
  have htdvd : 2 ^ m ∣ t := Nat.modEq_zero_iff_dvd.mp ht2
  obtain ⟨q, hq⟩ := e.surjective a
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk'_surjective Z q
  obtain ⟨q', hq'⟩ := e.surjective b
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk'_surjective Z q'
  have hπx₀ : π x₀ = a := hq
  have hπy₀ : π y₀ = b := hq'
  have hat : a ^ t = a := by
    rw [← pow_mod_orderOf a t, ha, htmod, pow_one]
  have hπx : π (x₀ ^ t) = a := by rw [map_pow, hπx₀, hat]
  have ha_ne : a ≠ 1 := by
    intro h
    exact hp.ne_one (ha.symm.trans (orderOf_eq_one_iff.mpr h))
  have hx_ne : x₀ ^ t ≠ 1 := by
    intro h
    exact ha_ne (by rw [← hπx, h, map_one])
  have hz0 : x₀ ^ p ∈ Z := by
    rw [← hker, MonoidHom.mem_ker]
    show π (x₀ ^ p) = 1
    rw [map_pow, hπx₀, ← ha]
    exact pow_orderOf_eq_one a
  have hz0pow : (x₀ ^ p) ^ (2 ^ m) = 1 := by
    have := hZkill ⟨x₀ ^ p, hz0⟩
    simpa using Subtype.ext_iff.mp this
  have hx_pow : (x₀ ^ t) ^ p = 1 := by
    obtain ⟨s, hs⟩ := htdvd
    rw [← pow_mul, mul_comm t p, pow_mul, hs, pow_mul, hz0pow, one_pow]
  let z := (x₀ ^ 2)⁻¹ * (y₀ * x₀ * y₀⁻¹)
  have hz : z ∈ Z := by
    rw [← hker, MonoidHom.mem_ker]
    show π ((x₀ ^ 2)⁻¹ * (y₀ * x₀ * y₀⁻¹)) = 1
    simp only [map_mul, map_pow, map_inv, hπx₀, hπy₀, hab]
    group
  have hzpow : z ^ (2 ^ m) = 1 := by
    have := hZkill ⟨z, hz⟩
    simpa using Subtype.ext_iff.mp this
  have hzpow_t : z ^ t = 1 := by
    obtain ⟨s, hs⟩ := htdvd
    rw [hs, pow_mul, hzpow, one_pow]
  have hyx : y₀ * x₀ * y₀⁻¹ = x₀ ^ 2 * z := by
    dsimp only [z]
    group
  have hcomm : Commute (x₀ ^ 2) z := Subgroup.mem_center_iff.mp hz (x₀ ^ 2)
  have hconj : y₀ * (x₀ ^ t) * y₀⁻¹ = (x₀ ^ t) ^ 2 := by
    rw [← conj_pow (a := y₀) (b := x₀) (i := t), hyx, hcomm.mul_pow, hzpow_t, mul_one]
    rw [← pow_mul, ← pow_mul, mul_comm 2 t]
  exact ⟨x₀ ^ t, y₀, orderOf_eq_prime hx_pow hx_ne, hconj⟩

end Lift

section Elements

theorem exists_orderOf_five_conj_sq_alternatingEight :
    ∃ a b : alternatingGroup (Fin 8), orderOf a = 5 ∧ b * a * b⁻¹ = a ^ 2 := by
  let c : Equiv.Perm (Fin 8) := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4
  let d : Equiv.Perm (Fin 8) := Equiv.swap 1 2 * Equiv.swap 2 4 * Equiv.swap 4 3 * Equiv.swap 5 6
  have hc : c ∈ alternatingGroup (Fin 8) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    simp [c]
  have hd : d ∈ alternatingGroup (Fin 8) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    simp [d]
  refine ⟨⟨c, hc⟩, ⟨d, hd⟩, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    exact orderOf_eq_prime (by decide +kernel) (by decide)
  · apply Subtype.ext
    change d * c * d⁻¹ = c ^ 2
    decide +kernel

theorem exists_orderOf_seven_conj_sq_alternatingEight :
    ∃ a b : alternatingGroup (Fin 8), orderOf a = 7 ∧ b * a * b⁻¹ = a ^ 2 := by
  let c : Equiv.Perm (Fin 8) :=
    Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4 * Equiv.swap 4 5 *
      Equiv.swap 5 6
  let d : Equiv.Perm (Fin 8) := Equiv.swap 1 2 * Equiv.swap 2 4 * Equiv.swap 3 6 * Equiv.swap 6 5
  have hc : c ∈ alternatingGroup (Fin 8) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    simp [c]
  have hd : d ∈ alternatingGroup (Fin 8) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    simp [d]
  refine ⟨⟨c, hc⟩, ⟨d, hd⟩, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]
    haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
    exact orderOf_eq_prime (by decide +kernel) (by decide)
  · apply Subtype.ext
    change d * c * d⁻¹ = c ^ 2
    decide +kernel

variable {J : Type*} [Group J] [Finite J]

theorem IsAlternatingEightCover.exists_orderOf_five_conj_sq (hJ : IsAlternatingEightCover J) :
    ∃ x y : J, orderOf x = 5 ∧ y * x * y⁻¹ = x ^ 2 := by
  obtain ⟨-, ⟨e⟩, hZ⟩ := hJ
  obtain ⟨a, b, ha, hab⟩ := exists_orderOf_five_conj_sq_alternatingEight
  exact exists_orderOf_prime_conj_sq_of_quotient hZ e Nat.prime_five (by norm_num) ha hab

theorem IsAlternatingEightCover.exists_orderOf_seven_conj_sq (hJ : IsAlternatingEightCover J) :
    ∃ x y : J, orderOf x = 7 ∧ y * x * y⁻¹ = x ^ 2 := by
  obtain ⟨-, ⟨e⟩, hZ⟩ := hJ
  obtain ⟨a, b, ha, hab⟩ := exists_orderOf_seven_conj_sq_alternatingEight
  exact exists_orderOf_prime_conj_sq_of_quotient hZ e (by decide) (by decide) ha hab

theorem IsAlternatingEightCover.eq_top_of_normal (hJ : IsAlternatingEightCover J)
    {N : Subgroup J} (hN : N.Normal) (h : ¬ N ≤ Subgroup.center J) : N = ⊤ := by
  obtain ⟨hperf, ⟨e⟩, hZ⟩ := hJ
  haveI : N.Normal := hN
  let Z := Subgroup.center J
  let π : J →* alternatingGroup (Fin 8) := e.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hker : π.ker = Z := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' Z x) = 1 ↔ x ∈ Z
    rw [← map_one e, e.injective.eq_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hsurj : Function.Surjective π := by
    intro g
    obtain ⟨q, hq⟩ := e.surjective g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z q
    exact ⟨x, hq⟩
  haveI : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : (N.map π).Normal := hN.map π hsurj
  rcases (Subgroup.Normal.eq_bot_or_eq_top (N.map π)) with hbot | htop
  · exfalso
    apply h
    have h1 : N ≤ π.ker := (Subgroup.map_eq_bot_iff (H := N) (f := π)).mp hbot
    rw [hker] at h1
    exact h1
  · have hsup : N ⊔ Z = ⊤ := by
      rw [eq_top_iff]
      intro g _
      have hgm : π g ∈ N.map π := by rw [htop]; trivial
      obtain ⟨n, hnN, hn⟩ := Subgroup.mem_map.mp hgm
      have hz : n⁻¹ * g ∈ Z := by
        rw [← hker, MonoidHom.mem_ker]
        show π (n⁻¹ * g) = 1
        rw [map_mul, map_inv, hn, inv_mul_cancel]
      have hg : g = n * (n⁻¹ * g) := by group
      rw [hg]
      exact Subgroup.mul_mem_sup hnN hz
    have hle : commutator J ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top (N := N) hsup
        (inferInstance : IsMulCommutative Z)
    rw [eq_top_iff]
    intro g _
    exact hle (by rw [hperf]; trivial)

theorem IsAlternatingEightCover.map_eq_one_of_map_eq_one (hJ : IsAlternatingEightCover J)
    {M : Type*} [Monoid M] {x : J} (hx : orderOf x = 5 ∨ orderOf x = 7) (ρ : J →* M)
    (hρ : ρ x = 1) (g : J) : ρ g = 1 := by
  have hZ : IsPGroup 2 (Subgroup.center J) := hJ.2.2
  let K := (ρ.toHomUnits).ker
  have hKx : x ∈ K := by
    rw [MonoidHom.mem_ker]
    exact Units.ext (by rw [MonoidHom.coe_toHomUnits, hρ, Units.val_one])
  have hKnot : ¬ K ≤ Subgroup.center J := by
    intro hle
    have hxc : x ∈ Subgroup.center J := hle hKx
    have h2 : ∃ k, orderOf x = 2 ^ k := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hZ) (⟨x, hxc⟩ : Subgroup.center J)
      exact ⟨k, (Subgroup.orderOf_mk x hxc).symm.trans hk⟩
    obtain ⟨k, hk⟩ := h2
    rcases hx with h5 | h7
    · have hdvd : 5 ∣ 2 ^ k := by rw [← hk, h5]
      have : 5 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_five hdvd
      norm_num at this
    · have hdvd : 7 ∣ 2 ^ k := by rw [← hk, h7]
      have : 7 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by decide) hdvd
      norm_num at this
  have hKtop : K = ⊤ := IsAlternatingEightCover.eq_top_of_normal hJ inferInstance hKnot
  have hKg : g ∈ K := by rw [hKtop]; trivial
  have h1 : ρ.toHomUnits g = 1 := hKg
  have : (ρ.toHomUnits g : M) = ((1 : Mˣ) : M) := congrArg Units.val h1
  rwa [MonoidHom.coe_toHomUnits, Units.val_one] at this

end Elements

end CFSG.StandardType
