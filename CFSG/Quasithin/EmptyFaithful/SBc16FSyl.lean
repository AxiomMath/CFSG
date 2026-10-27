module

public import CFSG.Quasithin.EmptyFaithful.SBc16FDec
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin

namespace SBc16

theorem zpowers_eq_of_mem_of_card_five {H : Type} [Group H] [Finite H] {Q : Subgroup H}
    (hQ : Nat.card Q = 5) {z : H} (hz : z ∈ Q) (hz1 : z ≠ 1) : Subgroup.zpowers z = Q := by
  have hle : Subgroup.zpowers z ≤ Q := (Subgroup.zpowers_le).mpr hz
  have hdvd : orderOf z ∣ 5 := by
    rw [← hQ]
    have := orderOf_dvd_natCard (⟨z, hz⟩ : Q)
    simpa using this
  have hne : orderOf z ≠ 1 := fun h => hz1 (orderOf_eq_one_iff.mp h)
  have h5 : orderOf z = 5 := by
    rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Nat.card_zpowers, h5, hQ]

theorem exists_gen_of_card_five {H : Type} [Group H] [Finite H] {Q : Subgroup H}
    (hQ : Nat.card Q = 5) : ∃ g : H, orderOf g = 5 ∧ Subgroup.zpowers g = Q := by
  have hbot : Q ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hQ
    omega
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have ha1 : (a : H) ≠ 1 := fun h => ha (Subtype.ext h)
  have hz := zpowers_eq_of_mem_of_card_five hQ a.2 ha1
  refine ⟨a, ?_, hz⟩
  have : Nat.card (Subgroup.zpowers (a : H)) = 5 := by rw [hz, hQ]
  rwa [Nat.card_zpowers] at this

theorem card_sylow_eq_five {H : Type} [Group H] [Finite H] (h480 : Nat.card H ∣ 480)
    (h5 : 5 ∣ Nat.card H) (Q : Sylow 5 H) : Nat.card Q = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [Sylow.card_eq_multiplicity]
  have hne : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have h1 : 0 < (Nat.card H).factorization 5 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_five hne h5
  have h2 : (Nat.card H).factorization 5 ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have h25 : 5 ^ 2 ∣ Nat.card H :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five hne).mpr hlt
    have := h25.trans h480
    norm_num at this
  have : (Nat.card H).factorization 5 = 1 := by omega
  rw [this]
  norm_num

theorem pow_ne_one_of_orderOf_eq_five {H : Type} [Group H] {g : H} (hg : orderOf g = 5)
    {k : ℕ} (hk0 : 0 < k) (hk5 : k < 5) : g ^ k ≠ 1 := by
  intro h
  have h1 := orderOf_dvd_of_pow_eq_one h
  rw [hg] at h1
  have := Nat.le_of_dvd hk0 h1
  omega

theorem all_isFive_mem_range {H : Type} [Group H] [Finite H] (φ : H →* GL25)
    (hφ : Function.Injective φ) (u : H) (hu : IsFive (φ u))
    (hmove : ¬ (Subgroup.zpowers u).Normal) :
    ∀ x : GL25, IsFive x → x ∈ φ.range := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hu5 : orderOf u = 5 := by
    rw [← orderOf_injective φ hφ u]
    exact orderOf_eq_prime hu.1 hu.2
  have h480 : Nat.card H ∣ 480 := by
    rw [← card_GL25]
    have h1 : Nat.card H = Nat.card φ.range := Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv
    rw [h1]
    exact Subgroup.card_subgroup_dvd_card _
  have h5 : 5 ∣ Nat.card H := hu5 ▸ orderOf_dvd_natCard u
  have hQ := card_sylow_eq_five h480 h5
  have hmod : Nat.card (Sylow 5 H) ≡ 1 [MOD 5] := card_sylow_modEq_one 5 H
  have hn1 : Nat.card (Sylow 5 H) ≠ 1 := by
    intro hn
    have hsub : Subsingleton (Sylow 5 H) := (Nat.card_eq_one_iff_unique.mp hn).1
    have hp : IsPGroup 5 (Subgroup.zpowers u) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu5]; norm_num)
    obtain ⟨Q, hQu⟩ := hp.exists_le_sylow
    have hQeq : Subgroup.zpowers u = Q :=
      Subgroup.eq_of_le_of_card_ge hQu (by rw [hQ Q, Nat.card_zpowers, hu5])
    have hnorm : (Q : Subgroup H).Normal := Sylow.normal_of_subsingleton Q
    exact hmove (hQeq ▸ hnorm)
  have hn6 : 6 ≤ Nat.card (Sylow 5 H) := by
    have hpos : 0 < Nat.card (Sylow 5 H) := Nat.card_pos
    unfold Nat.ModEq at hmod
    omega
  choose gen hgen using fun Q : Sylow 5 H => exists_gen_of_card_five (hQ Q)
  let f : Sylow 5 H × Fin 4 → GL25 := fun p => φ ((gen p.1) ^ (p.2.val + 1))
  have hfinj : Function.Injective f := by
    rintro ⟨Q, i⟩ ⟨Q', j⟩ hfij
    have hz : (gen Q) ^ (i.val + 1) = (gen Q') ^ (j.val + 1) := hφ hfij
    have hz1 : (gen Q) ^ (i.val + 1) ≠ 1 :=
      pow_ne_one_of_orderOf_eq_five (hgen Q).1 (by omega) (by have := i.is_lt; omega)
    have hzQ : (gen Q) ^ (i.val + 1) ∈ Q := by
      have : gen Q ∈ (Q : Subgroup H) := by rw [← (hgen Q).2]; exact Subgroup.mem_zpowers _
      exact Subgroup.pow_mem _ this _
    have hzQ' : (gen Q') ^ (j.val + 1) ∈ Q' := by
      have : gen Q' ∈ (Q' : Subgroup H) := by rw [← (hgen Q').2]; exact Subgroup.mem_zpowers _
      exact Subgroup.pow_mem _ this _
    rw [← hz] at hzQ'
    have e1 := zpowers_eq_of_mem_of_card_five (hQ Q) hzQ hz1
    have e2 := zpowers_eq_of_mem_of_card_five (hQ Q') hzQ' hz1
    have hQQ : Q = Q' := Sylow.ext (e1.symm.trans e2)
    subst hQQ
    have hmodeq := (pow_eq_pow_iff_modEq).mp hz
    rw [(hgen Q).1] at hmodeq
    unfold Nat.ModEq at hmodeq
    have hi := i.is_lt
    have hj := j.is_lt
    have hij : i = j := Fin.ext (by omega)
    rw [hij]
  have hfS : ∀ p, IsFive (f p) := by
    rintro ⟨Q, i⟩
    have hg5 : gen Q ^ 5 = 1 := by
      have := pow_orderOf_eq_one (gen Q)
      rwa [(hgen Q).1] at this
    have h1 : (gen Q) ^ (i.val + 1) ≠ 1 :=
      pow_ne_one_of_orderOf_eq_five (hgen Q).1 (by omega) (by have := i.is_lt; omega)
    refine ⟨?_, ?_⟩
    · show φ ((gen Q) ^ (i.val + 1)) ^ 5 = 1
      rw [← map_pow, ← pow_mul, mul_comm, pow_mul, hg5, one_pow, map_one]
    · intro h
      exact h1 (hφ (h.trans (map_one φ).symm))
  intro x hx
  by_contra hxr
  have hsubset : Set.range f ⊆ {y : GL25 | IsFive y} \ {x} := by
    rintro _ ⟨p, rfl⟩
    refine ⟨hfS p, ?_⟩
    intro hxp
    exact hxr ⟨_, hxp⟩
  have hfin : ({y : GL25 | IsFive y}).Finite := Set.toFinite _
  have hc1 : (Set.range f).ncard ≤ ({y : GL25 | IsFive y} \ {x}).ncard :=
    Set.ncard_le_ncard hsubset hfin.sdiff
  have hc2 : ({y : GL25 | IsFive y} \ {x}).ncard + 1 = ({y : GL25 | IsFive y}).ncard :=
    Set.ncard_sdiff_singleton_add_one hx hfin
  have hc3 : (Set.range f).ncard = Nat.card (Sylow 5 H) * 4 := by
    rw [Set.ncard_range_of_injective hfinj, Nat.card_prod, Nat.card_fin]
  have := ncard_isFive_le
  omega

end SBc16

end CFSG.Quasithin
