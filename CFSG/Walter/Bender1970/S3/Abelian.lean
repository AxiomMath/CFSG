module

public import Mathlib.GroupTheory.SpecificGroups.ZGroup

public section

namespace CFSG.Walter

universe u

theorem isCyclic_of_card_ker_powMonoidHom_le {p : ℕ} [hp : Fact p.Prime] :
    ∀ (n : ℕ) (P : Type u) [CommGroup P] [Finite P], Nat.card P = n → IsPGroup p P →
      Nat.card (powMonoidHom p : P →* P).ker ≤ p → IsCyclic P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P _ _ hn hP hker
  rcases subsingleton_or_nontrivial P with hs | hnt
  · infer_instance
  set π : P →* P := powMonoidHom p with hπ
  have hpP : p ∣ Nat.card P := by
    rcases hP.card_eq_or_dvd with h | h
    · exact absurd h (Finite.one_lt_card_iff_nontrivial.mpr hnt).ne'
    · exact h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) p hpP
  have hxker : x ∈ π.ker := by
    rw [MonoidHom.mem_ker, hπ, powMonoidHom_apply, ← hx, pow_orderOf_eq_one]
  have hker_ge : p ≤ Nat.card π.ker := by
    rw [← hx, ← Subgroup.orderOf_mk x hxker]
    exact Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard _)
  have hkerp : Nat.card π.ker = p := le_antisymm hker hker_ge
  have hcardP : Nat.card π.range * p = Nat.card P := by
    have h1 : π.ker.index = Nat.card π.range := by
      rw [Subgroup.index_eq_card]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivRange π).toEquiv
    rw [← hkerp, ← h1]
    exact π.ker.index_mul_card
  have hrange_lt : Nat.card π.range < n := by
    have := Nat.card_pos (α := π.range)
    have := hp.out.two_le
    rw [← hn, ← hcardP]
    nlinarith
  have hker' : Nat.card (powMonoidHom p : π.range →* π.range).ker ≤ p := by
    let ι : (powMonoidHom p : π.range →* π.range).ker →* π.ker :=
      { toFun := fun y => ⟨((y : π.range) : P), by
          have h := y.2
          rw [MonoidHom.mem_ker, powMonoidHom_apply] at h
          rw [MonoidHom.mem_ker]
          exact congrArg Subtype.val h⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : Function.Injective ι := by
      intro a b hab
      exact Subtype.ext (Subtype.ext (congrArg (fun z : π.ker => ((z : P))) hab))
    calc Nat.card (powMonoidHom p : π.range →* π.range).ker ≤ Nat.card π.ker :=
          Nat.card_le_card_of_injective ι hι
      _ = p := hkerp
  have hcyc : IsCyclic π.range :=
    ih _ hrange_lt π.range rfl (hP.to_subgroup _) hker'
  by_cases hr1 : Nat.card π.range = 1
  · rw [hr1, one_mul] at hcardP
    exact isCyclic_of_prime_card hcardP.symm
  · obtain ⟨g, hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hcyc
    obtain ⟨h, hh⟩ := g.2
    have hh' : h ^ p = (g : P) := hh
    have hne : h ≠ 1 := by
      intro h1
      apply hr1
      rw [← hg]
      have : g = 1 := by
        apply Subtype.ext
        rw [← hh', h1, one_pow]
        rfl
      rw [this, orderOf_one]
    have hdvd : p ∣ orderOf h := hP.dvd_orderOf hne
    have hord : orderOf h / p = Nat.card π.range := by
      rw [← orderOf_pow_of_dvd hp.out.ne_zero hdvd, hh', Subgroup.orderOf_coe, hg]
    refine isCyclic_of_orderOf_eq_card h ?_
    rw [← hcardP, ← hord, Nat.div_mul_cancel hdvd]

theorem exists_elementary_of_not_isCyclic {G : Type*} [Group G] [Finite G] {U : Subgroup G}
    (hU : IsMulCommutative U) (hcyc : ¬ IsCyclic U) :
    ∃ r : ℕ, r.Prime ∧ ∃ E : Subgroup G, E ≤ U ∧ IsMulCommutative E ∧ (∀ x ∈ E, x ^ r = 1) ∧
      r ^ 2 ≤ Nat.card E := by
  classical
  by_contra hcon
  push Not at hcon
  apply hcyc
  have : Group.IsNilpotent U := by
    let _ : CommGroup U := IsMulCommutative.instCommGroup
    exact CommGroup.isNilpotent
  suffices IsZGroup U by infer_instance
  refine ⟨fun r hr P => ?_⟩
  have : Fact r.Prime := ⟨hr⟩
  have hPcomm : IsMulCommutative (P : Subgroup U) :=
    ⟨⟨fun a b => Subtype.ext (hU.is_comm.comm (a : U) (b : U))⟩⟩
  let _ : CommGroup (P : Subgroup U) := IsMulCommutative.instCommGroup
  refine isCyclic_of_card_ker_powMonoidHom_le (p := r) _ (P : Subgroup U) rfl P.isPGroup' ?_
  set K := (powMonoidHom r : (P : Subgroup U) →* (P : Subgroup U)).ker
  set E : Subgroup G := (K.map (P : Subgroup U).subtype).map U.subtype
  have hEcard : Nat.card E = Nat.card K := by
    rw [Subgroup.card_map_of_injective U.subtype_injective,
      Subgroup.card_map_of_injective (P : Subgroup U).subtype_injective]
  have hEU : E ≤ U := Subgroup.map_subtype_le _
  have hEcomm : IsMulCommutative E := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨_, ⟨a', -, rfl⟩, ha⟩ := a.2
    obtain ⟨_, ⟨b', -, rfl⟩, hb⟩ := b.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb]
    exact congrArg Subtype.val (hU.is_comm.comm _ _)
  have hEexp : ∀ x ∈ E, x ^ r = 1 := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have h : y ^ r = 1 := hy
    have h' := congrArg (fun z : (P : Subgroup U) => ((z : U) : G)) h
    simpa using h'
  have hlt := hcon r hr E hEU hEcomm hEexp
  obtain ⟨k, hk⟩ := (P.isPGroup'.to_subgroup K).exists_card_eq
  rw [hEcard, hk] at hlt
  have hk1 : k ≤ 1 := by
    by_contra h
    push Not at h
    have : r ^ 2 ≤ r ^ k := Nat.pow_le_pow_right hr.pos h
    omega
  rw [hk]
  calc r ^ k ≤ r ^ 1 := Nat.pow_le_pow_right hr.pos hk1
    _ = r := pow_one r

end CFSG.Walter
