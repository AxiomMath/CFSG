module

public import CFSG.Quasithin.Vol2.Ch8Sec2L827XSL2Dickson
public import CFSG.Quasithin.Vol2.Ch8Sec2L827XSL2Line
public import CFSG.Quasithin.Vol2.Ch8Sec2L827XInputs

public section

namespace CFSG.Quasithin.H13.L827X.SL2Orb

section Three

theorem not_perfect_nonsolvable_three {E : Type*} [AddCommGroup E] [Module (ZMod 3) E]
    [Module.Finite (ZMod 3) E] (hE : Module.finrank (ZMod 3) E = 2)
    (Λ : Subgroup (E ≃ₗ[ZMod 3] E)) [Group.IsPerfect Λ] (hns : ¬ Group.IsSolvable Λ) : False := by
  classical
  let b : Module.Basis (Fin 2) (ZMod 3) E := Module.finBasisOfFinrankEq (ZMod 3) E hE
  have hK : ⁅(slHom b Λ).range, (slHom b Λ).range⁆ = (slHom b Λ).range :=
    Subgroup.isPerfect_iff.mp (Group.IsPerfect.range (slHom b Λ))
  have hbot := CFSG.Quasithin.Dickson.sl2_three_perfect_eq_bot (slHom b Λ).range hK
  have h1 : ∀ g : Λ, g = 1 := by
    intro g
    apply slHom_injective b Λ
    rw [map_one]
    have hmem : slHom b Λ g ∈ (slHom b Λ).range := MonoidHom.mem_range.mpr ⟨g, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  haveI : Subsingleton Λ := ⟨fun g h => (h1 g).trans (h1 h).symm⟩
  exact hns inferInstance

end Three

section Orbit

variable {p : ℕ} [Fact p.Prime] {E : Type*} [AddCommGroup E] [Module (ZMod p) E] [Finite E]

theorem card_stab_dvd (hE : Module.finrank (ZMod p) E = 2) (Λ : Subgroup (E ≃ₗ[ZMod p] E))
    [Group.IsPerfect Λ] {x : E} (hx : x ≠ 0) :
    Nat.card (MulAction.stabilizer Λ x) ∣ p := by
  classical
  obtain ⟨b, hb⟩ := exists_basis_zero_eq hE hx
  have hinj : Function.Injective
      ((Λ.subtype).comp (MulAction.stabilizer Λ x).subtype) :=
    Subtype.val_injective.comp Subtype.val_injective
  have hdiv := (fixing_comm_card_dvd (F := ZMod p) (E := E) b
    ((Λ.subtype).comp (MulAction.stabilizer Λ x).subtype) hinj
    (fun g => det_eq_one_of_isPerfect Λ (g : Λ))
    (fun g => by
      rw [hb]
      exact MulAction.mem_stabilizer_iff.mp g.2)).2
  simpa using hdiv

theorem orbit_ncard_ge (hp5 : 5 ≤ p) (hE : Module.finrank (ZMod p) E = 2)
    (Λ : Subgroup (E ≃ₗ[ZMod p] E)) [Group.IsPerfect Λ]
    (hcore : Nat.card Λ = 120 ∨ p * (p ^ 2 - 1) ≤ Nat.card Λ) {x : E} (hx : x ≠ 0) :
    24 ≤ Set.ncard {y : E | ∃ g ∈ Λ, g x = y} := by
  classical
  have hOorb : {y : E | ∃ g ∈ Λ, g x = y} = MulAction.orbit Λ x := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
    · rintro ⟨⟨g, hg⟩, rfl⟩
      exact ⟨g, hg, rfl⟩
  rw [hOorb]
  have hstab : Nat.card (MulAction.stabilizer Λ x) * (MulAction.orbit Λ x).ncard =
      Nat.card Λ := by
    rw [← MulAction.index_stabilizer Λ x]
    exact Subgroup.card_mul_index _
  have hdvd := card_stab_dvd hE Λ hx
  have hp : p.Prime := Fact.out
  have hp25 : 25 ≤ p ^ 2 := by nlinarith
  have h24 : 24 ≤ p ^ 2 - 1 := by omega
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
  ·
    rw [h1, one_mul] at hstab
    rw [hstab]
    rcases hcore with h | h
    · omega
    · nlinarith
  ·
    rw [h1] at hstab
    rcases hcore with h | h
    ·
      have hpd : p ∣ 120 := ⟨(MulAction.orbit Λ x).ncard, by rw [← h, ← hstab]⟩
      have hmem : p ∈ Nat.divisors 120 := Nat.mem_divisors.mpr ⟨hpd, by norm_num⟩
      have hall : ∀ q ∈ Nat.divisors 120, Nat.Prime q → 5 ≤ q → q ≤ 5 := by decide
      have hp_le : p ≤ 5 := hall p hmem hp (hp5)
      have hp5eq : p = 5 := by omega
      subst hp5eq
      omega
    ·
      have hle : p * (p ^ 2 - 1) ≤ p * (MulAction.orbit Λ x).ncard := by
        rw [hstab]
        exact h
      have hO : p ^ 2 - 1 ≤ (MulAction.orbit Λ x).ncard :=
        Nat.le_of_mul_le_mul_left hle hp.pos
      omega

end Orbit

end CFSG.Quasithin.H13.L827X.SL2Orb

namespace CFSG.Quasithin.H13.L827X

open CFSG.Quasithin.H13.L827X.SL2Orb

theorem sl2OrbitFacts_holds :
    SL2OrbitFacts := by
  unfold SL2OrbitFacts
  intro p hp hp2 E _ _ _ hE Λ hperf hns
  have hp5 : 5 ≤ p := by
    have hprime : Nat.Prime p := Fact.out
    have h2 := hprime.two_le
    by_contra hlt
    push Not at hlt
    interval_cases p
    · exact absurd rfl hp2
    · haveI : Module.Finite (ZMod 3) E := Module.Finite.of_finite
      exact (SL2Orb.not_perfect_nonsolvable_three hE Λ hns).elim
    · norm_num at hprime
  haveI : Module.Finite (ZMod p) E := Module.Finite.of_finite
  have hcore := SL2Orb.core_disj hp2 hE Λ hns
  refine ⟨hp5, ?_, ?_⟩
  · intro x hx
    exact SL2Orb.orbit_ncard_ge hp5 hE Λ hcore hx
  · intro x hx ℓ hℓ
    exact SL2Orb.line_bound hE Λ hns hx ℓ hℓ

end CFSG.Quasithin.H13.L827X

end
