module

public import CFSG.GroupTheory.FixedPointCount
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Rank

public section

open MulAction

namespace CFSG.Sporadic.J4.Struct

section Orbit

variable {G X : Type*} [Group G] [MulAction G X]

instance isPretransitive_orbit (w : X) : IsPretransitive G (orbit G w) := by
  refine ⟨fun p q => ?_⟩
  obtain ⟨_, g, rfl⟩ := p
  obtain ⟨_, k, rfl⟩ := q
  refine ⟨k * g⁻¹, Subtype.ext ?_⟩
  change (k * g⁻¹) • g • w = k • w
  rw [smul_smul, inv_mul_cancel_right]

theorem stabilizer_orbit_root (w : X) :
    stabilizer G (⟨w, mem_orbit_self w⟩ : orbit G w) = stabilizer G w := by
  ext g
  rw [mem_stabilizer_iff, mem_stabilizer_iff, Subtype.ext_iff]
  rfl

theorem card_fix_orbit_eq (w : X) (h : G) :
    Nat.card {x : orbit G w // h • x = x} = Nat.card {x : X // x ∈ orbit G w ∧ h • x = x} :=
  Nat.card_congr
    { toFun := fun x => ⟨x.1.1, x.1.2, congrArg Subtype.val x.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_fix_orbit_mul [Finite G] (w : X) (h : G) :
    Nat.card {x : X // x ∈ orbit G w ∧ h • x = x} * Nat.card (stabilizer G w) =
      Nat.card (Subgroup.centralizer ({h} : Set G)) *
        Nat.card {s : G // s ∈ stabilizer G w ∧ IsConj h s} := by
  have e := CFSG.GroupAction.card_fix_mul_card_stabilizer (G := G) (X := orbit G w)
    ⟨w, mem_orbit_self w⟩ h
  rw [stabilizer_orbit_root, card_fix_orbit_eq] at e
  exact e

theorem card_centralizer_mul_card_conj [Finite G] (h : G) :
    Nat.card (Subgroup.centralizer ({h} : Set G)) * Nat.card {s : G // IsConj h s} =
      Nat.card G := by
  rw [Subgroup.nat_card_centralizer_nat_card_stabilizer]
  have e := Subgroup.card_mul_index (stabilizer (ConjAct G) h)
  rw [index_stabilizer, Nat.card_congr (ConjAct.ofConjAct (G := G)).toEquiv] at e
  rw [← e, ← Nat.card_coe_set_eq]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight fun s => by rw [ConjAct.mem_orbit_conjAct, isConj_comm])

theorem card_fix_orbit_mul_card_conj [Finite G] (w : X) (h : G) :
    Nat.card {x : X // x ∈ orbit G w ∧ h • x = x} * Nat.card {s : G // IsConj h s} =
      (orbit G w).ncard * Nat.card {s : G // s ∈ stabilizer G w ∧ IsConj h s} := by
  have e1 := card_fix_orbit_mul w h
  have e2 := card_centralizer_mul_card_conj h
  have e3 := Subgroup.card_mul_index (stabilizer G w)
  rw [index_stabilizer] at e3
  have hS : 0 < Nat.card (stabilizer G w) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hS
  calc Nat.card (stabilizer G w) * (Nat.card {x : X // x ∈ orbit G w ∧ h • x = x} *
        Nat.card {s : G // IsConj h s})
      = Nat.card (Subgroup.centralizer ({h} : Set G)) *
          Nat.card {s : G // s ∈ stabilizer G w ∧ IsConj h s} * Nat.card {s : G // IsConj h s} := by
        rw [← e1]
        ring
    _ = Nat.card G * Nat.card {s : G // s ∈ stabilizer G w ∧ IsConj h s} := by
        rw [← e2]
        ring
    _ = _ := by
        rw [← e3]
        ring

theorem card_fix_conj (O : Set X) (hO : ∀ g : G, ∀ x ∈ O, g • x ∈ O) {h k : G}
    (hc : IsConj h k) :
    Nat.card {x : X // x ∈ O ∧ h • x = x} = Nat.card {x : X // x ∈ O ∧ k • x = x} := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hc
  refine Nat.card_congr
    { toFun := fun x => ⟨c • x.1, hO c _ x.2.1, by
        rw [smul_smul, inv_mul_cancel_right, mul_smul, x.2.2]⟩
      invFun := fun x => ⟨c⁻¹ • x.1, hO c⁻¹ _ x.2.1, by
        have e := congrArg (c⁻¹ • ·) x.2.2
        simp only [smul_smul] at e
        rw [smul_smul]
        rwa [show c⁻¹ * (c * h * c⁻¹) = h * c⁻¹ by group] at e⟩
      left_inv := fun x => Subtype.ext (inv_smul_smul c x.1)
      right_inv := fun x => Subtype.ext (smul_inv_smul c x.1) }

theorem card_stabilizer_smul [Finite G] (g : G) (w : X) :
    Nat.card (stabilizer G (g • w)) = Nat.card (stabilizer G w) := by
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem fix_orbit_eq_empty [Finite G] {p : ℕ} (w : X) {h : G} (ho : orderOf h = p)
    (hp : ¬ p ∣ Nat.card (stabilizer G w)) {x : X} (hx : x ∈ orbit G w) : h • x ≠ x := by
  intro hfix
  obtain ⟨g, rfl⟩ := hx
  apply hp
  rw [← card_stabilizer_smul g w, ← ho]
  exact Subgroup.orderOf_dvd_natCard (stabilizer G (g • w)) hfix

theorem card_fix_orbit_eq_zero [Finite G] (w : X) (h : G)
    (hc : ∀ s ∈ stabilizer G w, ¬ IsConj h s) :
    Nat.card {x : X // x ∈ orbit G w ∧ h • x = x} = 0 := by
  have e := card_fix_orbit_mul w h
  have h0 : Nat.card {s : G // s ∈ stabilizer G w ∧ IsConj h s} = 0 := by
    have : IsEmpty {s : G // s ∈ stabilizer G w ∧ IsConj h s} := ⟨fun s => hc s.1 s.2.1 s.2.2⟩
    exact Nat.card_of_isEmpty
  rw [h0, mul_zero] at e
  exact (Nat.mul_eq_zero.1 e).resolve_right Nat.card_pos.ne'

end Orbit

section Sylow

variable {L : Type*} [Group L] [Finite L] {p : ℕ} [hp : Fact p.Prime]

theorem exists_sylow_eq_zpowers (hp2 : ¬ p ^ 2 ∣ Nat.card L) {g : L} (hg : orderOf g = p) :
    ∃ Q : Sylow p L, (Q : Subgroup L) = Subgroup.zpowers g := by
  have hcard : Nat.card (Subgroup.zpowers g) = p := by rw [Nat.card_zpowers, hg]
  have hP : IsPGroup p (Subgroup.zpowers g) := IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  refine ⟨Q, (Subgroup.eq_of_le_of_card_ge hQ ?_).symm⟩
  rw [hcard, Q.card_eq_multiplicity]
  have hpos : Nat.card L ≠ 0 := Nat.card_pos.ne'
  have hlt : Nat.factorization (Nat.card L) p < 2 := by
    by_contra hge
    exact hp2 ((Nat.pow_dvd_pow p (not_lt.1 hge)).trans (Nat.ordProj_dvd _ p))
  interval_cases Nat.factorization (Nat.card L) p
  · simpa using hp.out.one_lt.le
  · simp

theorem card_orderOf_eq_le (hp2 : ¬ p ^ 2 ∣ Nat.card L) (P : Sylow p L) :
    Nat.card {g : L // orderOf g = p} ≤ (p - 1) * (Subgroup.normalizer (P : Set L)).index := by
  classical
  have : Fintype L := Fintype.ofFinite L
  choose f hf using fun g : {g : L // orderOf g = p} => exists_sylow_eq_zpowers hp2 g.2
  rw [← Sylow.card_eq_index_normalizer P]
  have hfib : ∀ Q : Sylow p L, Nat.card {g : {g : L // orderOf g = p} // f g = Q} ≤ p - 1 := by
    intro Q
    have hQ : Nat.card (Q : Subgroup L) = p ∨ ∀ g : {g : L // orderOf g = p}, f g ≠ Q := by
      by_cases hex : ∃ g : {g : L // orderOf g = p}, f g = Q
      · obtain ⟨g, rfl⟩ := hex
        left
        rw [hf g, Nat.card_zpowers, g.2]
      · exact Or.inr fun g hg => hex ⟨g, hg⟩
    rcases hQ with hQ | hQ
    · have hmem : ∀ g : {g : {g : L // orderOf g = p} // f g = Q}, g.1.1 ∈ (Q : Subgroup L) := by
        intro g
        have e := hf g.1
        rw [g.2] at e
        rw [e]
        exact Subgroup.mem_zpowers _
      let e : {g : {g : L // orderOf g = p} // f g = Q} → {x : (Q : Subgroup L) // x ≠ 1} :=
        fun g => ⟨⟨g.1.1, hmem g⟩, fun h1 => by
          have h2 := g.1.2
          rw [show g.1.1 = 1 from congrArg Subtype.val h1, orderOf_one] at h2
          exact hp.out.one_lt.ne h2⟩
      have he : Function.Injective e := fun a b h => Subtype.ext (Subtype.ext
        (congrArg (fun x : {x : (Q : Subgroup L) // x ≠ 1} => (x.1 : L)) h))
      have hlt := Finite.card_subtype_lt (p := fun x : (Q : Subgroup L) => x ≠ 1) (x := 1)
        (fun h => h rfl)
      have hle := Nat.card_le_card_of_injective e he
      rw [hQ] at hlt
      omega
    · have : IsEmpty {g : {g : L // orderOf g = p} // f g = Q} := ⟨fun g => hQ g.1 g.2⟩
      rw [Nat.card_of_isEmpty]
      exact Nat.zero_le _
  have : Fintype (Sylow p L) := Fintype.ofFinite _
  calc Nat.card {g : L // orderOf g = p}
      = ∑ Q : Sylow p L, Nat.card {g : {g : L // orderOf g = p} // f g = Q} := by
        rw [← Nat.card_sigma, Nat.card_congr (Equiv.sigmaFiberEquiv f)]
    _ ≤ ∑ _Q : Sylow p L, (p - 1) := Finset.sum_le_sum fun Q _ => hfib Q
    _ = (p - 1) * Nat.card (Sylow p L) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm, Nat.card_eq_fintype_card]

theorem index_normalizer_spec (P : Sylow p L) :
    (Subgroup.normalizer (P : Set L)).index ≡ 1 [MOD p] ∧
      (Subgroup.normalizer (P : Set L)).index ∣ (P : Subgroup L).index := by
  rw [← Sylow.card_eq_index_normalizer P]
  exact ⟨card_sylow_modEq_one p L, P.card_dvd_index⟩

end Sylow

end CFSG.Sporadic.J4.Struct

end
