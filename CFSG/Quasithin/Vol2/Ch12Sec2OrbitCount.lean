module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitTransfer

public section

namespace CFSG.Quasithin.H13.Orbit

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu

variable {V : Type*} [CommGroup V]

theorem orbitIn_eq_orbit (H : Subgroup (MulAut V)) (v : V) :
    orbitIn H v = MulAction.orbit ↥H v := by
  ext w
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, hh⟩, rfl⟩
  · rintro ⟨h, rfl⟩
    exact ⟨h, h.2, rfl⟩

theorem ne_one_of_mem_orbitIn {H : Subgroup (MulAut V)} {v w : V} (hv : v ≠ 1)
    (hw : w ∈ orbitIn H v) : w ≠ 1 := by
  obtain ⟨h, -, rfl⟩ := hw
  intro h1
  exact hv (h.injective (h1.trans (map_one h).symm))

theorem mem_fixedPoints_zpowers_iff {G α : Type*} [Group G] [MulAction G α] (a : G) (x : α) :
    x ∈ MulAction.fixedPoints ↥(Subgroup.zpowers a) α ↔ a • x = x := by
  constructor
  · intro h
    exact h ⟨a, Subgroup.mem_zpowers a⟩
  · intro h g
    have hle : Subgroup.zpowers a ≤ MulAction.stabilizer G x :=
      (Subgroup.zpowers_le (H := MulAction.stabilizer G x)).2 h
    exact hle g.2

theorem mem_fixV_zpowers {a : MulAut V} {v : V} : v ∈ fixV (Subgroup.zpowers a) ↔ a v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem card_fixV_modEq [Finite V] {a : MulAut V} {p : ℕ} [Fact p.Prime] (ha : orderOf a = p) :
    Nat.card V ≡ Nat.card ↥(fixV (Subgroup.zpowers a)) [MOD p] := by
  have hP : IsPGroup p ↥(Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  have h := hP.card_modEq_card_fixedPoints V
  have e : Nat.card ↑(MulAction.fixedPoints ↥(Subgroup.zpowers a) V) =
      Nat.card ↥(fixV (Subgroup.zpowers a)) := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro x
    rw [mem_fixedPoints_zpowers_iff, mem_fixV_zpowers]
    rfl
  rwa [e] at h

theorem card_orbitIn_modEq [Finite V] {H : Subgroup (MulAut V)} {a : ↥H} {p : ℕ} [Fact p.Prime]
    (ha : orderOf a = p) (v : V) :
    Nat.card ↥(orbitIn H v) ≡
      Nat.card ↥(orbitIn H v ∩ (fixV (Subgroup.zpowers (a : MulAut V)) : Set V)) [MOD p] := by
  have hP : IsPGroup p ↥(Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  have h := hP.card_modEq_card_fixedPoints ↥(MulAction.orbit ↥H v)
  have e : Nat.card ↑(MulAction.fixedPoints ↥(Subgroup.zpowers a) ↥(MulAction.orbit ↥H v)) =
      Nat.card ↥(orbitIn H v ∩ (fixV (Subgroup.zpowers (a : MulAut V)) : Set V)) := by
    apply Nat.card_congr
    refine
      { toFun := fun x => ⟨x.1.1, (orbitIn_eq_orbit H v).symm ▸ x.1.2, ?_⟩
        invFun := fun w => ⟨⟨w.1, (orbitIn_eq_orbit H v) ▸ w.2.1⟩, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · have hx := (mem_fixedPoints_zpowers_iff a x.1).1 x.2
      rw [SetLike.mem_coe, mem_fixV_zpowers]
      exact congrArg Subtype.val hx
    · rw [mem_fixedPoints_zpowers_iff]
      apply Subtype.ext
      exact mem_fixV_zpowers.1 w.2.2
  rw [orbitIn_eq_orbit H v] at e ⊢
  rwa [e] at h

theorem card_fixV_ne [Finite V] {H : Subgroup (MulAut V)} {a : ↥H} (ha : a ≠ 1) :
    Nat.card ↥(fixV (Subgroup.zpowers (a : MulAut V))) ≠ Nat.card V := by
  intro h
  apply ha
  have htop := Subgroup.eq_top_of_card_eq _ h
  apply Subtype.ext
  ext v
  have hv : v ∈ fixV (Subgroup.zpowers (a : MulAut V)) := htop ▸ Subgroup.mem_top v
  exact mem_fixV_zpowers.1 hv

theorem ncard_ne_one [Finite V] : ({x | x ≠ 1} : Set V).ncard + 1 = Nat.card V := by
  have e : ({x | x ≠ 1} : Set V) = Set.univ \ {1} := by
    ext x
    simp
  rw [e, Set.ncard_sdiff_singleton_add_one (Set.mem_univ _), Set.ncard_univ]

theorem orbits_of_card_eq [Finite V] (H : Subgroup (MulAut V))
    (h : ∀ v : V, v ≠ 1 → Nat.card ↥(orbitIn H v) + 1 = Nat.card V) :
    OrbitLengthsIn H [Nat.card V - 1] ∧ OrbitsSeparated H := by
  refine ⟨fun v hv => ?_, fun v w hv hw _ => ?_⟩
  · have := h v hv
    simp only [List.mem_singleton]
    omega
  · have hsub : orbitIn H v ⊆ {x | x ≠ 1} := fun x hx => ne_one_of_mem_orbitIn hv hx
    have heq : orbitIn H v = {x | x ≠ 1} := by
      refine Set.eq_of_subset_of_ncard_le hsub ?_
      have h1 := ncard_ne_one (V := V)
      have h2 := h v hv
      rw [Nat.card_coe_set_eq] at h2
      omega
    have hw' : w ∈ orbitIn H v := heq ▸ hw
    exact hw'

theorem orbits_of_transitive [Finite V] (H : Subgroup (MulAut V))
    (h : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ g ∈ H, (g : MulAut V) v = w) :
    OrbitLengthsIn H [Nat.card V - 1] ∧ OrbitsSeparated H := by
  refine orbits_of_card_eq H fun v hv => ?_
  have heq : orbitIn H v = {x | x ≠ 1} := by
    ext w
    refine ⟨fun hw => ne_one_of_mem_orbitIn hv hw, fun hw => h v w hv hw⟩
  rw [heq, Nat.card_coe_set_eq]
  exact ncard_ne_one

section Model

variable {D : FFModel} {H : Subgroup (MulAut V)} {π : D.Gam →* ↥H}
  {β : ↥(⊤ : Subgroup V) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec}

theorem exists_eq_of_transitive (hR : RealizesBy D H ⊤ ⊥ π β)
    (htrans : ∀ m ∈ D.sec, ∀ m' ∈ D.sec, m ∉ D.ker → m' ∉ D.ker →
      ∃ γ : D.Gam, ∃ k ∈ D.ker, D.act γ m = m' * k)
    {v w : V} (hv : v ≠ 1) (hw : w ≠ 1) : ∃ h ∈ H, (h : MulAut V) v = w := by
  obtain ⟨m, hm, hmk⟩ := exists_coordOf_eq hR hv
  obtain ⟨m', hm', hmk'⟩ := exists_coordOf_eq hR hw
  obtain ⟨γ, k, hk, he⟩ := htrans m m.2 m' m'.2 hmk hmk'
  refine ⟨π γ, (π γ).2, coordOf_injective hR ?_⟩
  rw [coordOf_act hR γ v m hm, hm']
  apply QuotientGroup.eq.2
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  change (D.act γ m)⁻¹ * (m' : D.Amb) ∈ D.ker
  rw [he, mul_inv_rev, inv_mul_cancel_right]
  exact D.ker.inv_mem hk

theorem card_eq_of_realizesBy (hR : RealizesBy D H ⊤ ⊥ π β) :
    Nat.card V * Nat.card ↥D.ker = Nat.card ↥D.sec := by
  have h1 : Nat.card V = Nat.card (↥D.sec ⧸ D.ker.subgroupOf D.sec) :=
    Nat.card_congr (Equiv.ofBijective _ ⟨coordOf_injective hR, coordOf_surjective hR⟩)
  have h2 : Nat.card ↥(D.ker.subgroupOf D.sec) = Nat.card ↥D.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR.2.2.1).toEquiv
  rw [h1, ← h2, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]

end Model

end CFSG.Quasithin.H13.Orbit
