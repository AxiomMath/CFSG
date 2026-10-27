module

public import CFSG.Quasithin.Vol2.Ch10SecEE3V

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

variable {G : Type} [Group G]

theorem relIndex_centralizer_eq_mul [Finite G] {q : G} {N Y : Subgroup G} (hNY : N ≤ Y)
    (hN : Y ⊓ Subgroup.centralizer ({q} : Set G) ≤ Subgroup.normalizer (N : Set G)) :
    (Subgroup.centralizer ({q} : Set G)).relIndex Y =
      (Subgroup.centralizer ({q} : Set G)).relIndex N *
        (N ⊔ Y ⊓ Subgroup.centralizer ({q} : Set G)).relIndex Y := by
  set C := Subgroup.centralizer ({q} : Set G)
  have h1 : (Y ⊓ C).relIndex (N ⊔ Y ⊓ C) * (N ⊔ Y ⊓ C).relIndex Y = (Y ⊓ C).relIndex Y :=
    Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right (sup_le hNY inf_le_left)
  have h2 : (Y ⊓ C).relIndex (N ⊔ Y ⊓ C) = (Y ⊓ C).relIndex N :=
    SecE.relIndex_sup_eq_relIndex hN
  have h3 : (Y ⊓ C).relIndex N = C.relIndex N := by
    have h := Subgroup.relIndex_inf_mul_relIndex C Y N
    rw [inf_eq_right.mpr hNY, Subgroup.relIndex_eq_one.mpr hNY, mul_one] at h
    rw [inf_comm, ← h]
  have h4 : (Y ⊓ C).relIndex Y = C.relIndex Y := by
    rw [inf_comm]
    exact Subgroup.inf_relIndex_right C Y
  rw [← h4, ← h1, h2, h3]

theorem exists_fixed_mul [Finite G] {q : G} (hq : q ^ 3 = 1) {N : Subgroup G}
    (hN2 : IsPGroup 2 N) (hqN : q ∈ Subgroup.normalizer (N : Set G)) {y : G}
    (hy : q * y * q⁻¹ * y⁻¹ ∈ N) : ∃ n ∈ N, q * (n * y) * q⁻¹ = n * y := by
  classical
  let α := {x : G // x * y⁻¹ ∈ N}
  have hmem : ∀ x : α, q * x.1 * q⁻¹ * y⁻¹ ∈ N := fun x => by
    have h1 : q * (x.1 * y⁻¹) * q⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hqN _).mp x.2
    have e : q * x.1 * q⁻¹ * y⁻¹ = q * (x.1 * y⁻¹) * q⁻¹ * (q * y * q⁻¹ * y⁻¹) := by group
    rw [e]
    exact N.mul_mem h1 hy
  let f : α → α := fun x => ⟨q * x.1 * q⁻¹, hmem x⟩
  have hq3 : q * (q * q) = 1 := (pow_three q).symm.trans hq
  have hf3 : ∀ x, f (f (f x)) = x := fun x => Subtype.ext (by
    show q * (q * (q * x.1 * q⁻¹) * q⁻¹) * q⁻¹ = x.1
    have e : q * (q * (q * x.1 * q⁻¹) * q⁻¹) * q⁻¹ = q * (q * q) * x.1 * (q * (q * q))⁻¹ := by
      group
    rw [e, hq3]
    group)
  let σ : Equiv.Perm α := ⟨f, fun x => f (f x), fun x => hf3 x, fun x => hf3 x⟩
  have hσ : σ ^ 3 ^ 1 = 1 := by
    refine Equiv.ext fun x => ?_
    rw [pow_one, show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two, Equiv.Perm.mul_apply,
      Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    exact hf3 x
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype α := Fintype.ofFinite α
  have hcard : ¬ 3 ∣ Fintype.card α := by
    let e : α ≃ N := ⟨fun x => ⟨x.1 * y⁻¹, x.2⟩, fun n => ⟨n.1 * y, by simp⟩,
      fun x => Subtype.ext (by simp), fun n => Subtype.ext (by simp)⟩
    rw [← Nat.card_eq_fintype_card, Nat.card_congr e]
    obtain ⟨k, hk⟩ := hN2.exists_card_eq
    rw [hk]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hσ
  refine ⟨x.1 * y⁻¹, x.2, ?_⟩
  have h := congrArg Subtype.val hx
  simp only [inv_mul_cancel_right]
  exact h

theorem le_sup_of_commutator [Finite G] {q : G} (hq : q ^ 3 = 1) {N Y : Subgroup G}
    (hY2 : IsPGroup 2 Y) (hNY : N ≤ Y) (hqN : q ∈ Subgroup.normalizer (N : Set G))
    (h : ∀ y ∈ Y, q * y * q⁻¹ * y⁻¹ ∈ N) :
    Y ≤ N ⊔ Y ⊓ Subgroup.centralizer ({q} : Set G) := by
  intro y hy
  obtain ⟨n, hn, hfix⟩ := exists_fixed_mul hq (hY2.to_le hNY) hqN (h y hy)
  have hc : n * y ∈ Y ⊓ Subgroup.centralizer ({q} : Set G) := by
    refine ⟨Y.mul_mem (hNY hn) hy, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc n * y * q = q * (n * y) * q⁻¹ * q := by rw [hfix]
      _ = q * (n * y) := by group
  have e : y = n⁻¹ * (n * y) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (N.inv_mem hn)) (Subgroup.mem_sup_right hc)

theorem relIndex_centralizer_eq_of_commutator [Finite G] {q : G} (hq : q ^ 3 = 1)
    {N Y : Subgroup G} (hY2 : IsPGroup 2 Y) (hNY : N ≤ Y)
    (hYN : Y ≤ Subgroup.normalizer (N : Set G)) (hqN : q ∈ Subgroup.normalizer (N : Set G))
    (h : ∀ y ∈ Y, q * y * q⁻¹ * y⁻¹ ∈ N) :
    (Subgroup.centralizer ({q} : Set G)).relIndex Y =
      (Subgroup.centralizer ({q} : Set G)).relIndex N := by
  rw [relIndex_centralizer_eq_mul hNY (inf_le_left.trans hYN),
    Subgroup.relIndex_eq_one.mpr (le_sup_of_commutator hq hY2 hNY hqN h), mul_one]

theorem relIndex_centralizer_le_of_le [Finite G] {q : G} {A B : Subgroup G} (hAB : A ≤ B) :
    (Subgroup.centralizer ({q} : Set G)).relIndex A ≤
      (Subgroup.centralizer ({q} : Set G)).relIndex B :=
  Subgroup.relIndex_le_of_le_right hAB (Subgroup.index_ne_zero_of_finite)

theorem eq_one_of_conj_fixed {q z : G} (hq : q ^ 3 = 1)
    (hfix : q * (q * z * q⁻¹ * z⁻¹) * q⁻¹ = q * z * q⁻¹ * z⁻¹)
    (hsq : (q * z * q⁻¹ * z⁻¹) * (q * z * q⁻¹ * z⁻¹) = 1) : q * z * q⁻¹ * z⁻¹ = 1 := by
  set u := q * z * q⁻¹ * z⁻¹ with hu
  have h1 : q * z * q⁻¹ = u * z := by rw [hu]; group
  have h2 : q * (q * z * q⁻¹) * q⁻¹ = z := by
    calc q * (q * z * q⁻¹) * q⁻¹ = q * (u * z) * q⁻¹ := by rw [h1]
      _ = (q * u * q⁻¹) * (q * z * q⁻¹) := by group
      _ = u * (u * z) := by rw [hfix, h1]
      _ = z := by rw [← mul_assoc, hsq, one_mul]
  have hq3 : q * (q * q) = 1 := (pow_three q).symm.trans hq
  have h3 : q * (q * q) * z * (q * (q * q))⁻¹ = q * z * q⁻¹ := by
    calc q * (q * q) * z * (q * (q * q))⁻¹ = q * (q * (q * z * q⁻¹) * q⁻¹) * q⁻¹ := by group
      _ = q * z * q⁻¹ := by rw [h2]
  rw [hq3, one_mul, inv_one, mul_one, h1] at h3
  have h4 : u * z * z⁻¹ = z * z⁻¹ := by rw [← h3]
  simpa using h4

theorem conj_mul_inv_eq {q z : G} (hq : q ^ 3 = 1)
    (hc₁ : z * (q * z * q⁻¹) = (q * z * q⁻¹) * z)
    (hc₃ : (q * z * q⁻¹) * (q * (q * z * q⁻¹) * q⁻¹) =
      (q * (q * z * q⁻¹) * q⁻¹) * (q * z * q⁻¹))
    (hs₀ : z * z = 1) (hs₂ : (q * (q * z * q⁻¹) * q⁻¹) * (q * (q * z * q⁻¹) * q⁻¹) = 1) :
    q * z * q⁻¹ * z⁻¹ =
      q * (q * (q * z * q⁻¹) * q⁻¹ * (q * z * q⁻¹)⁻¹) * q⁻¹ *
        (q * (q * z * q⁻¹) * q⁻¹ * (q * z * q⁻¹)⁻¹)⁻¹ := by
  set b := q * z * q⁻¹ with hb
  set a := q * b * q⁻¹ with ha
  have hq3 : q * (q * q) = 1 := (pow_three q).symm.trans hq
  have h3 : q * a * q⁻¹ = z := by
    rw [ha, hb]
    calc q * (q * (q * z * q⁻¹) * q⁻¹) * q⁻¹ = q * (q * q) * z * (q * (q * q))⁻¹ := by group
      _ = z := by rw [hq3]; group
  have hz : z⁻¹ = z := inv_eq_of_mul_eq_one_right hs₀
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right hs₂
  have e1 : q * (a * b⁻¹) * q⁻¹ = z * a⁻¹ := by
    calc q * (a * b⁻¹) * q⁻¹ = (q * a * q⁻¹) * (q * b * q⁻¹)⁻¹ := by group
      _ = z * a⁻¹ := by rw [h3, ← ha]
  rw [e1, ha', hz, mul_inv_rev, inv_inv, ha']
  calc b * z = z * b := hc₁.symm
    _ = z * ((a * a) * b) := by rw [hs₂, one_mul]
    _ = z * a * (b * a) := by rw [hc₃]; group

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
