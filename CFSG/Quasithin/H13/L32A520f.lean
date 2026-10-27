module

public import CFSG.Holt.Witt

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Holt

variable {G : Type*} [Group G]

abbrev conjSub (g : G) (X : Subgroup G) : Subgroup G := X.map (MulAut.conj g).toMonoidHom

theorem mem_conjSub {g x : G} {X : Subgroup G} : x ∈ conjSub g X ↔ g⁻¹ * x * g ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    refine ⟨g⁻¹ * x * g, h, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem conjSub_one (X : Subgroup G) : conjSub 1 X = X := by
  ext x
  rw [mem_conjSub]
  simp

theorem conjSub_mul (g h : G) (X : Subgroup G) : conjSub (g * h) X = conjSub g (conjSub h X) := by
  ext x
  rw [mem_conjSub, mem_conjSub, mem_conjSub]
  simp [mul_assoc]

theorem conjSub_eq_iff {g : G} {X : Subgroup G} :
    conjSub g X = X ↔ g ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    constructor
    · intro hx
      have : g * x * g⁻¹ ∈ conjSub g X := mem_conjSub.mpr (by simpa [mul_assoc] using hx)
      rwa [h] at this
    · intro hx
      rw [← h] at hx
      simpa [mul_assoc] using mem_conjSub.mp hx
  · intro h
    ext x
    rw [mem_conjSub]
    constructor
    · intro hx
      have := (h (g⁻¹ * x * g)).mp hx
      simpa [mul_assoc] using this
    · intro hx
      exact (h _).mpr (by simpa [mul_assoc] using hx)

@[expose, instance_reducible] def conjSubAction : MulAction G (Subgroup G) where
  smul := conjSub
  one_smul := conjSub_one
  mul_smul := conjSub_mul

section Orbit

attribute [local instance] conjSubAction

theorem card_conjOrbit [Finite G] (B X : Subgroup G) :
    Nat.card {Y : Subgroup G // ∃ b ∈ B, Y = conjSub b X} =
      ((Subgroup.normalizer (X : Set G)).subgroupOf B).index := by
  classical
  have horbit : MulAction.orbit B X = {Y : Subgroup G | ∃ b ∈ B, Y = conjSub b X} := by
    ext Y
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b, b.2, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, rfl⟩
  have hstab : MulAction.stabilizer B X = (Subgroup.normalizer (X : Set G)).subgroupOf B := by
    ext b
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    exact conjSub_eq_iff
  change Nat.card ↥{Y : Subgroup G | ∃ b ∈ B, Y = conjSub b X} = _
  rw [← horbit, Nat.card_coe_set_eq, ← MulAction.index_stabilizer B X, hstab]

end Orbit

theorem exists_le_normalizer_of_odd [Finite G] {A : Subgroup G} (hA : IsPGroup 2 A)
    (Ω : Set (Subgroup G)) (hΩ : ∀ a ∈ A, ∀ X ∈ Ω, conjSub a X ∈ Ω)
    (hodd : ¬ 2 ∣ Nat.card Ω) : ∃ X ∈ Ω, A ≤ Subgroup.normalizer (X : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let act : MulAction A Ω :=
    { smul := fun a X => ⟨conjSub (a : G) X.1, hΩ a a.2 X.1 X.2⟩
      one_smul := fun X => Subtype.ext (conjSub_one X.1)
      mul_smul := fun a b X => Subtype.ext (conjSub_mul (a : G) b X.1) }
  obtain ⟨X, hX⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card Ω hodd
  refine ⟨X.1, X.2, fun a ha => ?_⟩
  have h := congrArg Subtype.val ((MulAction.mem_fixedPoints.mp hX) ⟨a, ha⟩)
  exact conjSub_eq_iff.mp h

variable [Finite G] {p : ℕ} [Fact p.Prime]

theorem fusionIsSylowIn_inf_of_le_normalizer' {S H N : Subgroup G} (hS : fusionIsSylowIn p S H)
    (hNH : N ≤ H) (hHN : H ≤ Subgroup.normalizer (N : Set G)) :
    fusionIsSylowIn p (S ⊓ N) N := by
  refine ⟨inf_le_right, hS.2.1.to_le inf_le_left, fun P hPN hP hle => ?_⟩
  obtain ⟨R, hPR, hR⟩ := exists_fusionIsSylowIn_ge hP (hPN.trans hNH)
  obtain ⟨k, hk, hkR⟩ := exists_mem_conj_of_fusionIsSylowIn hS hR
  have hconj : ∀ x ∈ P, k⁻¹ * x * k ∈ S ⊓ N := fun x hx => ⟨(hkR x).mp (hPR hx), by
    have := (Subgroup.mem_normalizer_iff.mp (hHN (inv_mem hk)) x).mp (hPN hx)
    simpa using this⟩
  have hcard : Nat.card P ≤ Nat.card ↥(S ⊓ N) := Nat.card_le_card_of_injective
    (fun x : P => (⟨k⁻¹ * x * k, hconj x x.2⟩ : ↥(S ⊓ N))) (fun x y h => by
      have := congrArg Subtype.val h
      simp only [mul_left_inj, mul_right_inj] at this
      exact Subtype.ext this)
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem fusionIsSylowIn_map_conj' {P N : Subgroup G} (hP : fusionIsSylowIn p P N) {c : G}
    (hc : c ∈ Subgroup.normalizer (N : Set G)) : fusionIsSylowIn p (conjSub c P) N := by
  refine fusionIsSylowIn_of_card_eq (fun x hx => ?_) (hP.2.1.map _) ?_
  · obtain ⟨y, hy, rfl⟩ := hx
    exact (Subgroup.mem_normalizer_iff.mp hc y).mp (hP.1 hy)
  · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact card_eq_of_fusionIsSylowIn hP

theorem exists_mul_mem_normalizer {D N : Subgroup G} (hD : fusionIsSylowIn p D N) {c : G}
    (hc : c ∈ Subgroup.normalizer (N : Set G)) :
    ∃ n ∈ N, n⁻¹ * c ∈ Subgroup.normalizer (D : Set G) := by
  obtain ⟨n, hn, hnD⟩ := exists_mem_conj_of_fusionIsSylowIn hD (fusionIsSylowIn_map_conj' hD hc)
  refine ⟨n, hn, Subgroup.mem_normalizer_fintype fun d hd => ?_⟩
  have h1 : c * d * c⁻¹ ∈ conjSub c D := mem_conjSub.mpr (by simpa [mul_assoc] using hd)
  have h2 := (hnD _).mp h1
  rw [show n⁻¹ * c * d * (n⁻¹ * c)⁻¹ = n⁻¹ * (c * d * c⁻¹) * n by group]
  exact h2

end CFSG.Quasithin.H13.L32A
