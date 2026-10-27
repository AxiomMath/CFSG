module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.Quasithin.H13.K1262Two

open CFSG.Open CFSG.Blueprint

@[expose] def A6TypeCent {X : Type} [Group X] (Y : Subgroup X) (u : X) : Prop :=
  ⁅Y, Y⁆ = Y ∧ quasithinO2QuotientIso Y ↥(alternatingGroup (Fin 6)) ∧
    u ∈ Y ∧ orderOf u = 2 ∧ ∀ y ∈ Y, u * y = y * u

@[expose] def A6CentHe : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* NativeSporadic.He) →
    ∀ (Y P : Subgroup X) (u : X), A6TypeCent Y u → IsPGroup 2 ↥P →
      P ≤ Subgroup.normalizer (Y : Set X) → Nat.card ↥P < 2 ^ 9

@[expose] def A6PRu : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* NativeSporadic.Ru) →
    ∀ (Y P : Subgroup X), ⁅Y, Y⁆ = Y → quasithinO2QuotientIso Y ↥(alternatingGroup (Fin 6)) →
      IsPGroup 2 ↥P → P ≤ Subgroup.normalizer (Y : Set X) → Nat.card ↥P < 2 ^ 13

@[expose] def A6CentJ4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* NativeSporadic.J4) →
    ∀ (Y P : Subgroup X) (u : X), A6TypeCent Y u → IsPGroup 2 ↥P →
      P ≤ Subgroup.normalizer (Y : Set X) → Nat.card ↥P < 2 ^ 20

section CentInv

variable {X : Type} [Group X] [Finite X]

def centInv (Y : Subgroup X) : Subgroup X where
  carrier := {v | v ∈ Y ∧ v * v = 1 ∧ ∀ y ∈ Y, v * y = y * v}
  one_mem' := ⟨Y.one_mem, by simp, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha2, hac⟩ ⟨hb, hb2, hbc⟩
    refine ⟨Y.mul_mem ha hb, ?_, ?_⟩
    · calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hac b hb]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
    · intro y hy
      calc a * b * y = a * (y * b) := by rw [mul_assoc, hbc y hy]
        _ = y * (a * b) := by rw [← mul_assoc, hac y hy, mul_assoc]
  inv_mem' := by
    rintro a ⟨ha, ha2, hac⟩
    have : a⁻¹ = a := by rw [inv_eq_iff_mul_eq_one]; exact ha2
    rw [Set.mem_setOf_eq, this]; exact ⟨ha, ha2, hac⟩

theorem isPGroup_centInv (Y : Subgroup X) : IsPGroup 2 ↥(centInv Y) := by
  intro g
  refine ⟨1, ?_⟩
  ext; simp [pow_one, pow_two, g.2.2.1]

theorem exists_central_involution_fixed {Y P : Subgroup X} {u : X} (hu : u ∈ Y)
    (hu1 : u ≠ 1) (hu2 : u * u = 1) (hc : ∀ y ∈ Y, u * y = y * u) (hP : IsPGroup 2 ↥P)
    (hPN : P ≤ Subgroup.normalizer (Y : Set X)) :
    ∃ v ∈ Y, v ≠ 1 ∧ v * v = 1 ∧ (∀ y ∈ Y, v * y = y * v) ∧ ∀ p ∈ P, p * v = v * p := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centInv Y with hH
  have hconj : ∀ p ∈ P, ∀ v ∈ H, p * v * p⁻¹ ∈ H := by
    intro p hp v ⟨hv, hv2, hvc⟩
    have hpN := Subgroup.mem_normalizer_iff.mp (hPN hp)
    refine ⟨(hpN v).mp hv, ?_, ?_⟩
    · calc p * v * p⁻¹ * (p * v * p⁻¹) = p * (v * v) * p⁻¹ := by group
        _ = 1 := by rw [hv2]; group
    · intro y hy
      have hy' : p⁻¹ * y * p ∈ Y := by
        have := (hpN (p⁻¹ * y * p)).mpr (by simpa [mul_assoc] using hy)
        exact this
      have := hvc _ hy'
      calc p * v * p⁻¹ * y = p * (v * (p⁻¹ * y * p)) * p⁻¹ := by group
        _ = p * ((p⁻¹ * y * p) * v) * p⁻¹ := by rw [this]
        _ = y * (p * v * p⁻¹) := by group
  let act : MulAction ↥P ↥H :=
    { smul := fun p v => ⟨p * v * p⁻¹, hconj p p.2 v v.2⟩
      one_smul := fun v => by
        apply Subtype.ext; show ((1 : ↥P) : X) * v * ((1 : ↥P) : X)⁻¹ = v
        simp
      mul_smul := fun p q v => by
        apply Subtype.ext
        show ((p * q : ↥P) : X) * v * ((p * q : ↥P) : X)⁻¹ = p * (q * v * (q : X)⁻¹) * (p : X)⁻¹
        rw [Subgroup.coe_mul, mul_inv_rev]; simp only [mul_assoc] }
  have hcard : 2 ∣ Nat.card ↥H := by
    have hne : Nontrivial ↥H := ⟨⟨⟨u, hu, hu2, hc⟩, 1, fun h => hu1 (congrArg Subtype.val h)⟩⟩
    obtain ⟨n, hn⟩ := (isPGroup_centInv Y).exists_card_eq
    rw [hn]
    rcases n with _ | n
    · exfalso
      rw [pow_zero] at hn
      exact (Finite.one_lt_card_iff_nontrivial.mpr hne).ne' hn
    · exact dvd_pow_self 2 (Nat.succ_ne_zero n)
  have h1 : (1 : ↥H) ∈ MulAction.fixedPoints ↥P ↥H := by
    intro p; ext; show (p : X) * 1 * (p : X)⁻¹ = 1; group
  obtain ⟨b, hb, hb1⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥H hcard h1
  refine ⟨b, b.2.1, fun h => hb1 (Subtype.ext h.symm), b.2.2.1, b.2.2.2, ?_⟩
  intro p hp
  have := congrArg Subtype.val (hb ⟨p, hp⟩)
  change (p : X) * b * p⁻¹ = b at this
  calc p * (b : X) = p * b * p⁻¹ * p := by group
    _ = b * p := by rw [this]

end CentInv

end CFSG.Quasithin.H13.K1262Two
