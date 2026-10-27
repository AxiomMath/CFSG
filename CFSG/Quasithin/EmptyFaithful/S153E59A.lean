module

public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace S153E59

section CommCentral

variable {G : Type*} [Group G]

theorem commutator_mul_central_left {a z b : G} (hzb : z * b = b * z) : ⁅a * z, b⁆ = ⁅a, b⁆ := by
  simp only [commutatorElement_def]
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [hzb]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutator_mul_central_right {a b z : G} (hza : z * a = a * z) : ⁅a, b * z⁆ = ⁅a, b⁆ := by
  simp only [commutatorElement_def]
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by
      have : z * a⁻¹ = a⁻¹ * z := by
        calc z * a⁻¹ = a⁻¹ * (a * z) * a⁻¹ := by group
          _ = a⁻¹ * (z * a) * a⁻¹ := by rw [hza]
          _ = a⁻¹ * z := by group
      rw [this]
    _ = a * b * a⁻¹ * b⁻¹ := by group

end CommCentral

section Product

variable {G : Type*} [Group G]

theorem card_sup_mul_card_inf_of_normalizes [Finite G] {T D : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (D : Set G)) :
    Nat.card ↥(T ⊔ D) * Nat.card ↥(T ⊓ D) = Nat.card T * Nat.card D := by
  have h1 := A4.relIndex_sup_eq_of_le_normalizer' hT
  have h2 := Subgroup.relIndex_mul_card D (T ⊔ D)
  have h3 := Subgroup.relIndex_mul_card D T
  have h4 : D ⊓ (T ⊔ D) = D := inf_of_le_left le_sup_right
  rw [h4, h1] at h2
  rw [inf_comm] at h3
  rw [← h2, ← h3, inf_comm]
  ring

theorem isPGroup_sup_of_normalizes [Finite G] {p : ℕ} [Fact p.Prime] {T D : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (D : Set G)) (hTp : IsPGroup p T) (hDp : IsPGroup p D) :
    IsPGroup p ↥(T ⊔ D) := by
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := p)).mp hTp
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := p)).mp hDp
  have h := card_sup_mul_card_inf_of_normalizes hT
  have hdvd : Nat.card ↥(T ⊔ D) ∣ p ^ (a + b) := by
    refine Dvd.intro (Nat.card ↥(T ⊓ D)) ?_
    rw [h, ha, hb, pow_add]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
  exact (IsPGroup.iff_card (p := p)).mpr ⟨k, hk⟩

end Product

section Conj

variable {G : Type*} [Group G]

theorem card_conjSubgroup' (A : Subgroup G) (g : G) : Nat.card (conjSubgroup A g) = Nat.card A :=
  (Nat.card_congr (Subgroup.equivMapOfInjective A (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).injective).toEquiv).symm

end Conj

end S153E59

end CFSG.Quasithin
