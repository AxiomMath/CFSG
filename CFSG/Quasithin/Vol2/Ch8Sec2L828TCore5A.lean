module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.H13.L828T

open scoped commutatorElement

variable {G : Type*} [Group G]

private lemma mul_inv_eq_commutatorElement_L828T {p q c : G} (h : p = c * q * c⁻¹) :
    p * q⁻¹ = ⁅c, q⁆ := by
  rw [commutatorElement_def, h]

theorem x_norm_B {V B P U I : Subgroup G} {x : G}
    (hBV : B ≤ V) (hBP : B ≤ P) (hVI : V ≤ I)
    (hVcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v)
    (hIP : I ≤ Subgroup.normalizer (P : Set G))
    (hxP : x ∈ Subgroup.normalizer (P : Set G))
    (hIU : ∀ u ∈ U, ∀ i ∈ I, i * u * i⁻¹ = u)
    (hcI : ∀ w ∈ I, ∀ p ∈ P, ⁅⁅x, w⁆, p⁆ ∈ U)
    (hB5 : ∀ p ∈ P, (∀ v ∈ V, v * p * v⁻¹ * p⁻¹ ∈ U) → p ∈ B)
    {b : G} (hb : b ∈ B) : x * b * x⁻¹ ∈ B := by
  have hconj : ∀ g ∈ Subgroup.normalizer (P : Set G), ∀ k ∈ P, g * k * g⁻¹ ∈ P :=
    fun g hg k hk => (Subgroup.mem_normalizer_iff.mp hg k).mp hk
  have hbP : b ∈ P := hBP hb
  have hpP : x * b * x⁻¹ ∈ P := hconj x hxP b hbP
  apply hB5 _ hpP
  intro v hv
  have hvI : v ∈ I := hVI hv
  have hbV : b ∈ V := hBV hb
  have hvb : v * b * v⁻¹ = b := by
    rw [hVcomm v hv b hbV]
    group
  have hqP : v * (x * b * x⁻¹) * v⁻¹ ∈ P := hconj v (hIP hvI) _ hpP
  have hcq : ⁅⁅x, v⁆, v * (x * b * x⁻¹) * v⁻¹⁆ ∈ U := hcI v hvI _ hqP
  have hpc : x * b * x⁻¹
      = ⁅x, v⁆ * (v * (x * b * x⁻¹) * v⁻¹) * ⁅x, v⁆⁻¹ := by
    rw [commutatorElement_def]
    calc x * b * x⁻¹ = x * (v * b * v⁻¹) * x⁻¹ := by rw [hvb]
      _ = x * v * x⁻¹ * v⁻¹ * (v * (x * b * x⁻¹) * v⁻¹) * (x * v * x⁻¹ * v⁻¹)⁻¹ := by
          group
  have hpq := mul_inv_eq_commutatorElement_L828T hpc
  have hfin : v * (x * b * x⁻¹) * v⁻¹ * (x * b * x⁻¹)⁻¹
      = ((x * b * x⁻¹) * (v * (x * b * x⁻¹) * v⁻¹)⁻¹)⁻¹ := by
    group
  rw [hfin, hpq]
  exact U.inv_mem hcq

theorem x_comm_LU {P U : Subgroup G} {x l : G}
    (hlP : l ∈ Subgroup.normalizer (P : Set G))
    (hxP : x ∈ Subgroup.normalizer (P : Set G))
    (hc : ∀ p ∈ P, ⁅⁅x, l⁆, p⁆ ∈ U) {b : G} (hb : b ∈ P) :
    (x * (l * b * l⁻¹) * x⁻¹) * (l * (x * b * x⁻¹) * l⁻¹)⁻¹ ∈ U := by
  have hconj : ∀ g ∈ Subgroup.normalizer (P : Set G), ∀ k ∈ P, g * k * g⁻¹ ∈ P :=
    fun g hg k hk => (Subgroup.mem_normalizer_iff.mp hg k).mp hk
  have hxbP : x * b * x⁻¹ ∈ P := hconj x hxP b hb
  have hqP : l * (x * b * x⁻¹) * l⁻¹ ∈ P := hconj l hlP _ hxbP
  have hcq : ⁅⁅x, l⁆, l * (x * b * x⁻¹) * l⁻¹⁆ ∈ U := hc _ hqP
  have key : x * (l * b * l⁻¹) * x⁻¹
      = ⁅x, l⁆ * (l * (x * b * x⁻¹) * l⁻¹) * ⁅x, l⁆⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [key, ← commutatorElement_def]
  exact hcq

theorem x_triv_A {A B P U I : Subgroup G} {x h : G}
    (hAP : A ≤ P) (hBP : B ≤ P) (hhI : h ∈ I)
    (hIP : I ≤ Subgroup.normalizer (P : Set G))
    (hxP : x ∈ Subgroup.normalizer (P : Set G))
    (hIU : ∀ u ∈ U, ∀ i ∈ I, i * u * i⁻¹ = u)
    (hcI : ∀ w ∈ I, ∀ p ∈ P, ⁅⁅x, w⁆, p⁆ ∈ U)
    (hAB : ∀ a ∈ A, h⁻¹ * a * h ∈ B)
    (hBx : ∀ b ∈ B, x * b * x⁻¹ * b⁻¹ ∈ U)
    {a : G} (ha : a ∈ A) : x * a * x⁻¹ * a⁻¹ ∈ U := by
  have hconj : ∀ g ∈ Subgroup.normalizer (P : Set G), ∀ k ∈ P, g * k * g⁻¹ ∈ P :=
    fun g hg k hk => (Subgroup.mem_normalizer_iff.mp hg k).mp hk
  have hbB : h⁻¹ * a * h ∈ B := hAB a ha
  have hbP : h⁻¹ * a * h ∈ P := hBP hbB
  have hxbP : x * (h⁻¹ * a * h) * x⁻¹ ∈ P := hconj x hxP _ hbP
  have hqP : h * (x * (h⁻¹ * a * h) * x⁻¹) * h⁻¹ ∈ P := hconj h (hIP hhI) _ hxbP
  have hu₁ : ⁅⁅x, h⁆, h * (x * (h⁻¹ * a * h) * x⁻¹) * h⁻¹⁆ ∈ U := hcI h hhI _ hqP
  have hu₂ : x * (h⁻¹ * a * h) * x⁻¹ * (h⁻¹ * a * h)⁻¹ ∈ U := hBx _ hbB
  have hu₃ : h * (x * (h⁻¹ * a * h) * x⁻¹ * (h⁻¹ * a * h)⁻¹) * h⁻¹ ∈ U := by
    rw [hIU _ hu₂ h hhI]
    exact hu₂
  have hxa : x * a * x⁻¹ * a⁻¹
      = ⁅⁅x, h⁆, h * (x * (h⁻¹ * a * h) * x⁻¹) * h⁻¹⁆
          * (h * (x * (h⁻¹ * a * h) * x⁻¹ * (h⁻¹ * a * h)⁻¹) * h⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [hxa]
  exact U.mul_mem hu₁ hu₃

theorem x_triv_P {A B P U : Subgroup G} {x : G}
    (hxP : x ∈ Subgroup.normalizer (P : Set G))
    (hPU : ∀ u ∈ U, ∀ p ∈ P, p * u * p⁻¹ = u)
    (hPeq : P = A ⊔ B) (hAP : A ≤ P) (hBP : B ≤ P)
    (hA : ∀ a ∈ A, x * a * x⁻¹ * a⁻¹ ∈ U) (hB : ∀ b ∈ B, x * b * x⁻¹ * b⁻¹ ∈ U) :
    ∀ p ∈ P, x * p * x⁻¹ * p⁻¹ ∈ U := by
  let S : Subgroup G :=
    { carrier := {p | p ∈ P ∧ x * p * x⁻¹ * p⁻¹ ∈ U}
      mul_mem' := by
        rintro p q ⟨hpP, hp⟩ ⟨hqP, hq⟩
        refine ⟨P.mul_mem hpP hqP, ?_⟩
        have e : x * (p * q) * x⁻¹ * (p * q)⁻¹
            = (x * p * x⁻¹ * p⁻¹) * (p * (x * q * x⁻¹ * q⁻¹) * p⁻¹) := by
          group
        rw [e, hPU _ hq p hpP]
        exact U.mul_mem hp hq
      one_mem' := by
        refine ⟨P.one_mem, ?_⟩
        simp
      inv_mem' := by
        rintro p ⟨hpP, hp⟩
        refine ⟨P.inv_mem hpP, ?_⟩
        have e : x * p⁻¹ * x⁻¹ * p⁻¹⁻¹ = p⁻¹ * (x * p * x⁻¹ * p⁻¹)⁻¹ * p⁻¹⁻¹ := by
          group
        rw [e, hPU _ (U.inv_mem hp) p⁻¹ (P.inv_mem hpP)]
        exact U.inv_mem hp }
  have hAS : A ≤ S := fun a ha => ⟨hAP ha, hA a ha⟩
  have hBS : B ≤ S := fun b hb => ⟨hBP hb, hB b hb⟩
  have hPS : P ≤ S := by
    rw [hPeq]
    exact sup_le hAS hBS
  intro p hp
  exact (hPS hp).2

end CFSG.Quasithin.H13.L828T
