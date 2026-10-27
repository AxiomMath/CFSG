module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem normalizer_commutator {A B : Subgroup G} {x : G} (hA : x ∈ Subgroup.normalizer (A : Set G))
    (hB : x ∈ Subgroup.normalizer (B : Set G)) : x ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  have key : ∀ x : G, x ∈ Subgroup.normalizer (A : Set G) → x ∈ Subgroup.normalizer (B : Set G) →
      ∀ y ∈ ⁅A, B⁆, x * y * x⁻¹ ∈ ⁅A, B⁆ := by
    intro x hA hB y hy
    induction hy using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hg
      have h1 : x * a * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hA a).mp ha
      have h2 : x * b * x⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hB b).mp hb
      have : x * ⁅a, b⁆ * x⁻¹ = ⁅x * a * x⁻¹, x * b * x⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [this]
      exact Subgroup.commutator_mem_commutator h1 h2
    | one => simp
    | mul g h _ _ ihg ihh =>
      have : x * (g * h) * x⁻¹ = (x * g * x⁻¹) * (x * h * x⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ ihg ihh
    | inv g _ ih =>
      have : x * g⁻¹ * x⁻¹ = (x * g * x⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ ih
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key x hA hB y
  · intro hy
    have := key x⁻¹ (inv_mem hA) (inv_mem hB) _ hy
    simpa [mul_assoc] using this

theorem s151v_three_subgroups_le {H₁ H₂ H₃ N : Subgroup G} (h1 : H₁ ≤ Subgroup.normalizer (N : Set G))
    (h2 : H₂ ≤ Subgroup.normalizer (N : Set G)) (h3 : H₃ ≤ Subgroup.normalizer (N : Set G))
    (hA : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ N) (hB : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ N) : ⁅⁅H₁, H₂⁆, H₃⁆ ≤ N := by
  have hmem : ∀ x ∈ Subgroup.normalizer (N : Set G), ∀ n ∈ N, x * n * x⁻¹ ∈ N := fun x hx n hn =>
    (Subgroup.mem_normalizer_iff.mp hx n).mp hn
  rw [Subgroup.commutator_le]
  intro a ha z hz
  let Sz : Subgroup G :=
    { carrier := {a | a ∈ Subgroup.normalizer (N : Set G) ∧ ⁅a, z⁆ ∈ N}
      mul_mem' := by
        rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
        refine ⟨Subgroup.mul_mem _ haN hbN, ?_⟩
        have : ⁅a * b, z⁆ = (a * ⁅b, z⁆ * a⁻¹) * ⁅a, z⁆ := by
          simp only [commutatorElement_def]; group
        rw [this]
        exact N.mul_mem (hmem a haN _ hb) ha
      one_mem' := ⟨Subgroup.one_mem _, by simp⟩
      inv_mem' := by
        rintro a ⟨haN, ha⟩
        refine ⟨Subgroup.inv_mem _ haN, ?_⟩
        have : ⁅a⁻¹, z⁆ = a⁻¹ * ⁅a, z⁆⁻¹ * a := by
          simp only [commutatorElement_def]; group
        rw [this]
        have := hmem a⁻¹ (Subgroup.inv_mem _ haN) _ (N.inv_mem ha)
        simpa using this }
  have hgen : ⁅H₁, H₂⁆ ≤ Sz := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hxN := h1 hx
    have hyN := h2 hy
    have hzN := h3 hz
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hxN hyN)
        (Subgroup.inv_mem _ hxN)) (Subgroup.inv_mem _ hyN)
    ·
      have n1 : ⁅y, ⁅z⁻¹, x⁻¹⁆⁆ ∈ N := by
        apply hB
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hy
          (Subgroup.commutator_mem_commutator (H₃.inv_mem hz) (H₁.inv_mem hx))
      have n2 : ⁅x⁻¹, ⁅y⁻¹, z⁆⁆ ∈ N := by
        apply hA
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator (H₁.inv_mem hx)
          (Subgroup.commutator_mem_commutator (H₂.inv_mem hy) hz)
      have hid : ⁅z, ⁅x, y⁆⁆ =
          x * z * ⁅y, ⁅z⁻¹, x⁻¹⁆⁆⁻¹ * z⁻¹ * y * ⁅x⁻¹, ⁅y⁻¹, z⁆⁆⁻¹ * y⁻¹ * x⁻¹ := by
        simp [commutatorElement_def, mul_assoc]
      have hxz : x * z ∈ Subgroup.normalizer (N : Set G) := Subgroup.mul_mem _ hxN hzN
      have hxy : x * y ∈ Subgroup.normalizer (N : Set G) := Subgroup.mul_mem _ hxN hyN
      have e1 := hmem _ hxz _ (N.inv_mem n1)
      have e2 := hmem _ hxy _ (N.inv_mem n2)
      have hprod : x * z * ⁅y, ⁅z⁻¹, x⁻¹⁆⁆⁻¹ * z⁻¹ * y * ⁅x⁻¹, ⁅y⁻¹, z⁆⁆⁻¹ * y⁻¹ * x⁻¹ =
          ((x * z) * ⁅y, ⁅z⁻¹, x⁻¹⁆⁆⁻¹ * (x * z)⁻¹) * ((x * y) * ⁅x⁻¹, ⁅y⁻¹, z⁆⁆⁻¹ * (x * y)⁻¹) := by
        group
      have hz1 : ⁅z, ⁅x, y⁆⁆ ∈ N := by
        rw [hid, hprod]
        exact N.mul_mem e1 e2
      have : ⁅⁅x, y⁆, z⁆ = (⁅z, ⁅x, y⁆⁆)⁻¹ := (commutatorElement_inv _ _).symm
      rw [this]
      exact N.inv_mem hz1
  exact (hgen ha).2

theorem commutator_commutator_perfect {L Q : Subgroup G} (hperf : ⁅L, L⁆ = L) (hQL : Q ≤ L)
    (hQ : L ≤ Subgroup.normalizer (Q : Set G)) : ⁅⁅Q, L⁆, L⁆ = ⁅Q, L⁆ := by
  have hU : L ≤ Subgroup.normalizer ((⁅Q, L⁆ : Subgroup G) : Set G) := fun x hx =>
    normalizer_commutator (hQ hx) (Subgroup.le_normalizer hx)
  have hN : L ≤ Subgroup.normalizer ((⁅⁅Q, L⁆, L⁆ : Subgroup G) : Set G) := fun x hx =>
    normalizer_commutator (hU hx) (Subgroup.le_normalizer hx)
  have hle : ⁅⁅Q, L⁆, L⁆ ≤ ⁅Q, L⁆ := by
    rw [Subgroup.commutator_le]
    intro u hu ℓ hℓ
    have h1 : ℓ * u⁻¹ * ℓ⁻¹ ∈ ⁅Q, L⁆ := by
      have := (Subgroup.mem_normalizer_iff.mp (hU hℓ) u⁻¹).mp (Subgroup.inv_mem _ hu)
      exact this
    have : ⁅u, ℓ⁆ = u * (ℓ * u⁻¹ * ℓ⁻¹) := by simp only [commutatorElement_def, mul_assoc]
    rw [this]
    exact Subgroup.mul_mem _ hu h1
  refine le_antisymm hle ?_
  have key : ⁅⁅L, L⁆, Q⁆ ≤ ⁅⁅Q, L⁆, L⁆ := by
    refine s151v_three_subgroups_le hN hN (hQL.trans hN) ?_ le_rfl
    rw [Subgroup.commutator_comm L Q]
  rw [hperf, Subgroup.commutator_comm] at key
  exact key

theorem s151v_mem_normalizer_centralizer {H : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (H : Set G)) :
    x ∈ Subgroup.normalizer ((Subgroup.centralizer (H : Set G) : Subgroup G) : Set G) := by
  have key : ∀ x ∈ Subgroup.normalizer (H : Set G), ∀ y ∈ Subgroup.centralizer (H : Set G),
      x * y * x⁻¹ ∈ Subgroup.centralizer (H : Set G) := by
    intro x hx y hy
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 : x⁻¹ * h * x ∈ H := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hx) h).mp hh
      simpa using this
    have h2 := Subgroup.mem_centralizer_iff.mp hy _ h1
    calc h * (x * y * x⁻¹) = x * ((x⁻¹ * h * x) * y) * x⁻¹ := by group
      _ = x * (y * (x⁻¹ * h * x)) * x⁻¹ := by rw [h2]
      _ = x * y * x⁻¹ * h := by group
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key x hx y
  · intro hy
    have := key x⁻¹ (inv_mem hx) _ hy
    simpa [mul_assoc] using this

end CFSG.Quasithin
