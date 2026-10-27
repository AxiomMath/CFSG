module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

section Transport

variable {L M N : Type*} [Group L] [Group M] [Group N]

@[expose] def transport (J : L →* M) (ψ : L →* N) (X : Subgroup M) : Subgroup N :=
  (X.comap J).map ψ

variable {J : L →* M} {ψ : L →* N}

theorem transport_sup {X Y : Subgroup M} (hX : X ≤ J.range) (hY : Y ≤ J.range) :
    transport J ψ (X ⊔ Y) = transport J ψ X ⊔ transport J ψ Y := by
  simp only [transport]
  rw [← Subgroup.comap_sup_eq_of_le_range (f := J) hX hY, Subgroup.map_sup]

theorem transport_inf (hψ : Function.Injective ψ) {X Y : Subgroup M} :
    transport J ψ (X ⊓ Y) = transport J ψ X ⊓ transport J ψ Y := by
  simp only [transport]
  rw [Subgroup.comap_inf, Subgroup.map_inf_eq (X.comap J) (Y.comap J) ψ hψ]

theorem transport_commutator (hJ : Function.Injective J) {X Y : Subgroup M}
    (hX : X ≤ J.range) (hY : Y ≤ J.range) :
    transport J ψ ⁅X, Y⁆ = ⁅transport J ψ X, transport J ψ Y⁆ := by
  have h : Subgroup.map J ⁅X.comap J, Y.comap J⁆ = ⁅X, Y⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self hX, Subgroup.map_comap_eq_self hY]
  simp only [transport]
  rw [← h, Subgroup.comap_map_eq_self_of_injective hJ, Subgroup.map_commutator]

private theorem map_inf_centralizer_of_injective {G G' : Type*} [Group G] [Group G']
    (f : G →* G') (hf : Function.Injective f) (A B : Subgroup G) :
    (A ⊓ Subgroup.centralizer (B : Set G)).map f =
      A.map f ⊓ Subgroup.centralizer (B.map f : Set G') := by
  ext y
  constructor
  · rintro ⟨a, ⟨haA, haC⟩, rfl⟩
    refine ⟨⟨a, haA, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp haC) b hb]
  · rintro ⟨⟨a, haA, rfl⟩, hC⟩
    refine ⟨a, ⟨haA, Subgroup.mem_centralizer_iff.mpr fun b hb => hf ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact (Subgroup.mem_centralizer_iff.mp hC) (f b) ⟨b, hb, rfl⟩

theorem transport_centralizer_inf (hJ : Function.Injective J) (hψ : Function.Injective ψ)
    {X Y : Subgroup M} (hX : X ≤ J.range) :
    transport J ψ (Subgroup.centralizer (X : Set M) ⊓ Y) =
      Subgroup.centralizer (transport J ψ X : Set N) ⊓ transport J ψ Y := by
  have hC : (Subgroup.centralizer (X : Set M)).comap J =
      Subgroup.centralizer ((X.comap J : Subgroup L) : Set L) := by
    ext g
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h y hy
      have h' := h (J y) hy
      exact hJ (by rw [map_mul, map_mul, h'])
    · intro h x hx
      obtain ⟨y, rfl⟩ := hX hx
      calc
        J y * J g = J (y * g) := by rw [map_mul]
        _ = J (g * y) := by rw [h y hx]
        _ = J g * J y := by rw [map_mul]
  simp only [transport]
  calc
    ((Subgroup.centralizer (X : Set M) ⊓ Y).comap J).map ψ
        = (((Subgroup.centralizer (X : Set M)).comap J ⊓ Y.comap J)).map ψ := by
          rw [Subgroup.comap_inf]
    _ = ((Y.comap J) ⊓ Subgroup.centralizer ((X.comap J : Subgroup L) : Set L)).map ψ := by
          rw [hC, inf_comm]
    _ = (Y.comap J).map ψ ⊓
          Subgroup.centralizer (((X.comap J).map ψ : Subgroup N) : Set N) :=
          map_inf_centralizer_of_injective ψ hψ (Y.comap J) (X.comap J)
    _ = Subgroup.centralizer ((X.comap J).map ψ : Set N) ⊓ (Y.comap J).map ψ := by
          rw [inf_comm]

theorem card_transport (hJ : Function.Injective J) (hψ : Function.Injective ψ) {X : Subgroup M}
    (hX : X ≤ J.range) : Nat.card (transport J ψ X) = Nat.card X := by
  simp only [transport]
  rw [Subgroup.card_map_of_injective hψ]
  have h : (X.comap J).map J = X := Subgroup.map_comap_eq_self hX
  calc
    Nat.card (X.comap J) = Nat.card ((X.comap J).map J) :=
      (Subgroup.card_map_of_injective hJ).symm
    _ = Nat.card X := by rw [h]

end Transport

theorem eq_or_eq_of_le_sup_of_isSimpleGroup {H : Type*} [Group H] {A B X : Subgroup H}
    [Finite A] [Finite B] (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hA : IsSimpleGroup A)
    (hB : IsSimpleGroup B) (hX : X ≤ A ⊔ B) (hXn : A ⊔ B ≤ Subgroup.normalizer (X : Set H))
    (hXA : Nat.card X = Nat.card A) (hXB : Nat.card X = Nat.card B)
    (hXc : ∃ x ∈ X, ∃ y ∈ X, x * y ≠ y * x) : X = A ∨ X = B := by
  have hXfin : Finite X := Nat.finite_of_card_ne_zero (by rw [hXA]; exact Nat.card_pos.ne')
  have hBnormA : B ≤ Subgroup.normalizer (A : Set H) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb a ha
    have h : b * a * b⁻¹ = a := by rw [← hAB a ha b hb]; group
    rw [h]; exact ha
  have hAnormA : A ⊔ B ≤ Subgroup.normalizer (A : Set H) :=
    sup_le (Subgroup.le_normalizer (H := A)) hBnormA
  have hAnormB : A ⊔ B ≤ Subgroup.normalizer (B : Set H) := by
    refine sup_le ?_ (Subgroup.le_normalizer (H := B))
    rw [Subgroup.le_normalizer_iff]
    intro a ha b hb
    have h : a * b * a⁻¹ = b := by rw [hAB a ha b hb]; group
    rw [h]; exact hb
  have hAnormXA : A ≤ Subgroup.normalizer ((X ⊓ A : Subgroup H) : Set H) :=
    (le_inf (le_trans le_sup_left hXn) (le_trans le_sup_left hAnormA)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hBnormXB : B ≤ Subgroup.normalizer ((X ⊓ B : Subgroup H) : Set H) :=
    (le_inf (le_trans le_sup_right hXn) (le_trans le_sup_right hAnormB)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hAdich : X ⊓ A = ⊥ ∨ X ⊓ A = A :=
    ((Subgroup.isSimpleGroup_iff (H := A)).mp hA).2 (X ⊓ A) inf_le_right
      ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hAnormXA)
  have hBdich : X ⊓ B = ⊥ ∨ X ⊓ B = B :=
    ((Subgroup.isSimpleGroup_iff (H := B)).mp hB).2 (X ⊓ B) inf_le_right
      ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hBnormXB)
  rcases hAdich with hAint | hAint
  · rcases hBdich with hBint | hBint
    ·
      exfalso
      have hcentA : X ≤ Subgroup.centralizer (A : Set H) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        have hmemX : ⁅x, a⁆ ∈ X := by
          have haN : a ∈ Subgroup.normalizer (X : Set H) := hXn (Subgroup.mem_sup_left ha)
          have hconj : a * x⁻¹ * a⁻¹ ∈ X :=
            (Subgroup.mem_normalizer_iff.mp haN (x⁻¹)).mp (X.inv_mem hx)
          have hxconj : x * (a * x⁻¹ * a⁻¹) ∈ X := X.mul_mem hx hconj
          rw [commutatorElement_def]
          simpa only [mul_assoc] using hxconj
        have hmemA : ⁅x, a⁆ ∈ A := by
          have hxN : x ∈ Subgroup.normalizer (A : Set H) := hAnormA (hX hx)
          have hconj : x * a * x⁻¹ ∈ A :=
            (Subgroup.mem_normalizer_iff.mp hxN a).mp ha
          rw [commutatorElement_def]
          exact A.mul_mem hconj (A.inv_mem ha)
        have hbot : ⁅x, a⁆ = 1 := by
          have hmem : ⁅x, a⁆ ∈ X ⊓ A := ⟨hmemX, hmemA⟩
          rwa [hAint, Subgroup.mem_bot] at hmem
        rw [commutatorElement_def] at hbot
        have hxa : x * a * x⁻¹ = a := mul_inv_eq_one.mp hbot
        calc
          a * x = (x * a * x⁻¹) * x := by rw [hxa]
          _ = x * a := by group
      have hcentB : X ≤ Subgroup.centralizer (B : Set H) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        have hmemX : ⁅x, b⁆ ∈ X := by
          have hbN : b ∈ Subgroup.normalizer (X : Set H) := hXn (Subgroup.mem_sup_right hb)
          have hconj : b * x⁻¹ * b⁻¹ ∈ X :=
            (Subgroup.mem_normalizer_iff.mp hbN (x⁻¹)).mp (X.inv_mem hx)
          have hxconj : x * (b * x⁻¹ * b⁻¹) ∈ X := X.mul_mem hx hconj
          rw [commutatorElement_def]
          simpa only [mul_assoc] using hxconj
        have hmemB : ⁅x, b⁆ ∈ B := by
          have hxN : x ∈ Subgroup.normalizer (B : Set H) := hAnormB (hX hx)
          have hconj : x * b * x⁻¹ ∈ B :=
            (Subgroup.mem_normalizer_iff.mp hxN b).mp hb
          rw [commutatorElement_def]
          exact B.mul_mem hconj (B.inv_mem hb)
        have hbot : ⁅x, b⁆ = 1 := by
          have hmem : ⁅x, b⁆ ∈ X ⊓ B := ⟨hmemX, hmemB⟩
          rwa [hBint, Subgroup.mem_bot] at hmem
        rw [commutatorElement_def] at hbot
        have hxb : x * b * x⁻¹ = b := mul_inv_eq_one.mp hbot
        calc
          b * x = (x * b * x⁻¹) * x := by rw [hxb]
          _ = x * b := by group
      have hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
        intro x hx y hy
        have hAX : A ≤ Subgroup.centralizer (X : Set H) :=
          (Subgroup.le_centralizer_iff (H := X) (K := A)).mp hcentA
        have hBX : B ≤ Subgroup.centralizer (X : Set H) :=
          (Subgroup.le_centralizer_iff (H := X) (K := B)).mp hcentB
        have hsing : ({x} : Set H) ⊆ (X : Set H) := by
          intro z hz
          rw [Set.mem_singleton_iff] at hz
          exact hz ▸ hx
        have hAsing : A ≤ Subgroup.centralizer ({x} : Set H) :=
          hAX.trans (Subgroup.centralizer_le hsing)
        have hBsing : B ≤ Subgroup.centralizer ({x} : Set H) :=
          hBX.trans (Subgroup.centralizer_le hsing)
        have hycent : y ∈ Subgroup.centralizer ({x} : Set H) :=
          (sup_le hAsing hBsing) (hX hy)
        exact (Subgroup.mem_centralizer_singleton_iff.mp hycent).symm
      obtain ⟨x, hx, y, hy, hxy⟩ := hXc
      exact hxy (hcomm x hx y hy)
    ·
      right
      have hBX : B ≤ X := hBint ▸ inf_le_left
      exact (Subgroup.eq_of_le_of_card_ge hBX (by rw [hXB])).symm
  ·
    left
    have hAX : A ≤ X := hAint ▸ inf_le_left
    exact (Subgroup.eq_of_le_of_card_ge hAX (by rw [hXA])).symm

end CFSG.GroupTheory
