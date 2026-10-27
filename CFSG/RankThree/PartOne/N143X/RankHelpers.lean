module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.RingTheory.RootsOfUnity.Basic

public section

namespace CFSG.RankThree.PartOne.N143X

theorem isPGroup_of_pow_eq_one {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    (hE : ∀ x ∈ E, x ^ p = 1) : IsPGroup p E :=
  fun x => ⟨1, Subtype.ext (by simpa using hE x.1 x.2)⟩

theorem card_le_sq_of_injective_fun {E : Type} {L : Type} [Field L] {p : ℕ} (hp : 0 < p)
    (φ : E → (Fin 2 → Lˣ)) (hφ : Function.Injective φ) (hpow : ∀ x k, φ x k ^ p = 1) :
    Nat.card E ≤ p ^ 2 := by
  classical
  have : NeZero p := ⟨hp.ne'⟩
  let ψ : E → (Fin 2 → rootsOfUnity p L) := fun x k =>
    ⟨φ x k, (mem_rootsOfUnity p _).2 (hpow x k)⟩
  have hψ : Function.Injective ψ := fun x y h => hφ (funext fun k =>
    congrArg (fun z : rootsOfUnity p L => (z : Lˣ)) (congrFun h k))
  have hR : Nat.card (rootsOfUnity p L) ≤ p := card_rootsOfUnity L p
  calc Nat.card E ≤ Nat.card (Fin 2 → rootsOfUnity p L) := Nat.card_le_card_of_injective ψ hψ
    _ = Nat.card (rootsOfUnity p L) ^ 2 := by rw [Nat.card_fun]; simp
    _ ≤ p ^ 2 := Nat.pow_le_pow_left hR 2

theorem false_of_pow_three_of_isCyclic {G : Type} [Group G] {p : ℕ} (hp : p.Prime)
    {E : Subgroup G} [IsCyclic E] (hE : ∀ x ∈ E, x ^ p = 1) (hcard : Nat.card E = p ^ 3) :
    False := by
  obtain ⟨x, hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have h1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (Subtype.ext (hE x x.2))
  rw [hx, hcard] at h1
  have := Nat.le_of_dvd hp.pos h1
  have h3 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  rw [pow_one] at h3
  omega

theorem card_pow_eq_one_le_of_cyclic {C : Type} [Group C] [IsCyclic C] [Finite C] {p : ℕ}
    (hp : 0 < p) : Nat.card {c : C // c ^ p = 1} ≤ p := by
  classical
  have : Fintype C := Fintype.ofFinite C
  have h := IsCyclic.card_pow_eq_one_le (α := C) hp
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact h

theorem card_le_sq_of_injective_prod_cyclic {E A B : Type} [Group E] [Group A] [Group B]
    [IsCyclic A] [IsCyclic B] [Finite A] [Finite B] (ψ : E →* A × B)
    (hψ : Function.Injective ψ) {p : ℕ} (hp : 0 < p) (hE : ∀ x : E, x ^ p = 1) :
    Nat.card E ≤ p ^ 2 := by
  classical
  let f : E → {a : A // a ^ p = 1} × {b : B // b ^ p = 1} := fun x =>
    (⟨(ψ x).1, by
      have h := congrArg (fun y => (ψ y).1) (hE x)
      simpa [map_pow] using h⟩,
     ⟨(ψ x).2, by
      have h := congrArg (fun y => (ψ y).2) (hE x)
      simpa [map_pow] using h⟩)
  have hf : Function.Injective f := fun x y h => hψ (Prod.ext
    (congrArg (fun z => (z.1 : A)) h) (congrArg (fun z => (z.2 : B)) h))
  have hA := card_pow_eq_one_le_of_cyclic (C := A) hp
  have hB := card_pow_eq_one_le_of_cyclic (C := B) hp
  have : Finite ({a : A // a ^ p = 1} × {b : B // b ^ p = 1}) := inferInstance
  calc Nat.card E ≤ Nat.card ({a : A // a ^ p = 1} × {b : B // b ^ p = 1}) :=
        Nat.card_le_card_of_injective f hf
    _ = Nat.card {a : A // a ^ p = 1} * Nat.card {b : B // b ^ p = 1} := Nat.card_prod _ _
    _ ≤ p * p := Nat.mul_le_mul hA hB
    _ = p ^ 2 := (sq p).symm

theorem card_le_sq_of_map_into_prod {G H A B : Type} [Group G] [Group H] [Group A] [Group B]
    [IsCyclic A] [IsCyclic B] [Finite A] [Finite B] (φ : G →* H) (hφ : Function.Injective φ)
    (T : Subgroup H) (eT : T ≃* A × B) {p : ℕ} (hp : 0 < p) {E : Subgroup G}
    (hE : ∀ x ∈ E, x ^ p = 1) (hET : ∀ x ∈ E, φ x ∈ T) : Nat.card E ≤ p ^ 2 := by
  let ψ : E →* A × B := eT.toMonoidHom.comp
    (MonoidHom.codRestrict (φ.comp E.subtype) T fun x => hET x.1 x.2)
  have hψ : Function.Injective ψ := by
    intro x y h
    have h1 := eT.injective h
    exact Subtype.ext (hφ (congrArg Subtype.val h1))
  exact card_le_sq_of_injective_prod_cyclic ψ hψ hp fun x => Subtype.ext (hE x x.2)

end CFSG.RankThree.PartOne.N143X
