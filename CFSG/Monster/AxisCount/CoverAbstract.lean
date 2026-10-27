module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

public section

namespace CFSG.Monster.AxisCount

open MulAction

section Cover

variable {G X : Type*} [Group G] [MulAction G X]

theorem mem_doubleCoset_of_inv_smul_eq {H U : Subgroup G} (f : X) (hU : U ≤ H) {h : G}
    (hh : h ∈ H) {g : G} (hg : g ∈ H) {u : G} (hu : u ∈ U)
    (e : g⁻¹ • f = u • h⁻¹ • f) :
    g ∈ DoubleCoset.doubleCoset h ((H ⊓ stabilizer G f : Subgroup G) : Set G) (U : Set G) := by
  refine DoubleCoset.mem_doubleCoset.2 ⟨g * u * h⁻¹, ?_, u⁻¹, U.inv_mem hu, by group⟩
  refine Subgroup.mem_inf.2 ⟨H.mul_mem (H.mul_mem hg (hU hu)) (H.inv_mem hh), ?_⟩
  rw [mem_stabilizer_iff, mul_smul, mul_smul, ← e, smul_inv_smul]

theorem subset_iUnion_doubleCoset {R : Type*} {H U : Subgroup G} (f : X) (hU : U ≤ H)
    {h : R → G} (hh : ∀ r, h r ∈ H)
    (hcov : ∀ g ∈ H, ∃ r, ∃ u ∈ U, g⁻¹ • f = u • (h r)⁻¹ • f) :
    (H : Set G) ⊆ ⋃ r, DoubleCoset.doubleCoset (h r)
      ((H ⊓ stabilizer G f : Subgroup G) : Set G) (U : Set G) := by
  intro g hg
  obtain ⟨r, u, hu, e⟩ := hcov g hg
  exact Set.mem_iUnion.2 ⟨r, mem_doubleCoset_of_inv_smul_eq f hU (hh r) hg hu e⟩

theorem inv_smul_eq_of_mem_doubleCoset {H U : Subgroup G} (f : X) {h g : G}
    (hg : g ∈ DoubleCoset.doubleCoset h ((H ⊓ stabilizer G f : Subgroup G) : Set G)
      (U : Set G)) :
    ∃ u ∈ U, g⁻¹ • f = u • h⁻¹ • f := by
  obtain ⟨n, hn, u, hu, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
  have hn' : n⁻¹ • f = f := by
    have h1 : n • f = f := mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hn).2
    rw [inv_smul_eq_iff]
    exact h1.symm
  refine ⟨u⁻¹, U.inv_mem hu, ?_⟩
  rw [mul_inv_rev, mul_inv_rev, mul_smul, mul_smul, hn']

theorem disjoint_doubleCoset {H U : Subgroup G} (f : X) {h h' : G}
    (hd : Disjoint (orbit U (h⁻¹ • f)) (orbit U (h'⁻¹ • f))) :
    Disjoint (DoubleCoset.doubleCoset h ((H ⊓ stabilizer G f : Subgroup G) : Set G) (U : Set G))
      (DoubleCoset.doubleCoset h' ((H ⊓ stabilizer G f : Subgroup G) : Set G) (U : Set G)) := by
  refine Set.disjoint_left.2 fun g hg hg' => ?_
  obtain ⟨u, hu, e⟩ := inv_smul_eq_of_mem_doubleCoset f hg
  obtain ⟨u', hu', e'⟩ := inv_smul_eq_of_mem_doubleCoset f hg'
  exact Set.disjoint_left.1 hd (show g⁻¹ • f ∈ orbit U (h⁻¹ • f) from ⟨⟨u, hu⟩, e.symm⟩)
    (show g⁻¹ • f ∈ orbit U (h'⁻¹ • f) from ⟨⟨u', hu'⟩, e'.symm⟩)

theorem pairwise_disjoint_doubleCoset {R : Type*} {H U : Subgroup G} (f : X) {h : R → G}
    (hd : ∀ r r', r ≠ r' → Disjoint (orbit U ((h r)⁻¹ • f)) (orbit U ((h r')⁻¹ • f))) :
    Pairwise (Function.onFun Disjoint fun r => DoubleCoset.doubleCoset (h r)
      ((H ⊓ stabilizer G f : Subgroup G) : Set G) (U : Set G)) :=
  fun r r' hne => disjoint_doubleCoset f (hd r r' hne)

end Cover

section Card

variable {G X : Type*} [Group G] [MulAction G X]

theorem range_inv_smul_doubleCoset {H U : Subgroup G} (f : X) (h : G) :
    Set.range (fun g : DoubleCoset.doubleCoset h
      ((H ⊓ stabilizer G f : Subgroup G) : Set G) (U : Set G) => (g : G)⁻¹ • f) =
      orbit U (h⁻¹ • f) := by
  ext x
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨u, hu, e⟩ := inv_smul_eq_of_mem_doubleCoset f hg
    exact ⟨⟨u, hu⟩, e.symm⟩
  · rintro ⟨⟨u, hu⟩, rfl⟩
    refine ⟨⟨h * u⁻¹, DoubleCoset.mem_doubleCoset.2 ⟨1, Subgroup.one_mem _, u⁻¹, U.inv_mem hu,
      by group⟩⟩, ?_⟩
    show (h * u⁻¹)⁻¹ • f = u • h⁻¹ • f
    rw [mul_inv_rev, inv_inv, mul_smul]

theorem natCard_doubleCoset {H U : Subgroup G} (f : X) (hU : U ≤ H) {h : G} (hh : h ∈ H) :
    Nat.card (DoubleCoset.doubleCoset h ((H ⊓ stabilizer G f : Subgroup G) : Set G)
        (U : Set G)) =
      Nat.card (H ⊓ stabilizer G f : Subgroup G) * Nat.card (orbit U (h⁻¹ • f)) := by
  classical
  set N : Subgroup G := H ⊓ stabilizer G f with hN
  set D : Set G := DoubleCoset.doubleCoset h (N : Set G) (U : Set G) with hD
  have hDH : ∀ g ∈ D, g ∈ H := by
    intro g hg
    obtain ⟨n, hn, u, hu, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
    exact H.mul_mem (H.mul_mem (Subgroup.mem_inf.1 hn).1 hh) (hU hu)
  let Φ : D → X := fun g => (g : G)⁻¹ • f
  have hrange : Set.range Φ = orbit U (h⁻¹ • f) := range_inv_smul_doubleCoset f h
  let Φ' : D → Set.range Φ := Set.rangeFactorization Φ
  have hfib : ∀ g₀ : D, Nonempty ({g : D // Φ' g = Φ' g₀} ≃ N) := by
    intro g₀
    have key : ∀ g : D, Φ' g = Φ' g₀ → (g : G) * (g₀ : G)⁻¹ ∈ N := by
      intro g hg
      have e : (g : G)⁻¹ • f = (g₀ : G)⁻¹ • f := congrArg Subtype.val hg
      refine Subgroup.mem_inf.2 ⟨H.mul_mem (hDH g g.2) (H.inv_mem (hDH g₀ g₀.2)), ?_⟩
      rw [mem_stabilizer_iff, mul_smul, ← e, smul_inv_smul]
    have key' : ∀ n : N, ((n : G) * (g₀ : G)) ∈ D := by
      intro n
      obtain ⟨m, hm, u, hu, hg₀⟩ := DoubleCoset.mem_doubleCoset.1 g₀.2
      exact DoubleCoset.mem_doubleCoset.2 ⟨n * m, N.mul_mem n.2 hm, u, hu, by rw [hg₀]; group⟩
    refine ⟨{ toFun := fun g => ⟨(g : D) * (g₀ : G)⁻¹, key g g.2⟩
              invFun := fun n => ⟨⟨(n : G) * (g₀ : G), key' n⟩, ?_⟩
              left_inv := fun g => Subtype.ext (Subtype.ext (by simp))
              right_inv := fun n => Subtype.ext (by simp) }⟩
    apply Subtype.ext
    show (((n : G) * (g₀ : G))⁻¹ • f) = (g₀ : G)⁻¹ • f
    have hn : (n : G)⁻¹ • f = f := by
      rw [inv_smul_eq_iff]
      exact (mem_stabilizer_iff.1 (Subgroup.mem_inf.1 n.2).2).symm
    rw [mul_inv_rev, mul_smul, hn]
  calc Nat.card D = Nat.card (Σ y : Set.range Φ, {g : D // Φ' g = y}) :=
        Nat.card_congr (Equiv.sigmaFiberEquiv Φ').symm
    _ = Nat.card (Σ _ : Set.range Φ, N) := by
        refine Nat.card_congr (Equiv.sigmaCongrRight fun y => Classical.choice ?_)
        obtain ⟨g₀, rfl⟩ := Set.rangeFactorization_surjective y
        exact hfib g₀
    _ = Nat.card N * Nat.card (orbit U (h⁻¹ • f)) := by
        rw [Nat.card_congr (Equiv.sigmaEquivProd _ _), Nat.card_prod, mul_comm, hrange]

end Card

section Transport

variable {K G : Type*} [Group K] [Group G]

theorem image_doubleCoset (φ : K →* G) (a : K) (A B : Subgroup K) :
    φ '' DoubleCoset.doubleCoset a (A : Set K) (B : Set K) =
      DoubleCoset.doubleCoset (φ a) ((A.map φ : Subgroup G) : Set G)
        ((B.map φ : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨n, hn, u, hu, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hy
    exact DoubleCoset.mem_doubleCoset.2 ⟨φ n, Subgroup.mem_map_of_mem φ hn, φ u,
      Subgroup.mem_map_of_mem φ hu, by simp⟩
  · intro hx
    obtain ⟨n', hn', u', hu', rfl⟩ := DoubleCoset.mem_doubleCoset.1 hx
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hn'
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hu'
    exact ⟨n * a * u, DoubleCoset.mem_doubleCoset.2 ⟨n, hn, u, hu, rfl⟩, by simp⟩

theorem natCard_doubleCoset_map {φ : K →* G} (hφ : Function.Injective φ) (a : K)
    (A B : Subgroup K) :
    Nat.card (DoubleCoset.doubleCoset (φ a) ((A.map φ : Subgroup G) : Set G)
        ((B.map φ : Subgroup G) : Set G)) =
      Nat.card (DoubleCoset.doubleCoset a (A : Set K) (B : Set K)) := by
  rw [← image_doubleCoset]
  exact Nat.card_image_of_injective hφ _

end Transport

end CFSG.Monster.AxisCount
