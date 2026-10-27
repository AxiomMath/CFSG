module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Defs

import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Pointwise

namespace CFSG
end CFSG
open CFSG

open scoped commutatorElement

public lemma CFSG.isInvariant_of_characteristic {G A : Type*} [Group G] [Group A]
    [MulDistribMulAction A G] (H : Subgroup G) [H.Characteristic] : IsInvariant A G H := by
  refine ⟨?_⟩
  intro a g
  have hfixed :
      H.comap (MulDistribMulAction.toMulAut A G a).toMonoidHom = H :=
    (inferInstance : H.Characteristic).fixed (MulDistribMulAction.toMulAut A G a)
  constructor
  · intro hg
    have hg' : g ∈ H.comap (MulDistribMulAction.toMulAut A G a).toMonoidHom := by
      rw [hfixed]
      exact hg
    simpa [Subgroup.mem_comap] using hg'
  · intro hg
    have hg' : g ∈ H.comap (MulDistribMulAction.toMulAut A G a).toMonoidHom := by
      simpa [Subgroup.mem_comap] using hg
    have hg'' := hg'
    rw [hfixed] at hg''
    exact hg''

public lemma CFSG.isInvariant_normalizer_of_isInvariant {G A : Type*} [Group G] [Group A]
    [MulDistribMulAction A G] (H : Subgroup G) [IsInvariant A G H] :
    IsInvariant A G (Subgroup.normalizer H) := by
  have hforward : ∀ a : A, ∀ g : G, g ∈ Subgroup.normalizer H → a • g ∈ Subgroup.normalizer H := by
    intro a g hg
    rw [Subgroup.mem_normalizer_iff] at hg ⊢
    intro x
    calc
      x ∈ H ↔ a⁻¹ • x ∈ H :=
        (IsInvariant.invariant (A := A) (G := G) (H := H) a⁻¹ x)
      _ ↔ g * (a⁻¹ • x) * g⁻¹ ∈ H := hg (a⁻¹ • x)
      _ ↔ a • (g * (a⁻¹ • x) * g⁻¹) ∈ H :=
        (IsInvariant.invariant (A := A) (G := G) (H := H) a
          (g * (a⁻¹ • x) * g⁻¹))
      _ ↔ (a • g) * x * (a • g)⁻¹ ∈ H := by
        simp [smul_mul', smul_inv_smul, mul_assoc]
  refine ⟨?_⟩
  intro a g
  constructor
  · exact hforward a g
  · intro hg
    have : a⁻¹ • (a • g) ∈ Subgroup.normalizer H := hforward a⁻¹ (a • g) hg
    simpa [inv_smul_smul] using this

public lemma CFSG.isInvariant_map_subtype {G A : Type*} [Group G] [Group A]
    [MulDistribMulAction A G] (H : Subgroup G) [IsInvariant A G H] (K : Subgroup H)
    [IsInvariant A H K] : IsInvariant A G (K.map H.subtype) := by
  -- Use the restricted action on `H`.
  refine ⟨?_⟩
  intro a g
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨a • x, (IsInvariant.invariant (A := A) (G := H) (H := K) a x).1 hx, ?_⟩
    rfl
  · rintro ⟨x, hx, hxg⟩
    refine ⟨a⁻¹ • x, (IsInvariant.invariant (A := A) (G := H) (H := K) a⁻¹ x).1 hx, ?_⟩
    -- Show that the chosen element maps back to `g`.
    have : ((a⁻¹ • x : H) : G) = g := by
      calc
        ((a⁻¹ • x : H) : G) = a⁻¹ • (x : G) := by rfl
        _ = a⁻¹ • (a • g) := by simpa using congrArg (fun t : G => a⁻¹ • t) hxg
        _ = g := inv_smul_smul a g
    simp only [Subgroup.subtype_apply, this]


public lemma CFSG.isInvariant_sup {G A : Type*} [Group G] [Group A]
    [MulDistribMulAction A G] (H K : Subgroup G)
    [IsInvariant A G H] [IsInvariant A G K] :
    IsInvariant A G (H ⊔ K) := by
  refine ⟨?_⟩
  intro a g
  constructor
  · intro hg
    rw [Subgroup.sup_eq_closure] at hg ⊢
    refine Subgroup.closure_induction (p := fun x _ => a • x ∈ Subgroup.closure ((H : Set G) ∪ (K : Set G)))
      (x := g) ?_ ?_ ?_ ?_ hg
    · intro x hx
      rcases hx with (hx | hx)
      · exact Subgroup.subset_closure (Or.inl ((IsInvariant.invariant (A := A) (G := G) (H := H) a x).1 hx))
      · exact Subgroup.subset_closure (Or.inr ((IsInvariant.invariant (A := A) (G := G) (H := K) a x).1 hx))
    · simp
    · intro x y _ _ hx hy
      simpa [smul_mul'] using Subgroup.mul_mem _ hx hy
    · intro x _ hx
      simpa [smul_inv'] using (Subgroup.inv_mem _ hx)
  · intro hg
    have hg' : a⁻¹ • (a • g) ∈ H ⊔ K := by
      rw [Subgroup.sup_eq_closure] at hg ⊢
      refine Subgroup.closure_induction (p := fun x _ => a⁻¹ • x ∈ Subgroup.closure ((H : Set G) ∪ (K : Set G)))
        (x := a • g) ?_ ?_ ?_ ?_ hg
      · intro x hx
        rcases hx with (hx | hx)
        · exact Subgroup.subset_closure (Or.inl ((IsInvariant.invariant (A := A) (G := G) (H := H) a⁻¹ x).1 hx))
        · exact Subgroup.subset_closure (Or.inr ((IsInvariant.invariant (A := A) (G := G) (H := K) a⁻¹ x).1 hx))
      · simp
      · intro x y _ _ hx hy
        simpa [smul_mul'] using Subgroup.mul_mem _ hx hy
      · intro x _ hx
        simpa [smul_inv'] using (Subgroup.inv_mem _ hx)
    simpa [inv_smul_smul] using hg'

public lemma CFSG.isInvariant_commutator {G A : Type*} [Group G] [Group A]
    [MulDistribMulAction A G] (H K : Subgroup G)
    [IsInvariant A G H] [IsInvariant A G K] :
    IsInvariant A G ⁅H, K⁆ := by
  let S : Set G := {x : G | ∃ h ∈ H, ∃ k ∈ K, ⁅h, k⁆ = x}
  have hforward : ∀ a : A, ∀ x : G, x ∈ ⁅H, K⁆ → a • x ∈ ⁅H, K⁆ := by
    intro a x hx
    rw [Subgroup.commutator_def] at hx ⊢
    change x ∈ Subgroup.closure S at hx
    refine Subgroup.closure_induction (k := S) (p := fun y _ => a • y ∈ Subgroup.closure S) (x := x)
      ?mem ?one ?mul ?inv hx
    · rintro y ⟨h, hh, k, hk, rfl⟩
      refine Subgroup.subset_closure ?_
      refine ⟨a • h, (IsInvariant.invariant (A := A) (G := G) (H := H) a h).1 hh,
        a • k, (IsInvariant.invariant (A := A) (G := G) (H := K) a k).1 hk, ?_⟩
      calc
        ⁅a • h, a • k⁆ = (a • h) * (a • k) * (a • h)⁻¹ * (a • k)⁻¹ := rfl
        _ = a • (h * k * h⁻¹ * k⁻¹) := by
          simp [smul_mul', smul_inv', mul_assoc]
    · simp
    · intro y z _ _ hy hz
      simpa [smul_mul'] using (Subgroup.closure S).mul_mem hy hz
    · intro y _ hy
      simpa using (Subgroup.closure S).inv_mem hy
  refine ⟨?_⟩
  intro a x
  constructor
  · exact hforward a x
  · intro hx
    have : a⁻¹ • (a • x) ∈ ⁅H, K⁆ := hforward a⁻¹ (a • x) hx
    simpa [inv_smul_smul] using this

public lemma CFSG.isInvariant_centralizer {G A : Type*} [Group G] [Group A]
    [MulDistribMulAction A G] (H : Subgroup G) [IsInvariant A G H] :
    IsInvariant A G (Subgroup.centralizer (H : Set G)) := by
  have hforward : ∀ a : A, ∀ g : G,
      g ∈ Subgroup.centralizer (H : Set G) → a • g ∈ Subgroup.centralizer (H : Set G) := by
    intro a g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    intro h hh
    have hh' : a⁻¹ • h ∈ H :=
      (IsInvariant.invariant (A := A) (G := G) (H := H) a⁻¹ h).1 hh
    have hcomm : (a⁻¹ • h) * g = g * (a⁻¹ • h) := hg (a⁻¹ • h) hh'
    have hcomm' : a • ((a⁻¹ • h) * g) = a • (g * (a⁻¹ • h)) :=
      congrArg (fun x => a • x) hcomm
    simpa [smul_mul', smul_smul, inv_smul_smul, mul_assoc] using hcomm'
  refine ⟨?_⟩
  intro a g
  constructor
  · exact hforward a g
  · intro hg
    have : a⁻¹ • (a • g) ∈ Subgroup.centralizer (H : Set G) := hforward a⁻¹ (a • g) hg
    simpa [inv_smul_smul] using this

public lemma CFSG.isInvariant_inf {G A : Type*} [Group G] [Group A]
    [MulDistribMulAction A G] (H K : Subgroup G)
    [IsInvariant A G H] [IsInvariant A G K] :
    IsInvariant A G (H ⊓ K) := by
  refine ⟨?_⟩
  intro a g
  constructor
  · rintro ⟨hgH, hgK⟩
    exact ⟨(IsInvariant.invariant (A := A) (G := G) (H := H) a g).1 hgH,
      (IsInvariant.invariant (A := A) (G := G) (H := K) a g).1 hgK⟩
  · intro hg
    rcases hg with ⟨hgH, hgK⟩
    have hg' : a⁻¹ • (a • g) ∈ H ⊓ K := by
      refine ⟨(IsInvariant.invariant (A := A) (G := G) (H := H) a⁻¹ (a • g)).1 hgH,
        (IsInvariant.invariant (A := A) (G := G) (H := K) a⁻¹ (a • g)).1 hgK⟩
    simpa [inv_smul_smul] using hg'

public lemma CFSG.isInvariant_subgroupOf {G A : Type*} [Group G] [Group A]
    [MulDistribMulAction A G] (H K : Subgroup G)
    [IsInvariant A G H] [IsInvariant A G K] :
    IsInvariant A K (H.subgroupOf K) := by
  refine ⟨?_⟩
  intro a x
  constructor
  · intro hx
    have hx' : (x : G) ∈ H := hx
    have hmem : (a • (x : K) : K) ∈ H.subgroupOf K := by
      have : (a • (x : K) : G) ∈ H := by
        exact (IsInvariant.invariant (A := A) (G := G) (H := H) a (x : G)).1 hx'
      change a • (x : G) ∈ H
      exact this
    exact hmem
  · intro hx
    change (a • (x : G)) ∈ H at hx
    have hx' : (a • (x : K) : G) ∈ H := by
      exact hx
    have hx_inv : (x : G) ∈ H := by
      simpa using (IsInvariant.invariant (A := A) (G := G) (H := H) a (x : G)).2 hx'
    exact hx_inv


/-- If `X` and `Y` are invariant and `Y` normalizes `X`, then `X ⊔ Y` is invariant. -/
public theorem CFSG.isInvariant_sup_of_le_normalizer
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    (X Y : Subgroup G) (hY_le_normX : Y ≤ Subgroup.normalizer (X : Set G))
    [IsInvariant A G X] [IsInvariant A G Y] :
    IsInvariant A G (X ⊔ Y) := by
  have hXY_le_normX : X ⊔ Y ≤ Subgroup.normalizer (X : Set G) := sup_le X.le_normalizer hY_le_normX
  letI : (X.subgroupOf (X ⊔ Y)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := X ⊔ Y) (N := X) hXY_le_normX
  have hsub_sup : X.subgroupOf (X ⊔ Y) ⊔ Y.subgroupOf (X ⊔ Y) = ⊤ := by
    calc
      X.subgroupOf (X ⊔ Y) ⊔ Y.subgroupOf (X ⊔ Y) = (X ⊔ Y).subgroupOf (X ⊔ Y) := by
        symm
        exact Subgroup.subgroupOf_sup (A := X) (A' := Y) (B := X ⊔ Y) le_sup_left le_sup_right
      _ = ⊤ := by simp
  have hforward : ∀ a : A, ∀ g : G, g ∈ X ⊔ Y → a • g ∈ X ⊔ Y := by
    intro a g hg
    let gXY : ↥(X ⊔ Y) := ⟨g, hg⟩
    have hg_sup : gXY ∈ X.subgroupOf (X ⊔ Y) ⊔ Y.subgroupOf (X ⊔ Y) := by
      simp [hsub_sup]
    rcases (Subgroup.mem_sup_of_normal_left
      (s := X.subgroupOf (X ⊔ Y)) (t := Y.subgroupOf (X ⊔ Y)) (x := gXY)).1 hg_sup with
      ⟨x, hx, y, hy, hxy⟩
    have hxX : a • ((x : ↥(X ⊔ Y)) : G) ∈ X := by
      exact
        (IsInvariant.invariant (A := A) (G := G) (H := X) a (((x : ↥(X ⊔ Y)) : G))).1 <|
          by simpa [Subgroup.mem_subgroupOf] using hx
    have hyY : a • ((y : ↥(X ⊔ Y)) : G) ∈ Y := by
      exact
        (IsInvariant.invariant (A := A) (G := G) (H := Y) a (((y : ↥(X ⊔ Y)) : G))).1 <|
          by simpa [Subgroup.mem_subgroupOf] using hy
    have hxyG : ((x : ↥(X ⊔ Y)) : G) * ((y : ↥(X ⊔ Y)) : G) = g := by
      exact congrArg Subtype.val hxy
    have hsmulG :
        a • g = a • ((x : ↥(X ⊔ Y)) : G) * (a • ((y : ↥(X ⊔ Y)) : G)) := by
      calc
        a • g = a • (((x : ↥(X ⊔ Y)) : G) * ((y : ↥(X ⊔ Y)) : G)) := by rw [← hxyG]
        _ = a • ((x : ↥(X ⊔ Y)) : G) * (a • ((y : ↥(X ⊔ Y)) : G)) := by
            simp [smul_mul']
    have hmem : a • ((x : ↥(X ⊔ Y)) : G) * (a • ((y : ↥(X ⊔ Y)) : G)) ∈ X ⊔ Y :=
      Subgroup.mul_mem_sup hxX hyY
    exact hsmulG ▸ hmem
  refine ⟨?_⟩
  intro a g
  constructor
  · exact hforward a g
  · intro hg
    have : a⁻¹ • (a • g) ∈ X ⊔ Y := hforward a⁻¹ (a • g) hg
    simpa [inv_smul_smul] using this
