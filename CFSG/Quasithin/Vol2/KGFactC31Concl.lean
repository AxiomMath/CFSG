module

public import CFSG.Quasithin.Vol2.KGFactC31Shape
public import CFSG.Quasithin.Vol2.KGFactC31EBasis
public import CFSG.Quasithin.Background.C4Statement

public section

namespace CFSG.Quasithin.KGC31

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank Matrix
open scoped Pointwise

@[expose] def Concl {A : Type} [Group A] (S M₀ R M V : Subgroup A) : Prop :=
  (C31Case3 ⊤ R M M₀ V S ∨ C31Case4 ⊤ R M M₀ V S ∨ C31Case5 ⊤ R M M₀ V S ∨
      C31Case6 ⊤ R M M₀ V S ∨ C31Case7 ⊤ R M M₀ V S ∨ C31Case8 ⊤ R M M₀ V S ∨
      C31Case9 ⊤ R M M₀ V S) ∧
    (C48Case1 ⊤ R M M₀ V S ∨ C48Case2 ⊤ R M M₀ V S ∨ C48Case3 ⊤ R M M₀ V S ∨
      C48Case4 ⊤ R M M₀ V S ∨ C48Case5 ⊤ R M M₀ V S ∨ C48Case6 ⊤ R M M₀ V S ∨
      C48Case7 ⊤ R M M₀ V S) ∧
    ∀ m k : ℕ, (m = 3 ∨ m = 4) → IsPSL m 2 1 (ModO2 M₀) →
      IsSumOfNaturalModules (M₀ ⊔ R) V ⊥ (R.subgroupOf (M₀ ⊔ R)) (StatedSL m (ZMod 2)) false k →
      k ≤ 2

variable {A : Type} [Group A]

theorem sup_inf_centralizer_eq {M₀ R V : Subgroup A}
    (hRN : R ≤ Subgroup.normalizer (M₀ : Set A)) (hRC : R ≤ Subgroup.centralizer (V : Set A))
    (hM₀C : M₀ ⊓ Subgroup.centralizer (V : Set A) ≤ V) (hVR : V ≤ R) :
    (M₀ ⊔ R) ⊓ Subgroup.centralizer (V : Set A) = R := by
  refine le_antisymm (fun x ⟨hx, hxC⟩ => ?_) (le_inf le_sup_right hRC)
  have hx' : x ∈ ((M₀ : Set A) * (R : Set A)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left M₀ R hRN]
    exact hx
  obtain ⟨m, hm, r, hr, rfl⟩ := hx'
  have hmC : m ∈ Subgroup.centralizer (V : Set A) := by
    have : m = m * r * r⁻¹ := by group
    rw [this]
    exact (Subgroup.centralizer (V : Set A)).mul_mem hxC
      ((Subgroup.centralizer (V : Set A)).inv_mem (hRC hr))
  exact R.mul_mem (hVR (hM₀C ⟨hm, hmC⟩)) hr

theorem summand_of_card [Finite A] {M₀ R V : Subgroup A} (hV : Nat.card V ≤ 16) :
    ∀ m k : ℕ, (m = 3 ∨ m = 4) → IsPSL m 2 1 (ModO2 M₀) →
      IsSumOfNaturalModules (M₀ ⊔ R) V ⊥ (R.subgroupOf (M₀ ⊔ R)) (StatedSL m (ZMod 2)) false k →
      k ≤ 2 := by
  intro m k hm _ h
  have := summand_le hV (by omega) h
  omega

theorem conj_map {G₀ : Type*} [Group G₀] {k : ℕ} {v : Fin k → G₀} {g : G₀}
    {M : Matrix (Fin k) (Fin k) (ZMod 2)} (h : ∀ i, g * v i * g⁻¹ = eElt v fun r => M r i)
    (ι : G₀ →* A) (i : Fin k) :
    ι g * ι (v i) * (ι g)⁻¹ = eElt (fun i => ι (v i)) fun r => M r i := by
  rw [← map_inv, ← map_mul, ← map_mul, h i, map_eElt]

@[expose] noncomputable def ecoords {Γ : Type*} [Group Γ] {n : ℕ} {v : Fin n → Γ}
    (hv : EBasis v) : ↥(eSub hv) ≃* Multiplicative (Fin n → ZMod 2) :=
  (MonoidHom.ofInjective (f := eHom hv)
    (fun c d hcd => (eElt_injective hv hcd : Multiplicative.toAdd c = Multiplicative.toAdd d))).symm

theorem eElt_ecoords {Γ : Type*} [Group Γ] {n : ℕ} {v : Fin n → Γ} (hv : EBasis v)
    (x : ↥(eSub hv)) : eElt v (Multiplicative.toAdd (ecoords hv x)) = (x : Γ) := by
  have h := (MonoidHom.ofInjective (f := eHom hv)
    (fun c d hcd => (eElt_injective hv hcd : Multiplicative.toAdd c =
      Multiplicative.toAdd d))).apply_symm_apply x
  exact congrArg Subtype.val h

theorem ecoords_conj {Γ : Type*} [Group Γ] {n : ℕ} {v : Fin n → Γ} (hv : EBasis v)
    (g : ↥(eNorm hv)) (u w : ↥(eSub hv)) (hw : (w : Γ) = g * u * g⁻¹) :
    Multiplicative.toAdd (ecoords hv w) = eMat hv g *ᵥ Multiplicative.toAdd (ecoords hv u) := by
  apply eElt_injective hv
  rw [eElt_ecoords, ← conj_eq_eElt_mulVec, eElt_ecoords]
  exact hw

theorem mem_eNorm_of_cent {Γ : Type*} [Group Γ] {n : ℕ} {v : Fin n → Γ} (hv : EBasis v) {r : Γ}
    (hr : r ∈ Subgroup.centralizer (eSub hv : Set Γ)) : r ∈ eNorm hv :=
  Subgroup.centralizer_le_normalizer _ hr

end CFSG.Quasithin.KGC31

end
