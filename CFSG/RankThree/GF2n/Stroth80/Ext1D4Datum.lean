module

public import CFSG.RankThree.GF2n.Stroth80.Ext1D4Assembly
public import CFSG.LieType.D4Small.Datum

public section

namespace CFSG.RankThree.GF2n.Stroth80.Ext1D4

open CFSG.LieType.D4Small Matrix
open scoped commutatorElement

@[expose] def halfVec (β : Fin 4 → ℤ) : Fin 4 → ℤ := fun i => β i / 2

theorem isD4Root_halfVec : ∀ β ∈ posRoot, IsD4Root (halfVec β) := by
  unfold IsD4Root
  decide +kernel

theorem halfVec_dot_nonneg : ∀ β ∈ posRoot, ∀ γ ∈ posRoot, β + γ ∉ posRoot →
    0 ≤ halfVec β ⬝ᵥ halfVec γ := by
  decide +kernel

theorem halfVec_dot_eq : ∀ β ∈ posRoot, ∀ γ ∈ posRoot, β + γ ∈ posRoot →
    halfVec β ⬝ᵥ halfVec γ = -1 ∧ halfVec (β + γ) = halfVec β + halfVec γ := by
  decide +kernel

theorem two_mul_halfVec : ∀ β ∈ posRoot, ∀ i, β i = 2 * halfVec β i := by
  decide +kernel

section Datum

variable {G : Type*} [Group G] {K : Type*} [Field K] (D : D4Datum G K)

@[expose] def posX (β : Fin 4 → ℤ) (t : K) : G := D.x (halfVec β) t

theorem posX_add : ∀ β ∈ posRoot, ∀ s t, posX D β (s + t) = posX D β s * posX D β t :=
  fun β hβ s t => D.x_add _ (isD4Root_halfVec β hβ) s t

theorem posX_commute : ∀ β ∈ posRoot, ∀ γ ∈ posRoot, β + γ ∉ posRoot →
    posX D β 1 * posX D γ 1 = posX D γ 1 * posX D β 1 :=
  fun β hβ γ hγ h => (D.commute _ _ (isD4Root_halfVec β hβ) (isD4Root_halfVec γ hγ)
    (halfVec_dot_nonneg β hβ γ hγ h) 1 1).eq

theorem posX_comm_eq : ∀ β ∈ posRoot, ∀ γ ∈ posRoot, β + γ ∈ posRoot →
    posX D β 1 * posX D γ 1 = posX D (β + γ) 1 * posX D γ 1 * posX D β 1 := by
  intro β hβ γ hγ h
  obtain ⟨h1, h2⟩ := halfVec_dot_eq β hβ γ hγ h
  have hc := D.comm_eq _ _ (isD4Root_halfVec β hβ) (isD4Root_halfVec γ hγ) h1 1 1
  rw [mul_one, commutatorElement_def] at hc
  simp only [posX, h2]
  rw [← hc]
  group

theorem torusChar_halfVec [Fintype K] {m : ℕ} (hm : 2 * m = Fintype.card K) :
    ∀ β ∈ posRoot, ∀ z : Fin 4 → Kˣ, torusChar (halfVec β) z = wtChar m 0 β z := by
  intro β hβ z
  have hu : ∀ u : Kˣ, u ^ ((2 * m : ℕ) : ℤ) = u := fun u => by
    rw [zpow_natCast, hm]
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, FiniteField.pow_card])
  rw [torusChar_apply, wtChar, pow_zero, pow_one]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [two_mul_halfVec β hβ i, show 2 * halfVec β i * (m : ℤ) = ((2 * m : ℕ) : ℤ) * halfVec β i by
    push_cast; ring, zpow_mul, hu]

theorem h_posX [Fintype K] {m : ℕ} (hm : 2 * m = Fintype.card K) :
    ∀ β ∈ posRoot, ∀ z t, D.h z * posX D β t = posX D β ((wtChar m 0 β z : K) * t) * D.h z := by
  intro β hβ z t
  have h := D.h_conj _ (isD4Root_halfVec β hβ) z t
  rw [torusChar_halfVec hm β hβ] at h
  rw [posX, posX, ← h]
  group

@[expose] def borel : Subgroup G :=
  Subgroup.closure ({g | ∃ β ∈ posRoot, ∃ t, posX D β t = g} ∪ Set.range D.h)

theorem preserves_of_mem_borel [Finite G] {E : Type*} [AddCommGroup E] [Module K E]
    (ρ : G →* Module.End K E) (C : Submodule K E)
    (hx : ∀ β ∈ posRoot, ∀ t, ∀ c ∈ C, ρ (posX D β t) c ∈ C)
    (hz : ∀ z, ∀ c ∈ C, ρ (D.h z) c ∈ C) : ∀ g ∈ borel D, ∀ c ∈ C, ρ g c ∈ C :=
  preserves_of_mem_closure ρ C _ (by
    rintro s (⟨β, hβ, t, rfl⟩ | ⟨z, rfl⟩)
    · exact hx β hβ t
    · exact hz z)

theorem exists_invariant_compl_of_datum [Fintype K] [CharP K 2] [Finite G] {f m : ℕ}
    (hf : Fintype.card K = 2 ^ f) (hm : 2 * m = Fintype.card K) (hq : 4 ≤ Fintype.card K)
    (hB : ((borel D).index : K) ≠ 0) {E : Type*} [AddCommGroup E] [Module K E]
    (ρ : G →* Module.End K E) (A : Submodule K E) (hAinv : ∀ g, ∀ a ∈ A, ρ g a ∈ A)
    {W₁ W₂ : Finset (Fin 4 → ℤ)} (hW₁ : IsMinWt W₁) (hW₂ : IsMinWt W₂) {a₁ a₂ : ℕ}
    (ha₁ : a₁ < f) (ha₂ : a₂ < f) (bA : Module.Basis W₁ K A)
    (hbAx : ∀ β ∈ posRoot, ∀ t χ,
      ρ (posX D β t) (bA χ) = ∑ ψ, rootElt W₁ β (t ^ 2 ^ a₁) ψ χ • (bA ψ : E))
    (hbAh : ∀ z χ, ρ (D.h z) (bA χ) = (wtChar m a₁ (χ : Fin 4 → ℤ) z : K) • (bA χ : E))
    (bQ : Module.Basis W₂ K (E ⧸ A))
    (hbQx : ∀ β ∈ posRoot, ∀ t χ (e : E), A.mkQ e = bQ χ →
      A.mkQ (ρ (posX D β t) e) = ∑ ψ, rootElt W₂ β (t ^ 2 ^ a₂) ψ χ • bQ ψ)
    (hbQh : ∀ z χ (e : E), A.mkQ e = bQ χ →
      A.mkQ (ρ (D.h z) e) = (wtChar m a₂ (χ : Fin 4 → ℤ) z : K) • bQ χ) :
    ∃ C : Submodule K E, IsCompl A C ∧ ∀ g, ∀ c ∈ C, ρ g c ∈ C :=
  exists_invariant_compl_of_minuscule hf hm hq ρ A hAinv (posX D) D.h (posX_add D)
    (posX_commute D) (posX_comm_eq D) (h_posX D hm) (borel D) hB
    (fun C hxC hzC => preserves_of_mem_borel D ρ C hxC hzC) hW₁ hW₂ ha₁ ha₂ bA hbAx hbAh bQ
    hbQx hbQh

end Datum

end CFSG.RankThree.GF2n.Stroth80.Ext1D4
