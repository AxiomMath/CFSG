module

public import CFSG.SignalizerFunctorTheorem.NonLocal.OrthRat
public import CFSG.SignalizerFunctorTheorem.NonLocal.HeisDist
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataQuotient

public section

open Matrix QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.NonLocal.Orth

variable {k : Type} [Field k] {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)}

@[expose] noncomputable def omegaLin :
    matrixDerived Q₀ →* ((Fin d → k) ≃ₗ[k] (Fin d → k)) :=
  (matrixLinearIso (d := d) (K := k)).toMonoidHom.comp (matrixDerived Q₀).subtype

theorem omegaLin_injective : Function.Injective (omegaLin (Q₀ := Q₀)) :=
  (matrixLinearIso (d := d) (K := k)).injective.comp Subtype.val_injective

theorem polar_sum_smul_right {ι : Type*} [Fintype ι] (x : Fin d → k) (v : ι → k)
    (g : ι → (Fin d → k)) :
    polar Q₀ x (∑ j, v j • g j) = ∑ j, v j * polar Q₀ x (g j) := by
  have h := map_sum (polarBilin Q₀ x) (fun j => v j • g j) Finset.univ
  simp only [map_smul, smul_eq_mul, polarBilin_apply_apply] at h
  exact h

section Heis

variable (hex : ∀ u w : Fin d → k, ∃ x : matrixDerived Q₀,
  matrixLinearIso (d := d) (K := k) x.val = eichler Q₀ u w)

@[expose] noncomputable def eMat (u w : Fin d → k) : matrixDerived Q₀ := (hex u w).choose

theorem omegaLin_eMat (u w : Fin d → k) : omegaLin (eMat hex u w) = eichler Q₀ u w :=
  (hex u w).choose_spec

theorem eMat_mul {u v w : Fin d → k} (hv : polar Q₀ u v = 0) (hw : polar Q₀ u w = 0) :
    eMat hex u v * eMat hex u w = eMat hex u (v + w) := by
  apply omegaLin_injective
  rw [map_mul, omegaLin_eMat, omegaLin_eMat, omegaLin_eMat, eichler_mul hv hw]

theorem eMat_zero (u : Fin d → k) : eMat hex u 0 = 1 := by
  apply omegaLin_injective
  rw [omegaLin_eMat, map_one, eichler_zero_right]

theorem eMat_inv {u w : Fin d → k} (hw : polar Q₀ u w = 0) :
    (eMat hex u w)⁻¹ = eMat hex u (-w) := by
  apply omegaLin_injective
  rw [map_inv, omegaLin_eMat, omegaLin_eMat, eichler_inv hw]

theorem eMat_pow {u w : Fin d → k} (hw : polar Q₀ u w = 0) (n : ℕ) :
    (eMat hex u w) ^ n = eMat hex u ((n : k) • w) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_smul, eMat_zero]
  | succ n ih =>
    rw [pow_succ, ih, eMat_mul hex (by rw [polar_smul_right_eq, hw, mul_zero]) hw]
    congr 1
    rw [Nat.cast_succ, add_smul, one_smul]

include hex

theorem exists_heisenberg_system_of_dual (e₁ e₂ : Fin d → k) (he₂ : Q₀ e₂ = 0)
    (h12 : polar Q₀ e₁ e₂ = 0) {m : ℕ} (t g : Fin m → (Fin d → k))
    (ht1 : ∀ j, polar Q₀ e₁ (t j) = 0) (ht2 : ∀ j, polar Q₀ e₂ (t j) = 0)
    (hg : ∀ j, polar Q₀ e₁ (g j) = 0 ∧ polar Q₀ e₂ (g j) = 0)
    (hgd : ∀ i j, polar Q₀ (t i) (g j) = if i = j then 1 else 0)
    {r : ℕ} [Fact r.Prime] [CharP k r] :
    ∃ (A Z : Subgroup (matrixDerived Q₀)) (y : (Fin m → k) → matrixDerived Q₀),
      IsMulCommutative A ∧ IsPGroup r A ∧ Z ≤ A ∧
      (∀ i, ∀ a ∈ A, ⁅(y i)⁻¹, a⁆ ∈ Z) ∧
      (∃ z ∈ Z, matrixLinearIso (d := d) (K := k) z.val = eichler Q₀ e₁ e₂) ∧
      (∀ (F : Type) [Field F] (ξ : matrixDerived Q₀ → F),
        (∀ z ∈ Z, ∀ z' ∈ Z, ξ (z * z') = ξ z * ξ z') → (∀ z ∈ Z, ξ z ≠ 0) →
        (∃ z ∈ Z, ξ z ≠ 1) → ∀ i j, i ≠ j →
          ∃ a ∈ A, ξ ⁅(y i)⁻¹, a⁆ ≠ ξ ⁅(y j)⁻¹, a⁆) := by
  classical
  obtain ⟨ζ, hζ⟩ : ∃ ζ : k → matrixDerived Q₀, ∀ s, ζ s = eMat hex e₁ (s • e₂) :=
    ⟨_, fun s => rfl⟩
  have hpol1 : ∀ s : k, polar Q₀ e₁ (s • e₂) = 0 := fun s => by
    rw [polar_smul_right_eq, h12, mul_zero]
  have hpol2 : ∀ s : k, polar Q₀ e₂ (s • e₂) = 0 := fun s => by
    rw [polar_smul_right_eq, (polar_self_eq_zero he₂), mul_zero]
  have hζmul : ∀ s s' : k, ζ (s + s') = ζ s * ζ s' := fun s s' => by
    rw [hζ, hζ, hζ, eMat_mul hex (hpol1 s) (hpol1 s'), add_smul]
  obtain ⟨Z, hZ⟩ : ∃ Z : Subgroup (matrixDerived Q₀), ∀ z, z ∈ Z ↔ ∃ s, ζ s = z :=
    ⟨{ carrier := {z | ∃ s, ζ s = z}
       mul_mem' := by
         rintro _ _ ⟨s, rfl⟩ ⟨s', rfl⟩
         exact ⟨s + s', hζmul s s'⟩
       one_mem' := ⟨0, by rw [hζ, zero_smul, eMat_zero]⟩
       inv_mem' := by
         rintro _ ⟨s, rfl⟩
         refine ⟨-s, ?_⟩
         rw [hζ, hζ, eMat_inv hex (hpol1 s), neg_smul] }, fun z => Iff.rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Subgroup (matrixDerived Q₀), ∀ a, a ∈ A ↔
      ∃ w, polar Q₀ e₁ w = 0 ∧ polar Q₀ e₂ w = 0 ∧ eMat hex e₁ w = a :=
    ⟨{ carrier := {a | ∃ w, polar Q₀ e₁ w = 0 ∧ polar Q₀ e₂ w = 0 ∧ eMat hex e₁ w = a}
       mul_mem' := by
         rintro _ _ ⟨w, hw1, hw2, rfl⟩ ⟨w', hw1', hw2', rfl⟩
         exact ⟨w + w', by rw [polar_add_right, hw1, hw1', add_zero],
           by rw [polar_add_right, hw2, hw2', add_zero], (eMat_mul hex hw1 hw1').symm⟩
       one_mem' := ⟨0, polar_zero_right Q₀ _, polar_zero_right Q₀ _, eMat_zero hex e₁⟩
       inv_mem' := by
         rintro _ ⟨w, hw1, hw2, rfl⟩
         exact ⟨-w, by rw [polar_neg_right, hw1, neg_zero],
           by rw [polar_neg_right, hw2, neg_zero], (eMat_inv hex hw1).symm⟩ },
      fun a => Iff.rfl⟩
  have hwv1 : ∀ v : Fin m → k, polar Q₀ e₁ (∑ j, v j • g j) = 0 := fun v => by
    rw [polar_sum_smul_right]
    exact Finset.sum_eq_zero fun j _ => by rw [(hg j).1, mul_zero]
  have hwv2 : ∀ v : Fin m → k, polar Q₀ e₂ (∑ j, v j • g j) = 0 := fun v => by
    rw [polar_sum_smul_right]
    exact Finset.sum_eq_zero fun j _ => by rw [(hg j).2, mul_zero]
  obtain ⟨y, hy⟩ : ∃ y : (Fin m → k) → matrixDerived Q₀,
      ∀ v, y v = eMat hex e₂ (∑ j, v j • g j) := ⟨_, fun v => rfl⟩
  have key : ∀ (v : Fin m → k) (w : Fin d → k), polar Q₀ e₁ w = 0 → polar Q₀ e₂ w = 0 →
      ⁅(y v)⁻¹, eMat hex e₁ w⁆ = ζ (polar Q₀ w (∑ j, v j • g j)) := by
    intro v w hw1 hw2
    apply omegaLin_injective
    rw [map_commutatorElement, map_inv, hy, omegaLin_eMat, omegaLin_eMat, hζ, omegaLin_eMat]
    exact commutator_eichler_heis he₂ h12 hw1 hw2 (hwv1 v) (hwv2 v)
  have hζA : ∀ s, ζ s ∈ A := fun s => (hA _).mpr ⟨s • e₂, hpol1 s, hpol2 s, (hζ s).symm⟩
  have hZζ : ∀ z ∈ Z, ∃ s, ζ s = z := fun z hz => (hZ z).mp hz
  have hζZ : ∀ s, ζ s ∈ Z := fun s => (hZ _).mpr ⟨s, rfl⟩
  refine ⟨A, Z, y, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨w, hw1, hw2, hwa⟩ := (hA a.1).mp a.2
    obtain ⟨w', hw1', hw2', hwb⟩ := (hA b.1).mp b.2
    apply Subtype.ext
    show (a : matrixDerived Q₀) * b = b * a
    rw [← hwa, ← hwb, eMat_mul hex hw1 hw1', eMat_mul hex hw1' hw1, add_comm]
  · have hApow : ∀ a ∈ A, a ^ r = 1 := by
      intro a ha
      obtain ⟨w, hw1, hw2, rfl⟩ := (hA a).mp ha
      rw [eMat_pow hex hw1, CharP.cast_eq_zero, zero_smul, eMat_zero]
    refine IsPGroup.iff_orderOf.mpr fun a => ?_
    have h1 : orderOf a ∣ r := orderOf_dvd_of_pow_eq_one (Subtype.ext (hApow a a.2))
    rcases (Nat.dvd_prime (Fact.out : r.Prime)).mp h1 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  · intro z hz
    obtain ⟨s, rfl⟩ := (hZ z).mp hz
    exact hζA s
  · intro i a ha
    obtain ⟨w, hw1, hw2, rfl⟩ := (hA a).mp ha
    rw [key i w hw1 hw2]
    exact hζZ _
  · refine ⟨ζ 1, hζZ 1, ?_⟩
    change omegaLin (ζ 1) = _
    rw [hζ, omegaLin_eMat, one_smul]
  · intro F _ ξ hmul hne0 hnt i j hij
    let a : k → Fin m → matrixDerived Q₀ := fun s j => eMat hex e₁ (s • t j)
    have haA : ∀ s j, a s j ∈ A := fun s j => (hA _).mpr ⟨s • t j,
      by rw [polar_smul_right_eq, ht1 j, mul_zero], by rw [polar_smul_right_eq, ht2 j, mul_zero],
      rfl⟩
    have hcomm' : ∀ (v : Fin m → k) (s : k) (j : Fin m), ⁅(y v)⁻¹, a s j⁆ = ζ (s * v j) := by
      intro v s j
      have h1 := key v (s • t j) (by rw [polar_smul_right_eq, ht1 j, mul_zero])
        (by rw [polar_smul_right_eq, ht2 j, mul_zero])
      have h2 : polar Q₀ (s • t j) (∑ i, v i • g i) = s * v j := by
        rw [polar_smul_left_eq, polar_sum_smul_right]
        simp only [hgd, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      rw [h2] at h1
      exact h1
    exact hdist_of_pairing Z A ζ hζmul hζZ hZζ y a haA hcomm' ξ hmul hne0 hnt i j hij


theorem exists_heisenberg_system (hnd₀ : (polarBilin Q₀).Nondegenerate) (P₁ P₂ : HypPair Q₀)
    (h : P₁.Orth P₂) {r : ℕ} [Fact r.Prime] [CharP k r] :
    ∃ (m : ℕ) (A Z : Subgroup (matrixDerived Q₀)) (y : (Fin m → k) → matrixDerived Q₀),
      d ≤ m + 4 ∧ IsMulCommutative A ∧ IsPGroup r A ∧ Z ≤ A ∧
      (∀ i, ∀ a ∈ A, ⁅(y i)⁻¹, a⁆ ∈ Z) ∧
      (∃ z ∈ Z, matrixLinearIso (d := d) (K := k) z.val = eichler Q₀ P₁.e P₂.e) ∧
      (∀ (F : Type) [Field F] (ξ : matrixDerived Q₀ → F),
        (∀ z ∈ Z, ∀ z' ∈ Z, ξ (z * z') = ξ z * ξ z') → (∀ z ∈ Z, ξ z ≠ 0) →
        (∃ z ∈ Z, ξ z ≠ 1) → ∀ i j, i ≠ j →
          ∃ a ∈ A, ξ ⁅(y i)⁻¹, a⁆ ≠ ξ ⁅(y j)⁻¹, a⁆) := by
  classical
  let W' : Submodule k (Fin d → k) := P₁.perp ⊓ P₂.perp
  let b := Module.finBasisOfFinrankEq k W' rfl
  let t : Fin (Module.finrank k W') → (Fin d → k) := fun j => (b j : Fin d → k)
  have ht : LinearIndependent k t := b.linearIndependent.map' W'.subtype W'.ker_subtype
  have htP : ∀ j, t j ∈ P₁.perp ⊓ P₂.perp := fun j => (b j).2
  obtain ⟨g, hg, hgd⟩ := exists_dual_perp hnd₀ P₁ P₂ h ht htP
  have ht1 : ∀ j, polar Q₀ P₁.e (t j) = 0 := fun j =>
    (HypPair.mem_perp.mp (Submodule.mem_inf.mp (htP j)).1).1
  have ht2 : ∀ j, polar Q₀ P₂.e (t j) = 0 := fun j =>
    (HypPair.mem_perp.mp (Submodule.mem_inf.mp (htP j)).2).1
  obtain ⟨A, Z, y, h1, h2, h3, h4, h5, h6⟩ :=
    exists_heisenberg_system_of_dual hex P₁.e P₂.e P₂.Q_e h.ee t g ht1 ht2 hg hgd (r := r)
  refine ⟨Module.finrank k W', A, Z, y, ?_, h1, h2, h3, h4, h5, h6⟩
  have := finrank_perp2_ge P₁ P₂
  rwa [Module.finrank_fin_fun] at this

end Heis

end CFSG.SignalizerFunctorTheorem.NonLocal.Orth
