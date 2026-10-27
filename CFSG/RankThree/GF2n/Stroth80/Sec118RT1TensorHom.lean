module

public import CFSG.RankThree.GF2n.Stroth80.Sec118RT1Tensor
public import CFSG.ClassicalGroups.Symplectic.TensorUnique

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix
open CFSG.ClassicalGroups.Symplectic

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.exists_tensorHom (hc : Ctx M Q Z B)
    (h : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {m : ℕ} (hm : 1 ≤ m) {W₁ W₂ : Submodule K M₀.E} (hdisj : W₁ ⊓ W₂ = ⊥)
    (hsup : W₁ ⊔ W₂ = cmComm M Q Z B K γ M₀ φ)
    (hW₁ : ∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W₁, φ s w ∈ W₁)
    (hW₂ : ∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W₂, φ s w ∈ W₂)
    (ρ : ↥(XbarH M Q Z B) →* GL (Fin m ⊕ Fin m) K) (hρr : ρ.range = StatedSp m K)
    (e₁ : W₁ ≃ₗ[K] (Fin m ⊕ Fin m → K)) (e₂ : W₂ ≃ₗ[K] (Fin m ⊕ Fin m → K))
    (he₁ : ∀ (s : ↥(XbarH M Q Z B)) (w : W₁),
      e₁ ⟨φ s w, hW₁ s w w.2⟩ = (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ e₁ w)
    (he₂ : ∀ (s : ↥(XbarH M Q Z B)) (w : W₂),
      e₂ ⟨φ s w, hW₂ s w w.2⟩ = (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ e₂ w) :
    ∃ (σ : ↥(H0 M Z) →* GL (Fin m ⊕ Fin m) K) (η : ↥(H0 M Z) →* Matrix (Fin 2) (Fin 2) K),
      (∀ l, σ l ∈ StatedSp m K) ∧
      (∀ s : ↥(XbarH M Q Z B), σ (s : ↥(H0 M Z)) = ρ s ∧ η (s : ↥(H0 M Z)) = 1) ∧
      ∀ (l : ↥(H0 M Z)) (x : Fin m ⊕ Fin m → K),
        φ l ((e₁.symm x : W₁) : M₀.E) =
          ((e₁.symm (η l 0 0 • ((σ l : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₁) :
            M₀.E) +
          ((e₂.symm (η l 1 0 • ((σ l : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₂) :
            M₀.E) ∧
        φ l ((e₂.symm x : W₂) : M₀.E) =
          ((e₁.symm (η l 0 1 • ((σ l : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₁) :
            M₀.E) +
          ((e₂.symm (η l 1 1 • ((σ l : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₂) :
            M₀.E) := by
  classical
  let N := Fin m ⊕ Fin m → K
  have hex := fun l : ↥(H0 M Z) =>
    hc.exists_tensor_of_mem_H0 h φ hφπ hm hdisj hsup hW₁ hW₂ ρ hρr e₁ e₂ he₁ he₂ l.2
  choose σ₀ a₁₁ a₁₂ a₂₁ a₂₂ hσ₀ hT using hex
  have hT1 : ∀ (l : ↥(H0 M Z)) (x : N), φ l ((e₁.symm x : W₁) : M₀.E) =
      ((e₁.symm (a₁₁ l • ((σ₀ l : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₁) :
        M₀.E) +
      ((e₂.symm (a₂₁ l • ((σ₀ l : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₂) :
        M₀.E) := fun l x => (hT l x).1
  have hT2 : ∀ (l : ↥(H0 M Z)) (x : N), φ l ((e₂.symm x : W₂) : M₀.E) =
      ((e₁.symm (a₁₂ l • ((σ₀ l : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₁) :
        M₀.E) +
      ((e₂.symm (a₂₂ l • ((σ₀ l : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₂) :
        M₀.E) := fun l x => (hT l x).2
  let i0 : Fin m := ⟨0, hm⟩
  let x₀ : N := Pi.single (Sum.inl i0) 1
  have hx₀ : x₀ ≠ 0 := by
    intro hx
    have h' : (Pi.single (Sum.inl i0) 1 : Fin m ⊕ Fin m → K) = 0 := hx
    have := congrFun h' (Sum.inl i0)
    simp at this
  have hne : ∀ l : ↥(H0 M Z), a₁₁ l ≠ 0 ∨ a₁₂ l ≠ 0 ∨ a₂₁ l ≠ 0 ∨ a₂₂ l ≠ 0 := by
    intro l
    by_contra hcon
    push Not at hcon
    obtain ⟨c11, c12, c21, c22⟩ := hcon
    have h1 := hT1 l x₀
    rw [c11, c21] at h1
    simp only [zero_smul, map_zero, Submodule.coe_zero, add_zero] at h1
    have h2 : ((e₁.symm x₀ : W₁) : M₀.E) = 0 :=
      (φ l).injective (h1.trans (map_zero (φ l)).symm)
    exact hx₀ ((LinearEquiv.map_eq_zero_iff e₁.symm).mp (Subtype.ext h2))
  have hprod : ∀ (l l' : ↥(H0 M Z)) (x : N),
      φ (l * l') ((e₁.symm x : W₁) : M₀.E) =
        ((e₁.symm ((a₁₁ l * a₁₁ l' + a₁₂ l * a₂₁ l') •
          (((σ₀ l * σ₀ l' : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
            x)) : W₁) : M₀.E) +
        ((e₂.symm ((a₂₁ l * a₁₁ l' + a₂₂ l * a₂₁ l') •
          (((σ₀ l * σ₀ l' : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
            x)) : W₂) : M₀.E) ∧
      φ (l * l') ((e₂.symm x : W₂) : M₀.E) =
        ((e₁.symm ((a₁₁ l * a₁₂ l' + a₁₂ l * a₂₂ l') •
          (((σ₀ l * σ₀ l' : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
            x)) : W₁) : M₀.E) +
        ((e₂.symm ((a₂₁ l * a₁₂ l' + a₂₂ l * a₂₂ l') •
          (((σ₀ l * σ₀ l' : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
            x)) : W₂) : M₀.E) := by
    intro l l' x
    have hv : ∀ (c : K) (v : N), (σ₀ l : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
        (c • ((σ₀ l' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v)) =
        c • (((σ₀ l * σ₀ l' : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
          v) := by
      intro c v
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Units.val_mul]
    constructor
    · rw [map_mul, LinearEquiv.mul_apply, hT1 l' x, map_add, hT1 l, hT2 l, hv, hv]
      simp only [map_smul, smul_smul, add_smul, map_add, Submodule.coe_add, Submodule.coe_smul]
      abel
    · rw [map_mul, LinearEquiv.mul_apply, hT2 l' x, map_add, hT1 l, hT2 l, hv, hv]
      simp only [map_smul, smul_smul, add_smul, map_add, Submodule.coe_add, Submodule.coe_smul]
      abel
  have hone : σ₀ 1 = 1 ∧ a₁₁ 1 = 1 ∧ a₁₂ 1 = 0 ∧ a₂₁ 1 = 0 ∧ a₂₂ 1 = 1 := by
    refine eq_of_tensor_eq hm hdisj e₁ e₂ (hσ₀ 1) (StatedSp m K).one_mem
      (h₁ := fun x => ?_) (h₂ := fun x => ?_) (hne 1)
    · rw [← hT1 1 x, map_one]
      simp
    · rw [← hT2 1 x, map_one]
      simp
  have hmul : ∀ l l' : ↥(H0 M Z), σ₀ (l * l') = σ₀ l * σ₀ l' ∧
      a₁₁ (l * l') = a₁₁ l * a₁₁ l' + a₁₂ l * a₂₁ l' ∧
      a₁₂ (l * l') = a₁₁ l * a₁₂ l' + a₁₂ l * a₂₂ l' ∧
      a₂₁ (l * l') = a₂₁ l * a₁₁ l' + a₂₂ l * a₂₁ l' ∧
      a₂₂ (l * l') = a₂₁ l * a₁₂ l' + a₂₂ l * a₂₂ l' := by
    intro l l'
    refine eq_of_tensor_eq hm hdisj e₁ e₂ (hσ₀ (l * l'))
      ((StatedSp m K).mul_mem (hσ₀ l) (hσ₀ l')) (h₁ := fun x => ?_) (h₂ := fun x => ?_)
      (hne (l * l'))
    · rw [← hT1 (l * l') x]
      exact (hprod l l' x).1
    · rw [← hT2 (l * l') x]
      exact (hprod l l' x).2
  have hXbar : ∀ s : ↥(XbarH M Q Z B), σ₀ (s : ↥(H0 M Z)) = ρ s ∧
      a₁₁ (s : ↥(H0 M Z)) = 1 ∧ a₁₂ (s : ↥(H0 M Z)) = 0 ∧ a₂₁ (s : ↥(H0 M Z)) = 0 ∧
      a₂₂ (s : ↥(H0 M Z)) = 1 := by
    intro s
    have hρs : ρ s ∈ StatedSp m K := hρr ▸ ⟨s, rfl⟩
    have hΦ₁ : ∀ x : N, φ (s : ↥(H0 M Z)) ((e₁.symm x : W₁) : M₀.E) = ((e₁.symm
        ((ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) : W₁) : M₀.E) := by
      intro x
      have h1 := he₁ s (e₁.symm x)
      rw [LinearEquiv.apply_symm_apply] at h1
      have h2 : (⟨φ s ((e₁.symm x : W₁) : M₀.E), hW₁ s _ (e₁.symm x).2⟩ : W₁) =
          e₁.symm ((ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) := by
        apply e₁.injective
        rw [h1, LinearEquiv.apply_symm_apply]
      exact congrArg Subtype.val h2
    have hΦ₂ : ∀ x : N, φ (s : ↥(H0 M Z)) ((e₂.symm x : W₂) : M₀.E) = ((e₂.symm
        ((ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) : W₂) : M₀.E) := by
      intro x
      have h1 := he₂ s (e₂.symm x)
      rw [LinearEquiv.apply_symm_apply] at h1
      have h2 : (⟨φ s ((e₂.symm x : W₂) : M₀.E), hW₂ s _ (e₂.symm x).2⟩ : W₂) =
          e₂.symm ((ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) := by
        apply e₂.injective
        rw [h1, LinearEquiv.apply_symm_apply]
      exact congrArg Subtype.val h2
    have := eq_of_tensor_eq hm hdisj e₁ e₂ (hσ₀ (s : ↥(H0 M Z))) hρs
      (h₁₁' := 1) (h₁₂' := 0) (h₂₁' := 0) (h₂₂' := 1)
      (h₁ := fun x => by
        rw [← hT1 _ x, hΦ₁ x]
        simp)
      (h₂ := fun x => by
        rw [← hT2 _ x, hΦ₂ x]
        simp) (hne _)
    exact this
  let σ : ↥(H0 M Z) →* GL (Fin m ⊕ Fin m) K :=
    { toFun := σ₀
      map_one' := hone.1
      map_mul' := fun l l' => (hmul l l').1 }
  let η : ↥(H0 M Z) →* Matrix (Fin 2) (Fin 2) K :=
    { toFun := fun l => !![a₁₁ l, a₁₂ l; a₂₁ l, a₂₂ l]
      map_one' := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hone.2.1, hone.2.2.1, hone.2.2.2.1, hone.2.2.2.2]
      map_mul' := fun l l' => by
        ext i j
        obtain ⟨-, m11, m12, m21, m22⟩ := hmul l l'
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, m11, m12, m21, m22] }
  refine ⟨σ, η, hσ₀, fun s => ?_, fun l x => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hXbar s
    refine ⟨h1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [η, h2, h3, h4, h5]
  · exact ⟨hT1 l x, hT2 l x⟩

end CFSG.RankThree.GF2n.Stroth80
