module

public import CFSG.RankThree.GF2n.Stroth80.Sec118RT1Form
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalGroups.Symplectic.TensorUnique
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.GF2n.Stroth80.Sec11A2Line
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix
open CFSG.ClassicalGroups.Symplectic

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}


omit [Finite G] [(Q.subgroupOf M).Normal] [Finite K] [CharP K 2] in
theorem action_eq_id_of_mem_Q (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (l : ↥(H0 M Z)) (hlQ : (l : G) ∈ Q) (e : M₀.E) : φ l e = e := by
  obtain ⟨x, hx, rfl⟩ := M₀.π_surj e
  rw [← hφπ l x hx]
  exact Tim79.QuadModel.pi_conj_self (M₀ := M₀) hlQ hx

omit [Finite G] [(Q.subgroupOf M).Normal] in
theorem tensorHom_eq_one_of_mem_Q (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    {m : ℕ} (hm : 1 ≤ m) {W₁ W₂ : Submodule K M₀.E} (hdisj : W₁ ⊓ W₂ = ⊥)
    (e₁ : W₁ ≃ₗ[K] (Fin m ⊕ Fin m → K)) (e₂ : W₂ ≃ₗ[K] (Fin m ⊕ Fin m → K))
    (σ : ↥(H0 M Z) →* GL (Fin m ⊕ Fin m) K) (η : ↥(H0 M Z) →* Matrix (Fin 2) (Fin 2) K)
    (hσ : ∀ l, σ l ∈ StatedSp m K)
    (hT : ∀ (l : ↥(H0 M Z)) (x : Fin m ⊕ Fin m → K),
      φ l ((e₁.symm x : W₁) : M₀.E) =
        ((e₁.symm (η l 0 0 • ((σ l : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₁) :
          M₀.E) +
        ((e₂.symm (η l 1 0 • ((σ l : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₂) :
          M₀.E) ∧
      φ l ((e₂.symm x : W₂) : M₀.E) =
        ((e₁.symm (η l 0 1 • ((σ l : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₁) :
          M₀.E) +
        ((e₂.symm (η l 1 1 • ((σ l : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₂) :
          M₀.E))
    (l : ↥(H0 M Z)) (hφl : ∀ e, φ l e = e) : σ l = 1 ∧ η l = 1 := by
  classical
  obtain ⟨hs, e00, e01, e10, e11⟩ := eq_of_tensor_eq hm hdisj e₁ e₂ (s := 1) (s' := σ l)
    (h₁₁ := 1) (h₁₂ := 0) (h₂₁ := 0) (h₂₂ := 1) (h₁₁' := η l 0 0) (h₁₂' := η l 0 1)
    (h₂₁' := η l 1 0) (h₂₂' := η l 1 1) (Subgroup.one_mem _) (hσ l)
    (fun x => by rw [← (hT l x).1, hφl]; simp) (fun x => by rw [← (hT l x).2, hφl]; simp)
    (Or.inl one_ne_zero)
  refine ⟨hs.symm, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [← e00, ← e01, ← e10, ← e11]

omit [CharP K 2] in
theorem Ctx.mem_Q_of_tensor_eq_one (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {m : ℕ} {W₁ W₂ : Submodule K M₀.E} (hsup : W₁ ⊔ W₂ = cmComm M Q Z B K γ M₀ φ)
    (e₁ : W₁ ≃ₗ[K] (Fin m ⊕ Fin m → K)) (e₂ : W₂ ≃ₗ[K] (Fin m ⊕ Fin m → K))
    (σ : ↥(H0 M Z) →* GL (Fin m ⊕ Fin m) K) (η : ↥(H0 M Z) →* Matrix (Fin 2) (Fin 2) K)
    (hT : ∀ (l : ↥(H0 M Z)) (x : Fin m ⊕ Fin m → K),
      φ l ((e₁.symm x : W₁) : M₀.E) =
        ((e₁.symm (η l 0 0 • ((σ l : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₁) :
          M₀.E) +
        ((e₂.symm (η l 1 0 • ((σ l : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₂) :
          M₀.E) ∧
      φ l ((e₂.symm x : W₂) : M₀.E) =
        ((e₁.symm (η l 0 1 • ((σ l : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₁) :
          M₀.E) +
        ((e₂.symm (η l 1 1 • ((σ l : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₂) :
          M₀.E))
    (l : ↥(H0 M Z))
    (hperp : ∀ z ∈ M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ), φ l z = z)
    (hσl : σ l = 1) (hηl : η l = 1) : (l : G) ∈ Q := by
  classical
  have hcompl := hc.isCompl_cmComm_orthogonal h φ hφπ
  have hall : ∀ e, φ l e = e := by
    intro e
    have he : e ∈ cmComm M Q Z B K γ M₀ φ ⊔ M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ) := by
      rw [hcompl.sup_eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp he
    rw [map_add, hperp z hz]
    congr 1
    rw [← hsup] at hy
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp hy
    have h1 : φ l w₁ = w₁ := by
      have := (hT l (e₁ ⟨w₁, hw₁⟩)).1
      rw [LinearEquiv.symm_apply_apply] at this
      rw [show φ l w₁ = φ l ((⟨w₁, hw₁⟩ : W₁) : M₀.E) from rfl, this, hσl, hηl]
      simp
    have h2 : φ l w₂ = w₂ := by
      have := (hT l (e₂ ⟨w₂, hw₂⟩)).2
      rw [LinearEquiv.symm_apply_apply] at this
      rw [show φ l w₂ = φ l ((⟨w₂, hw₂⟩ : W₂) : M₀.E) from rfl, this, hσl, hηl]
      simp
    rw [map_add, h1, h2]
  refine mem_Q_of_pi_conj_eq (M₀ := M₀) hc.hyp l.2.1 fun x hx => ?_
  rw [hφπ l x hx]
  exact hall _

omit [CharP K 2] in
theorem Ctx.mem_XbarPre_of_eta_eq_one (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {m : ℕ} {W₁ W₂ : Submodule K M₀.E}
    (hsup : W₁ ⊔ W₂ = cmComm M Q Z B K γ M₀ φ)
    (e₁ : W₁ ≃ₗ[K] (Fin m ⊕ Fin m → K)) (e₂ : W₂ ≃ₗ[K] (Fin m ⊕ Fin m → K))
    (σ : ↥(H0 M Z) →* GL (Fin m ⊕ Fin m) K) (η : ↥(H0 M Z) →* Matrix (Fin 2) (Fin 2) K)
    (hT : ∀ (l : ↥(H0 M Z)) (x : Fin m ⊕ Fin m → K),
      φ l ((e₁.symm x : W₁) : M₀.E) =
        ((e₁.symm (η l 0 0 • ((σ l : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₁) :
          M₀.E) +
        ((e₂.symm (η l 1 0 • ((σ l : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₂) :
          M₀.E) ∧
      φ l ((e₂.symm x : W₂) : M₀.E) =
        ((e₁.symm (η l 0 1 • ((σ l : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₁) :
          M₀.E) +
        ((e₂.symm (η l 1 1 • ((σ l : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₂) :
          M₀.E))
    (hσ : ∀ l, σ l ∈ StatedSp m K)
    (ρ : ↥(XbarH M Q Z B) →* GL (Fin m ⊕ Fin m) K) (hρr : ρ.range = StatedSp m K)
    (hση : ∀ s : ↥(XbarH M Q Z B), σ (s : ↥(H0 M Z)) = ρ s ∧ η (s : ↥(H0 M Z)) = 1)
    (l : ↥(H0 M Z)) (hlLB : (l : G) ∈ LB M Q B) (hηl : η l = 1) :
    (l : G) ∈ XbarPre M Q Z B := by
  classical
  obtain ⟨x, hx⟩ : σ l ∈ ρ.range := by rw [hρr]; exact hσ l
  set x' : ↥(H0 M Z) := (x : ↥(H0 M Z)) with hx'
  have hσx : σ x' = ρ x := (hση x).1
  have hηx : η x' = 1 := (hση x).2
  have hσl' : σ (l * x'⁻¹) = 1 := by
    rw [map_mul, map_inv, hσx, hx, mul_inv_cancel]
  have hηinv : η x'⁻¹ = 1 := by
    calc η x'⁻¹ = η x'⁻¹ * η x' := by rw [hηx, mul_one]
      _ = η (x'⁻¹ * x') := (map_mul η _ _).symm
      _ = 1 := by rw [inv_mul_cancel, map_one]
  have hηl' : η (l * x'⁻¹) = 1 := by rw [map_mul, hηinv, hηl, mul_one]
  have hperp : ∀ z ∈ M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ), φ (l * x'⁻¹) z = z := by
    intro z hz
    have h1 : φ l z = z := hc.action_fixes_orthogonal h φ hφπ ha2 hlLB l.2 hz
    have h2 : φ x' z = z := hc.action_fixes_orthogonal_of_mem_XbarH h φ hφπ x hz
    have h3 : φ x'⁻¹ z = z := by
      calc φ x'⁻¹ z = φ x'⁻¹ (φ x' z) := by rw [h2]
        _ = z := by rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
    rw [map_mul, LinearEquiv.mul_apply, h3, h1]
  have hq : ((l * x'⁻¹ : ↥(H0 M Z)) : G) ∈ Q :=
    hc.mem_Q_of_tensor_eq_one h φ hφπ hsup e₁ e₂ σ η hT (l * x'⁻¹) hperp hσl' hηl'
  have hxX : ((x' : ↥(H0 M Z)) : G) ∈ XbarPre M Q Z B := (mem_XbarH_iff hc _).mp x.2
  have hlx : (l : G) = ((l * x'⁻¹ : ↥(H0 M Z)) : G) * (x' : G) := by simp
  rw [hlx]
  exact (XbarPre M Q Z B).mul_mem (Q_le_XbarPre hc hq) hxX

omit [CharP K 2] in
theorem Ctx.exists_decomp_of_dictB (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {m : ℕ} {W₁ W₂ : Submodule K M₀.E}
    (hsup : W₁ ⊔ W₂ = cmComm M Q Z B K γ M₀ φ)
    (hW₁ : ∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W₁, φ s w ∈ W₁)
    (hW₂ : ∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W₂, φ s w ∈ W₂)
    (ρ : ↥(XbarH M Q Z B) →* GL (Fin m ⊕ Fin m) K)
    (e₁ : W₁ ≃ₗ[K] (Fin m ⊕ Fin m → K)) (e₂ : W₂ ≃ₗ[K] (Fin m ⊕ Fin m → K))
    (he₁ : ∀ (s : ↥(XbarH M Q Z B)) (w : W₁),
      e₁ ⟨φ s w, hW₁ s w w.2⟩ = (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ e₁ w)
    (he₂ : ∀ (s : ↥(XbarH M Q Z B)) (w : W₂),
      e₂ ⟨φ s w, hW₂ s w w.2⟩ = (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ e₂ w)
    {a : G} (haL : a ∈ LB M Q B) (hA : IsA2 Q Z a) (haX : a ∈ XbarPre M Q Z B)
    {u : Fin m ⊕ Fin m → K}
    (hrange : LinearMap.range (Matrix.mulVecLin
      (((ρ ⟨⟨a, XbarPre_le_H0 hc haX⟩, (mem_XbarH_iff hc _).mpr haX⟩ : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1)) = Submodule.span K {u})
    {b₀ : M₀.E} (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b₀) :
    ∃ c₁ c₂ : K, b₀ = c₁ • ((e₁.symm u : W₁) : M₀.E) + c₂ • ((e₂.symm u : W₂) : M₀.E) := by
  classical
  have haH : a ∈ H0 M Z := XbarPre_le_H0 hc haX
  set sa : ↥(XbarH M Q Z B) := ⟨⟨a, haH⟩, (mem_XbarH_iff hc _).mpr haX⟩ with hsa
  obtain ⟨y, hyB, hyQ, hyb⟩ := (hB b₀).mpr ⟨1, (one_smul K b₀).symm⟩
  have hyD : y ∈ (⁅Q, Subgroup.zpowers a⁆ ⊔ Z : Subgroup G) :=
    hc.B_le_commutator_of_a2 haL hA hyB
  have hrange0 : b₀ ∈ LinearMap.range
      (((φ ⟨a, haH⟩ : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1) :=
    (hc.mem_img_zpowers_sup_iff φ hφπ haH hA.2.2.1 b₀).mp ⟨y, hyD, hyQ, hyb⟩
  rw [hc.range_sub_one_eq_map_cmComm h φ hφπ ha2 haL haH, ← hsup, Submodule.map_sup,
    map_sub_one_eq_span_of_range e₁ ((φ ⟨a, haH⟩ : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E)
      (hW₁ sa) _ (he₁ sa) hrange,
    map_sub_one_eq_span_of_range e₂ ((φ ⟨a, haH⟩ : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E)
      (hW₂ sa) _ (he₂ sa) hrange] at hrange0
  obtain ⟨x₁, hx₁, x₂, hx₂, hsum⟩ := Submodule.mem_sup.mp hrange0
  obtain ⟨c₁, rfl⟩ := Submodule.mem_span_singleton.mp hx₁
  obtain ⟨c₂, rfl⟩ := Submodule.mem_span_singleton.mp hx₂
  exact ⟨c₁, c₂, hsum.symm⟩

end CFSG.RankThree.GF2n.Stroth80
