module

public import CFSG.Quasithin.Recognition.G112A2ModNineCore
public import CFSG.Quasithin.Recognition.G112A2ModStmts
public import CFSG.Quasithin.Background.G119Group2

public section

namespace CFSG.Quasithin.G112A2

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open CFSG.ASVolI.ChG
open scoped TensorProduct

theorem nine_finrank_permCore_five_le : Module.finrank (ZMod 2) ↥(permCore 5) ≤ 4 := by
  have h := g119_finrank_permCore (n := 5) (by norm_num)
  omega

theorem nine_permAct_one {n : ℕ} (x : Fin n → ZMod 2) : permAct (1 : Equiv.Perm (Fin n)) x = x := by
  funext i
  simp [permAct]

@[expose] noncomputable def nineMatLin (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) :
    (Fin 2 → GaloisField 2 2) →ₗ[ZMod 2] (Fin 2 → GaloisField 2 2) :=
  (Matrix.mulVecLin M).restrictScalars (ZMod 2)

theorem nineMatLin_apply (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) (b : Fin 2 → GaloisField 2 2) :
    nineMatLin M b = M.mulVec b := rfl

@[expose] noncomputable def nineFrobLin :
    (Fin 2 → GaloisField 2 2) →ₗ[ZMod 2] (Fin 2 → GaloisField 2 2) where
  toFun b := fun c => b c ^ 2
  map_add' b b' := by
    funext c
    simp only [Pi.add_apply]
    exact CharTwo.add_sq (b c) (b' c)
  map_smul' c b := by
    funext i
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) c with rfl | rfl <;> simp

@[expose] noncomputable def nineSemi (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) (tw : Bool) :
    (Fin 2 → GaloisField 2 2) →ₗ[ZMod 2] (Fin 2 → GaloisField 2 2) :=
  nineMatLin M ∘ₗ (if tw then nineFrobLin else LinearMap.id)

theorem nineSemi_apply (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) (tw : Bool)
    (b : Fin 2 → GaloisField 2 2) :
    nineSemi M tw b = M.mulVec (fun c => if tw then b c ^ 2 else b c) := by
  cases tw <;> simp [nineSemi, nineMatLin_apply, nineFrobLin]

theorem nine_clause_perm5 {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (hV : Module.finrank (ZMod 2) V = 8)
    (hT : IsTensorD3Perm5 Γ) {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ Γ) (ht2 : t * t = 1) {v₁ : V}
    (hv₁ : v₁ ≠ 0)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 2) :
    ∃ γ ∈ Γ, (∀ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id),
      γ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id)) ∧ γ v₁ ≠ v₁ := by
  obtain ⟨φ, ψ, hψ⟩ := hT
  have hsurj : ∀ σ' : Equiv.Perm (Fin 3), ∃ γ ∈ Γ, ∀ (a : permCore 3) (b : permCore 5),
      ψ (γ (ψ.symm (a ⊗ₜ[ZMod 2] b))) = nineAct 3 σ' a ⊗ₜ[ZMod 2] b := by
    intro σ'
    obtain ⟨g, hg⟩ : ∃ g : ↥Γ, φ g = (σ', 1) := ⟨φ.symm (σ', 1), φ.apply_symm_apply _⟩
    refine ⟨(g : V ≃ₗ[ZMod 2] V), g.2, fun a b => ?_⟩
    have h1 : ((nineAct 3 σ' a : permCore 3) : Fin 3 → ZMod 2) = permAct (φ g).1 a := by
      rw [hg]
      exact coe_nineAct 3 σ' a
    have h2 : ((b : permCore 5) : Fin 5 → ZMod 2) = permAct (φ g).2 b := by
      rw [hg]
      exact (nine_permAct_one _).symm
    exact hψ g a (nineAct 3 σ' a) b b h1 h2
  have hT' : ∃ (σ : Equiv.Perm (Fin 3)) (τ : permCore 5 →ₗ[ZMod 2] permCore 5),
      ∀ (a : permCore 3) (b : permCore 5),
        ψ (t (ψ.symm (a ⊗ₜ[ZMod 2] b))) = nineAct 3 σ a ⊗ₜ[ZMod 2] τ b := by
    refine ⟨(φ ⟨t, ht⟩).1, nineAct 5 (φ ⟨t, ht⟩).2, fun a b => ?_⟩
    have h1 : ((nineAct 3 (φ ⟨t, ht⟩).1 a : permCore 3) : Fin 3 → ZMod 2) =
        permAct (φ ⟨t, ht⟩).1 a := coe_nineAct 3 _ a
    have h2 : ((nineAct 5 (φ ⟨t, ht⟩).2 b : permCore 5) : Fin 5 → ZMod 2) =
        permAct (φ ⟨t, ht⟩).2 b := coe_nineAct 5 _ b
    exact hψ ⟨t, ht⟩ a _ b _ h1 h2
  exact nine_clause_of_model Γ ψ hV nine_finrank_permCore_five_le hsurj ht2 hT' hv₁ hr

theorem nine_clause_core5 {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (hV : Module.finrank (ZMod 2) V = 8)
    (hT : IsTensorD3Core5 Γ) {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ Γ) (ht2 : t * t = 1) {v₁ : V}
    (hv₁ : v₁ ≠ 0)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 2) :
    ∃ γ ∈ Γ, (∀ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id),
      γ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id)) ∧ γ v₁ ≠ v₁ := by
  obtain ⟨φ, ψ, hψ⟩ := hT
  have hsurj : ∀ σ' : Equiv.Perm (Fin 3), ∃ γ ∈ Γ, ∀ (a : permCore 3) (b : permCore 5),
      ψ (γ (ψ.symm (a ⊗ₜ[ZMod 2] b))) = nineAct 3 σ' a ⊗ₜ[ZMod 2] b := by
    intro σ'
    obtain ⟨g, hg⟩ : ∃ g : ↥Γ, φ g = (σ', 1) := ⟨φ.symm (σ', 1), φ.apply_symm_apply _⟩
    refine ⟨(g : V ≃ₗ[ZMod 2] V), g.2, fun a b => ?_⟩
    have h1 : ((nineAct 3 σ' a : permCore 3) : Fin 3 → ZMod 2) = permAct (φ g).1 a := by
      rw [hg]
      exact coe_nineAct 3 σ' a
    have h2 : ((b : permCore 5) : Fin 5 → ZMod 2) = permAct ((φ g).2 : Equiv.Perm (Fin 5)) b := by
      rw [hg]
      exact (nine_permAct_one _).symm
    exact hψ g a (nineAct 3 σ' a) b b h1 h2
  have hT' : ∃ (σ : Equiv.Perm (Fin 3)) (τ : permCore 5 →ₗ[ZMod 2] permCore 5),
      ∀ (a : permCore 3) (b : permCore 5),
        ψ (t (ψ.symm (a ⊗ₜ[ZMod 2] b))) = nineAct 3 σ a ⊗ₜ[ZMod 2] τ b := by
    refine ⟨(φ ⟨t, ht⟩).1, nineAct 5 ((φ ⟨t, ht⟩).2 : Equiv.Perm (Fin 5)), fun a b => ?_⟩
    have h1 : ((nineAct 3 (φ ⟨t, ht⟩).1 a : permCore 3) : Fin 3 → ZMod 2) =
        permAct (φ ⟨t, ht⟩).1 a := coe_nineAct 3 _ a
    have h2 : ((nineAct 5 ((φ ⟨t, ht⟩).2 : Equiv.Perm (Fin 5)) b : permCore 5) :
        Fin 5 → ZMod 2) = permAct ((φ ⟨t, ht⟩).2 : Equiv.Perm (Fin 5)) b := coe_nineAct 5 _ b
    exact hψ ⟨t, ht⟩ a _ b _ h1 h2
  exact nine_clause_of_model Γ ψ hV nine_finrank_permCore_five_le hsurj ht2 hT' hv₁ hr

theorem nine_clause_nat24 {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (hV : Module.finrank (ZMod 2) V = 8)
    (hT : IsTensorD3Nat24 Γ) {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ Γ) (ht2 : t * t = 1) {v₁ : V}
    (hv₁ : v₁ ≠ 0)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 2) :
    ∃ γ ∈ Γ, (∀ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id),
      γ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id)) ∧ γ v₁ ≠ v₁ := by
  obtain ⟨φ, ψ, hψ⟩ := hT
  have hsurj : ∀ σ' : Equiv.Perm (Fin 3), ∃ γ ∈ Γ, ∀ (a : permCore 3) (b : Fin 2 → GaloisField 2 2),
      ψ (γ (ψ.symm (a ⊗ₜ[ZMod 2] b))) = nineAct 3 σ' a ⊗ₜ[ZMod 2] b := by
    intro σ'
    obtain ⟨g, hg⟩ : ∃ g : ↥Γ, φ g = (σ', 1) := ⟨φ.symm (σ', 1), φ.apply_symm_apply _⟩
    refine ⟨(g : V ≃ₗ[ZMod 2] V), g.2, fun a b => ?_⟩
    have h1 : ((nineAct 3 σ' a : permCore 3) : Fin 3 → ZMod 2) = permAct (φ g).1 a := by
      rw [hg]
      exact coe_nineAct 3 σ' a
    have h2 : (((φ g).2 : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 2)).mulVec b = b := by
      rw [hg]
      simp
    exact (hψ g a (nineAct 3 σ' a) b _ h1 h2.symm)
  have hT' : ∃ (σ : Equiv.Perm (Fin 3)) (τ : (Fin 2 → GaloisField 2 2) →ₗ[ZMod 2] (Fin 2 → GaloisField 2 2)),
      ∀ (a : permCore 3) (b : Fin 2 → GaloisField 2 2),
        ψ (t (ψ.symm (a ⊗ₜ[ZMod 2] b))) = nineAct 3 σ a ⊗ₜ[ZMod 2] τ b := by
    refine ⟨(φ ⟨t, ht⟩).1, nineMatLin (((φ ⟨t, ht⟩).2 : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 2)), fun a b => ?_⟩
    have h1 : ((nineAct 3 (φ ⟨t, ht⟩).1 a : permCore 3) : Fin 3 → ZMod 2) =
        permAct (φ ⟨t, ht⟩).1 a := coe_nineAct 3 _ a
    exact hψ ⟨t, ht⟩ a _ b _ h1 rfl
  have hQ : Module.finrank (ZMod 2) (Fin 2 → GaloisField 2 2) ≤ 4 := by
    rw [Module.finrank_pi_fintype]
    simp [GaloisField.finrank 2 (show (2 : ℕ) ≠ 0 by norm_num)]
  exact nine_clause_of_model Γ ψ hV hQ hsurj ht2 hT' hv₁ hr

theorem nine_clause_semi {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (hV : Module.finrank (ZMod 2) V = 8)
    (hT : IsTensorD3Semilin24 Γ) {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ Γ) (ht2 : t * t = 1) {v₁ : V}
    (hv₁ : v₁ ≠ 0)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 2) :
    ∃ γ ∈ Γ, (∀ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id),
      γ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id)) ∧ γ v₁ ≠ v₁ := by
  obtain ⟨ψ, hS1, hS2⟩ := hT
  have hsurj : ∀ σ' : Equiv.Perm (Fin 3), ∃ γ ∈ Γ, ∀ (a : permCore 3) (b : Fin 2 → GaloisField 2 2),
      ψ (γ (ψ.symm (a ⊗ₜ[ZMod 2] b))) = nineAct 3 σ' a ⊗ₜ[ZMod 2] b := by
    intro σ'
    obtain ⟨g, hg⟩ := hS2 σ' 1 false
    refine ⟨(g : V ≃ₗ[ZMod 2] V), g.2, fun a b => ?_⟩
    have h1 : ((nineAct 3 σ' a : permCore 3) : Fin 3 → ZMod 2) = permAct σ' a := coe_nineAct 3 σ' a
    have h2 := hg a (nineAct 3 σ' a) b h1
    simpa using h2
  obtain ⟨σ, M, tw, hform⟩ := hS1 ⟨t, ht⟩
  have hT' : ∃ (σ : Equiv.Perm (Fin 3)) (τ : (Fin 2 → GaloisField 2 2) →ₗ[ZMod 2] (Fin 2 → GaloisField 2 2)),
      ∀ (a : permCore 3) (b : Fin 2 → GaloisField 2 2),
        ψ (t (ψ.symm (a ⊗ₜ[ZMod 2] b))) = nineAct 3 σ a ⊗ₜ[ZMod 2] τ b := by
    refine ⟨σ, nineSemi (((M : ↥(StatedSL 2 (GaloisField 2 2))) : Matrix.GeneralLinearGroup
        (Fin 2) (GaloisField 2 2)) : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) tw, fun a b => ?_⟩
    have h1 : ((nineAct 3 σ a : permCore 3) : Fin 3 → ZMod 2) = permAct σ a := coe_nineAct 3 σ a
    have h2 := hform a (nineAct 3 σ a) b h1
    rw [nineSemi_apply]
    exact h2
  have hQ : Module.finrank (ZMod 2) (Fin 2 → GaloisField 2 2) ≤ 4 := by
    rw [Module.finrank_pi_fintype]
    simp [GaloisField.finrank 2 (show (2 : ℕ) ≠ 0 by norm_num)]
  exact nine_clause_of_model Γ ψ hV hQ hsurj ht2 hT' hv₁ hr

theorem g112A2OpenConcl9_holds : G112A2OpenConcl9 := by
  intro V _ _ _ B Γ v₁ W X X₀ hH hN
  intro t ht hr _ _
  have ht2 : t * t = 1 := hH.X_sq t ht
  have htΓ : t ∈ Γ := hH.X_le ht
  have hv₁ : v₁ ≠ 0 := hH.point
  obtain ⟨hV8, hcases⟩ := hN
  rcases hcases with ⟨-, hmod⟩ | hCore | hNat
  · rcases hmod with hP | hS
    · exact nine_clause_perm5 Γ hV8 hP htΓ ht2 hv₁ hr
    · exact nine_clause_semi Γ hV8 hS htΓ ht2 hv₁ hr
  · exact nine_clause_core5 Γ hV8 hCore htΓ ht2 hv₁ hr
  · exact nine_clause_nat24 Γ hV8 hNat htΓ ht2 hv₁ hr

end CFSG.Quasithin.G112A2
