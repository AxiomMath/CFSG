module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveChart
public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveForm
import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveRigid

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 Matrix

variable {G : Type} [Group G]

theorem fiveReflectionsIn_top (k : ℕ) (ε π : Bool) :
    fiveReflectionsIn k ε π ⊤ = fiveReflections k ε π := by
  ext g
  simp only [fiveReflectionsIn, fiveReflections, Submodule.mem_top, true_and]

theorem fiveReflectionGroupIn_top (k : ℕ) (ε π : Bool) :
    fiveReflectionGroupIn k ε π ⊤ = fiveReflectionGroup k ε π := by
  rw [fiveReflectionGroupIn, fiveReflectionsIn_top]
  rfl

theorem FiveLocalModel.exists_isometry {D : Set G} {x : G} {k : ℕ} {ε π : Bool} (hk : 3 ≤ k)
    (c c' : FiveLocalModel D x k ε π) :
    ∃ M : GL (Fin (k + 1)) (ZMod 5),
      (∀ u v, fiveForm k ε ((M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ u)
        ((M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ v) = fiveForm k ε u v) ∧
      ∀ y, (c'.toMulEquiv y : GL (Fin (k + 1)) (ZMod 5)) =
        M * (c.toMulEquiv y : GL (Fin (k + 1)) (ZMod 5)) * M⁻¹ := by
  let GLn := GL (Fin (k + 1)) (ZMod 5)
  let θ₀ : fiveReflectionGroup k ε π ≃* fiveReflectionGroup k ε π :=
    c.toMulEquiv.symm.trans c'.toMulEquiv
  have hθ₀ : ∀ g : fiveReflectionGroup k ε π, (g : GLn) ∈ fiveReflections k ε π ↔
      (θ₀ g : GLn) ∈ fiveReflections k ε π := by
    intro g
    have h1 := c.mem_iff (c.toMulEquiv.symm g)
    have h2 := c'.mem_iff (c.toMulEquiv.symm g)
    have hg : c.toMulEquiv (c.toMulEquiv.symm g) = g := MulEquiv.apply_symm_apply _ _
    have hθ : (θ₀ g : GLn) = (c'.toMulEquiv (c.toMulEquiv.symm g) : GLn) := rfl
    rw [hθ]
    simpa only [hg] using h1.symm.trans h2
  let e := fiveReflectionGroupIn_top k ε π
  let θ : fiveReflectionGroupIn k ε π ⊤ ≃* fiveReflectionGroupIn k ε π ⊤ :=
    (MulEquiv.subgroupCongr e).trans (θ₀.trans (MulEquiv.subgroupCongr e).symm)
  have hcoe : ∀ x : fiveReflectionGroupIn k ε π ⊤, (x : GLn) = ((MulEquiv.subgroupCongr e) x : GLn) :=
    fun x => by simp only [MulEquiv.subgroupCongr_apply]
  have hcoe' : ∀ x : fiveReflectionGroup k ε π, (x : GLn) =
      (((MulEquiv.subgroupCongr e).symm x : fiveReflectionGroupIn k ε π ⊤) : GLn) := by
    intro x
    have h := hcoe ((MulEquiv.subgroupCongr e).symm x)
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  have hθcoe : ∀ g : fiveReflectionGroupIn k ε π ⊤, (θ g : GLn) =
      (θ₀ ((MulEquiv.subgroupCongr e) g) : GLn) :=
    fun g => (hcoe' (θ₀ ((MulEquiv.subgroupCongr e) g))).symm
  have hθ : ∀ g : fiveReflectionGroupIn k ε π ⊤, (g : GLn) ∈ fiveReflectionsIn k ε π ⊤ ↔
      (θ g : GLn) ∈ fiveReflectionsIn k ε π ⊤ := by
    intro g
    rw [fiveReflectionsIn_top, hcoe g, hθcoe g]
    exact hθ₀ ((MulEquiv.subgroupCongr e) g)
  have h4 : 4 ≤ Module.finrank (ZMod 5) (⊤ : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)) := by
    rw [finrank_top, Module.finrank_fin_fun]; omega
  obtain ⟨M, hMform, -, hMconj⟩ := exists_isometry_of_markedIso
    (W := ⊤) (W' := ⊤) (isFiveNondeg_top k ε) rfl h4 θ hθ
  refine ⟨M, hMform, ?_⟩
  intro y
  let g : fiveReflectionGroupIn k ε π ⊤ := (MulEquiv.subgroupCongr e).symm (c.toMulEquiv y)
  have hθg : (c'.toMulEquiv y : GLn) = (θ g : GLn) := by
    rw [show (θ g : GLn) = (θ₀ ((MulEquiv.subgroupCongr e) g) : GLn) from hθcoe g,
      show (MulEquiv.subgroupCongr e) g = c.toMulEquiv y from MulEquiv.apply_symm_apply _ _]
    simp only [θ₀, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [hθg, show (c.toMulEquiv y : GLn) = (g : GLn) from (hcoe' _).symm]
  exact hMconj g

theorem hasHyperplane_of_conj {D : Set G} {x : G} {k : ℕ} {ε π : Bool}
    {c c' : FiveLocalModel D x k ε π} {M : GL (Fin (k + 1)) (ZMod 5)}
    (hM : ∀ u, fiveForm k ε ((M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ u)
      ((M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ u) = fiveForm k ε u u)
    (hcc' : ∀ y, (c'.toMulEquiv y : GL (Fin (k + 1)) (ZMod 5)) =
      M * (c.toMulEquiv y : GL (Fin (k + 1)) (ZMod 5)) * M⁻¹)
    {s : G} (hs : HasHyperplane c s) : HasHyperplane c' s := by
  let Mat := Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)
  let GLn := GL (Fin (k + 1)) (ZMod 5)
  obtain ⟨z, hz0, hsign, hcomm⟩ := hs
  have hinj : Function.Injective (fun w : Fin (k + 1) → ZMod 5 => (M : Mat) *ᵥ w) := by
    intro a b hab
    have h := congrArg (fun w => ((M⁻¹ : GLn) : Mat) *ᵥ w) hab
    simpa [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec] using h
  have hmv : ∀ y : Subgroup.closure (commSet D x),
      ((c'.toMulEquiv y : GLn) : Mat) *ᵥ ((M : Mat) *ᵥ z) =
        (M : Mat) *ᵥ (((c.toMulEquiv y : GLn) : Mat) *ᵥ z) := by
    intro y
    have hMA : ((M : Mat) * ((c.toMulEquiv y : GLn) : Mat) * ((M⁻¹ : GLn) : Mat)) *
        (M : Mat) = (M : Mat) * ((c.toMulEquiv y : GLn) : Mat) := by
      have h : (((M * c.toMulEquiv y * M⁻¹) * M : GLn) = M * c.toMulEquiv y) := by group
      simpa only [Matrix.GeneralLinearGroup.coe_mul] using
        congrArg (fun u : GLn => (u : Mat)) h
    simp only [hcc' y, Matrix.GeneralLinearGroup.coe_mul]
    rw [Matrix.mulVec_mulVec, hMA, Matrix.mulVec_mulVec]
  refine ⟨(M : Mat) *ᵥ z, ?_, ?_, ?_⟩
  · intro h0
    exact hz0 (hinj (by simpa using h0))
  · simpa only [hM z] using hsign
  · intro y hy
    rw [hmv y, hinj.eq_iff]
    exact hcomm y hy

theorem FiveHyperplaneData.of_localModel {D : Set G} {x : G} {k : ℕ} {ε π : Bool} (hk : 3 ≤ k)
    {c : FiveLocalModel D x k ε π} (hc : FiveHyperplaneData c) (c' : FiveLocalModel D x k ε π) :
    FiveHyperplaneData c' := by
  obtain ⟨M, hMform, hconj⟩ := c.exists_isometry hk c'
  intro s hs hsx
  exact hasHyperplane_of_conj (fun u => hMform u u) hconj (hc s hs hsx)

theorem FiveHyperplaneData.of_pivot {D : Set G} (hS : Setup G D) {k : ℕ} {ε π : Bool} (hk : 3 ≤ k)
    {x₀ : G} (hx₀ : x₀ ∈ D) {c₀ : FiveLocalModel D x₀ k ε π} (h₀ : FiveHyperplaneData c₀)
    {x : G} (hx : x ∈ D) (c : FiveLocalModel D x k ε π) : FiveHyperplaneData c :=
  (fiveLocalData_of_pivot hS hx₀ ⟨c₀⟩ (fun c' => h₀.of_localModel hk c') x hx).2 c

end CFSG.OddTranspositions.PartThree

end
