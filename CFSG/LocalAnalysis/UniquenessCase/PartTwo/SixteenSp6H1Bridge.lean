module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.Module
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

private lemma s16sp_invariant_functional_eq_zero {W : Type} [CommGroup W]
    {Γ : Type} [Group Γ] {H : Subgroup (MulAut W)} (hcomm : commV H = ⊤)
    (π : Γ →* ↥H) (hπ : Function.Surjective π) [Module (ZMod 2) (Additive W)]
    (ρM : Representation (ZMod 2) Γ (Additive W))
    (hρM : ∀ (γ : Γ) (w : W),
      ρM γ (Additive.ofMul w) = Additive.ofMul ((π γ : MulAut W) w))
    (ψ : Additive W →ₗ[ZMod 2] ZMod 2)
    (hψ : ∀ γ m, ψ (ρM γ m) = ψ m) : ψ = 0 := by
  ext m
  have key : ∀ w : W, w ∈ commV H → ψ (Additive.ofMul w) = 0 := by
    intro w hw
    refine Subgroup.closure_induction (p := fun w _ => ψ (Additive.ofMul w) = 0)
      ?_ ?_ ?_ ?_ hw
    · intro c hc
      obtain ⟨a, ha, l, rfl⟩ := hc
      obtain ⟨γ, hγ⟩ := hπ ⟨a, ha⟩
      have hγ' : (π γ : MulAut W) = a := congrArg Subtype.val hγ
      have h1 : ψ (Additive.ofMul (a l)) = ψ (Additive.ofMul l) := by
        have h := hψ γ (Additive.ofMul l)
        rw [hρM γ l, hγ'] at h
        exact h
      have e : Additive.ofMul (a l * l⁻¹) = Additive.ofMul (a l) - Additive.ofMul l := by
        rw [ofMul_mul, ofMul_inv, sub_eq_add_neg]
      rw [e, map_sub, h1, sub_self]
    · simp
    · intro x y hx hy ihx ihy
      rw [ofMul_mul, map_add, ihx, ihy, add_zero]
    · intro x hx ih
      rw [ofMul_inv, map_neg, ih, neg_zero]
  have hm : Additive.toMul m ∈ commV H := by rw [hcomm]; trivial
  simpa using key (Additive.toMul m) hm

theorem s16sp_module_data_of_cover {W : Type} [CommGroup W] [Finite W]
    (hexp : ∀ w : W, w ^ 2 = 1) {Γ : Type} [Group Γ] {H : Subgroup (MulAut W)}
    {Z : Subgroup W} (hZ : Z ≤ fixV H) (hcomm : commV H = ⊤) (π : Γ →* ↥H)
    (hπ : Function.Surjective π) {Q : Type} [AddCommGroup Q] [Module (ZMod 2) Q]
    (ρQ : Representation (ZMod 2) Γ Q) (β : W →* Multiplicative Q)
    (hβs : Function.Surjective β) (hβk : ∀ w : W, β w = 1 ↔ w ∈ Z)
    (hβe : ∀ (γ : Γ) (w : W),
      β ((π γ : MulAut W) w) = Multiplicative.ofAdd (ρQ γ (Multiplicative.toAdd (β w)))) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module (ZMod 2) M) (_ : Finite M)
      (θ : W ≃* Multiplicative M) (ρM : Representation (ZMod 2) Γ M) (q : M →ₗ[ZMod 2] Q),
      Function.Surjective q ∧ (∀ γ m, q (ρM γ m) = ρQ γ (q m)) ∧
      (∀ γ m, q m = 0 → ρM γ m = m) ∧
      (∀ ψ : M →ₗ[ZMod 2] ZMod 2, (∀ γ m, ψ (ρM γ m) = ψ m) → ψ = 0) ∧
      (∀ (γ : Γ) (w : W),
        θ ((π γ : MulAut W) w) = Multiplicative.ofAdd (ρM γ (Multiplicative.toAdd (θ w)))) ∧
      (∀ w : W, q (Multiplicative.toAdd (θ w)) = 0 ↔ w ∈ Z) := by
  have h2 : ∀ x : Additive W, (2 : ℕ) • x = 0 := fun x => by
    apply Additive.toMul.injective
    rw [two_nsmul, toMul_add, toMul_zero]
    simpa [pow_two] using hexp (Additive.toMul x)
  letI : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule h2
  let θ : W ≃* Multiplicative (Additive W) :=
    { toFun := fun w => Multiplicative.ofAdd (Additive.ofMul w)
      invFun := fun m => Additive.toMul (Multiplicative.toAdd m)
      left_inv := fun w => rfl
      right_inv := fun m => rfl
      map_mul' := fun a b => rfl }
  let actHom : Γ → (W →* W) := fun γ =>
    { toFun := fun w => (π γ : MulAut W) w
      map_one' := map_one _
      map_mul' := fun a b => map_mul _ a b }
  have actHom_mul : ∀ γ δ w, actHom (γ * δ) w = actHom γ (actHom δ w) := by
    intro γ δ w
    simp [actHom, map_mul]
  have actHom_one : ∀ w, actHom 1 w = w := by
    intro w
    simp [actHom]
  let ρM : Representation (ZMod 2) Γ (Additive W) :=
    { toFun := fun γ => AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive (actHom γ))
      map_one' := by
        ext m
        simp [actHom_one]
      map_mul' := fun γ δ => by
        ext m
        simp [actHom_mul] }
  have hρM : ∀ (γ : Γ) (w : W),
      ρM γ (Additive.ofMul w) = Additive.ofMul ((π γ : MulAut W) w) := fun γ w => rfl
  let qa : Additive W →+ Q :=
    { toFun := fun m => Multiplicative.toAdd (β (Additive.toMul m))
      map_zero' := by simp
      map_add' := fun a b => by simp [map_mul] }
  let q : Additive W →ₗ[ZMod 2] Q := AddMonoidHom.toZModLinearMap 2 qa
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨w, hw⟩ := hβs (Multiplicative.ofAdd y)
    exact ⟨Additive.ofMul w, by simpa [q, qa] using congrArg Multiplicative.toAdd hw⟩
  have hqρ : ∀ γ m, q (ρM γ m) = ρQ γ (q m) := by
    intro γ m
    have h := hβe γ (Additive.toMul m)
    simpa [q, qa, ρM, actHom] using congrArg Multiplicative.toAdd h
  have hZ' : ∀ γ m, q m = 0 → ρM γ m = m := by
    intro γ m hm
    have h1 : β (Additive.toMul m) = 1 := by
      have h0 : Multiplicative.toAdd (β (Additive.toMul m)) = 0 := by simpa [q, qa] using hm
      exact Multiplicative.toAdd.injective (by simpa using h0)
    have h2' := mem_fixV.1 (hZ ((hβk _).mp h1)) (π γ) (π γ).2
    apply Additive.toMul.injective
    simpa [ρM, actHom] using h2'
  have hperf : ∀ ψ : Additive W →ₗ[ZMod 2] ZMod 2,
      (∀ γ m, ψ (ρM γ m) = ψ m) → ψ = 0 :=
    fun ψ hψ => s16sp_invariant_functional_eq_zero hcomm π hπ ρM hρM ψ hψ
  have hθ : ∀ (γ : Γ) (w : W),
      θ ((π γ : MulAut W) w) =
        Multiplicative.ofAdd (ρM γ (Multiplicative.toAdd (θ w))) := fun γ w => rfl
  have hker : ∀ w : W, q (Multiplicative.toAdd (θ w)) = 0 ↔ w ∈ Z := by
    intro w
    have hq0 : q (Multiplicative.toAdd (θ w)) = Multiplicative.toAdd (β w) := rfl
    rw [hq0, toAdd_eq_zero]
    exact hβk w
  exact ⟨Additive W, inferInstance, inferInstance, inferInstance, θ, ρM, q,
    hq, hqρ, hZ', hperf, hθ, hker⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
