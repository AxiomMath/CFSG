module

public import CFSG.LocalAnalysis.StandardType.GGTBJXDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJXClass
public import CFSG.LocalAnalysis.StandardType.GGTBJXKernel
public import CFSG.LocalAnalysis.StandardType.GGTBJXRefl
public import CFSG.LocalAnalysis.StandardType.GGTBJXRoots
public import CFSG.LocalAnalysis.StandardType.GGTBJReflPlain
public import CFSG.LocalAnalysis.StandardType.GGTBJXNoncommAux
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem ggTBJX_core
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K]
    {ζ : Kˣ} {L' : Type} [Group L'] [Finite L'] {ψ : L' →* ModGL τ K}
    {σ : Multiplicative (Fin τ.rank → ZMod p) →* L'} (hstd : GGTBJXStd p τ ζ ψ σ)
    (f₀ : Multiplicative (Fin τ.rank → ZMod p)) {J : Subgroup L'}
    (hJ : IsComponentOf J (Subgroup.centralizer ({σ f₀} : Set L')))
    (hcount : p ^ 2 * Nat.card {f : Multiplicative (Fin τ.rank → ZMod p) //
      ∀ j ∈ J, σ f * j = j * σ f} ≤ p ^ τ.rank) :
    ∃ (m₁ m₂ : L') (s₁ s₂ : MulAut (Multiplicative (Fin τ.rank → ZMod p))),
      m₁ ∈ J ∧ m₂ ∈ J ∧
      (∀ f, ψ m₁ * ψ (σ f) * (ψ m₁)⁻¹ = ψ (σ (s₁ f))) ∧
      (∀ f, ψ m₂ * ψ (σ f) * (ψ m₂)⁻¹ = ψ (σ (s₂ f))) ∧
      s₁ ^ 2 = 1 ∧ s₂ ^ 2 = 1 ∧
      Nat.card {f // s₁ f = f} * p = p ^ τ.rank ∧ Nat.card {f // s₂ f = f} * p = p ^ τ.rank ∧
      s₁ * s₂ ≠ s₂ * s₁ := by
  classical
  have hp : p.Prime := Fact.out
  let χ : Multiplicative (Fin τ.rank → ℤ) →* Kˣ := rootCharHom (ggTBJXa p τ ζ f₀)
  obtain ⟨i, hJi⟩ := ggTBJX_class (p := p) (ζ := ζ) (ψ := ψ) (σ := σ) hp2 hstd f₀ hJ
  let ι := {β : Fin τ.rank → ℤ // β ∈ componentRoots χ i}
  have : Nonempty ι := by
    obtain ⟨a, ha⟩ := Quotient.exists_rep i
    exact ⟨⟨a.1, ⟨a.2, ha⟩⟩⟩
  let f : ι → (Fin τ.rank → ZMod p) → ZMod p := fun a w => ggTBJXFun p τ a.1 w
  let v : ι → (Fin τ.rank → ZMod p) := fun a => ggTBJXVec p τ a.1
  have hfv : ∀ a, f a (v a) = 2 := by
    intro a
    exact ggTBJX_fun_vec_self p (isRoot_of_mem_componentRoots a.2)
  have hadd : ∀ a (x y : Fin τ.rank → ZMod p), f a (x + y) = f a x + f a y := fun a x y =>
    map_add (ggTBJXFun p τ a.1) x y
  have hsmul : ∀ a (c : ZMod p) (x : Fin τ.rank → ZMod p), f a (c • x) = c * f a x := fun a c x =>
    (map_smul (ggTBJXFun p τ a.1) c x).trans (smul_eq_mul c _)
  have hconn : ∀ S : Set ι, S.Nonempty →
      (∀ a b, (f a (v b) ≠ 0 ∨ f b (v a) ≠ 0) → (a ∈ S ↔ b ∈ S)) → S = Set.univ := by
    intro S hSne hSclosed
    let S' : Set (Fin τ.rank → ℤ) := (fun a : ι => (a : Fin τ.rank → ℤ)) '' S
    have hS'sub : S' ⊆ componentRoots χ i := by
      rintro β ⟨a, -, rfl⟩
      exact a.2
    have hS'ne : S'.Nonempty := by
      obtain ⟨a, ha⟩ := hSne
      exact ⟨(a : Fin τ.rank → ℤ), ⟨a, ha, rfl⟩⟩
    have hS'closed : ∀ β ∈ componentRoots χ i, ∀ γ ∈ componentRoots χ i,
        ((corootPair (τ := τ) γ β : ZMod p) ≠ 0 ∨
          (corootPair (τ := τ) β γ : ZMod p) ≠ 0) →
        (β ∈ S' ↔ γ ∈ S') := by
      intro β hβ γ hγ hp
      have key : ∀ (δ : Fin τ.rank → ℤ) (hδ : δ ∈ componentRoots χ i),
          (δ ∈ S' ↔ (⟨δ, hδ⟩ : ι) ∈ S) := by
        intro δ hδ
        constructor
        · rintro ⟨a, ha, hae⟩
          have hEq : a = ⟨δ, hδ⟩ := Subtype.ext hae
          rwa [hEq] at ha
        · intro h
          exact ⟨⟨δ, hδ⟩, h, rfl⟩
      rw [key β hβ, key γ hγ]
      refine hSclosed ⟨β, hβ⟩ ⟨γ, hγ⟩ ?_
      have e1 : f ⟨β, hβ⟩ (v ⟨γ, hγ⟩) = (corootPair (τ := τ) γ β : ZMod p) := by
        simpa only [f, v] using ggTBJX_fun_vec p (isRoot_of_mem_componentRoots hγ)
      have e2 : f ⟨γ, hγ⟩ (v ⟨β, hβ⟩) = (corootPair (τ := τ) β γ : ZMod p) := by
        simpa only [f, v] using ggTBJX_fun_vec p (isRoot_of_mem_componentRoots hβ)
      rw [e1, e2]
      exact hp
    have hSuniv := ggTBJX_connected hτ hp hp2 i S' hS'sub hS'ne hS'closed
    refine Set.eq_univ_of_forall fun a => ?_
    have ha : (a : Fin τ.rank → ℤ) ∈ S' := by
      rw [hSuniv]
      exact a.2
    obtain ⟨b, hb, hba⟩ := ha
    have hEq : b = a := Subtype.ext hba
    rwa [hEq] at hb
  have hcard : p ^ 2 * Nat.card {w : Fin τ.rank → ZMod p // ∀ a, f a w = 0} ≤
      Nat.card (Fin τ.rank → ZMod p) := by
    have hmap : ∀ w : {w : Fin τ.rank → ZMod p // ∀ a, f a w = 0}, ∀ j ∈ J,
        σ (Multiplicative.ofAdd (w : Fin τ.rank → ZMod p)) * j =
          j * σ (Multiplicative.ofAdd (w : Fin τ.rank → ZMod p)) := by
      intro w j hj
      have hw : ∀ β ∈ componentRoots χ i, ggTBJXFun p τ β (w : Fin τ.rank → ZMod p) = 0 :=
        fun β hβ =>
        w.2 ⟨β, hβ⟩
      exact ggTBJX_kernel (p := p) (ζ := ζ) (ψ := ψ) (σ := σ) hstd f₀ hJ i hJi
        (Multiplicative.ofAdd (w : Fin τ.rank → ZMod p)) (by simpa using hw) j hj
    let toW : {w : Fin τ.rank → ZMod p // ∀ a, f a w = 0} →
        {g : Multiplicative (Fin τ.rank → ZMod p) // ∀ j ∈ J, σ g * j = j * σ g} :=
      fun w => ⟨Multiplicative.ofAdd (w : Fin τ.rank → ZMod p), hmap w⟩
    have hinj : Function.Injective toW := by
      intro a b hab
      have h1 : (toW a).val = (toW b).val := Subtype.ext_iff.mp hab
      exact Subtype.ext (Multiplicative.ofAdd.injective h1)
    have hle := Nat.card_le_card_of_injective toW hinj
    have hV : Nat.card (Fin τ.rank → ZMod p) = p ^ τ.rank := by
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [hV]
    exact le_trans (Nat.mul_le_mul_left (p ^ 2) hle) hcount
  obtain ⟨a₁, a₂, w, hw⟩ :=
    @exists_not_commute_reflection_plain p _ hp2 (Fin τ.rank → ZMod p) Pi.addCommGroup
      (Pi.Function.module (Fin τ.rank) (ZMod p) (ZMod p)) inferInstance ι _ f v hadd hsmul hfv
      hconn hcard
  have hrefl_eq : ∀ (a : ι) (y : Fin τ.rank → ZMod p), ggTBJXRefl p τ a.1 y = y - f a y • v a := by
    intro a y
    funext x
    simp [ggTBJXRefl, f, v, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hwR : ggTBJXRefl p τ a₁.1 (ggTBJXRefl p τ a₂.1 w) ≠
      ggTBJXRefl p τ a₂.1 (ggTBJXRefl p τ a₁.1 w) := by
    have e1 : (w - f a₂ w • v a₂) - f a₁ (w - f a₂ w • v a₂) • v a₁ =
        ggTBJXRefl p τ a₁.1 (ggTBJXRefl p τ a₂.1 w) := by
      rw [hrefl_eq a₂ w]
      exact (hrefl_eq a₁ _).symm
    have e2 : (w - f a₁ w • v a₁) - f a₂ (w - f a₁ w • v a₁) • v a₂ =
        ggTBJXRefl p τ a₂.1 (ggTBJXRefl p τ a₁.1 w) := by
      rw [hrefl_eq a₁ w]
      exact (hrefl_eq a₂ _).symm
    intro h
    have h' : (w - f a₂ w • v a₂) - f a₁ (w - f a₂ w • v a₂) • v a₁ =
        (w - f a₁ w • v a₁) - f a₂ (w - f a₁ w • v a₁) • v a₂ := by
      rw [e1, e2]
      exact h
    exact hw h'
  obtain ⟨m₁, hm₁, hact₁⟩ :=
    ggTBJX_refl (p := p) (ζ := ζ) (ψ := ψ) (σ := σ) hstd f₀ i hJi a₁.2
  obtain ⟨m₂, hm₂, hact₂⟩ :=
    ggTBJX_refl (p := p) (ζ := ζ) (ψ := ψ) (σ := σ) hstd f₀ i hJi a₂.2
  have hfv₁ : ggTBJXFun p τ a₁.1 (ggTBJXVec p τ a₁.1) = 2 :=
    ggTBJX_fun_vec_self p (isRoot_of_mem_componentRoots a₁.2)
  have hfv₂ : ggTBJXFun p τ a₂.1 (ggTBJXVec p τ a₂.1) = 2 :=
    ggTBJX_fun_vec_self p (isRoot_of_mem_componentRoots a₂.2)
  have hnc : ggTBJXReflAut p τ a₁.1 * ggTBJXReflAut p τ a₂.1 ≠
      ggTBJXReflAut p τ a₂.1 * ggTBJXReflAut p τ a₁.1 := by
    intro hcom
    have hw' := congrArg
      (fun s : MulAut (Multiplicative (Fin τ.rank → ZMod p)) => s (Multiplicative.ofAdd w)) hcom
    rw [MulAut.mul_apply, MulAut.mul_apply] at hw'
    rw [ggTBJX_reflAut_ofAdd p hfv₂, ggTBJX_reflAut_ofAdd p hfv₁,
      ggTBJX_reflAut_ofAdd p hfv₁, ggTBJX_reflAut_ofAdd p hfv₂] at hw'
    exact hwR (Multiplicative.ofAdd.injective hw')
  exact ⟨m₁, m₂, ggTBJXReflAut p τ a₁.1, ggTBJXReflAut p τ a₂.1, hm₁, hm₂, hact₁, hact₂,
    ggTBJX_reflAut_sq p hfv₁, ggTBJX_reflAut_sq p hfv₂,
    ggTBJX_card_fixed_mul p hp2 hfv₁, ggTBJX_card_fixed_mul p hp2 hfv₂, hnc⟩

end CFSG.StandardType

end