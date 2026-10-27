module

public import CFSG.LocalAnalysis.StandardType.GGTBJF4Defs
public import CFSG.LocalAnalysis.StandardType.GGTBJF4Class
public import CFSG.LocalAnalysis.StandardType.GGTBJF4Kernel
public import CFSG.LocalAnalysis.StandardType.GGTBJF4Refl
public import CFSG.LocalAnalysis.StandardType.GGTBJF4Roots
public import CFSG.LocalAnalysis.StandardType.GGTBJReflFour
public import CFSG.LocalAnalysis.StandardType.GGTBJF4NoncommAux
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem ggTBJ_f4_core
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K]
    {ζ : Kˣ} {L' : Type} [Group L'] [Finite L'] {ψ : L' →* ModGL Tag.F4 K}
    {σ : Multiplicative (Fin 4 → ZMod p) →* L'} (hstd : GGTBJF4Std p ζ ψ σ)
    (f₀ : Multiplicative (Fin 4 → ZMod p)) {J : Subgroup L'}
    (hJ : IsComponentOf J (Subgroup.centralizer ({σ f₀} : Set L')))
    (hJl : ∀ Q : Subgroup L',
      IsComponentOf Q (Subgroup.centralizer ({σ f₀} : Set L')) → Q ≤ J)
    (hcount : p ^ 2 * Nat.card {f : Multiplicative (Fin 4 → ZMod p) // ∀ j ∈ J, σ f * j = j * σ f} ≤
      p ^ 4) :
    ∃ (m₁ m₂ : L') (s₁ s₂ : MulAut (Multiplicative (Fin 4 → ZMod p))),
      m₁ ∈ J ∧ m₂ ∈ J ∧
      (∀ f, ψ m₁ * ψ (σ f) * (ψ m₁)⁻¹ = ψ (σ (s₁ f))) ∧
      (∀ f, ψ m₂ * ψ (σ f) * (ψ m₂)⁻¹ = ψ (σ (s₂ f))) ∧
      s₁ ^ 2 = 1 ∧ s₂ ^ 2 = 1 ∧
      Nat.card {f // s₁ f = f} * p = p ^ 4 ∧ Nat.card {f // s₂ f = f} * p = p ^ 4 ∧
      s₁ * s₂ ≠ s₂ * s₁ := by
  classical
  have hp : p.Prime := Fact.out
  let χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* Kˣ := rootCharHom (ggTBJa p ζ f₀)
  obtain ⟨i, hJi⟩ := ggTBJ_f4_class (p := p) (ζ := ζ) (ψ := ψ) (σ := σ) hp2 hstd f₀ hJ hJl
  let ι := {β : Fin Tag.F4.rank → ℤ // β ∈ componentRoots χ i}
  haveI : Nonempty ι := by
    obtain ⟨a, ha⟩ := Quotient.exists_rep i
    exact ⟨⟨a.1, ⟨a.2, ha⟩⟩⟩
  let f : ι → (Fin 4 → ZMod p) → ZMod p := fun a w => ggTBJFun p a.1 w
  let v : ι → (Fin 4 → ZMod p) := fun a => ggTBJVec p a.1
  have hfv : ∀ a, f a (v a) = 2 := by
    intro a
    exact ggTBJ_fun_vec_self p (isRoot_of_mem_componentRoots a.2)
  have hadd : ∀ a (x y : Fin 4 → ZMod p), f a (x + y) = f a x + f a y := fun a x y =>
    map_add (ggTBJFun p a.1) x y
  have hsmul : ∀ a (c : ZMod p) (x : Fin 4 → ZMod p), f a (c • x) = c * f a x := fun a c x =>
    (map_smul (ggTBJFun p a.1) c x).trans (smul_eq_mul c _)
  have hconn : ∀ S : Set ι, S.Nonempty →
      (∀ a b, (f a (v b) ≠ 0 ∨ f b (v a) ≠ 0) → (a ∈ S ↔ b ∈ S)) → S = Set.univ := by
    intro S hSne hSclosed
    let S' : Set (Fin Tag.F4.rank → ℤ) := (fun a : ι => (a : Fin Tag.F4.rank → ℤ)) '' S
    have hS'sub : S' ⊆ componentRoots χ i := by
      rintro β ⟨a, -, rfl⟩
      exact a.2
    have hS'ne : S'.Nonempty := by
      obtain ⟨a, ha⟩ := hSne
      exact ⟨(a : Fin Tag.F4.rank → ℤ), ⟨a, ha, rfl⟩⟩
    have hS'closed : ∀ β ∈ componentRoots χ i, ∀ γ ∈ componentRoots χ i,
        ((corootPair (τ := Tag.F4) γ β : ZMod p) ≠ 0 ∨
          (corootPair (τ := Tag.F4) β γ : ZMod p) ≠ 0) →
        (β ∈ S' ↔ γ ∈ S') := by
      intro β hβ γ hγ hp
      have key : ∀ (δ : Fin Tag.F4.rank → ℤ) (hδ : δ ∈ componentRoots χ i),
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
      have e1 : f ⟨β, hβ⟩ (v ⟨γ, hγ⟩) = (corootPair (τ := Tag.F4) γ β : ZMod p) := by
        simpa only [f, v] using ggTBJ_fun_vec p (isRoot_of_mem_componentRoots hγ)
      have e2 : f ⟨γ, hγ⟩ (v ⟨β, hβ⟩) = (corootPair (τ := Tag.F4) β γ : ZMod p) := by
        simpa only [f, v] using ggTBJ_fun_vec p (isRoot_of_mem_componentRoots hβ)
      rw [e1, e2]
      exact hp
    have hSuniv := ggTBJ_f4_connected hp hp2 i S' hS'sub hS'ne hS'closed
    refine Set.eq_univ_of_forall fun a => ?_
    have ha : (a : Fin Tag.F4.rank → ℤ) ∈ S' := by
      rw [hSuniv]
      exact a.2
    obtain ⟨b, hb, hba⟩ := ha
    have hEq : b = a := Subtype.ext hba
    rwa [hEq] at hb
  have hcard : p ^ 2 * Nat.card {w : Fin 4 → ZMod p // ∀ a, f a w = 0} ≤ p ^ 4 := by
    have hmap : ∀ w : {w : Fin 4 → ZMod p // ∀ a, f a w = 0}, ∀ j ∈ J,
        σ (Multiplicative.ofAdd (w : Fin 4 → ZMod p)) * j =
          j * σ (Multiplicative.ofAdd (w : Fin 4 → ZMod p)) := by
      intro w j hj
      have hw : ∀ β ∈ componentRoots χ i, ggTBJFun p β (w : Fin 4 → ZMod p) = 0 := fun β hβ =>
        w.2 ⟨β, hβ⟩
      exact ggTBJ_f4_kernel (p := p) (ζ := ζ) (ψ := ψ) (σ := σ) hstd f₀ hJ i hJi
        (Multiplicative.ofAdd (w : Fin 4 → ZMod p)) (by simpa using hw) j hj
    let toW : {w : Fin 4 → ZMod p // ∀ a, f a w = 0} →
        {g : Multiplicative (Fin 4 → ZMod p) // ∀ j ∈ J, σ g * j = j * σ g} :=
      fun w => ⟨Multiplicative.ofAdd (w : Fin 4 → ZMod p), hmap w⟩
    have hinj : Function.Injective toW := by
      intro a b hab
      have h1 : (toW a).val = (toW b).val := Subtype.ext_iff.mp hab
      exact Subtype.ext (Multiplicative.ofAdd.injective h1)
    have hle := Nat.card_le_card_of_injective toW hinj
    exact le_trans (Nat.mul_le_mul_left (p ^ 2) hle) hcount
  obtain ⟨a₁, a₂, w, hw⟩ := exists_not_commute_reflection_four hp2 f v hadd hsmul hfv hconn hcard
  have hrefl_eq : ∀ (a : ι) (y : Fin 4 → ZMod p), ggTBJRefl p a.1 y = y - f a y • v a := by
    intro a y
    funext x
    simp [ggTBJRefl, f, v, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hwR : ggTBJRefl p a₁.1 (ggTBJRefl p a₂.1 w) ≠
      ggTBJRefl p a₂.1 (ggTBJRefl p a₁.1 w) := by
    have e1 : (w - f a₂ w • v a₂) - f a₁ (w - f a₂ w • v a₂) • v a₁ =
        ggTBJRefl p a₁.1 (ggTBJRefl p a₂.1 w) := by
      rw [hrefl_eq a₂ w]
      exact (hrefl_eq a₁ _).symm
    have e2 : (w - f a₁ w • v a₁) - f a₂ (w - f a₁ w • v a₁) • v a₂ =
        ggTBJRefl p a₂.1 (ggTBJRefl p a₁.1 w) := by
      rw [hrefl_eq a₁ w]
      exact (hrefl_eq a₂ _).symm
    rw [e1, e2] at hw
    exact hw
  obtain ⟨m₁, hm₁, hact₁⟩ :=
    ggTBJ_f4_refl (p := p) (ζ := ζ) (ψ := ψ) (σ := σ) hstd f₀ i hJi a₁.2
  obtain ⟨m₂, hm₂, hact₂⟩ :=
    ggTBJ_f4_refl (p := p) (ζ := ζ) (ψ := ψ) (σ := σ) hstd f₀ i hJi a₂.2
  have hfv₁ : ggTBJFun p a₁.1 (ggTBJVec p a₁.1) = 2 :=
    ggTBJ_fun_vec_self p (isRoot_of_mem_componentRoots a₁.2)
  have hfv₂ : ggTBJFun p a₂.1 (ggTBJVec p a₂.1) = 2 :=
    ggTBJ_fun_vec_self p (isRoot_of_mem_componentRoots a₂.2)
  have hnc : ggTBJReflAut p a₁.1 * ggTBJReflAut p a₂.1 ≠
      ggTBJReflAut p a₂.1 * ggTBJReflAut p a₁.1 := by
    intro hcom
    have hw' := congrArg
      (fun s : MulAut (Multiplicative (Fin 4 → ZMod p)) => s (Multiplicative.ofAdd w)) hcom
    rw [MulAut.mul_apply, MulAut.mul_apply] at hw'
    rw [ggTBJ_reflAut_ofAdd p hfv₂, ggTBJ_reflAut_ofAdd p hfv₁,
      ggTBJ_reflAut_ofAdd p hfv₁, ggTBJ_reflAut_ofAdd p hfv₂] at hw'
    exact hwR (Multiplicative.ofAdd.injective hw')
  exact ⟨m₁, m₂, ggTBJReflAut p a₁.1, ggTBJReflAut p a₂.1, hm₁, hm₂, hact₁, hact₂,
    ggTBJ_reflAut_sq p hfv₁, ggTBJ_reflAut_sq p hfv₂,
    ggTBJ_card_fixed_mul p hp2 hfv₁, ggTBJ_card_fixed_mul p hp2 hfv₂, hnc⟩

end CFSG.StandardType

end