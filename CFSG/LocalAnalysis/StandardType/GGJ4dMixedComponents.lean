module

public import CFSG.LocalAnalysis.StandardType.GGJ4dComponents
public import CFSG.LieType.Chevalley.RationalToralSignDiagramTheta
public import CFSG.LocalAnalysis.StandardType.GGLatDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidRank

import all CFSG.LocalAnalysis.StandardType.GGJ4dComponents

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.StandardType CFSG.HardMathSupport.Timmesfeld.LangTorus

variable {τ : Tag}

private theorem latPerm_add (π : Equiv.Perm (Fin τ.rank)) (x y : Fin τ.rank → ℤ) :
    latPerm π (x + y) = latPerm π x + latPerm π y := by
  ext i
  simp [latPerm, Pi.add_apply]

private theorem latPerm_smul (π : Equiv.Perm (Fin τ.rank)) (c : ℤ) (x : Fin τ.rank → ℤ) :
    latPerm π (c • x) = c • latPerm π x := by
  ext i
  simp [latPerm, Pi.smul_apply]

private theorem latPerm_sub (π : Equiv.Perm (Fin τ.rank)) (x y : Fin τ.rank → ℤ) :
    latPerm π (x - y) = latPerm π x - latPerm π y := by
  ext i
  simp [latPerm, Pi.sub_apply]

private theorem latPerm_eq_self_of_rho_eq_neg
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {π : Equiv.Perm (Fin τ.rank)} {ε : ℤ} (hε : ε = -1)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = ε • latPerm π γ)
    {x : Fin τ.rank → ℤ} (hxr : IsRoot τ x) (hxρ : S.ρ x = -x) :
    latPerm π x = x := by
  have h := hρ x hxr
  rw [hxρ, hε] at h
  exact (neg_inj.mp (by simpa using h)).symm

theorem j4d_stableRoots_isRoot
    {τ : Tag} (hτ : SimplyLacedTag τ) {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ j k, τ.cartan (π j) (π k) = τ.cartan j k)
    {ε : ℤ} (hε : ε = -1)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = ε • latPerm π γ)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {x : Fin τ.rank → ℤ} (hx : x ∈ Ψ) (hxρ : S.ρ x = -x) :
    IsRoot τ x :=
  hΨ.isRoot x hx

theorem j4d_stableRoots_neg
    {τ : Tag} (hτ : SimplyLacedTag τ) {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ j k, τ.cartan (π j) (π k) = τ.cartan j k)
    {ε : ℤ} (hε : ε = -1)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = ε • latPerm π γ)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {x : Fin τ.rank → ℤ} (hx : x ∈ Ψ) (hxρ : S.ρ x = -x) :
    -x ∈ Ψ ∧ S.ρ (-x) = -(-x) := by
  refine ⟨hΨ.neg_mem x hx, ?_⟩
  rw [S.frob.neg_eq, hxρ]

theorem j4d_stableRoots_add
    {τ : Tag} (hτ : SimplyLacedTag τ) {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ j k, τ.cartan (π j) (π k) = τ.cartan j k)
    {ε : ℤ} (hε : ε = -1)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = ε • latPerm π γ)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {x y : Fin τ.rank → ℤ} (hx : x ∈ Ψ) (hxρ : S.ρ x = -x)
    (hy : y ∈ Ψ) (hyρ : S.ρ y = -y) (hsum : IsRoot τ (x + y)) :
    x + y ∈ Ψ ∧ S.ρ (x + y) = -(x + y) := by
  have hxr : IsRoot τ x := hΨ.isRoot x hx
  have hyr : IsRoot τ y := hΨ.isRoot y hy
  have hlatx : latPerm π x = x := latPerm_eq_self_of_rho_eq_neg S hε hρ hxr hxρ
  have hlaty : latPerm π y = y := latPerm_eq_self_of_rho_eq_neg S hε hρ hyr hyρ
  refine ⟨hΨ.add_mem x hx y hy hsum, ?_⟩
  have h := hρ (x + y) hsum
  rw [latPerm_add, smul_add, hlatx, hlaty, hε] at h
  rw [h]
  simp only [neg_one_smul, neg_add]

theorem j4d_stableRoots_reflection
    {τ : Tag} (hτ : SimplyLacedTag τ) {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ j k, τ.cartan (π j) (π k) = τ.cartan j k)
    {ε : ℤ} (hε : ε = -1)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = ε • latPerm π γ)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {x y : Fin τ.rank → ℤ} (hx : x ∈ Ψ) (hxρ : S.ρ x = -x)
    (hy : y ∈ Ψ) (hyρ : S.ρ y = -y) :
    rootReflection y • x ∈ Ψ ∧ S.ρ (rootReflection y • x) = -(rootReflection y • x) := by
  have hxr : IsRoot τ x := hΨ.isRoot x hx
  have hyr : IsRoot τ y := hΨ.isRoot y hy
  have hlatx : latPerm π x = x := latPerm_eq_self_of_rho_eq_neg S hε hρ hxr hxρ
  have hlaty : latPerm π y = y := latPerm_eq_self_of_rho_eq_neg S hε hρ hyr hyρ
  have hrefΨ : rootReflection y • x ∈ Ψ := hΨ.reflection_mem x hx y hy
  refine ⟨hrefΨ, ?_⟩
  have hlin : latPerm π (rootReflection y • x) = rootReflection y • x := by
    rw [rootReflection_smul hyr x, latPerm_sub, latPerm_smul, hlatx, hlaty]
  rw [hρ _ (hΨ.isRoot _ hrefΨ), hε, hlin]
  simp

private theorem FConn_symm
    {F : Set (Fin τ.rank → ℤ)} {x y : Fin τ.rank → ℤ} (h : FConn F x y) :
    FConn F y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hstep ih =>
      exact Relation.ReflTransGen.head ⟨hstep.2.1, hstep.1, by
        rw [iform_comm]
        exact hstep.2.2⟩ ih

theorem j4d_fcomp_orthogonal
    {F : Set (Fin τ.rank → ℤ)} {γ x y : Fin τ.rank → ℤ}
    (hx : x ∈ FComp F γ) (hyF : y ∈ F) (hy : y ∉ FComp F γ) :
    iform x y = 0 := by
  by_contra hne
  exact hy ⟨hyF, hx.2.trans (Relation.ReflTransGen.single ⟨hx.1, hyF, hne⟩)⟩

end CFSG.StandardType.LangRat

end
