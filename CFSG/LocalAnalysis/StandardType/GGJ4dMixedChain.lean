module

public import CFSG.LieType.Chevalley.RationalToralSignDiagramTheta
public import CFSG.LieType.Steinberg.Adjoint.Pairs
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidRank
public import CFSG.LocalAnalysis.StandardType.GGLatDefs

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Chevalley.ToralSign CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.StandardType

variable {τ : Tag}

private theorem symmetrizedCartan_eq_cartan_of_simplyLaced (hτ : SimplyLacedTag τ) :
    τ.symmetrizedCartan = τ.cartan := by
  rcases hτ with rfl | rfl | rfl | rfl <;>
    ext i j <;>
    simp [Tag.symmetrizedCartan, Tag.symmetrizer, Matrix.mul_apply, Matrix.one_apply]

private theorem symmetrizedCartan_perm_of_cartan (hτ : SimplyLacedTag τ)
    {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ j k, τ.cartan (π j) (π k) = τ.cartan j k) :
    ∀ j k, τ.symmetrizedCartan (π j) (π k) = τ.symmetrizedCartan j k := by
  intro j k
  rw [symmetrizedCartan_eq_cartan_of_simplyLaced hτ, hπ j k]

private theorem iform_latPerm (hτ : SimplyLacedTag τ) {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ j k, τ.cartan (π j) (π k) = τ.cartan j k)
    (u v : Fin τ.rank → ℤ) :
    iform (latPerm π u) (latPerm π v) = iform u v :=
  iform_permLattice (symmetrizedCartan_perm_of_cartan hτ hπ) u v

theorem j4d_chain_orth_one
    {τ : Tag} (hτ : SimplyLacedTag τ) {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ j k, τ.cartan (π j) (π k) = τ.cartan j k)
    {γ δ : Fin τ.rank → ℤ}
    (hγγ : iform γ γ = 2) (hσγ : latPerm π γ = γ)
    (hδorth : iform δ (latPerm π δ) = 0)
    (hne : iform γ δ = 1) :
    iform (γ - δ) (γ - latPerm π δ) = 0 := by
  have hγσδ : iform γ (latPerm π δ) = 1 := by
    calc
      iform γ (latPerm π δ) = iform (latPerm π γ) (latPerm π δ) := by rw [hσγ]
      _ = iform γ δ := iform_latPerm hτ hπ γ δ
      _ = 1 := hne
  rw [iform_sub_left, iform_sub_right, iform_sub_right, hγγ, hγσδ,
    iform_comm δ γ, hne, hδorth]
  ring

theorem j4d_chain_orth_negone
    {τ : Tag} (hτ : SimplyLacedTag τ) {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ j k, τ.cartan (π j) (π k) = τ.cartan j k)
    {γ δ : Fin τ.rank → ℤ}
    (hγγ : iform γ γ = 2) (hσγ : latPerm π γ = γ)
    (hδorth : iform δ (latPerm π δ) = 0)
    (hne : iform γ δ = -1) :
    iform (γ + δ) (γ + latPerm π δ) = 0 := by
  have hγσδ : iform γ (latPerm π δ) = -1 := by
    calc
      iform γ (latPerm π δ) = iform (latPerm π γ) (latPerm π δ) := by rw [hσγ]
      _ = iform γ δ := iform_latPerm hτ hπ γ δ
      _ = -1 := hne
  rw [iform_add_left, iform_add_right, iform_add_right, hγγ, hγσδ,
    iform_comm δ γ, hne, hδorth]
  ring

end CFSG.StandardType.LangRat
