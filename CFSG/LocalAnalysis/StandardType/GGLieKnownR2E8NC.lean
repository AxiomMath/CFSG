module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ExcNCRoots
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongE8
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2CoverNC
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortTransport

public section

namespace CFSG.StandardType.LieKnownR2.E8

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.Blueprint.Chevalley

theorem ggRootNoCentral_e8
    {n f : ℕ}
    {β : Fin (ggU .E8 n f).D.rank → ℤ} (hβ : β ∈ (ggU .E8 n f).D.roots)
    (u : (ggU .E8 n f).K) :
    GGRootNoCentralAt (⊤ : Subgroup (ggU .E8 n f).K)
      (ggRootSub (ggU .E8 n f).D (MonoidHom.id (ggU .E8 n f).K) β u) := by
  have hNC : GGRootNoCentralAt (⊤ : Subgroup (ggU .E8 n f).K)
      ((ggU .E8 n f).D.rootGroup β) :=
    ExcNC.rootNoCentral_adj_simplyLaced .E8 (Or.inr (Or.inr rfl)) (GaloisField 2 f) hβ
  have hmap : ((ggU .E8 n f).D.rootGroup β).map (MulAut.conj u).toMonoidHom =
      ggRootSub (ggU .E8 n f).D (MonoidHom.id (ggU .E8 n f).K) β u := by
    simp only [ggRootSub, Subgroup.map_id]
  have h := ggRootNoCentralAt_top_map_mulEquiv (MulAut.conj u) hNC
  rwa [hmap] at h

theorem ggRootNoCentralAt_ggU_e8
    {n f : ℕ} {X : Type} [Group X] [Finite X]
    (φ : (ggU .E8 n f).K →* X) (hker : φ.ker ≤ Subgroup.center (ggU .E8 n f).K)
    {β : Fin (ggU .E8 n f).D.rank → ℤ} (hβ : β ∈ (ggU .E8 n f).D.roots)
    (u : (ggU .E8 n f).K) :
    GGRootNoCentralAt φ.range (ggRootSub (ggU .E8 n f).D φ β u) := by
  have hcenter : Subgroup.center (ggU .E8 n f).K = ⊥ :=
    center_adjointGroup_eq_bot (τ := .E8) (K := GaloisField 2 f)
  have hker_bot : φ.ker = ⊥ := le_bot_iff.mp (hker.trans (le_of_eq hcenter))
  have hodd : Odd (Nat.card φ.ker) := by
    rw [hker_bot, Subgroup.card_bot]
    exact odd_one
  have hR : IsPGroup 2 (ggRootSub (ggU .E8 n f).D (MonoidHom.id (ggU .E8 n f).K) β u) :=
    rootGroup_isPGroup_E8 hβ u rfl
  have hbase : GGRootNoCentralAt (⊤ : Subgroup (ggU .E8 n f).K)
      (ggRootSub (ggU .E8 n f).D (MonoidHom.id (ggU .E8 n f).K) β u) :=
    ggRootNoCentral_e8 hβ u
  have h := SpecialLinearNC.ggRootNoCentralAt_map_of_odd_central_ker φ hker hodd hR hbase
  have hgoal : (ggRootSub (ggU .E8 n f).D (MonoidHom.id (ggU .E8 n f).K) β u).map φ =
      ggRootSub (ggU .E8 n f).D φ β u :=
    (Short.ggRootSub_eq_map (ggU .E8 n f).D φ β u).symm
  rwa [hgoal] at h

end CFSG.StandardType.LieKnownR2.E8
