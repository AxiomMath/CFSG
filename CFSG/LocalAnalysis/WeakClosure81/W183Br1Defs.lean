module

public import CFSG.LocalAnalysis.WeakClosure81.W18PackG
public import CFSG.LocalAnalysis.WeakClosure81.W18PackMod
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def packDeltaU (D : Data G) (V H : Subgroup G) (i : ℕ)
    (M : ModDataE H (eOmegaZ H D.T)) (A : Subgroup (LGL 2 M.W)) : ℕ :=
  sInf {k | ∃ g : G, Gam183 V H (eOmegaZ H D.T) i g ∧ M.img (vInH V H g) = A ∧
    E3.mQuot (conjSubgroup V g) (vInH V H g) = k}

@[expose] def packGensU (D : Data G) (V H : Subgroup G) (i : ℕ)
    (M : ModDataE H (eOmegaZ H D.T)) : Set (Subgroup (LGL 2 M.W)) :=
  {B | B ≠ ⊥ ∧ ∃ B₀ ∈ E3.gammaSet V i D.T, B = M.img B₀}

@[expose] noncomputable def packZsU (D : Data G) (H : Subgroup G)
    (M : ModDataE H (eOmegaZ H D.T)) : Submodule (ZMod 2) M.W :=
  M.sp (omegaOneCenterOf D.T)

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i j : ℕ}

@[expose] noncomputable def mB (x : Ctx188 D V₀ V H i j) : ℕ :=
  mBar D.M V₀ V x.hyp.setting.isElemAbelian

end Ctx188

end CFSG.LocalAnalysis.WeakClosure81

end
