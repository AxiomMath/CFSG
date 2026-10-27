module

public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksDefs

public section

namespace CFSG.StandardType.GGQ2Frame.OrthBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition Matrix
open CFSG.Open (StatedSp)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {K : Type} [Field K] (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)
  (t : ℕ) (δ : Fin 2)

@[expose] def liftV : PlaneRaw.V t →ₗ[ZMod 3] PlaneRaw.V (t + δ.val) where
  toFun u := Fin.append u 0
  map_add' u v := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp
  map_smul' c u := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp

@[expose] def liftSupport (S : Finset (Fin t)) : Finset (Fin (t + δ.val)) :=
  S.map (Fin.castAddEmb δ.val) ∪ Finset.univ.map (Fin.natAddEmb t)

@[expose] def liftCode : PlaneRaw.Code t → PlaneRaw.Code (t + δ.val)
  | .zero S => .zero (liftSupport t δ S)
  | .extension e => .extension (liftV t δ e)

@[expose] def planeQ : (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) → K :=
  fun w => ∑ i : Fin (t + δ.val),
    (w (Sum.inl i) * w (Sum.inr i) +
      if (i : ℕ) < t then w (Sum.inl i) ^ 2 + w (Sum.inr i) ^ 2 else 0)

abbrev omegaQ : Subgroup (GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :=
  LargeEvenOmega (planeQ (K := K) t δ)

@[expose] def otau (u : PlaneRaw.V t) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K :=
  ((SpBlocks.tau ζ (t + δ.val) (liftV t δ u) : ↥(StatedSp (t + δ.val) K)) :
    GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)

@[expose] def oTorusSet (U : Submodule (ZMod 3) (PlaneRaw.V t)) :
    Set (GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :=
  SpBlocks.torusSet ζ (t + δ.val) (U.map (liftV t δ))

@[expose] def oBlockGroup (c : PlaneRaw.Code t) : Subgroup ↥(omegaQ (K := K) t δ) :=
  ((SpBlocks.blockGroup ζ (t + δ.val) (liftCode t δ c)).map
    (StatedSp (t + δ.val) K).subtype).comap (omegaQ (K := K) t δ).subtype

@[expose] def oYcode (c : PlaneRaw.Code t) : Subgroup ↥(omegaQ (K := K) t δ) :=
  ⁅oBlockGroup ζ t δ c, oBlockGroup ζ t δ c⁆

end

end CFSG.StandardType.GGQ2Frame.OrthBlocks
