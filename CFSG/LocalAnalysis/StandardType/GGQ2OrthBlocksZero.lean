module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthAmbient
public import CFSG.LocalAnalysis.StandardType.GGQ2OrthAmbientSmall
public import CFSG.LocalAnalysis.StandardType.GGQ2OrthBlocksZero4

public section

namespace CFSG.StandardType.GGQ2Frame.OrthBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition Matrix
open CFSG.Open (StatedSp)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (δ : Fin 2)

theorem orthIsQuasisimpleYcode_zero (hK : Nat.card K = 2) (S : Finset (Fin t))
    (hS : PlaneRaw.admissible (.orthogonal δ) (.zero S : PlaneRaw.Code t)) :
    IsQuasisimple ↥(oYcode ζ t δ (.zero S)) :=
  isQuasisimple_oYcode_zero ζ hK t δ S hS

theorem orthNotIsComponentOfYcode_zero (hK : Nat.card K = 2) (S : Finset (Fin t))
    (hS : ¬ PlaneRaw.admissible (.orthogonal δ) (.zero S : PlaneRaw.Code t))
    (X : Subgroup ↥(omegaQ (K := K) t δ)) : ¬ IsComponentOf X (oYcode ζ t δ (.zero S)) :=
  not_isComponentOf_oYcode_zero ζ hK t δ S hS X

theorem orthTauMemYcodeIff_zero (hτ : OrthTauMemOmega) (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) (S : Finset (Fin t))
    (hS : PlaneRaw.admissible (.orthogonal δ) (.zero S : PlaneRaw.Code t)) (u : PlaneRaw.V t) :
    otau ζ t δ u ∈ (oYcode ζ t δ (.zero S)).map (omegaQ (K := K) t δ).subtype ↔
      u ∈ PlaneRaw.inside (.orthogonal δ) (.zero S : PlaneRaw.Code t) :=
  mem_oYcode_zero_iff ζ hτ hK hζ t δ S hS u

theorem orthTauCommuteYcodeIff_zero (hτ : OrthTauMemOmega) (hK : Nat.card K = 2)
    (hζ : Function.Injective ζ) (S : Finset (Fin t))
    (hS : PlaneRaw.admissible (.orthogonal δ) (.zero S : PlaneRaw.Code t)) (u : PlaneRaw.V t) :
    (∀ g ∈ oYcode ζ t δ (.zero S), otau ζ t δ u * (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
        (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * otau ζ t δ u) ↔
      u ∈ PlaneRaw.cent (.orthogonal δ) (.zero S : PlaneRaw.Code t) :=
  commute_oYcode_zero_iff ζ hτ hK hζ t δ S hS u

theorem orthMarkedYcode_zero (hK : Nat.card K = 2) (S : Finset (Fin t))
    (hS : PlaneRaw.admissible (.orthogonal δ) (.zero S : PlaneRaw.Code t)) :
    LargeEvenMarking ↥(oYcode ζ t δ (.zero S))
      (fun lab _ _ _ _ _ => lab = PlaneRaw.label (.orthogonal δ) (.zero S : PlaneRaw.Code t)) :=
  marked_oYcode_zero ζ hK t δ S hS

end CFSG.StandardType.GGQ2Frame.OrthBlocks
