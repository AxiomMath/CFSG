module

public import CFSG.LocalAnalysis.StandardType.GGQ2PlaneCutThree
public import CFSG.LocalAnalysis.StandardType.GGQ2FrameCore
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalNormalizers

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module
open CFSG.StandardType (GGLabelIso)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

@[expose] def emptyEntry (kind : FrameKind) : RawFrameData where
  V := PUnit
  instAddCommGroup := inferInstance
  instModule := inferInstance
  instFiniteDimensional := inferInstance
  Code := PEmpty
  instFintype := inferInstance
  kind := kind
  ambientLabel := ⟨.A, 0, 1⟩
  admissible := fun _ => False
  occurs := fun _ _ => False
  label := fun c => c.elim
  cent := fun c => c.elim
  inside := fun c => c.elim
  normalizerGroup := fun c => c.elim
  ambientNormalizer := ⊥
  absRank := fun c => c.elim
  rootMap := fun c => c.elim
  equivLabels := fun c => c.elim
  Root := PEmpty
  instRootFintype := inferInstance
  root := fun r => r.elim
  coroot := fun r => r.elim
  pairing := fun r _ => r.elim
  pairing_eq := fun r => r.elim
  pairing_self := fun r => r.elim
  reflection := fun r => r.elim
  reflection_apply := fun r => r.elim

@[expose] def planeFrameKind : PlaneRaw.PlaneKind → ℕ → FrameKind
  | .linear ε, t => .lin t ε
  | .symplectic, t => .symp t
  | .orthogonal δ, t => .orth t δ

@[expose] def planeAmbientLabel : PlaneRaw.PlaneKind → ℕ → LargeEvenLabel
  | .linear ε, t => ⟨.A, 2 * t + ε.val - 1, 1⟩
  | .symplectic, t => ⟨.C, t, 1⟩
  | .orthogonal δ, t => if Even t then ⟨.D, t + δ.val, 1⟩ else ⟨.twD, t + δ.val, 1⟩

@[expose] def planeEntry (k : PlaneRaw.PlaneKind) (t : ℕ) : RawFrameData where
  V := PlaneRaw.V t
  instAddCommGroup := inferInstance
  instModule := inferInstance
  instFiniteDimensional := inferInstance
  Code := PlaneRaw.Code t
  instFintype := inferInstance
  kind := planeFrameKind k t
  ambientLabel := planeAmbientLabel k t
  admissible := fun c => 4 ≤ t ∧ PlaneRaw.admissible k c
  occurs := PlaneRaw.occurs
  label := PlaneRaw.label k
  cent := PlaneRaw.cent k
  inside := PlaneRaw.inside k
  normalizerGroup := PlaneRaw.normalizerOf k t
  ambientNormalizer := PlaneRaw.ambientNormalizer k t
  absRank := fun _ => t
  rootMap := fun _ => LinearMap.id
  equivLabels := PlaneRaw.equivLabels k
  Root := PEmpty
  instRootFintype := inferInstance
  root := fun r => r.elim
  coroot := fun r => r.elim
  pairing := fun r _ => r.elim
  pairing_eq := fun r => r.elim
  pairing_self := fun r => r.elim
  reflection := fun r => r.elim
  reflection_apply := fun r => r.elim

theorem planeEntry_rawNoInternalTwoNode (k : PlaneRaw.PlaneKind) (t : ℕ) :
    RawNoInternalTwoNode (planeEntry k t) := by
  intro v hv U hU hvU c j hc hj hocc_c hocc_j hcent_c hcent_j hin labK hlabK labJ hlabJ
  exact PlaneRaw.plane_noInternalTwoNode hc.1 k v hv U hU hvU c j hc.2 hj.2 hocc_c hocc_j hcent_c
    hcent_j hin labK hlabK labJ hlabJ

theorem planeEntry_literalDictionaryInput (hrig : GGLabelRigidInput) (k : PlaneRaw.PlaneKind)
    (t : ℕ) : LiteralDictionaryInput (planeEntry k t) :=
  literalDictionaryInput_of_rigid hrig (planeEntry k t) fun _ _ _ h => h

end

end CFSG.StandardType.GGQ2Frame
