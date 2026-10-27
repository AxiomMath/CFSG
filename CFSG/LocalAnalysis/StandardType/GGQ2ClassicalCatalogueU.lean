module

public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCatalogue
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalNormalizers
public import CFSG.LocalAnalysis.StandardType.GGQ2UnitCutThree
public import CFSG.LocalAnalysis.StandardType.GGQ2UnitHeartCutThree

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module
open CFSG.StandardType (GGLabelIso)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

@[expose] def unitDiffMap (N : ℕ) :
    UnitRaw.Vfull N →ₗ[ZMod 3] (Fin (Fintype.card (Fin N × Fin N)) → ZMod 3) :=
  (LinearEquiv.funCongrLeft (ZMod 3) (ZMod 3) (Fintype.equivFin (Fin N × Fin N)).symm).toLinearMap ∘ₗ
    LinearMap.pi (fun q : Fin N × Fin N => UnitRaw.diffFun N q.1 q.2)

@[expose] def unitFullEntry (N : ℕ) : RawFrameData where
  V := UnitRaw.Vfull N
  instAddCommGroup := inferInstance
  instModule := inferInstance
  instFiniteDimensional := inferInstance
  Code := Finset (Fin N)
  instFintype := inferInstance
  kind := .unitFull N
  ambientLabel := ⟨.twA, N - 1, 1⟩
  admissible := fun S => 4 ≤ N ∧ UnitRaw.admissible S
  occurs := UnitRaw.occurs
  label := UnitRaw.label
  cent := UnitRaw.cent
  inside := UnitRaw.inside
  normalizerGroup := fun S => UnitRaw.normalizerOf S
  ambientNormalizer := UnitRaw.ambientNormalizer N
  absRank := fun _ => Fintype.card (Fin N × Fin N)
  rootMap := fun _ => unitDiffMap N
  equivLabels := UnitRaw.equivLabels
  Root := PEmpty
  instRootFintype := inferInstance
  root := fun r => r.elim
  coroot := fun r => r.elim
  pairing := fun r _ => r.elim
  pairing_eq := fun r => r.elim
  pairing_self := fun r => r.elim
  reflection := fun r => r.elim
  reflection_apply := fun r => r.elim

@[expose] def unitHeartEntry (N : ℕ) : RawFrameData where
  V := ↥(UnitRaw.heart N)
  instAddCommGroup := inferInstance
  instModule := inferInstance
  instFiniteDimensional := inferInstance
  Code := Finset (Fin N)
  instFintype := inferInstance
  kind := .unitHeart N
  ambientLabel := ⟨.twA, N - 1, 1⟩
  admissible := fun S => 4 ≤ N ∧ 3 ∣ N ∧ UnitRaw.admissible S
  occurs := UnitRaw.occursH
  label := UnitRaw.label
  cent := UnitRaw.centH
  inside := UnitRaw.insideH
  normalizerGroup := fun S => UnitRaw.normalizerOfH S
  ambientNormalizer := UnitRaw.ambientNormalizerH N
  absRank := fun _ => Fintype.card (Fin N × Fin N)
  rootMap := fun _ => unitDiffMap N ∘ₗ (UnitRaw.heart N).subtype
  equivLabels := UnitRaw.equivLabelsH
  Root := PEmpty
  instRootFintype := inferInstance
  root := fun r => r.elim
  coroot := fun r => r.elim
  pairing := fun r _ => r.elim
  pairing_eq := fun r => r.elim
  pairing_self := fun r => r.elim
  reflection := fun r => r.elim
  reflection_apply := fun r => r.elim

@[expose] def classicalCatalogue : FrameKind → RawFrameData
  | .lin t ε => planeEntry (.linear ε) t
  | .symp t => planeEntry .symplectic t
  | .orth t δ => planeEntry (.orthogonal δ) t
  | .unitFull N => unitFullEntry N
  | .unitHeart N => unitHeartEntry N
  | .exceptional m => emptyEntry (.exceptional m)

theorem classicalCatalogue_kind (k : FrameKind) : (classicalCatalogue k).kind = k := by
  cases k <;> rfl

theorem unitFullEntry_rawNoInternalTwoNode (N : ℕ) : RawNoInternalTwoNode (unitFullEntry N) := by
  intro v hv U hU hvU S T hS hT hocc_S hocc_T hcent_S hcent_T hin labK hlabK labJ hlabJ
  exact UnitRaw.unitFull_noInternalTwoNode hS.1 v hv U hU hvU S T hS.2 hT.2 hocc_S hocc_T
    hcent_S hcent_T hin labK hlabK labJ hlabJ

theorem unitHeartEntry_rawNoInternalTwoNode (N : ℕ) : RawNoInternalTwoNode (unitHeartEntry N) := by
  intro v hv U hU hvU S T hS hT hocc_S hocc_T hcent_S hcent_T hin labK hlabK labJ hlabJ
  exact UnitRaw.unitHeart_noInternalTwoNode hS.1 hS.2.1 v hv U hU hvU S T hS.2.2 hT.2.2 hocc_S
    hocc_T hcent_S hcent_T hin labK hlabK labJ hlabJ

theorem classicalCatalogue_cutThreeInput (k : FrameKind) : CutThreeInput (classicalCatalogue k) := by
  intro _
  cases k with
  | lin t ε => exact planeEntry_rawNoInternalTwoNode (.linear ε) t
  | symp t => exact planeEntry_rawNoInternalTwoNode .symplectic t
  | orth t δ => exact planeEntry_rawNoInternalTwoNode (.orthogonal δ) t
  | unitFull N => exact unitFullEntry_rawNoInternalTwoNode N
  | unitHeart N => exact unitHeartEntry_rawNoInternalTwoNode N
  | exceptional m =>
    intro v hv U hU hvU c
    exact c.elim

theorem classicalCatalogue_literalDictionaryInput (hrig : GGLabelRigidInput) (k : FrameKind) :
    LiteralDictionaryInput (classicalCatalogue k) := by
  cases k with
  | lin t ε => exact planeEntry_literalDictionaryInput hrig (.linear ε) t
  | symp t => exact planeEntry_literalDictionaryInput hrig .symplectic t
  | orth t δ => exact planeEntry_literalDictionaryInput hrig (.orthogonal δ) t
  | unitFull N => exact literalDictionaryInput_of_rigid hrig (unitFullEntry N) fun _ _ _ h => h
  | unitHeart N => exact literalDictionaryInput_of_rigid hrig (unitHeartEntry N) fun _ _ _ h => h
  | exceptional m =>
    exact literalDictionaryInput_of_rigid hrig (emptyEntry (.exceptional m)) fun c => c.elim

theorem classicalCatalogue_actualCutThreeInput (hrig : GGLabelRigidInput) (k : FrameKind) :
    ActualCutThreeInput (classicalCatalogue k) :=
  actualCutThreeInput_of_raw (classicalCatalogue k) (classicalCatalogue_cutThreeInput k)
    (classicalCatalogue_literalDictionaryInput hrig k)

end

end CFSG.StandardType.GGQ2Frame
