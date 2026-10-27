module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoReflLin
public import Certificates.Data.SUSmallBase

public section

namespace CFSG.StandardType.HdRo7SU.Small

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def smGroup (m : ℕ) (X : List (SMV m × SMV m)) : Subgroup (SMGL m) :=
  Subgroup.closure ({g | SMIsPerm g} ∪ {r | ∃ q ∈ X, SMRefl r q.1 (smDual q.2)})


@[expose] def SMRulesLeaf : Prop :=
  SUNormalizerLeaf → ∀ (m : ℕ), (m = 7 ∨ m = 8) → ∀ (H : Subgroup (SMGL m)),
    (∀ g, SMIsPerm g → g ∈ H) → QTwoLin.TransvectionFree H →
    (∀ g ∈ H, g (smOnes m) = smOnes m → ∀ s, SMIsPerm s → SMIsPerm (g * s * g⁻¹)) →
    SMRCl (smRefSet H)

@[expose] def SMClassSetLeaf : Prop :=
  (∀ R : Set (SMV 7 × SMV 7), SMRCl R → ∃ X ∈ smAllowed7,
    ∀ p, p ∈ R ↔ (SMTClass p ∨ ∃ q ∈ X, SMClass p q)) ∧
  (∀ R : Set (SMV 8 × SMV 8), SMRCl R → ∃ X ∈ smAllowed8,
    ∀ p, p ∈ R ↔ (SMTClass p ∨ ∃ q ∈ X, SMClass p q))

@[expose] def SMModelsBDLeaf : Prop :=
  ZS.LinWeyl 3 (smGroup 7 [sm7D7b]) ∧ ZS.LinWeyl 3 (smGroup 7 [sm7B7b, sm7D7b]) ∧
  ZS.LinWeyl 3 (smGroup 8 [sm8D8b]) ∧ ZS.LinWeyl 3 (smGroup 8 [sm8B8b, sm8D8b])

@[expose] def SMModelsALeaf : Prop :=
  ZS.LinWeyl 3 (smGroup 7 []) ∧ ZS.LinWeyl 3 (smGroup 8 []) ∧ ZS.LinWeyl 3 (smGroup 7 [sm7A7b]) ∧
  ZS.LinWeyl 3 (smGroup 7 [sm7A7b, sm7A7a, sm7cx]) ∧ ZS.LinWeyl 3 (smGroup 8 [sm8A8a])

@[expose] def SMModelsELeaf : Prop :=
  ZS.LinWeyl 3 (smGroup 7 [sm7E7b, sm7A7a])

@[expose] def SMConjLeaf : Prop :=
  SMModelsBDLeaf → SMModelsALeaf → SMModelsELeaf →
  (∀ X ∈ smAllowed7, X ≠ [sm7cx] → ZS.LinWeyl 3 (smGroup 7 X)) ∧
  (∀ X ∈ smAllowed8, X ≠ [sm8cx] → ZS.LinWeyl 3 (smGroup 8 X))

end CFSG.StandardType.HdRo7SU.Small
