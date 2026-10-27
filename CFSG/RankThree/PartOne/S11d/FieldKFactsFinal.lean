module

public import CFSG.RankThree.PartOne.S11d.FixedFactsAll
public import CFSG.RankThree.PartOne.S11d.FieldKFacts

public section

namespace CFSG.RankThree.PartOne.FieldFix


theorem fieldAutCoset_final (hNL : ChevalleySubfieldNonLocalized)
    (hTits : LargeReeTitsNonLocalized) : FieldAutCoset :=
  fieldAutCoset_of_tags (tagFixedFacts_all hNL hTits)

theorem fieldFixedPElements_final (hNL : ChevalleySubfieldNonLocalized)
    (hTits : LargeReeTitsNonLocalized) : FieldFixedPElements :=
  fieldFixedPElements_of_tags (tagFixedFacts_all hNL hTits)

theorem fieldFixedCentralizer_final (hNL : ChevalleySubfieldNonLocalized)
    (hTits : LargeReeTitsNonLocalized) : FieldFixedCentralizer :=
  fieldFixedCentralizer_of_tags (tagFixedFacts_all hNL hTits)

theorem fieldFixedNonLocal_final (hNL : ChevalleySubfieldNonLocalized)
    (hTits : LargeReeTitsNonLocalized) : FieldFixedNonLocal :=
  fieldFixedNonLocal_of_tags (tagFixedFacts_all hNL hTits)

end CFSG.RankThree.PartOne.FieldFix
