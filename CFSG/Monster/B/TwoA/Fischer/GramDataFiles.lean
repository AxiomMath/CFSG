module

public import CFSG.Monster.B.TwoA.Fischer.GramDataAlgText0
public import CFSG.Monster.B.TwoA.Fischer.GramDataAlgText1
public import CFSG.Monster.B.TwoA.Fischer.GramDataAlgText2
public import CFSG.Monster.B.TwoA.Fischer.GramDataAlgText3
public import CFSG.Monster.B.TwoA.Fischer.GramDataAlgText4
public import CFSG.Monster.B.TwoA.Fischer.GramDataAlgText5
public import CFSG.Monster.B.TwoA.Fischer.GramDataAdjText0
public import CFSG.Monster.B.TwoA.Fischer.GramDataAdjText1
public import CFSG.Monster.B.TwoA.Fischer.GramDataLit
public import Lean.Data.Json.FromToJson.Basic
public import Lean.Data.Json.Parser

public section

namespace CFSG.Monster.B.TwoA.Fischer

open Lean (Json)

@[expose] def dAlgText : String :=
  dAlgText0 ++ dAlgText1 ++ dAlgText2 ++ dAlgText3 ++ dAlgText4 ++ dAlgText5

@[expose] def dAdjText : String := dAdjText0 ++ dAdjText1

@[expose] def jsonStrPairs (j : Json) : Except String (List (String × String)) := do
  (← j.getObj?).toArray.toList.mapM fun p => do pure (p.1, ← p.2.getStr?)

@[expose] def jsonNatPairs (j : Json) : Except String (List (Nat × Nat)) := do
  (← j.getObj?).toArray.toList.mapM fun p => do
    match p.1.toNat? with
    | some k => pure (k, ← p.2.getNat?)
    | none => throw s!"key {p.1} is not a natural number"

@[expose] def jsonKeys (s : String) : Except String (List String) := do
  let o ← (← Json.parse s).getObj?
  pure (o.toArray.map (·.1)).toList

structure DAlgCandidate where
  name : String
  vector : Nat
  adjointRank : Nat
  commutingNativeLabels : List Nat
  commutingNativeLabelCount : Nat
  rootFormulaOperator : List Nat
  rootFormulaInvolutive : Bool
  rootFormulaIsometry : Bool
  rootFormulaLieAutomorphism : Bool
  deriving DecidableEq, Inhabited

structure DAlgFile where
  author : String
  generatedAt : String
  status : String
  inputSha256 : List (String × String)
  graphDegree : Nat
  noncommutationMatrixBinaryRank : Nat
  basisNativePoints : List Nat
  noncommutationBasisRowsHex : List String
  noncommutationRowCoordinates : List Nat
  invariantBilinearFormRows : List Nat
  basisProductTable : List (List Nat)
  basisVersusAllPointsProductChecks : Nat
  distinctBasisJacobiTriples : Nat
  fourPermutationGenerators : List (List Nat)
  fourModuleGeneratorColumns : List (List Nat)
  cliqueLabelSpanDimension : Nat
  cliqueFixedVector : Nat
  bracketSeedHexadVertex : Nat
  candidateAmbientVectors : List DAlgCandidate
  limits : List String
  deriving DecidableEq, Inhabited

@[expose] def DAlgCandidate.ofJson (j : Json) : Except String DAlgCandidate := do
  pure
    { name := ← j.getObjValAs? String "name"
      vector := ← j.getObjValAs? Nat "vector"
      adjointRank := ← j.getObjValAs? Nat "adjoint_rank"
      commutingNativeLabels := ← j.getObjValAs? (List Nat) "commuting_native_labels"
      commutingNativeLabelCount := ← j.getObjValAs? Nat "commuting_native_label_count"
      rootFormulaOperator := ← j.getObjValAs? (List Nat) "root_formula_operator"
      rootFormulaInvolutive := ← j.getObjValAs? Bool "root_formula_involutive"
      rootFormulaIsometry := ← j.getObjValAs? Bool "root_formula_isometry"
      rootFormulaLieAutomorphism := ← j.getObjValAs? Bool "root_formula_Lie_automorphism" }

@[expose] def DAlgFile.ofJson (j : Json) : Except String DAlgFile := do
  let cs ← (← (← j.getObjVal? "candidate_ambient_vectors").getArr?).toList.mapM
    DAlgCandidate.ofJson
  pure
    { author := ← j.getObjValAs? String "author"
      generatedAt := ← j.getObjValAs? String "generated_at"
      status := ← j.getObjValAs? String "status"
      inputSha256 := ← jsonStrPairs (← j.getObjVal? "input_sha256")
      graphDegree := ← j.getObjValAs? Nat "graph_degree"
      noncommutationMatrixBinaryRank := ← j.getObjValAs? Nat "noncommutation_matrix_binary_rank"
      basisNativePoints := ← j.getObjValAs? (List Nat) "basis_native_points"
      noncommutationBasisRowsHex := ← j.getObjValAs? (List String)
        "noncommutation_basis_rows_hex"
      noncommutationRowCoordinates := ← j.getObjValAs? (List Nat)
        "noncommutation_row_coordinates"
      invariantBilinearFormRows := ← j.getObjValAs? (List Nat) "invariant_bilinear_form_rows"
      basisProductTable := ← j.getObjValAs? (List (List Nat)) "basis_product_table"
      basisVersusAllPointsProductChecks := ← j.getObjValAs? Nat
        "basis_versus_all_points_product_checks"
      distinctBasisJacobiTriples := ← j.getObjValAs? Nat "distinct_basis_Jacobi_triples"
      fourPermutationGenerators := ← j.getObjValAs? (List (List Nat))
        "four_permutation_generators"
      fourModuleGeneratorColumns := ← j.getObjValAs? (List (List Nat))
        "four_module_generator_columns"
      cliqueLabelSpanDimension := ← j.getObjValAs? Nat "clique_label_span_dimension"
      cliqueFixedVector := ← j.getObjValAs? Nat "clique_fixed_vector"
      bracketSeedHexadVertex := ← j.getObjValAs? Nat "bracket_seed_hexad_vertex"
      candidateAmbientVectors := cs
      limits := ← j.getObjValAs? (List String) "limits" }

@[expose] def dAlgFile : Except String DAlgFile := do
  DAlgFile.ofJson (← Json.parse dAlgText)

@[expose] def hexStr0x (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

@[expose] def dAlgRec : DAlgFile where
  author := "/root/type_v_exclusion"
  generatedAt := "2026-09-24T10:12:17.312749+00:00"
  status := "Original finite binary algebra proposal; no ambient root identification asserted"
  inputSha256 := [("MON-M22-induced-Fischer-permutations-proposal.json",
    "4519020e9cc9820da5ae510ed210340df0543966f012f028058416c6052f6b4c")]
  graphDegree := 693
  noncommutationMatrixBinaryRank := 78
  basisNativePoints := GramLit.basisPts
  noncommutationBasisRowsHex := GramLit.ncRows.map hexStr0x
  noncommutationRowCoordinates := GramLit.rowCoords
  invariantBilinearFormRows := GramLit.formRows
  basisProductTable := open GramLit in [bt0, bt1, bt2, bt3, bt4, bt5, bt6, bt7, bt8, bt9, bt10,
    bt11, bt12, bt13, bt14, bt15, bt16, bt17, bt18, bt19, bt20, bt21, bt22, bt23, bt24, bt25, bt26,
    bt27, bt28, bt29, bt30, bt31, bt32, bt33, bt34, bt35, bt36, bt37, bt38, bt39, bt40, bt41, bt42,
    bt43, bt44, bt45, bt46, bt47, bt48, bt49, bt50, bt51, bt52, bt53, bt54, bt55, bt56, bt57, bt58,
    bt59, bt60, bt61, bt62, bt63, bt64, bt65, bt66, bt67, bt68, bt69, bt70, bt71, bt72, bt73, bt74,
    bt75, bt76, bt77]
  basisVersusAllPointsProductChecks := 273780
  distinctBasisJacobiTriples := 76076
  fourPermutationGenerators := [GramLit.perm0, GramLit.perm1, GramLit.perm2, GramLit.perm3]
  fourModuleGeneratorColumns :=
    [GramLit.fourCol0, GramLit.fourCol1, GramLit.fourCol2, GramLit.fourCol3]
  cliqueLabelSpanDimension := 11
  cliqueFixedVector := 949
  bracketSeedHexadVertex := 1046
  candidateAmbientVectors :=
    [{ name := "clique_fixed", vector := 949, adjointRank := 22,
       commutingNativeLabels := GramLit.cand0Labels, commutingNativeLabelCount := 22,
       rootFormulaOperator := GramLit.cand0Op, rootFormulaInvolutive := true,
       rootFormulaIsometry := true, rootFormulaLieAutomorphism := true },
     { name := "clique_fixed_plus_label", vector := 948, adjointRank := 22,
       commutingNativeLabels := GramLit.cand1Labels, commutingNativeLabelCount := 22,
       rootFormulaOperator := GramLit.cand1Op, rootFormulaInvolutive := true,
       rootFormulaIsometry := true, rootFormulaLieAutomorphism := true },
     { name := "bracket_with_hexad_fiber_label", vector := 522240, adjointRank := 22,
       commutingNativeLabels := GramLit.cand2Labels, commutingNativeLabelCount := 22,
       rootFormulaOperator := GramLit.cand2Op, rootFormulaInvolutive := true,
       rootFormulaIsometry := true, rootFormulaLieAutomorphism := true }]
  limits :=
    ["This is the new binary Gram/algebra question; no graph-isomorphism search, full group census \
      or earlier producer is replayed.",
     "The78-dimensional algebra has the verified displayed structure constants. A \
      native-to-standard twisted E6 Lie algebra map is not proved by this diagnostic.",
     "Adjoint rank22 and the tested root formula alone are not being treated as a classification \
      of actual ambient root vectors."]

structure DAdjFile where
  author : String
  generatedAt : String
  status : String
  inputSha256 : List (String × String)
  rootBasisOrder : String
  e6BasisProductTable : List (List Nat)
  e6BilinearFormRows : List Nat
  e6DistinctBasisJacobiTriples : Nat
  e6InvariantFormBasisTriples : Nat
  e6SimpleOperatorParametersChecked : Nat
  diagramBasisPermutation : List Nat
  diagramFixedIndices : List Nat
  diagramTwoCycles : List (List Nat)
  nativeBasisPoints : List Nat
  nativeBasisLabelWords : List (List Nat)
  nativeGramMinorRows : List Nat
  nativeGramMinorEchelon : List (Nat × Nat)
  nativeCoordinatePairingsChecked : Nat
  cliqueSpanRank : Nat
  cliqueFixedMask : Nat
  cliqueFixedCoordinates : Nat
  fGeneratorColumns : List (List Nat)
  fFixedConstraintEchelon : List (Nat × Nat)
  fFixedDimension : Nat
  limits : List String
  deriving DecidableEq, Inhabited

@[expose] def DAdjFile.ofJson (j : Json) : Except String DAdjFile := do
  pure
    { author := ← j.getObjValAs? String "author"
      generatedAt := ← j.getObjValAs? String "generated_at"
      status := ← j.getObjValAs? String "status"
      inputSha256 := ← jsonStrPairs (← j.getObjVal? "input_sha256")
      rootBasisOrder := ← j.getObjValAs? String "root_basis_order"
      e6BasisProductTable := ← j.getObjValAs? (List (List Nat)) "E6_basis_product_table"
      e6BilinearFormRows := ← j.getObjValAs? (List Nat) "E6_bilinear_form_rows"
      e6DistinctBasisJacobiTriples := ← j.getObjValAs? Nat "E6_distinct_basis_Jacobi_triples"
      e6InvariantFormBasisTriples := ← j.getObjValAs? Nat "E6_invariant_form_basis_triples"
      e6SimpleOperatorParametersChecked := ← j.getObjValAs? Nat
        "E6_simple_operator_parameters_checked"
      diagramBasisPermutation := ← j.getObjValAs? (List Nat) "diagram_basis_permutation"
      diagramFixedIndices := ← j.getObjValAs? (List Nat) "diagram_fixed_indices"
      diagramTwoCycles := ← j.getObjValAs? (List (List Nat)) "diagram_two_cycles"
      nativeBasisPoints := ← j.getObjValAs? (List Nat) "native_basis_points"
      nativeBasisLabelWords := ← j.getObjValAs? (List (List Nat)) "native_basis_label_words"
      nativeGramMinorRows := ← j.getObjValAs? (List Nat) "native_Gram_minor_rows"
      nativeGramMinorEchelon := ← jsonNatPairs (← j.getObjVal? "native_Gram_minor_echelon")
      nativeCoordinatePairingsChecked := ← j.getObjValAs? Nat
        "native_coordinate_pairings_checked"
      cliqueSpanRank := ← j.getObjValAs? Nat "clique_span_rank"
      cliqueFixedMask := ← j.getObjValAs? Nat "clique_fixed_mask"
      cliqueFixedCoordinates := ← j.getObjValAs? Nat "clique_fixed_coordinates"
      fGeneratorColumns := ← j.getObjValAs? (List (List Nat)) "F_generator_columns"
      fFixedConstraintEchelon := ← jsonNatPairs (← j.getObjVal? "F_fixed_constraint_echelon")
      fFixedDimension := ← j.getObjValAs? Nat "F_fixed_dimension"
      limits := ← j.getObjValAs? (List String) "limits" }

@[expose] def dAdjFile : Except String DAdjFile := do
  DAdjFile.ofJson (← Json.parse dAdjText)

@[expose] def dAdjRec : DAdjFile where
  author := "/root/type_v_exclusion"
  generatedAt := "2026-09-24T10:20:25.800965+00:00"
  status := "Finite interface certificate, not an ambient root-vector classification"
  inputSha256 :=
    [("data/exceptional/root-orbit-certificates.json",
      "44a14f95ef8b46c4f75c5aaca3157a936fecdf564d316060a33daf35c96231d8"),
     ("research/monster/MON-Fischer-binary-noncommutation-algebra-proposal.json",
      "991e3457a3839c73c78fb41e996e26a6dbef9d68dd7e09f89b8d3c7b6d6c3748"),
     ("research/monster/MON-M22-induced-Fischer-permutations-proposal.json",
      "4519020e9cc9820da5ae510ed210340df0543966f012f028058416c6052f6b4c")]
  rootBasisOrder := "h_1,...,h_6, then the exact E6 roots in root-orbit-certificates.json"
  e6BasisProductTable := open GramLit in [e6bt0, e6bt1, e6bt2, e6bt3, e6bt4, e6bt5, e6bt6, e6bt7,
    e6bt8, e6bt9, e6bt10, e6bt11, e6bt12, e6bt13, e6bt14, e6bt15, e6bt16, e6bt17, e6bt18, e6bt19,
    e6bt20, e6bt21, e6bt22, e6bt23, e6bt24, e6bt25, e6bt26, e6bt27, e6bt28, e6bt29, e6bt30, e6bt31,
    e6bt32, e6bt33, e6bt34, e6bt35, e6bt36, e6bt37, e6bt38, e6bt39, e6bt40, e6bt41, e6bt42, e6bt43,
    e6bt44, e6bt45, e6bt46, e6bt47, e6bt48, e6bt49, e6bt50, e6bt51, e6bt52, e6bt53, e6bt54, e6bt55,
    e6bt56, e6bt57, e6bt58, e6bt59, e6bt60, e6bt61, e6bt62, e6bt63, e6bt64, e6bt65, e6bt66, e6bt67,
    e6bt68, e6bt69, e6bt70, e6bt71, e6bt72, e6bt73, e6bt74, e6bt75, e6bt76, e6bt77]
  e6BilinearFormRows := GramLit.e6Form
  e6DistinctBasisJacobiTriples := 76076
  e6InvariantFormBasisTriples := 474552
  e6SimpleOperatorParametersChecked := 36
  diagramBasisPermutation := GramLit.diagPerm
  diagramFixedIndices := GramLit.diagFixed
  diagramTwoCycles := [[0, 5], [2, 4], [9, 11], [10, 22], [13, 23], [15, 25], [16, 28], [18, 32],
    [19, 36], [20, 39], [21, 41], [27, 29], [34, 37], [35, 40], [42, 62], [43, 48], [44, 63],
    [46, 49], [47, 64], [51, 65], [54, 56], [55, 67], [58, 68], [60, 70], [61, 73], [72, 74]]
  nativeBasisPoints := GramLit.adjPts
  nativeBasisLabelWords := open GramLit in [word0, word1, word2, word3, word4, word5, word6,
    word7, word8, word9, word10, word11, word12, word13, word14, word15, word16, word17, word18,
    word19, word20, word21, word22, word23, word24, word25, word26, word27, word28, word29, word30,
    word31, word32, word33, word34, word35, word36, word37, word38, word39, word40, word41, word42,
    word43, word44, word45, word46, word47, word48, word49, word50, word51, word52, word53, word54,
    word55, word56, word57, word58, word59, word60, word61, word62, word63, word64, word65, word66,
    word67, word68, word69, word70, word71, word72, word73, word74, word75, word76, word77]
  nativeGramMinorRows := GramLit.gramRows
  nativeGramMinorEchelon := GramLit.gramEchKeys.zip GramLit.gramEchVals
  nativeCoordinatePairingsChecked := 273780
  cliqueSpanRank := 11
  cliqueFixedMask := 5461
  cliqueFixedCoordinates := 949
  fGeneratorColumns := open GramLit in [fCol0, fCol1, fCol2, fCol3, fCol4, fCol5, fCol6, fCol7,
    fCol8, fCol9, fCol10, fCol11]
  fFixedConstraintEchelon := GramLit.fEchKeys.zip GramLit.fEchVals
  fFixedDimension := 1
  limits := ["No claim that the new F-fixed vector is in the actual ambient root orbit.",
    "The ambient/native transport is a separate mathematical proof using these bounded identities."]

end CFSG.Monster.B.TwoA.Fischer
