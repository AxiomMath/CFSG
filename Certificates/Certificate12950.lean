module

public import CFSG.RankThree.PartTwo.Sec21.Item226DataCertificate12950Inputs
public import CFSG.RankThree.PartTwo.Sec21.Notation

public section

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec21 Matrix

namespace CertificateChecks.Batch12950

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec21 Matrix

private theorem reflCensus_0_0 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![0, 0, 0, 1] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_1_1 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![0, 0, 1, 0] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_2_2 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![0, 0, 1, 1] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_3_3 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![0, 0, 1, 2] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_4_4 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![0, 1, 0, 0] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_5_5 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![0, 1, 0, 1] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_6_6 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![0, 1, 0, 2] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_7_7 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![0, 1, 1, 0] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_8_8 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![0, 1, 1, 1] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_9_9 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![0, 1, 1, 2] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_10_10 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![0, 1, 2, 0] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_11_11 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![0, 1, 2, 1] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_12_12 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![0, 1, 2, 2] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_13_13 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 0, 0, 0] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_14_14 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 0, 0, 1] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_15_15 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 0, 0, 2] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_16_16 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 0, 1, 0] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_17_17 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 0, 1, 1] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_18_18 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 0, 1, 2] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_19_19 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 0, 2, 0] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_20_20 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 0, 2, 1] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_21_21 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 0, 2, 2] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_22_22 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 1, 0, 0] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_23_23 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 1, 0, 1] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_24_24 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 1, 0, 2] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_25_25 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 1, 1, 0] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_26_26 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 1, 1, 1] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_27_27 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 1, 1, 2] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_28_28 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 1, 2, 0] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_29_29 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 1, 2, 1] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_30_30 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 1, 2, 2] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_31_31 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 2, 0, 0] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_32_32 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 2, 0, 1] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_33_33 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 2, 0, 2] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_34_34 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 2, 1, 0] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_35_35 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 2, 1, 1] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_36_36 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 2, 1, 2] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_37_37 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 2, 2, 0] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_38_38 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 2, 2, 1] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem reflCensus_39_39 : ∀ b0 b1 b2 b3 : ZMod 3,
    ReflCheck (1 + vecMulVec ![1, 2, 2, 2] ![b0, b1, b2, b3]) := by
  decide +kernel

private theorem normVec_exists_40 : ∀ a0 a1 a2 a3 : ZMod 3, ![a0, a1, a2, a3] ≠ 0 →
    ∃ k : Fin 40, ∃ s : ZMod 3, ![a0, a1, a2, a3] = s • normVec k := by
  decide +kernel

private theorem refl_types_41 : ∀ c ∈ List.range' 6 39,
    c ∈ tripleTable.map Prod.fst ∨ c ∈ s5aSeeds ∨ c ∈ s5bSeeds ∨ c ∈ g648aSeeds ∨
      c ∈ g648bSeeds := by
  decide +kernel

private theorem tripleTable_spec_42 : ∀ p ∈ tripleTable, CommTriple p.2.1 p.2.2 p.1 ∧ p.2.1 < 6 ∧
    p.2.2 < 6 := by
  decide +kernel

private theorem s5a_cert_43 : ∀ c ∈ s5aSeeds, checkDeriv (c :: List.range 6) (certOf c) = true ∧
    ∀ i ∈ s5aL, i ∈ (c :: List.range 6) ++ (certOf c).map Prod.fst := by
  decide +kernel

private theorem s5b_cert_44 : ∀ c ∈ s5bSeeds, checkDeriv (c :: List.range 6) (certOf c) = true ∧
    ∀ i ∈ s5bL, i ∈ (c :: List.range 6) ++ (certOf c).map Prod.fst := by
  decide +kernel

private theorem g648a_cert_45 : ∀ c ∈ g648aSeeds, checkDeriv (c :: List.range 6) (certOf c) = true ∧
    ∀ i ∈ g648aL, i ∈ (c :: List.range 6) ++ (certOf c).map Prod.fst := by
  decide +kernel

private theorem g648b_cert_46 : ∀ c ∈ g648bSeeds, checkDeriv (c :: List.range 6) (certOf c) = true ∧
    ∀ i ∈ g648bL, i ∈ (c :: List.range 6) ++ (certOf c).map Prod.fst := by
  decide +kernel

private theorem g648a_max_0_47 :
    ∀ i ∈ List.range' 0 9, (∀ j ∈ g648aL, CompatAt i j) → i ∈ g648aL := by
  decide +kernel

private theorem g648a_max_1_48 :
    ∀ i ∈ List.range' 9 9, (∀ j ∈ g648aL, CompatAt i j) → i ∈ g648aL := by
  decide +kernel

private theorem g648a_max_2_49 :
    ∀ i ∈ List.range' 18 9, (∀ j ∈ g648aL, CompatAt i j) → i ∈ g648aL := by
  decide +kernel

private theorem g648a_max_3_50 :
    ∀ i ∈ List.range' 27 9, (∀ j ∈ g648aL, CompatAt i j) → i ∈ g648aL := by
  decide +kernel

private theorem g648a_max_4_51 :
    ∀ i ∈ List.range' 36 9, (∀ j ∈ g648aL, CompatAt i j) → i ∈ g648aL := by
  decide +kernel

private theorem g648b_max_0_52 :
    ∀ i ∈ List.range' 0 9, (∀ j ∈ g648bL, CompatAt i j) → i ∈ g648bL := by
  decide +kernel

private theorem g648b_max_1_53 :
    ∀ i ∈ List.range' 9 9, (∀ j ∈ g648bL, CompatAt i j) → i ∈ g648bL := by
  decide +kernel

private theorem g648b_max_2_54 :
    ∀ i ∈ List.range' 18 9, (∀ j ∈ g648bL, CompatAt i j) → i ∈ g648bL := by
  decide +kernel

private theorem g648b_max_3_55 :
    ∀ i ∈ List.range' 27 9, (∀ j ∈ g648bL, CompatAt i j) → i ∈ g648bL := by
  decide +kernel

private theorem g648b_max_4_56 :
    ∀ i ∈ List.range' 36 9, (∀ j ∈ g648bL, CompatAt i j) → i ∈ g648bL := by
  decide +kernel

private theorem g648a_centers_57 : ∀ j ∈ g648aL, ∀ k : Fin 4, (reflAt j - 1) 0 k = 0 := by
  decide +kernel

private theorem g648b_fix_58 :
    ∀ j ∈ g648bL, ∀ k : Fin 4, reflAt j k 0 = if k = 0 then 1 else 0 := by
  decide +kernel

private theorem s5aExt_spec_59 :
    ∀ p ∈ s5aExt, CommTriple p.2.1 p.2.2 p.1 ∧ p.2.1 ∈ s5aL ∧ p.2.2 ∈ s5aL := by
  decide +kernel

private theorem s5a_max_0_60 : ∀ i ∈ List.range' 0 9, (∀ j ∈ s5aL, CompatAt i j) →
    i ∈ s5aL ∨ i ∈ s5aExt.map Prod.fst := by
  decide +kernel

private theorem s5a_max_1_61 : ∀ i ∈ List.range' 9 9, (∀ j ∈ s5aL, CompatAt i j) →
    i ∈ s5aL ∨ i ∈ s5aExt.map Prod.fst := by
  decide +kernel

private theorem s5a_max_2_62 : ∀ i ∈ List.range' 18 9, (∀ j ∈ s5aL, CompatAt i j) →
    i ∈ s5aL ∨ i ∈ s5aExt.map Prod.fst := by
  decide +kernel

private theorem s5a_max_3_63 : ∀ i ∈ List.range' 27 9, (∀ j ∈ s5aL, CompatAt i j) →
    i ∈ s5aL ∨ i ∈ s5aExt.map Prod.fst := by
  decide +kernel

private theorem s5a_max_4_64 : ∀ i ∈ List.range' 36 9, (∀ j ∈ s5aL, CompatAt i j) →
    i ∈ s5aL ∨ i ∈ s5aExt.map Prod.fst := by
  decide +kernel

private theorem s5bExt_spec_65 :
    ∀ p ∈ s5bExt, CommTriple p.2.1 p.2.2 p.1 ∧ p.2.1 ∈ s5bL ∧ p.2.2 ∈ s5bL := by
  decide +kernel

private theorem s5b_max_0_66 : ∀ i ∈ List.range' 0 9, (∀ j ∈ s5bL, CompatAt i j) →
    i ∈ s5bL ∨ i ∈ s5bExt.map Prod.fst := by
  decide +kernel

private theorem s5b_max_1_67 : ∀ i ∈ List.range' 9 9, (∀ j ∈ s5bL, CompatAt i j) →
    i ∈ s5bL ∨ i ∈ s5bExt.map Prod.fst := by
  decide +kernel

private theorem s5b_max_2_68 : ∀ i ∈ List.range' 18 9, (∀ j ∈ s5bL, CompatAt i j) →
    i ∈ s5bL ∨ i ∈ s5bExt.map Prod.fst := by
  decide +kernel

private theorem s5b_max_3_69 : ∀ i ∈ List.range' 27 9, (∀ j ∈ s5bL, CompatAt i j) →
    i ∈ s5bL ∨ i ∈ s5bExt.map Prod.fst := by
  decide +kernel

private theorem s5b_max_4_70 : ∀ i ∈ List.range' 36 9, (∀ j ∈ s5bL, CompatAt i j) →
    i ∈ s5bL ∨ i ∈ s5bExt.map Prod.fst := by
  decide +kernel

private theorem s5aChain_spec_71 :
    reflAt 0 * reflAt 1 * reflAt 0 = reflAt 1 * reflAt 0 * reflAt 1 ∧
    reflAt 1 * reflAt 5 * reflAt 1 = reflAt 5 * reflAt 1 * reflAt 5 ∧
    reflAt 5 * reflAt 43 * reflAt 5 = reflAt 43 * reflAt 5 * reflAt 43 ∧
    CommAt 0 5 ∧ CommAt 0 43 ∧ CommAt 1 43 ∧ reflAt 0 ≠ reflAt 1 := by
  decide +kernel

private theorem s5aChain_gen_72 : checkDeriv s5aChain s5aChainCert = true ∧
    ∀ i ∈ s5aL, i ∈ s5aChain ++ s5aChainCert.map Prod.fst := by
  decide +kernel

private theorem s5bChain_spec_73 :
    reflAt 0 * reflAt 1 * reflAt 0 = reflAt 1 * reflAt 0 * reflAt 1 ∧
    reflAt 1 * reflAt 5 * reflAt 1 = reflAt 5 * reflAt 1 * reflAt 5 ∧
    reflAt 5 * reflAt 38 * reflAt 5 = reflAt 38 * reflAt 5 * reflAt 38 ∧
    CommAt 0 5 ∧ CommAt 0 38 ∧ CommAt 1 38 ∧ reflAt 0 ≠ reflAt 1 := by
  decide +kernel

private theorem s5bChain_gen_74 : checkDeriv s5bChain s5bChainCert = true ∧
    ∀ i ∈ s5bL, i ∈ s5bChain ++ s5bChainCert.map Prod.fst := by
  decide +kernel

end CertificateChecks.Batch12950

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec21 Matrix in
theorem certificate12950 :
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![0, 0, 0, 1] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![0, 0, 1, 0] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![0, 0, 1, 1] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![0, 0, 1, 2] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![0, 1, 0, 0] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![0, 1, 0, 1] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![0, 1, 0, 2] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![0, 1, 1, 0] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![0, 1, 1, 1] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![0, 1, 1, 2] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![0, 1, 2, 0] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![0, 1, 2, 1] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![0, 1, 2, 2] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![1, 0, 0, 0] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![1, 0, 0, 1] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![1, 0, 0, 2] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![1, 0, 1, 0] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![1, 0, 1, 1] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![1, 0, 1, 2] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![1, 0, 2, 0] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![1, 0, 2, 1] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![1, 0, 2, 2] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![1, 1, 0, 0] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![1, 1, 0, 1] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![1, 1, 0, 2] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![1, 1, 1, 0] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![1, 1, 1, 1] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![1, 1, 1, 2] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![1, 1, 2, 0] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![1, 1, 2, 1] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![1, 1, 2, 2] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![1, 2, 0, 0] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![1, 2, 0, 1] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![1, 2, 0, 2] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![1, 2, 1, 0] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![1, 2, 1, 1] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![1, 2, 1, 2] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![1, 2, 2, 0] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![1, 2, 2, 1] ![b0, b1, b2, b3])) ∧
    (∀ b0 b1 b2 b3 : ZMod 3,
      ReflCheck (1 + vecMulVec ![1, 2, 2, 2] ![b0, b1, b2, b3])) ∧
    (∀ a0 a1 a2 a3 : ZMod 3, ![a0, a1, a2, a3] ≠ 0 →
      ∃ k : Fin 40, ∃ s : ZMod 3, ![a0, a1, a2, a3] = s • normVec k) ∧
    (∀ c ∈ List.range' 6 39,
      c ∈ tripleTable.map Prod.fst ∨ c ∈ s5aSeeds ∨ c ∈ s5bSeeds ∨ c ∈ g648aSeeds ∨
        c ∈ g648bSeeds) ∧
    (∀ p ∈ tripleTable, CommTriple p.2.1 p.2.2 p.1 ∧ p.2.1 < 6 ∧
      p.2.2 < 6) ∧
    (∀ c ∈ s5aSeeds, checkDeriv (c :: List.range 6) (certOf c) = true ∧
      ∀ i ∈ s5aL, i ∈ (c :: List.range 6) ++ (certOf c).map Prod.fst) ∧
    (∀ c ∈ s5bSeeds, checkDeriv (c :: List.range 6) (certOf c) = true ∧
      ∀ i ∈ s5bL, i ∈ (c :: List.range 6) ++ (certOf c).map Prod.fst) ∧
    (∀ c ∈ g648aSeeds, checkDeriv (c :: List.range 6) (certOf c) = true ∧
      ∀ i ∈ g648aL, i ∈ (c :: List.range 6) ++ (certOf c).map Prod.fst) ∧
    (∀ c ∈ g648bSeeds, checkDeriv (c :: List.range 6) (certOf c) = true ∧
      ∀ i ∈ g648bL, i ∈ (c :: List.range 6) ++ (certOf c).map Prod.fst) ∧
    (∀ i ∈ List.range' 0 9, (∀ j ∈ g648aL, CompatAt i j) → i ∈ g648aL) ∧
    (∀ i ∈ List.range' 9 9, (∀ j ∈ g648aL, CompatAt i j) → i ∈ g648aL) ∧
    (∀ i ∈ List.range' 18 9, (∀ j ∈ g648aL, CompatAt i j) → i ∈ g648aL) ∧
    (∀ i ∈ List.range' 27 9, (∀ j ∈ g648aL, CompatAt i j) → i ∈ g648aL) ∧
    (∀ i ∈ List.range' 36 9, (∀ j ∈ g648aL, CompatAt i j) → i ∈ g648aL) ∧
    (∀ i ∈ List.range' 0 9, (∀ j ∈ g648bL, CompatAt i j) → i ∈ g648bL) ∧
    (∀ i ∈ List.range' 9 9, (∀ j ∈ g648bL, CompatAt i j) → i ∈ g648bL) ∧
    (∀ i ∈ List.range' 18 9, (∀ j ∈ g648bL, CompatAt i j) → i ∈ g648bL) ∧
    (∀ i ∈ List.range' 27 9, (∀ j ∈ g648bL, CompatAt i j) → i ∈ g648bL) ∧
    (∀ i ∈ List.range' 36 9, (∀ j ∈ g648bL, CompatAt i j) → i ∈ g648bL) ∧
    (∀ j ∈ g648aL, ∀ k : Fin 4, (reflAt j - 1) 0 k = 0) ∧
    (∀ j ∈ g648bL, ∀ k : Fin 4, reflAt j k 0 = if k = 0 then 1 else 0) ∧
    (∀ p ∈ s5aExt, CommTriple p.2.1 p.2.2 p.1 ∧ p.2.1 ∈ s5aL ∧ p.2.2 ∈ s5aL) ∧
    (∀ i ∈ List.range' 0 9, (∀ j ∈ s5aL, CompatAt i j) →
      i ∈ s5aL ∨ i ∈ s5aExt.map Prod.fst) ∧
    (∀ i ∈ List.range' 9 9, (∀ j ∈ s5aL, CompatAt i j) →
      i ∈ s5aL ∨ i ∈ s5aExt.map Prod.fst) ∧
    (∀ i ∈ List.range' 18 9, (∀ j ∈ s5aL, CompatAt i j) →
      i ∈ s5aL ∨ i ∈ s5aExt.map Prod.fst) ∧
    (∀ i ∈ List.range' 27 9, (∀ j ∈ s5aL, CompatAt i j) →
      i ∈ s5aL ∨ i ∈ s5aExt.map Prod.fst) ∧
    (∀ i ∈ List.range' 36 9, (∀ j ∈ s5aL, CompatAt i j) →
      i ∈ s5aL ∨ i ∈ s5aExt.map Prod.fst) ∧
    (∀ p ∈ s5bExt, CommTriple p.2.1 p.2.2 p.1 ∧ p.2.1 ∈ s5bL ∧ p.2.2 ∈ s5bL) ∧
    (∀ i ∈ List.range' 0 9, (∀ j ∈ s5bL, CompatAt i j) →
      i ∈ s5bL ∨ i ∈ s5bExt.map Prod.fst) ∧
    (∀ i ∈ List.range' 9 9, (∀ j ∈ s5bL, CompatAt i j) →
      i ∈ s5bL ∨ i ∈ s5bExt.map Prod.fst) ∧
    (∀ i ∈ List.range' 18 9, (∀ j ∈ s5bL, CompatAt i j) →
      i ∈ s5bL ∨ i ∈ s5bExt.map Prod.fst) ∧
    (∀ i ∈ List.range' 27 9, (∀ j ∈ s5bL, CompatAt i j) →
      i ∈ s5bL ∨ i ∈ s5bExt.map Prod.fst) ∧
    (∀ i ∈ List.range' 36 9, (∀ j ∈ s5bL, CompatAt i j) →
      i ∈ s5bL ∨ i ∈ s5bExt.map Prod.fst) ∧
    (reflAt 0 * reflAt 1 * reflAt 0 = reflAt 1 * reflAt 0 * reflAt 1 ∧
      reflAt 1 * reflAt 5 * reflAt 1 = reflAt 5 * reflAt 1 * reflAt 5 ∧
      reflAt 5 * reflAt 43 * reflAt 5 = reflAt 43 * reflAt 5 * reflAt 43 ∧
      CommAt 0 5 ∧ CommAt 0 43 ∧ CommAt 1 43 ∧ reflAt 0 ≠ reflAt 1) ∧
    (checkDeriv s5aChain s5aChainCert = true ∧
      ∀ i ∈ s5aL, i ∈ s5aChain ++ s5aChainCert.map Prod.fst) ∧
    (reflAt 0 * reflAt 1 * reflAt 0 = reflAt 1 * reflAt 0 * reflAt 1 ∧
      reflAt 1 * reflAt 5 * reflAt 1 = reflAt 5 * reflAt 1 * reflAt 5 ∧
      reflAt 5 * reflAt 38 * reflAt 5 = reflAt 38 * reflAt 5 * reflAt 38 ∧
      CommAt 0 5 ∧ CommAt 0 38 ∧ CommAt 1 38 ∧ reflAt 0 ≠ reflAt 1) ∧
    (checkDeriv s5bChain s5bChainCert = true ∧
      ∀ i ∈ s5bL, i ∈ s5bChain ++ s5bChainCert.map Prod.fst) := by
  exact ⟨CertificateChecks.Batch12950.reflCensus_0_0, CertificateChecks.Batch12950.reflCensus_1_1, CertificateChecks.Batch12950.reflCensus_2_2,
    CertificateChecks.Batch12950.reflCensus_3_3, CertificateChecks.Batch12950.reflCensus_4_4, CertificateChecks.Batch12950.reflCensus_5_5,
    CertificateChecks.Batch12950.reflCensus_6_6, CertificateChecks.Batch12950.reflCensus_7_7, CertificateChecks.Batch12950.reflCensus_8_8,
    CertificateChecks.Batch12950.reflCensus_9_9, CertificateChecks.Batch12950.reflCensus_10_10, CertificateChecks.Batch12950.reflCensus_11_11,
    CertificateChecks.Batch12950.reflCensus_12_12, CertificateChecks.Batch12950.reflCensus_13_13, CertificateChecks.Batch12950.reflCensus_14_14,
    CertificateChecks.Batch12950.reflCensus_15_15, CertificateChecks.Batch12950.reflCensus_16_16, CertificateChecks.Batch12950.reflCensus_17_17,
    CertificateChecks.Batch12950.reflCensus_18_18, CertificateChecks.Batch12950.reflCensus_19_19, CertificateChecks.Batch12950.reflCensus_20_20,
    CertificateChecks.Batch12950.reflCensus_21_21, CertificateChecks.Batch12950.reflCensus_22_22, CertificateChecks.Batch12950.reflCensus_23_23,
    CertificateChecks.Batch12950.reflCensus_24_24, CertificateChecks.Batch12950.reflCensus_25_25, CertificateChecks.Batch12950.reflCensus_26_26,
    CertificateChecks.Batch12950.reflCensus_27_27, CertificateChecks.Batch12950.reflCensus_28_28, CertificateChecks.Batch12950.reflCensus_29_29,
    CertificateChecks.Batch12950.reflCensus_30_30, CertificateChecks.Batch12950.reflCensus_31_31, CertificateChecks.Batch12950.reflCensus_32_32,
    CertificateChecks.Batch12950.reflCensus_33_33, CertificateChecks.Batch12950.reflCensus_34_34, CertificateChecks.Batch12950.reflCensus_35_35,
    CertificateChecks.Batch12950.reflCensus_36_36, CertificateChecks.Batch12950.reflCensus_37_37, CertificateChecks.Batch12950.reflCensus_38_38,
    CertificateChecks.Batch12950.reflCensus_39_39, CertificateChecks.Batch12950.normVec_exists_40, CertificateChecks.Batch12950.refl_types_41,
    CertificateChecks.Batch12950.tripleTable_spec_42, CertificateChecks.Batch12950.s5a_cert_43, CertificateChecks.Batch12950.s5b_cert_44,
    CertificateChecks.Batch12950.g648a_cert_45, CertificateChecks.Batch12950.g648b_cert_46, CertificateChecks.Batch12950.g648a_max_0_47,
    CertificateChecks.Batch12950.g648a_max_1_48, CertificateChecks.Batch12950.g648a_max_2_49, CertificateChecks.Batch12950.g648a_max_3_50,
    CertificateChecks.Batch12950.g648a_max_4_51, CertificateChecks.Batch12950.g648b_max_0_52, CertificateChecks.Batch12950.g648b_max_1_53,
    CertificateChecks.Batch12950.g648b_max_2_54, CertificateChecks.Batch12950.g648b_max_3_55, CertificateChecks.Batch12950.g648b_max_4_56,
    CertificateChecks.Batch12950.g648a_centers_57, CertificateChecks.Batch12950.g648b_fix_58, CertificateChecks.Batch12950.s5aExt_spec_59,
    CertificateChecks.Batch12950.s5a_max_0_60, CertificateChecks.Batch12950.s5a_max_1_61, CertificateChecks.Batch12950.s5a_max_2_62,
    CertificateChecks.Batch12950.s5a_max_3_63, CertificateChecks.Batch12950.s5a_max_4_64, CertificateChecks.Batch12950.s5bExt_spec_65,
    CertificateChecks.Batch12950.s5b_max_0_66, CertificateChecks.Batch12950.s5b_max_1_67, CertificateChecks.Batch12950.s5b_max_2_68,
    CertificateChecks.Batch12950.s5b_max_3_69, CertificateChecks.Batch12950.s5b_max_4_70, CertificateChecks.Batch12950.s5aChain_spec_71,
    CertificateChecks.Batch12950.s5aChain_gen_72, CertificateChecks.Batch12950.s5bChain_spec_73, CertificateChecks.Batch12950.s5bChain_gen_74⟩

end Certificates
