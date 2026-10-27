module

public import CFSG.LieType.Chevalley.TwistMap

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.RootSystem

set_option linter.unusedSectionVars false

section CharTwo

variable {τ : Tag} {R : Type} [CommRing R] [CharP R 2]

theorem neg_one_units_of_charTwo : (-1 : Rˣ) = 1 :=
  Units.ext (CharTwo.neg_eq (1 : R))

theorem weylElt_mul_canonicalRep_charTwo (i : Fin τ.rank) (w : WeylGroup τ) :
    weylElt τ R i 1 * canonicalRep (coxeterSystem τ) R w =
      canonicalRep (coxeterSystem τ) R ((coxeterSystem τ).simple i * w) := by
  rw [weylElt_mul_canonicalRep]
  split_ifs
  · rfl
  · rw [neg_one_units_of_charTwo, torusElt_one, one_mul]

theorem canonicalRep_wordProd_mul_charTwo (ω : List (Fin τ.rank)) (v : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) R ((coxeterSystem τ).wordProd ω * v) =
      (ω.map fun i => weylElt τ R i 1).prod * canonicalRep (coxeterSystem τ) R v := by
  induction ω with
  | nil => rw [CoxeterSystem.wordProd_nil, one_mul, List.map_nil, List.prod_nil, one_mul]
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_assoc, ← weylElt_mul_canonicalRep_charTwo, ih,
      List.map_cons, List.prod_cons, mul_assoc]

theorem canonicalRep_mul_charTwo (w v : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) R (w * v) =
      canonicalRep (coxeterSystem τ) R w * canonicalRep (coxeterSystem τ) R v := by
  obtain ⟨ω, -, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  have h := canonicalRep_wordProd_mul_charTwo (R := R) ω 1
  rw [mul_one, canonicalRep_one, mul_one] at h
  rw [canonicalRep_wordProd_mul_charTwo, h]

end CharTwo

section NegOne

theorem wordProd_smul' {τ : Tag} (l : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    (coxeterSystem τ).wordProd l • v = l.foldr (reflect τ) v := by
  induction l with
  | nil => rw [CoxeterSystem.wordProd_nil, one_smul, List.foldr_nil]
  | cons i l ih => rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul, List.foldr_cons]

@[expose] def d4NegOneWord : List (Fin TwistTag.D4.tag.rank) :=
  ([2, 0, 1, 3, 2, 0, 1, 3, 2, 0, 1, 3] : List (Fin 4))

@[expose] def d4NegOne : WeylGroup TwistTag.D4.tag :=
  (coxeterSystem TwistTag.D4.tag).wordProd d4NegOneWord

theorem d4NegOne_smul_single (i : Fin TwistTag.D4.tag.rank) :
    d4NegOne • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) = -Pi.single i 1 := by
  rw [d4NegOne, wordProd_smul']
  revert i
  decide +kernel

theorem d4NegOne_smul (v : Fin TwistTag.D4.tag.rank → ℤ) : d4NegOne • v = -v := by
  have h : CFSG.LieType.RootSystem.weylAction (isFiniteType_cartan TwistTag.D4.tag) d4NegOne =
      -LinearMap.id := by
    refine LinearMap.pi_ext fun i x => ?_
    rw [← mul_one x, ← smul_eq_mul, Pi.single_smul, map_smul, map_smul, ← smul_def,
      d4NegOne_smul_single]
    simp
  rw [smul_def, h]
  rfl

theorem d4NegOne_mul_comm (w : WeylGroup TwistTag.D4.tag) : w * d4NegOne = d4NegOne * w := by
  refine ext_single fun i => ?_
  rw [mul_smul, mul_smul, d4NegOne_smul, d4NegOne_smul, smul_neg]

theorem weylTwist_d4NegOne : weylTwist TwistTag.D4 d4NegOne = d4NegOne := by
  refine ext_single fun i => ?_
  have h := weylTwist_smul_permLattice (t := TwistTag.D4) d4NegOne
    (permLattice TwistTag.D4.perm.symm (Pi.single i 1))
  rw [permLattice_permLattice_symm, d4NegOne_smul, permLattice_neg, permLattice_permLattice_symm]
    at h
  rw [h, d4NegOne_smul]

end NegOne

end CFSG.RankThree.PartOne.Q1327T
