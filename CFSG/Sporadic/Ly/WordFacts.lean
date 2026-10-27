module

public import CFSG.Sporadic.Schreier.LyData
public import CFSG.Sporadic.Fi23.SlpSpec
public import Certificates.Data.GH74.LyTwoWeights
public import Certificates.Data.GH74.LyHH
public import Certificates.Data.GH74.LyGen

public section

namespace CFSG.Sporadic.Ly.Omega

open CFSG.Sporadic.Th (wordG)
open CFSG.Sporadic.Fi23 (slpG)

@[expose] noncomputable def seedLetter [LySeed] (z : ℤ) : J :=
  if z = 1 then a else if z = -1 then a⁻¹ else if z = 2 then b else b⁻¹

@[expose] noncomputable def slpLetter [LySeed] (words : Array (List ℤ)) (z : ℤ) : J :=
  if z.natAbs ≤ 2 then seedLetter z
  else if 0 < z then slpG seedLetter words (z.natAbs - 3)
  else (slpG seedLetter words (z.natAbs - 3))⁻¹

@[expose] noncomputable def genU [LySeed] : J := slpG seedLetter Gen.genWords 2

@[expose] noncomputable def genZ [LySeed] : J := slpG seedLetter Gen.genWords 4

@[expose] noncomputable def genT [LySeed] : J := slpG seedLetter Gen.genWords 5

@[expose] def LyGenFacts [LySeed] : Prop :=
  genU ^ 21 = 1 ∧ genU ^ 7 ≠ 1 ∧ genU ^ 3 ≠ 1 ∧ a * genU = genU * a ∧ a * genZ = genZ * a ∧
    genU ^ 7 * genT = genT * genU ^ 7 ∧ genZ ^ 22 = 1 ∧ genZ ^ 2 ≠ 1 ∧
    ∀ j, 2 ≤ j → j ≤ 6 → CFSG.Sporadic.LySchreier.aStar j ∈ Subgroup.closure {genZ, genT}

@[expose] def LyTwFacts [LySeed] : Prop :=
  ∀ r ∈ TwoWeights.twRels, wordG (slpLetter TwoWeights.twWords) r.1 =
    wordG (slpLetter TwoWeights.twWords) r.2

@[expose] def LyHHFacts [LySeed] : Prop :=
  (∀ r ∈ HH.hhRels, wordG (slpLetter HH.hhWords) r.1 = wordG (slpLetter HH.hhWords) r.2) ∧
    ∀ r ∈ HH.hhNe, wordG (slpLetter HH.hhWords) r.1 ≠ wordG (slpLetter HH.hhWords) r.2.1

@[expose] def LyWordFacts [LySeed] : Prop := LyGenFacts ∧ LyTwFacts ∧ LyHHFacts

end CFSG.Sporadic.Ly.Omega
