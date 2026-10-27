module

public import CFSG.Quasithin.Vol2.KGFactC31Cover
public import CFSG.Quasithin.Vol2.KGFactC31RuData
public import CFSG.Quasithin.Vol2.KGFactC31RuRefData

public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.RuSchreier
  CFSG.Quasithin.KGC31.Native CFSG.Sporadic.Schreier.PairNative

@[expose] def ruLevJ : Array Level := rawLevels 4060 (ruField4060 3) (ruBaseArr 4060 ruJoinBase)

@[expose] def cGensA : Array (Array ℕ) := #[ruC0A, ruC1A]

@[expose] def repsZA : List (Array ℕ) :=
  hWordsZ.map (fun w => conjA (abA w) ruZA) ++ otherZW.map wA

@[expose] def repsAA : List (Array ℕ) :=
  hWordsA.map (fun w => conjA (abA w) ruA0A) ++ otherAW.map abA

@[expose] def coverZ : Bool :=
  coverOK 4060 ruLevJ ruJoinBase cGensA (cGensA.map ruInv) ruZA repsZA 2000
    (blocksOf 4060 ruLevC [[0], [1, 2]])

@[expose] def coverA : Bool :=
  coverOK 4060 ruLevJ ruJoinBase ruLGensA (ruLGensA.map ruInv) ruA0A repsAA 2000
    (blocksOf 4060 ruLevL [[0], [1]])

@[expose] def baseChecks : Bool :=
  coverZ && coverA && (otherZW.all fun w => (fixedList 4060 (wA w)).length == 0) &&
    otherAW.all fun w => (fixedList 4060 (abA w)).length == 92

end CFSG.Quasithin.KGC31.Ru

end
