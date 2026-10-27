module

public import CFSG.Sporadic.Schreier.RuData
public import CFSG.Certificates.NativeSchreierArrays
public import CFSG.Certificates.NativeSetOrbit
public import Certificates.Data.CFSGNative.MonsterB.Max2Tower

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open scoped Pointwise

@[expose] def ruHexAt (b : ByteArray) (o w : ℕ) : ℕ := CFSG.Monster.B.Max2.Native.hexAt b o w

@[expose] def ruHexRow (b : ByteArray) (n L : ℕ) : Array ℕ :=
  Array.ofFn (n := n) fun i => ruHexAt b (L * (3 * n + 1) + 3 * i.val) 3

@[expose] def ruBytes4060 : ByteArray := ru4060Text.toUTF8

@[expose] def ruBytes1920 : ByteArray := ru1920Text.toUTF8

@[expose] def ruBytes80 : ByteArray := ru80Text.toUTF8

@[expose] def ruBytesPts : ByteArray := ruPtsText.toUTF8

@[expose] def ruBytesTree : ByteArray := ruTreeText.toUTF8

@[expose] def ruBytesSigma : ByteArray := ruSigmaText.toUTF8

@[expose] def ruArr4060 (L : ℕ) : Array ℕ := ruHexRow ruBytes4060 4060 L

@[expose] def ruArr1920 (L : ℕ) : Array ℕ := ruHexRow ruBytes1920 1920 L

@[expose] def ruArr80 (L : ℕ) : Array ℕ := ruHexRow ruBytes80 80 L

@[expose] def ruField4060 (f : ℕ) : Array (Array ℕ) :=
  Array.ofFn (n := (ruLines4060.getD f (0, 0)).2) fun j =>
    ruArr4060 ((ruLines4060.getD f (0, 0)).1 + j.val)

@[expose] def ruField1920 (f : ℕ) : Array (Array ℕ) :=
  Array.ofFn (n := (ruLines1920.getD f (0, 0)).2) fun j =>
    ruArr1920 ((ruLines1920.getD f (0, 0)).1 + j.val)

@[expose] def ruField80 : Array (Array ℕ) := Array.ofFn (n := 8) fun j => ruArr80 j.val

@[expose] def ruPtList (f : ℕ) : Array ℕ :=
  Array.ofFn (n := (ruPtsOffsets.getD f (0, 0)).2) fun i =>
    ruHexAt ruBytesPts (3 * ((ruPtsOffsets.getD f (0, 0)).1 + i.val)) 3

@[expose] def ruWordsArr (k s : ℕ) (D : List (List ℤ)) : Array (List ℤ) :=
  Array.ofFn (n := s) fun j => if j.val < k then [] else D.getD (j.val - k) []

@[expose] def ruFinList (n : ℕ) (hn : 0 < n) (b : List ℕ) : List (Fin n) :=
  b.map fun x => ⟨x % n, Nat.mod_lt _ hn⟩

@[expose] def ruA0 : Equiv.Perm (Fin 4060) := permOfArr 4060 (ruArr4060 0)

@[expose] def ruA1 : Equiv.Perm (Fin 4060) := permOfArr 4060 (ruArr4060 1)

@[expose] def ruP : Subgroup (Equiv.Perm (Fin 4060)) := Subgroup.closure {ruA0, ruA1}

@[expose] def ruC0 : Equiv.Perm (Fin 4060) := (slotRun ruCProg ruA0 ruA1).1

@[expose] def ruC1 : Equiv.Perm (Fin 4060) := (slotRun ruCProg ruA0 ruA1).2

@[expose] def ruN0 : Equiv.Perm (Fin 4060) := (slotRun ruNProg ruA0 ruA1).1

@[expose] def ruN1 : Equiv.Perm (Fin 4060) := (slotRun ruNProg ruA0 ruA1).2

@[expose] def ruC : Subgroup (Equiv.Perm (Fin 4060)) := Subgroup.closure {ruC0, ruC1}

@[expose] def ruZ : Equiv.Perm (Fin 4060) := ruC0 ^ 10

@[expose] def ruZ0 : Equiv.Perm (Fin 4060) := evalSigned [ruN0, ruN1] ruNCenterWord

@[expose] def ruW : Equiv.Perm (Fin 4060) := evalSigned [ruA0, ruA1] ruSeedWord

@[expose] def ruU : Equiv.Perm (Fin 4060) := ruW * ruZ0 * ruW⁻¹ * ruZ

@[expose] def ruH : Equiv.Perm (Fin 4060) := ruU ^ 3 * ruW

@[expose] def ruNs0 : Equiv.Perm (Fin 4060) := ruH * ruN0 * ruH⁻¹

@[expose] def ruNs1 : Equiv.Perm (Fin 4060) := ruH * ruN1 * ruH⁻¹

@[expose] def ruN : Subgroup (Equiv.Perm (Fin 4060)) := Subgroup.closure {ruNs0, ruNs1}

@[expose] def ruSGens : List (Equiv.Perm (Fin 4060)) := ruSWords.map (evalSigned [ruNs0, ruNs1])

@[expose] def ruKGens : List (Equiv.Perm (Fin 4060)) := ruKWords.map (evalSigned [ruNs0, ruNs1])

@[expose] def ruJGens : List (Equiv.Perm (Fin 4060)) := ruJWords.map (evalSigned [ruC0, ruC1])

@[expose] def ruRGens : List (Equiv.Perm (Fin 4060)) := ruRWords.map (evalSigned ruSGens)

@[expose] def ruS : Subgroup (Equiv.Perm (Fin 4060)) := Subgroup.closure {g | g ∈ ruSGens}

@[expose] def ruK : Subgroup (Equiv.Perm (Fin 4060)) := Subgroup.closure {g | g ∈ ruKGens}

@[expose] def ruJ : Subgroup (Equiv.Perm (Fin 4060)) := Subgroup.closure {g | g ∈ ruJGens}

@[expose] def ruR : Subgroup (Equiv.Perm (Fin 4060)) := Subgroup.closure {g | g ∈ ruRGens}

@[expose] def ruE : Set (Equiv.Perm (Fin 4060)) :=
  {1} ∪ {g | ∃ m ∈ ruN, g = m * ruZ * m⁻¹}

@[expose] def ruCOrbit (i : ℕ) : Array ℕ := ruPtList i

@[expose] def ruNOrbit (i : ℕ) : Array ℕ := ruPtList (4 + i)

@[expose] def ruF : Array ℕ := ruPtList 7

@[expose] def ruY : Array ℕ := ruPtList 8

@[expose] def ruCBlockList (i : ℕ) : List ℕ :=
  (List.range 12).filterMap fun k =>
    if ruCSmallPartition.getD k 0 = i then some (ruCSmallOrbit.getD k 0) else none

@[expose] def ruNBlockList (i : ℕ) : List ℕ :=
  (List.range 28).filterMap fun k =>
    if ruNSmallPartition.getD k 0 = i then some (ruNSmallOrbit.getD k 0) else none

@[expose] def ruCBlock (i : Fin 6) : Set (Fin 4060) := finSet 4060 (ruCBlockList i)

@[expose] def ruNBlock (i : Fin 7) : Set (Fin 4060) := finSet 4060 (ruNBlockList i)

@[expose] def ruChainC : RawSchreierDatum 4060 :=
  RawSchreierDatum.ofArrays 4060 (by decide) (ruField4060 1) ruCGenCount
    (by rw [ruField4060, Array.size_ofFn]; decide) (ruFinList 4060 (by decide) ruCBase)
    (by decide) (ruWordsArr ruCGenCount 7 ruCDerivations)

@[expose] def ruChainN : RawSchreierDatum 4060 :=
  RawSchreierDatum.ofArrays 4060 (by decide) (ruField4060 2) ruNGenCount
    (by rw [ruField4060, Array.size_ofFn]; decide) (ruFinList 4060 (by decide) ruNBase)
    (by decide) (ruWordsArr ruNGenCount 6 ruNDerivations)

@[expose] def ruChainJoin : RawSchreierDatum 4060 :=
  RawSchreierDatum.ofArrays 4060 (by decide) (ruField4060 3) ruJoinGenCount
    (by rw [ruField4060, Array.size_ofFn]; decide) (ruFinList 4060 (by decide) ruJoinBase)
    (by decide) (ruWordsArr ruJoinGenCount 18 ruJoinDerivations)

@[expose] def ruChainCFaithful : RawSchreierDatum 1920 :=
  RawSchreierDatum.ofArrays 1920 (by decide) (ruField1920 0) ruCFaithfulGenCount
    (by rw [ruField1920, Array.size_ofFn]; decide) (ruFinList 1920 (by decide) ruCFaithfulBase)
    (by decide) (ruWordsArr ruCFaithfulGenCount 7 ruCFaithfulDerivations)

@[expose] def ruChainS : RawSchreierDatum 1920 :=
  RawSchreierDatum.ofArrays 1920 (by decide) (ruField1920 1) ruSGenCount
    (by rw [ruField1920, Array.size_ofFn]; decide) (ruFinList 1920 (by decide) ruSBase)
    (by decide) (ruWordsArr ruSGenCount 7 ruSDerivations)

@[expose] def ruChainK : RawSchreierDatum 1920 :=
  RawSchreierDatum.ofArrays 1920 (by decide) (ruField1920 2) ruKGenCount
    (by rw [ruField1920, Array.size_ofFn]; decide) (ruFinList 1920 (by decide) ruKBase)
    (by decide) (ruWordsArr ruKGenCount 10 ruKDerivations)

@[expose] def ruChainJ : RawSchreierDatum 1920 :=
  RawSchreierDatum.ofArrays 1920 (by decide) (ruField1920 3) ruJGenCount
    (by rw [ruField1920, Array.size_ofFn]; decide) (ruFinList 1920 (by decide) ruJBase)
    (by decide) (ruWordsArr ruJGenCount 10 ruJDerivations)

@[expose] def ruChainR : RawSchreierDatum 1920 :=
  RawSchreierDatum.ofArrays 1920 (by decide) (ruField1920 4) ruRGenCount
    (by rw [ruField1920, Array.size_ofFn]; decide) (ruFinList 1920 (by decide) ruRBase)
    (by decide) (ruWordsArr ruRGenCount 7 ruRDerivations)

@[expose] def ruChainCQuotient80 : RawSchreierDatum 80 :=
  RawSchreierDatum.ofArrays 80 (by decide) ruField80 ruCQuotient80GenCount
    (by rw [ruField80, Array.size_ofFn]; decide) (ruFinList 80 (by decide) ruCQuotient80Base)
    (by decide) (ruWordsArr ruCQuotient80GenCount 8 ruCQuotient80Derivations)

@[expose] def ruTreeCount : ℕ := 593775

@[expose] def ruTreeParent (j : ℕ) : ℕ := ruHexAt ruBytesTree (6 * (j - 1)) 5

@[expose] def ruTreeGen (j : ℕ) : ℕ := ruHexAt ruBytesTree (6 * (j - 1) + 5) 1

@[expose] def ruGen (g : ℕ) : Equiv.Perm (Fin 4060) := if g = 0 then ruA0 else ruA1

@[expose] def ruTreeSet : ℕ → Set (Fin 4060)
  | 0 => {x | ruZ x = x}
  | j + 1 => if _h : ruTreeParent (j + 1) < j + 1 then
      ruGen (ruTreeGen (j + 1)) • ruTreeSet (ruTreeParent (j + 1)) else ∅
termination_by j => j
decreasing_by assumption

end CFSG.Sporadic.RuSchreier
