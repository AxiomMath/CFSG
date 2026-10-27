module

public import Certificates.Data.HuppertU38.Model
public import CFSG.RankThree.PartOne.KS.PKitLines

@[expose] public section

open CFSG.RankThree.PartTwo.Sec4.Item434U38 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.RankThree.Native CFSG.RankThree.PartOne

namespace Certificates

abbrev Cert188002Field : Prop :=
  (∀ a b c : GF64, a + b + c = a + (b + c)) ∧ (∀ a : GF64, 0 + a = a) ∧
    (∀ a : GF64, -a + a = 0) ∧ (∀ a b c : GF64, a * b * c = a * (b * c)) ∧
    (∀ a b : GF64, a * b = b * a) ∧ (∀ a : GF64, 1 * a = a) ∧
    (∀ a : GF64, a ≠ 0 → a * a⁻¹ = 1) ∧ ((0 : GF64)⁻¹ = 0) ∧
    (∀ a b c : GF64, a * (b + c) = a * b + a * c) ∧ (∃ a b : GF64, a ≠ b)

abbrev Cert188002Points : Prop :=
  (∀ i : Fin 513, NormalizedV (ptsV i) ∧ Iso3 (ptsV i 0) (ptsV i 1) (ptsV i 2)) ∧
    (∀ i : Fin 513, idxTable[vcode (ptsV i)]! = i.val) ∧
    (∀ a b c : GF64, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) → Iso3 a b c →
      ptsV (ptIdx idxTable[vcode (normV3 a b c)]!) = normV3 a b c)

abbrev Cert188002Roots : Prop :=
  ∀ k : Fin 6, rootB k + (rootB k).conj8 + rootA k * (rootA k).conj8 = 0

abbrev Cert188002Gens : Prop :=
  (∀ k : Fin 7, SpecialUnitaryM (genMat k)) ∧ (∀ (k : Fin 7) (j : Fin 513), GenAct k j)

abbrev Cert188002Chain : Prop :=
  (rawChainOK 513 (strong3.extract 0 7) strong3 base3 words3 1 = true ∧
    rawOrbitSizes 513 strong3 base3 = [513, 512, 7, 3]) ∧
  allLt 9 (fun k => validA 513 gensO[k]!) = true ∧
  allLt 2 (fun a => allLt 7 fun i =>
    siftA 513 (rawLevels 513 strong3 base3) base3 0 (conjA 513 gensO[7 + a]! gensO[i]!) &&
      siftA 513 (rawLevels 513 strong3 base3) base3 0 (conjInvA 513 gensO[7 + a]! gensO[i]!)) =
    true



end Certificates
