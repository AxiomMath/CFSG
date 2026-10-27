module

public import CFSG.RankThree.PartTwo.Sec21.FF81Sec36Defs
public import CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434KitWreath
public import Certificates.Data.RudvalisFF81Sp6RefS

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp6RefS

open CFSG.RankThree.PartTwo.Sec21.FF79 CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)
open CFSG.Quasithin.G2U

@[expose] def nGrp (z : Fin 3 → H6) (t f0 sw : H6) : Subgroup H6 :=
  Subgroup.closure {z 0, f0, sw, t}

@[expose] def repSE (f2 sw : H6) : Fin 5 → H6 := ![f2, f2, sw, sw, sw]

@[expose] def repLE (z : Fin 3 → H6) : Fin 5 → H6 :=
  ![z 0, z 0 * z 1, z 2, z 0 * z 1, z 0 * z 1 * z 2]

@[expose] def Sp6RefSAt (z : Fin 3 → H6) (t f0 f2 sw c0 c1 : H6) : Prop :=
  (∀ a < 6, ∀ b < 6, ∀ c < 6, [a / 2, b / 2, c / 2].Nodup → ∃ n ∈ nGrp z t f0 sw,
    mat6 (n * z 0 * n⁻¹) = dec6 (l1C.getD a []) ∧ mat6 (n * z 1 * n⁻¹) = dec6 (l1C.getD b []) ∧
      mat6 (n * z 2 * n⁻¹) = dec6 (l1C.getD c [])) ∧
  Subgroup.closure {c0, c1} = Cen (z 0 * z 1 * z 2) ∧
  (∀ k : Fin 5, Nat.card (Op 2 (Cen (repSE f2 sw k) ⊓ Cen (repLE z k))) = ![8, 2, 8, 2, 8] k) ∧
  (∀ k : Fin 5, (k = 0 ∨ k = 2) →
    (∀ u ∈ Op 2 (Cen (repSE f2 sw k) ⊓ Cen (repLE z k)),
      ∀ v ∈ Op 2 (Cen (repSE f2 sw k) ⊓ Cen (repLE z k)), u * v = v * u) ∧
    ∀ u ∈ Op 2 (Cen (repSE f2 sw k) ⊓ Cen (repLE z k)), u * u = 1) ∧
  (∃ u ∈ Op 2 (Cen (repSE f2 sw 4) ⊓ Cen (repLE z 4)),
    ∃ v ∈ Op 2 (Cen (repSE f2 sw 4) ⊓ Cen (repLE z 4)), u * v ≠ v * u) ∧
  (∀ s ∈ nGrp z t f0 sw, orderOf s = 2 → ∀ x y : Fin 3 → ZMod 3, x ≠ 0 →
    (∀ c : ZMod 3, y ≠ c • x) → s * vecElt z x = vecElt z x * s →
      s * vecElt z y = vecElt z y * s → ∃ n : H6, ∃ k : Fin 5,
        n * repSE f2 sw k * n⁻¹ = s ∧ n * repLE z k * n⁻¹ = vecElt z x ∧
          ![1, 2, 1, 2, 3] k = torWt x) ∧
  ∃ g : H6, t = g * (z 0 * z 1) * g⁻¹

@[expose] def Sp6RefSFacts : Prop :=
  ((∃ g : H6, mat6 g = dec6 sw01C) ∧ (∃ g : H6, mat6 g = dec6 c7Gen0) ∧
    ∃ g : H6, mat6 g = dec6 c7Gen1) ∧
  (∀ (z : Fin 3 → H6) (t f0 f2 sw c0 c1 : H6), (∀ i, mat6 (z i) = dec6 (zCode i)) →
    mat6 t = dec6 tCode → mat6 f0 = dec6 fl0C → mat6 f2 = dec6 fl2C → mat6 sw = dec6 sw01C →
    mat6 c0 = dec6 c7Gen0 → mat6 c1 = dec6 c7Gen1 → Sp6RefSAt z t f0 f2 sw c0 c1) ∧
  closureOK (c7P.map Prod.fst) (closureT (c7P.map Prod.fst)) 648 = true

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp6RefS

end
