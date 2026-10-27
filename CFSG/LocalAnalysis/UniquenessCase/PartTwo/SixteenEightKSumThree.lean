module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKCtx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Main

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_false_of_sum_three (h : S16kBase D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hq : CFSG.Open.IsQuasisimple ↥(lBar V₀ V hV L)) {n : ℕ}
    (hfam :
      (IsSLn ↥(lBar V₀ V hV L) n 1 ∧
        SumOfNat (fun H U Z => BinaryNaturalSL H U Z n 1) (lBar V₀ V hV L)
          (commSub ⊤ (lBar V₀ V hV L)) (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 3) ∨
      (IsSpn ↥(lBar V₀ V hV L) n 1 ∧
        SumOfNat (fun H U Z => NatSpn H U Z n 1) (lBar V₀ V hV L)
          (commSub ⊤ (lBar V₀ V hV L)) (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 3) ∨
      (IsOmegaPlus ↥(lBar V₀ V hV L) n 1 ∧
        SumOfNat (fun H U Z => NatOmegaPlus H U Z n 1) (lBar V₀ V hV L)
          (commSub ⊤ (lBar V₀ V hV L)) (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 3) ∨
      (IsOmegaMinus ↥(lBar V₀ V hV L) n 1 ∧
        SumOfNat (fun H U Z => NatOmegaMinus H U Z n 1) (lBar V₀ V hV L)
          (commSub ⊤ (lBar V₀ V hV L)) (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 3) ∨
      (IsAlt ↥(lBar V₀ V hV L) n ∧
        SumOfNat (fun H U Z => AlternatingNatural H U Z n) (lBar V₀ V hV L)
          (commSub ⊤ (lBar V₀ V hV L)) (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 3))
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L), ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓ normalizer
          ((lBar V₀ V hV L : Subgroup (MulAut (Vtil V₀ V hV))) : Set (MulAut (Vtil V₀ V hV))),
        I₂ = I₁.map g.toMonoidHom) : False :=
  (h.toRowCtx hq).false_of_sum_three_nat hGA hSchur ⟨n, hfam⟩ htrans

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
