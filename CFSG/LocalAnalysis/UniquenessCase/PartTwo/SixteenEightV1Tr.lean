module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private noncomputable def s16e_case2At (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V)
    (V₁ : Subgroup G) : Prop :=
  IsSym ↥(kBar D.M V₀ V hV L) 3 ∧
    (∃ L₀ : Subgroup (MulAut (Vtil V₀ V hV)),
      IsInternalDirect (kBar D.M V₀ V hV L) L₀ (Mbar D.M V₀ V hV) ∧
        ((∃ n : ℕ, 5 ≤ n ∧ n ≤ 11 ∧ IsSym ↥L₀ n ∧ UC22.IsAlt ↥(lBar V₀ V hV L) n ∧
            SumOfNat (fun H U Z => AlternatingNatural H U Z n)
              (barSub V₁ V hV L) (⊤ : Subgroup (Vtil V₁ V hV)) ⊥ 2) ∨
          (∃ m : ℕ, 3 ≤ m ∧ m ≤ 5 ∧ IsLn ↥L₀ m 1 ∧ IsLn ↥(lBar V₀ V hV L) m 1 ∧
            SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1)
              (barSub V₁ V hV L) (⊤ : Subgroup (Vtil V₁ V hV)) ⊥ 2) ∨
          (IsSpn ↥L₀ 6 1 ∧ IsSpn ↥(lBar V₀ V hV L) 6 1 ∧
            SumOfNat (fun H U Z => NatSpn H U Z 6 1)
              (barSub V₁ V hV L) (⊤ : Subgroup (Vtil V₁ V hV)) ⊥ 2) ∨
          (IsOMinus ↥L₀ 6 1 ∧ IsOmegaMinus ↥(lBar V₀ V hV L) 6 1 ∧
            SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 1)
              (barSub V₁ V hV L) (⊤ : Subgroup (Vtil V₁ V hV)) ⊥ 2) ∨
          (IsOMinus ↥L₀ 8 1 ∧ IsOmegaMinus ↥(lBar V₀ V hV L) 8 1 ∧
            SumOfNat (fun H U Z => NatOmegaMinus H U Z 8 1)
              (barSub V₁ V hV L) (⊤ : Subgroup (Vtil V₁ V hV)) ⊥ 2))) ∧
    D.sig = {3}

private noncomputable def s16e_case5At (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V)
    (V₁ : Subgroup G) : Prop :=
  Nonempty (↥(fstarBar D.M V₀ V hV) ≃* (Multiplicative (ZMod 3) × ↥(lBar V₀ V hV L))) ∧
    IsOmegaPlus ↥(lBar V₀ V hV L) 4 2 ∧
    NatOmegaPlus (barSub V₁ V hV L) (⊤ : Subgroup (Vtil V₁ V hV)) ⊥ 4 2 ∧ D.sig = {3}

theorem s16e_case168_2Star_iff (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V)
    (h : v1Sub D.M V₀ V hV L = V₀) :
    Case168_2Star D V₀ V hV L ↔ Case168_2 D V₀ V hV L := by
  have h1 : Case168_2Star D V₀ V hV L ↔ s16e_case2At D V₀ V L hV (v1Sub D.M V₀ V hV L) :=
    Iff.rfl
  have h2 : Case168_2 D V₀ V hV L ↔ s16e_case2At D V₀ V L hV V₀ := Iff.rfl
  rw [h1, h2, h]

theorem s16e_case168_5Star_iff (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V)
    (h : v1Sub D.M V₀ V hV L = V₀) :
    Case168_5Star D V₀ V hV L ↔ Case168_5 D V₀ V hV L := by
  have h1 : Case168_5Star D V₀ V hV L ↔ s16e_case5At D V₀ V L hV (v1Sub D.M V₀ V hV L) :=
    Iff.rfl
  have h2 : Case168_5 D V₀ V hV L ↔ s16e_case5At D V₀ V L hV V₀ := Iff.rfl
  rw [h1, h2, h]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
