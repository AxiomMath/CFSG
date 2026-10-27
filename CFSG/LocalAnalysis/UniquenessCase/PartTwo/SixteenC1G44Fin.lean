module

public import CFSG.LargeExtraspecial.O62Model

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LargeExtraspecial.O62 CFSG.LargeExtraspecial.O62.Code

@[expose] def s16c1G44_tCode : ℕ := reflC 16

@[expose] def s16c1G44_goodList : List ℕ :=
  [34628444424, 34628702724, 34630287489, 34630292097, 34630295689, 34630549889, 34630811781,
    35704297345, 36778303645, 38930235781, 40001869572, 41075613980, 43220300425, 44292192008,
    45366194716, 50741475229, 51808313608, 51808571908, 51810156673, 51810161281, 51810164873,
    51810419073, 51810680965, 52884166529, 53958172829, 56110104965, 57181738756, 58255483164,
    60400169609, 61472061192, 62546063900, 67921344413]

@[expose] def s16c1G44_cond (M a₀ a₁ a₂ a₃ a₅ : ℕ) : Prop :=
  ∀ v < 64, v &&& M = v →
    qB true (actCols a₀ a₁ a₂ a₃ 16 a₅ v) = qB true v ∧
      (v < 32 → qB true (actCols a₀ a₁ a₂ a₃ 16 a₅ v ^^^ v) = false)

instance (M a₀ a₁ a₂ a₃ a₅ : ℕ) : Decidable (s16c1G44_cond M a₀ a₁ a₂ a₃ a₅) := by
  unfold s16c1G44_cond
  infer_instance

@[expose] def s16c1G44_L5 (a₀ a₁ a₂ a₃ : ℕ) : Prop :=
  ∀ a₅ < 64, s16c1G44_cond 63 a₀ a₁ a₂ a₃ a₅ → pack a₀ a₁ a₂ a₃ 16 a₅ ∈ s16c1G44_goodList

instance (a₀ a₁ a₂ a₃ : ℕ) : Decidable (s16c1G44_L5 a₀ a₁ a₂ a₃) := by
  unfold s16c1G44_L5
  infer_instance

@[expose] def s16c1G44_L3 (a₀ a₁ a₂ : ℕ) : Prop :=
  ∀ a₃ < 64, s16c1G44_cond 31 a₀ a₁ a₂ a₃ 0 → s16c1G44_L5 a₀ a₁ a₂ a₃

instance (a₀ a₁ a₂ : ℕ) : Decidable (s16c1G44_L3 a₀ a₁ a₂) := by
  unfold s16c1G44_L3
  infer_instance

@[expose] def s16c1G44_L2 (a₀ a₁ : ℕ) : Prop :=
  ∀ a₂ < 64, s16c1G44_cond 23 a₀ a₁ a₂ 0 0 → s16c1G44_L3 a₀ a₁ a₂

instance (a₀ a₁ : ℕ) : Decidable (s16c1G44_L2 a₀ a₁) := by
  unfold s16c1G44_L2
  infer_instance

@[expose] def s16c1G44_L1 (a₀ : ℕ) : Prop :=
  ∀ a₁ < 64, s16c1G44_cond 19 a₀ a₁ 0 0 0 → s16c1G44_L2 a₀ a₁

instance (a₀ : ℕ) : Decidable (s16c1G44_L1 a₀) := by
  unfold s16c1G44_L1
  infer_instance

theorem s16c1G44_F1 :
    ∀ a₀ < 64, s16c1G44_cond 17 a₀ 0 0 0 0 → s16c1G44_L1 a₀ := by
  decide +kernel

theorem s16c1G44_F2 : ∀ x ∈ s16c1G44_goodList, ∀ y ∈ s16c1G44_goodList, mul x y = mul y x →
    mul x y ∈ s16c1G44_goodList →
      x = one ∨ x = s16c1G44_tCode ∨ y = one ∨ y = s16c1G44_tCode ∨ y = x ∨
        y = mul s16c1G44_tCode x := by
  decide +kernel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
