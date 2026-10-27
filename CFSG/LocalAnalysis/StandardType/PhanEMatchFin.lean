module

public import CFSG.LocalAnalysis.StandardType.PhanEMatchCode
public import CFSG.LocalAnalysis.StandardType.PhanEReduction

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Match

open CFSG.ClassicalInvolution.Phan.PhanE CFSG.ClassicalInvolution.Phan.PhanE.PhanCode

@[expose] def codes1 : List PhanCode := [.a1far, .a1moved]

@[expose] def codes2 : List PhanCode :=
  [.a2chamber, .a2panel, .a2coll, .a2pol, .exchA1A1] ++
    (codes1.flatMap fun a => codes1.map fun b => .prod a b)

@[expose] def codes3 : List PhanCode :=
  [.a3_1111, .a3_211, .a3_121, .a3_22p, .a3_22x, .a3_13c, .a3_13p, .a3_4c, .a3_4p, .exchA2A1] ++
    (codes2.flatMap fun a => codes1.map fun b => .prod a b)

@[expose] def perms2 : List (Fin 2 → Fin 2) := [![0, 1], ![1, 0]]

@[expose] def perms3 : List (Fin 3 → Fin 3) :=
  [![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]]

@[expose] def cx2 (e01 : Bool) (i j : Fin 2) : ℕ :=
  if i.val = j.val then 1 else if e01 then 3 else 2

@[expose] def cx3 (e01 e12 e02 : Bool) (i j : Fin 3) : ℕ :=
  if i.val = j.val then 1
  else if (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) then (if e01 then 3 else 2)
  else if (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) then (if e12 then 3 else 2)
  else if e02 then 3 else 2

@[expose] def Valid2 (e01 : Bool) (I : Fin 2 → Bool) (π : Fin 2 → Fin 2) : Prop :=
  (∀ i, I i = true → I (π i) = true) ∧ (∀ i, I i = true → π (π i) = i) ∧
    ∀ i j, I i = true → I j = true → cx2 e01 (π i) (π j) = cx2 e01 i j

@[expose] def Valid3 (e01 e12 e02 : Bool) (I : Fin 3 → Bool) (π : Fin 3 → Fin 3) : Prop :=
  ¬ (e01 = true ∧ e12 = true ∧ e02 = true) ∧
    (∀ i, I i = true → I (π i) = true) ∧ (∀ i, I i = true → π (π i) = i) ∧
      ∀ i j, I i = true → I j = true → cx3 e01 e12 e02 (π i) (π j) = cx3 e01 e12 e02 i j

@[expose] def Match2 (e01 : Bool) (I : Fin 2 → Bool) (π : Fin 2 → Fin 2) (c : PhanCode)
    (σ : Fin 2 → Fin 2) : Prop :=
  c.rank = 2 ∧ (∀ i j : Fin 2, i ≠ j → cx2 e01 (σ i) (σ j) = c.coxN i j) ∧
    (∀ i : Fin 2, I (σ i) = c.coreN i) ∧
      ∀ i : Fin 2, I (σ i) = true → ∃ j : Fin 2, j.val = c.permN i ∧ σ j = π (σ i)

@[expose] def Match3 (e01 e12 e02 : Bool) (I : Fin 3 → Bool) (π : Fin 3 → Fin 3) (c : PhanCode)
    (σ : Fin 3 → Fin 3) : Prop :=
  c.rank = 3 ∧ (∀ i j : Fin 3, i ≠ j → cx3 e01 e12 e02 (σ i) (σ j) = c.coxN i j) ∧
    (∀ i : Fin 3, I (σ i) = c.coreN i) ∧
      ∀ i : Fin 3, I (σ i) = true → ∃ j : Fin 3, j.val = c.permN i ∧ σ j = π (σ i)

instance (e01 : Bool) (I : Fin 2 → Bool) (π : Fin 2 → Fin 2) (c : PhanCode) (σ : Fin 2 → Fin 2) :
    Decidable (Match2 e01 I π c σ) := by
  unfold Match2; infer_instance

instance (e01 e12 e02 : Bool) (I : Fin 3 → Bool) (π : Fin 3 → Fin 3) (c : PhanCode)
    (σ : Fin 3 → Fin 3) : Decidable (Match3 e01 e12 e02 I π c σ) := by
  unfold Match3; infer_instance

instance (e01 : Bool) (I : Fin 2 → Bool) (π : Fin 2 → Fin 2) : Decidable (Valid2 e01 I π) := by
  unfold Valid2; infer_instance

instance (e01 e12 e02 : Bool) (I : Fin 3 → Bool) (π : Fin 3 → Fin 3) :
    Decidable (Valid3 e01 e12 e02 I π) := by
  unfold Valid3; infer_instance

theorem classify2 : ∀ (e01 : Bool) (I : Fin 2 → Bool) (π : Fin 2 → Fin 2), Valid2 e01 I π →
    ∃ c ∈ codes2, ∃ σ ∈ perms2, Match2 e01 I π c σ := by
  decide +kernel

theorem classify3 : ∀ (e01 e12 e02 : Bool) (I : Fin 3 → Bool) (π : Fin 3 → Fin 3),
    Valid3 e01 e12 e02 I π → ∃ c ∈ codes3, ∃ σ ∈ perms3, Match3 e01 e12 e02 I π c σ := by
  decide +kernel

theorem perms2_injective : ∀ σ ∈ perms2, Function.Injective σ := by decide +kernel

theorem perms3_injective : ∀ σ ∈ perms3, Function.Injective σ := by decide +kernel

theorem perms2_surjective : ∀ σ ∈ perms2, Function.Surjective σ := by decide +kernel

theorem perms3_surjective : ∀ σ ∈ perms3, Function.Surjective σ := by decide +kernel

end CFSG.ClassicalInvolution.Phan.PhanE.Match

end
