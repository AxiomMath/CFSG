module

public import CFSG.LocalAnalysis.StandardType.GGForkNullPos

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Transfer

variable {Λ : Type} [Fintype Λ] [DecidableEq Λ]

theorem ggForkConcl_of_std {C : Matrix Λ Λ ℤ} {b c : Λ} {m : ℕ} {C₀ : Matrix (Fin m) (Fin m) ℤ}
    (e : Fin m ≃ Λ) (hC : ∀ i j, C (e i) (e j) = C₀ i j) (hF : GGForkMatrix C b c)
    (P : Fin m → Prop) (hP : ∀ i, P i → GGForkAffineCell C (e i))
    (hstd : ∀ i k, GGLeafPos C₀ i k →
      ¬ GGAttachNullPos C₀ k ∧ (¬ GGAttachNullPos C₀ i ∨ P i)) :
    ¬ GGAttachNullPos C c ∧ (¬ GGAttachNullPos C b ∨ GGForkAffineCell C b) := by
  obtain ⟨h1, h2⟩ := hstd _ _ (hF.leafPos e hC)
  refine ⟨fun h => h1 (GGAttachNullPos.of_equiv e hC (e.apply_symm_apply c).symm h), ?_⟩
  rcases h2 with h2 | h2
  · exact Or.inl fun h => h2 (GGAttachNullPos.of_equiv e hC (e.apply_symm_apply b).symm h)
  · right
    have := hP _ h2
    rwa [e.apply_symm_apply] at this

end Transfer


theorem ggNoNullPos_A2_0 : ¬ GGAttachNullPos (CartanMatrix.A 2) 0 :=
  ggAttachNullPos_false_of_cert _ _
    (fun | none => 1 | some i => ![2, 1] i)
    (by decide +kernel) (by decide +kernel)

theorem ggNoNullPos_A2_1 : ¬ GGAttachNullPos (CartanMatrix.A 2) 1 :=
  ggAttachNullPos_false_of_cert _ _
    (fun | none => 1 | some i => ![1, 2] i)
    (by decide +kernel) (by decide +kernel)

theorem ggLeafPos_A2 {i k : Fin 2} (h : GGLeafPos (CartanMatrix.A 2) i k) :
    (i = 0 ∧ k = 1) ∨ (i = 1 ∧ k = 0) := by
  revert i k
  decide +kernel

theorem ggStdCell_A2 {i k : Fin 2} (h : GGLeafPos (CartanMatrix.A 2) i k) :
    ¬ GGAttachNullPos (CartanMatrix.A 2) k ∧
      (¬ GGAttachNullPos (CartanMatrix.A 2) i ∨ False) := by
  rcases ggLeafPos_A2 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨ggNoNullPos_A2_1, Or.inl ggNoNullPos_A2_0⟩
  · exact ⟨ggNoNullPos_A2_0, Or.inl ggNoNullPos_A2_1⟩

theorem ggForkCell_A2 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ}
    (e : Fin 2 ≃ Λ) (hC : ∀ i j, C (e i) (e j) = CartanMatrix.A 2 i j) (hF : GGForkMatrix C b c) :
    ¬ GGAttachNullPos C c ∧ (¬ GGAttachNullPos C b ∨ GGForkAffineCell C b) :=
  ggForkConcl_of_std e hC hF (fun _ => False) (fun _ h => h.elim) fun _ _ h => ggStdCell_A2 h

theorem ggNoNullPos_E6_2 : ¬ GGAttachNullPos (CartanMatrix.E 6) 2 :=
  ggAttachNullPos_false_of_cert _ _
    (fun | none => -1 | some i => ![-1, -1, -2, -2, -1, 0] i)
    (by decide +kernel) (by decide +kernel)

theorem ggNoNullPos_E6_3 : ¬ GGAttachNullPos (CartanMatrix.E 6) 3 :=
  ggAttachNullPos_false_of_cert _ _
    (fun | none => -1 | some i => ![-2, -3, -4, -6, -4, -2] i)
    (by decide +kernel) (by decide +kernel)

theorem ggNoNullPos_E6_4 : ¬ GGAttachNullPos (CartanMatrix.E 6) 4 :=
  ggAttachNullPos_false_of_cert _ _
    (fun | none => -1 | some i => ![0, -1, -1, -2, -2, -1] i)
    (by decide +kernel) (by decide +kernel)

theorem ggNoNullPos_E6_0 : ¬ GGAttachNullPos (CartanMatrix.E 6) 0 :=
  ggAttachNullPos_false_of_cert _ _
    (fun | none => 1 | some i => ![2, 2, 3, 4, 3, 2] i)
    (by decide +kernel) (by decide +kernel)

theorem ggNoNullPos_E6_5 : ¬ GGAttachNullPos (CartanMatrix.E 6) 5 :=
  ggAttachNullPos_false_of_cert _ _
    (fun | none => 1 | some i => ![2, 2, 3, 4, 3, 2] i)
    (by decide +kernel) (by decide +kernel)

theorem ggLeafPos_E6 {i k : Fin 6} (h : GGLeafPos (CartanMatrix.E 6) i k) :
    (i = 0 ∧ k = 2) ∨ (i = 1 ∧ k = 3) ∨ (i = 5 ∧ k = 4) := by
  revert i k
  decide +kernel

theorem ggStdCell_E6 {i k : Fin 6} (h : GGLeafPos (CartanMatrix.E 6) i k) :
    ¬ GGAttachNullPos (CartanMatrix.E 6) k ∧
      (¬ GGAttachNullPos (CartanMatrix.E 6) i ∨ i = 1) := by
  rcases ggLeafPos_E6 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨ggNoNullPos_E6_2, Or.inl ggNoNullPos_E6_0⟩
  · exact ⟨ggNoNullPos_E6_3, Or.inr rfl⟩
  · exact ⟨ggNoNullPos_E6_4, Or.inl ggNoNullPos_E6_5⟩

theorem ggForkCell_E6 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ}
    (e : Fin 6 ≃ Λ) (hC : ∀ i j, C (e i) (e j) = CartanMatrix.E 6 i j)
    (hF : GGForkMatrix C b c) :
    ¬ GGAttachNullPos C c ∧ (¬ GGAttachNullPos C b ∨ GGForkAffineCell C b) :=
  ggForkConcl_of_std e hC hF (fun i => i = 1)
    (fun i hi => by
      subst hi
      exact Or.inl ⟨e, hC, rfl⟩)
    fun _ _ h => ggStdCell_E6 h

theorem ggNoNullPos_E7_2 : ¬ GGAttachNullPos (CartanMatrix.E 7) 2 :=
  ggAttachNullPos_false_of_cert _ _
    (fun | none => -1 | some i => ![-1, -1, -2, -2, -1, 0, 0] i)
    (by decide +kernel) (by decide +kernel)

theorem ggNoNullPos_E7_3 : ¬ GGAttachNullPos (CartanMatrix.E 7) 3 :=
  ggAttachNullPos_false_of_cert _ _
    (fun | none => -2 | some i => ![2, -2, -1, -4, -3, -2, -1] i)
    (by decide +kernel) (by decide +kernel)

theorem ggNoNullPos_E7_5 : ¬ GGAttachNullPos (CartanMatrix.E 7) 5 :=
  ggAttachNullPos_false_of_cert _ _
    (fun | none => -1 | some i => ![0, -1, -1, -2, -2, -2, -1] i)
    (by decide +kernel) (by decide +kernel)

theorem ggNoNullPos_E7_1 : ¬ GGAttachNullPos (CartanMatrix.E 7) 1 :=
  ggAttachNullPos_false_of_cert _ _
    (fun | none => -1 | some i => ![-1, -2, -2, -3, -2, -1, 0] i)
    (by decide +kernel) (by decide +kernel)

theorem ggNoNullPos_E7_6 : ¬ GGAttachNullPos (CartanMatrix.E 7) 6 :=
  ggAttachNullPos_false_of_cert _ _
    (fun | none => 2 | some i => ![2, 3, 4, 6, 5, 4, 3] i)
    (by decide +kernel) (by decide +kernel)

theorem ggLeafPos_E7 {i k : Fin 7} (h : GGLeafPos (CartanMatrix.E 7) i k) :
    (i = 0 ∧ k = 2) ∨ (i = 1 ∧ k = 3) ∨ (i = 6 ∧ k = 5) := by
  revert i k
  decide +kernel

theorem ggStdCell_E7 {i k : Fin 7} (h : GGLeafPos (CartanMatrix.E 7) i k) :
    ¬ GGAttachNullPos (CartanMatrix.E 7) k ∧
      (¬ GGAttachNullPos (CartanMatrix.E 7) i ∨ i = 0) := by
  rcases ggLeafPos_E7 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨ggNoNullPos_E7_2, Or.inr rfl⟩
  · exact ⟨ggNoNullPos_E7_3, Or.inl ggNoNullPos_E7_1⟩
  · exact ⟨ggNoNullPos_E7_5, Or.inl ggNoNullPos_E7_6⟩

theorem ggForkCell_E7 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ}
    (e : Fin 7 ≃ Λ) (hC : ∀ i j, C (e i) (e j) = CartanMatrix.E 7 i j)
    (hF : GGForkMatrix C b c) :
    ¬ GGAttachNullPos C c ∧ (¬ GGAttachNullPos C b ∨ GGForkAffineCell C b) :=
  ggForkConcl_of_std e hC hF (fun i => i = 0)
    (fun i hi => by
      subst hi
      exact Or.inr <| Or.inl ⟨e, hC, rfl⟩)
    fun _ _ h => ggStdCell_E7 h

theorem ggNoNullPos_E8_2 : ¬ GGAttachNullPos (CartanMatrix.E 8) 2 :=
  ggAttachNullPos_false_of_cert _ _
    (fun | none => -1 | some i => ![-1, -1, -2, -2, -1, 0, 0, 0] i)
    (by decide +kernel) (by decide +kernel)

theorem ggNoNullPos_E8_3 : ¬ GGAttachNullPos (CartanMatrix.E 8) 3 :=
  ggAttachNullPos_false_of_cert _ _
    (fun | none => -3 | some i => ![-2, -3, -4, -6, -2, 2, 6, 3] i)
    (by decide +kernel) (by decide +kernel)

theorem ggNoNullPos_E8_6 : ¬ GGAttachNullPos (CartanMatrix.E 8) 6 :=
  ggAttachNullPos_false_of_cert _ _
    (fun | none => -1 | some i => ![0, -1, -1, -2, -2, -2, -2, -1] i)
    (by decide +kernel) (by decide +kernel)

theorem ggNoNullPos_E8_0 : ¬ GGAttachNullPos (CartanMatrix.E 8) 0 :=
  ggAttachNullPos_false_of_cert _ _
    (fun | none => -1 | some i => ![-2, -2, -3, -4, -3, -2, -1, 0] i)
    (by decide +kernel) (by decide +kernel)

theorem ggNoNullPos_E8_1 : ¬ GGAttachNullPos (CartanMatrix.E 8) 1 :=
  ggAttachNullPos_false_of_cert _ _
    (fun | none => -1 | some i => ![-1, -2, -2, -3, -2, -1, 0, 0] i)
    (by decide +kernel) (by decide +kernel)

theorem ggLeafPos_E8 {i k : Fin 8} (h : GGLeafPos (CartanMatrix.E 8) i k) :
    (i = 0 ∧ k = 2) ∨ (i = 1 ∧ k = 3) ∨ (i = 7 ∧ k = 6) := by
  revert i k
  decide +kernel

theorem ggStdCell_E8 {i k : Fin 8} (h : GGLeafPos (CartanMatrix.E 8) i k) :
    ¬ GGAttachNullPos (CartanMatrix.E 8) k ∧
      (¬ GGAttachNullPos (CartanMatrix.E 8) i ∨ i = 7) := by
  rcases ggLeafPos_E8 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨ggNoNullPos_E8_2, Or.inl ggNoNullPos_E8_0⟩
  · exact ⟨ggNoNullPos_E8_3, Or.inl ggNoNullPos_E8_1⟩
  · exact ⟨ggNoNullPos_E8_6, Or.inr rfl⟩

theorem ggForkCell_E8 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ}
    (e : Fin 8 ≃ Λ) (hC : ∀ i j, C (e i) (e j) = CartanMatrix.E 8 i j)
    (hF : GGForkMatrix C b c) :
    ¬ GGAttachNullPos C c ∧ (¬ GGAttachNullPos C b ∨ GGForkAffineCell C b) :=
  ggForkConcl_of_std e hC hF (fun i => i = 7)
    (fun i hi => by
      subst hi
      exact Or.inr <| Or.inr <| Or.inl ⟨e, hC, rfl⟩)
    fun _ _ h => ggStdCell_E8 h

theorem ggNoNullPos_F4_1 : ¬ GGAttachNullPos CartanMatrix.F₄ 1 :=
  ggAttachNullPos_false_of_cert _ _
    (fun | none => -1 | some i => ![-1, -2, -1, 0] i)
    (by decide +kernel) (by decide +kernel)

theorem ggNoNullPos_F4_2 : ¬ GGAttachNullPos CartanMatrix.F₄ 2 :=
  ggAttachNullPos_false_of_cert _ _
    (fun | none => -1 | some i => ![0, -2, -2, -1] i)
    (by decide +kernel) (by decide +kernel)

theorem ggLeafPos_F4 {i k : Fin 4} (h : GGLeafPos CartanMatrix.F₄ i k) :
    (i = 0 ∧ k = 1) ∨ (i = 3 ∧ k = 2) := by
  revert i k
  decide +kernel

theorem ggStdCell_F4 {i k : Fin 4} (h : GGLeafPos CartanMatrix.F₄ i k) :
    ¬ GGAttachNullPos CartanMatrix.F₄ k ∧
      (¬ GGAttachNullPos CartanMatrix.F₄ i ∨ (i = 0 ∨ i = 3)) := by
  rcases ggLeafPos_F4 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨ggNoNullPos_F4_1, Or.inr (Or.inl rfl)⟩
  · exact ⟨ggNoNullPos_F4_2, Or.inr (Or.inr rfl)⟩

theorem ggForkCell_F4 {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ}
    (e : Fin 4 ≃ Λ) (hC : ∀ i j, C (e i) (e j) = CartanMatrix.F₄ i j)
    (hF : GGForkMatrix C b c) :
    ¬ GGAttachNullPos C c ∧ (¬ GGAttachNullPos C b ∨ GGForkAffineCell C b) :=
  ggForkConcl_of_std (C₀ := CartanMatrix.F₄) e hC hF (fun i => i = 0 ∨ i = 3)
    (fun i hi => by
      rcases hi with rfl | rfl
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨e, hC, rfl⟩
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨e, hC, rfl⟩)
    fun _ _ h => ggStdCell_F4 h

theorem ggNoNullPos_F4T_1 : ¬ GGAttachNullPos (Matrix.transpose CartanMatrix.F₄) 1 :=
  ggAttachNullPos_false_of_cert _ _
    (fun | none => -1 | some i => ![-1, -2, -2, -1] i)
    (by decide +kernel) (by decide +kernel)

theorem ggNoNullPos_F4T_2 : ¬ GGAttachNullPos (Matrix.transpose CartanMatrix.F₄) 2 :=
  ggAttachNullPos_false_of_cert _ _
    (fun | none => -1 | some i => ![0, -1, -2, -1] i)
    (by decide +kernel) (by decide +kernel)

theorem ggLeafPos_F4T {i k : Fin 4} (h : GGLeafPos (Matrix.transpose CartanMatrix.F₄) i k) :
    (i = 0 ∧ k = 1) ∨ (i = 3 ∧ k = 2) := by
  revert i k
  decide +kernel

theorem ggStdCell_F4T {i k : Fin 4} (h : GGLeafPos (Matrix.transpose CartanMatrix.F₄) i k) :
    ¬ GGAttachNullPos (Matrix.transpose CartanMatrix.F₄) k ∧
      (¬ GGAttachNullPos (Matrix.transpose CartanMatrix.F₄) i ∨ (i = 0 ∨ i = 3)) := by
  rcases ggLeafPos_F4T h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨ggNoNullPos_F4T_1, Or.inr (Or.inl rfl)⟩
  · exact ⟨ggNoNullPos_F4T_2, Or.inr (Or.inr rfl)⟩

theorem ggForkCell_F4T {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ}
    (e : Fin 4 ≃ Λ) (hC : ∀ i j, C (e i) (e j) = CartanMatrix.F₄ j i)
    (hF : GGForkMatrix C b c) :
    ¬ GGAttachNullPos C c ∧ (¬ GGAttachNullPos C b ∨ GGForkAffineCell C b) :=
  ggForkConcl_of_std (C₀ := (Matrix.transpose CartanMatrix.F₄)) e hC hF (fun i => i = 0 ∨ i = 3)
    (fun i hi => by
      rcases hi with rfl | rfl
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨e, hC, rfl⟩
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨e, hC, rfl⟩)
    fun _ _ h => ggStdCell_F4T h

end CFSG.StandardType
