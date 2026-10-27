module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Enc
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.C48PfFourModPfGrp
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCHeis
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitG2Cert
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open Matrix CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.C48Pf.FMod

namespace Stellmacher.PU.L3YC

@[expose] def blk4 (y : Fin 3 → ZMod 2) (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, y 0, y 1, y 2;
     0, A 0 0, A 0 1, A 0 2;
     0, A 1 0, A 1 1, A 1 2;
     0, A 2 0, A 2 1, A 2 2]

theorem det_blk4 (y : Fin 3 → ZMod 2) (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    (blk4 y A).det = A.det := by
  rw [Matrix.det_succ_column_zero]
  simp [Fin.sum_univ_succ, blk4, Matrix.det_fin_three]

@[expose] def ptStab : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2)) where
  carrier := {M | (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ (Pi.single 0 1 : Fin 4 → ZMod 2) =
    Pi.single 0 1}
  one_mem' := by
    show ((1 : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
      (Pi.single 0 1 : Fin 4 → ZMod 2) = Pi.single 0 1
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  mul_mem' := by
    intro M N hM hN
    show ((M * N : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
      (Pi.single 0 1 : Fin 4 → ZMod 2) = Pi.single 0 1
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
    have hN' : (N : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ (Pi.single 0 1 : Fin 4 → ZMod 2) =
      Pi.single 0 1 := hN
    have hM' : (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ (Pi.single 0 1 : Fin 4 → ZMod 2) =
      Pi.single 0 1 := hM
    rw [hN', hM']
  inv_mem' := by
    intro M hM
    have hM' : (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ (Pi.single 0 1 : Fin 4 → ZMod 2) =
      Pi.single 0 1 := hM
    show ((M⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
      (Pi.single 0 1 : Fin 4 → ZMod 2) = Pi.single 0 1
    have h1 : ((M⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
        ((M : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ (Pi.single 0 1 : Fin 4 → ZMod 2)) =
        (Pi.single 0 1 : Fin 4 → ZMod 2) := by
      rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    rwa [hM'] at h1

theorem mem_ptStab_iff (M : SpecialLinearGroup (Fin 4) (ZMod 2)) :
    M ∈ ptStab ↔ ∀ i : Fin 4, (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) i 0 =
      if i = 0 then 1 else 0 := by
  constructor
  · intro h i
    have := congrFun h i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  · intro h
    show _ = _
    ext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, h]

theorem exists_mat3 : ∀ u v : Fin 3 → ZMod 2, u ≠ 0 → v ≠ 0 →
    ∃ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.det = 1 ∧ A *ᵥ u = v := by
  decide +kernel

theorem exists_dot : ∀ u : Fin 3 → ZMod 2, u ≠ 0 → ∀ c : ZMod 2,
    ∃ y : Fin 3 → ZMod 2, y ⬝ᵥ u = c := by
  decide +kernel

theorem tail_zero {w : Fin 4 → ZMod 2} (h : (fun i : Fin 3 => w i.succ) = 0) :
    w = 0 ∨ w = Pi.single 0 1 := by
  have h1 : w 1 = 0 := congrFun h 0
  have h2 : w 2 = 0 := congrFun h 1
  have h3 : w 3 = 0 := congrFun h 2
  have h0 : w 0 = 0 ∨ w 0 = 1 := by
    generalize w 0 = t
    revert t
    decide
  rcases h0 with e | e
  · left
    ext i
    fin_cases i <;> simp [*]
  · right
    ext i
    fin_cases i <;> simp [*]

theorem ptStab_trans (w w' : Fin 4 → ZMod 2) (hw0 : w ≠ 0) (hw1 : w ≠ Pi.single 0 1)
    (hw0' : w' ≠ 0) (hw1' : w' ≠ Pi.single 0 1) :
    ∃ a ∈ ptStab, (a : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ w = w' := by
  have hwb : (fun i : Fin 3 => w i.succ) ≠ 0 := fun h => (tail_zero h).elim hw0 hw1
  have hwb' : (fun i : Fin 3 => w' i.succ) ≠ 0 := fun h => (tail_zero h).elim hw0' hw1'
  obtain ⟨A, hAdet, hA⟩ := exists_mat3 _ _ hwb hwb'
  obtain ⟨y, hy⟩ := exists_dot _ hwb (w' 0 + w 0)
  let a : SpecialLinearGroup (Fin 4) (ZMod 2) := ⟨blk4 y A, by rw [det_blk4]; exact hAdet⟩
  have ha : (a : Matrix (Fin 4) (Fin 4) (ZMod 2)) = blk4 y A := rfl
  refine ⟨a, ?_, ?_⟩
  · rw [mem_ptStab_iff, ha]
    intro i
    fin_cases i <;> simp [blk4]
  · rw [ha]
    have hy' : y 0 * w 1 + y 1 * w 2 + y 2 * w 3 = w' 0 + w 0 := by
      simpa [dotProduct, Fin.sum_univ_three] using hy
    have hA0 := congrFun hA 0
    have hA1 := congrFun hA 1
    have hA2 := congrFun hA 2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at hA0 hA1 hA2
    ext i
    fin_cases i
    · simp [blk4, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
      have e : w 0 + y 0 * w 1 + y 1 * w 2 + y 2 * w 3 =
          w 0 + (y 0 * w 1 + y 1 * w 2 + y 2 * w 3) := by ring
      rw [e, hy', add_comm (w' 0), ← add_assoc, Heis.zmod2_add_self, zero_add]
    · simpa [blk4, Matrix.mulVec, dotProduct, Fin.sum_univ_four] using hA0
    · simpa [blk4, Matrix.mulVec, dotProduct, Fin.sum_univ_four] using hA1
    · simpa [blk4, Matrix.mulVec, dotProduct, Fin.sum_univ_four] using hA2

theorem sl_mulVec_mul {n : ℕ} (M N : SpecialLinearGroup (Fin n) (ZMod 2)) (v : Fin n → ZMod 2) :
    ((M * N : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v =
      (M : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ ((N : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]

theorem sl_mulVec_inv_self {n : ℕ} (M : SpecialLinearGroup (Fin n) (ZMod 2))
    (v : Fin n → ZMod 2) :
    ((M⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      ((M : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v) = v := by
  rw [← sl_mulVec_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem ptStab_double (g h : SpecialLinearGroup (Fin 4) (ZMod 2)) (hg : g ∉ ptStab) :
    h ∈ ptStab ∨ ∃ a ∈ ptStab, ∃ b ∈ ptStab, h = a * g * b := by
  by_cases hh : h ∈ ptStab
  · exact Or.inl hh
  right
  have he0 : (Pi.single 0 1 : Fin 4 → ZMod 2) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  have hne : ∀ M : SpecialLinearGroup (Fin 4) (ZMod 2), M ∉ ptStab →
      ((M : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ (Pi.single 0 1 : Fin 4 → ZMod 2) ≠ 0 ∧
        (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ (Pi.single 0 1 : Fin 4 → ZMod 2) ≠
          Pi.single 0 1) := by
    intro M hM
    refine ⟨fun h0 => ?_, fun h1 => hM h1⟩
    have := sl_mulVec_inv_self M (Pi.single 0 1 : Fin 4 → ZMod 2)
    rw [h0, Matrix.mulVec_zero] at this
    exact he0 this.symm
  obtain ⟨h1, h2⟩ := hne g hg
  obtain ⟨h3, h4⟩ := hne h hh
  obtain ⟨a, ha, hax⟩ := ptStab_trans _ _ h1 h2 h3 h4
  refine ⟨a, ha, g⁻¹ * a⁻¹ * h, ?_, by group⟩
  show ((g⁻¹ * a⁻¹ * h : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4)
    (ZMod 2)) *ᵥ (Pi.single 0 1 : Fin 4 → ZMod 2) = Pi.single 0 1
  rw [sl_mulVec_mul, sl_mulVec_mul, ← hax, sl_mulVec_inv_self, sl_mulVec_inv_self]

theorem ptStab_shape (M : SpecialLinearGroup (Fin 4) (ZMod 2)) (hM : M ∈ ptStab) :
    (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      blk4 (fun i : Fin 3 => (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 i.succ)
        (Matrix.of fun i j : Fin 3 => (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) i.succ j.succ) := by
  have h := (mem_ptStab_iff M).1 hM
  have h0 : (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 0 = 1 := by simpa using h 0
  have h1 : (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 0 = 0 := by simpa using h 1
  have h2 : (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) 2 0 = 0 := by simpa using h 2
  have h3 : (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) 3 0 = 0 := by simpa using h 3
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk4, *]

@[expose] def blk4SL (y : Fin 3 → ZMod 2) (A : SpecialLinearGroup (Fin 3) (ZMod 2)) :
    SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨blk4 y (A : Matrix (Fin 3) (Fin 3) (ZMod 2)), by rw [det_blk4]; exact A.2⟩

theorem blk4SL_coe (y : Fin 3 → ZMod 2) (A : SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ((blk4SL y A : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      blk4 y (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) := rfl

theorem blk4SL_mem (y : Fin 3 → ZMod 2) (A : SpecialLinearGroup (Fin 3) (ZMod 2)) :
    blk4SL y A ∈ ptStab := by
  rw [mem_ptStab_iff, blk4SL_coe]
  intro i
  fin_cases i <;> simp [blk4]

theorem card_ptStab : Nat.card ptStab = 1344 := by
  have hdetA : ∀ M : ptStab, (Matrix.of fun i j : Fin 3 =>
      ((M : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) i.succ
        j.succ).det = 1 := by
    intro M
    have h1 := ptStab_shape M M.2
    have h2 := congrArg Matrix.det h1
    rw [det_blk4] at h2
    rw [← h2]
    exact (M : SpecialLinearGroup (Fin 4) (ZMod 2)).2
  let e : ptStab ≃ (Fin 3 → ZMod 2) × SpecialLinearGroup (Fin 3) (ZMod 2) :=
    { toFun := fun M => (fun i => ((M : SpecialLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 i.succ,
        ⟨Matrix.of fun i j : Fin 3 => ((M : SpecialLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)) i.succ j.succ, hdetA M⟩)
      invFun := fun p => ⟨blk4SL p.1 p.2, blk4SL_mem _ _⟩
      left_inv := fun M => by
        apply Subtype.ext
        apply Subtype.ext
        exact (ptStab_shape M M.2).symm
      right_inv := fun p => by
        refine Prod.ext ?_ ?_
        · funext i
          fin_cases i <;> simp [blk4SL_coe, blk4]
        · apply Subtype.ext
          ext i j
          fin_cases i <;> fin_cases j <;> simp [blk4SL_coe, blk4] }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_fun, Nat.card_zmod, Nat.card_fin,
    Matrix.card_SL_field 3, ZMod.card]
  simp [Fin.prod_univ_succ]

end Stellmacher.PU.L3YC

end CFSG.Quasithin
