module

public import CFSG.RankThree.PartTwo.Sec11.Item116H3KFact

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1.FieldCent.L2

open scoped MatrixGroups
open CFSG.GorensteinWalter

section Fixed

variable {F : Type} [Field F]

theorem mem_fixedSub_iff {X : Type*} [Group X] (α : MulAut X) (x : X) :
    x ∈ Sec11.fixedSub α ↔ α x = x := Iff.rfl

@[expose] noncomputable def subfieldToPSL (S : Subfield F) : SL(2, S) →* PSL2 F :=
  (QuotientGroup.mk' (Subgroup.center SL(2, F))).comp
    (Matrix.SpecialLinearGroup.map S.subtype)

theorem subfieldToPSL_apply (S : Subfield F) (A : SL(2, S)) :
    subfieldToPSL S A =
      QuotientGroup.mk' (Subgroup.center SL(2, F))
        (Matrix.SpecialLinearGroup.map S.subtype A) := rfl

theorem map_subtype_injective (S : Subfield F) :
    Function.Injective (Matrix.SpecialLinearGroup.map S.subtype : SL(2, S) →* SL(2, F)) := by
  intro A B h
  apply Subtype.ext
  ext i j
  have := congrArg (fun C : SL(2, F) => (C : Matrix (Fin 2) (Fin 2) F) i j) h
  simpa using this

theorem ker_subfieldToPSL (S : Subfield F) :
    (subfieldToPSL S).ker = Subgroup.center SL(2, S) := by
  ext A
  rw [MonoidHom.mem_ker, subfieldToPSL_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    rw [Subgroup.mem_center_iff]
    intro B
    apply map_subtype_injective S
    rw [map_mul, map_mul]
    exact (Subgroup.mem_center_iff.1 h (Matrix.SpecialLinearGroup.map S.subtype B))
  · intro h
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 h
    refine Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨S.subtype r, ?_, ?_⟩
    · rw [← map_pow, hr, map_one]
    · rw [Matrix.SpecialLinearGroup.map_apply_coe, ← hrA]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, hij]

theorem range_subfieldToPSL (S : Subfield F) (σ : F ≃+* F) (hσ3 : ∀ x, σ (σ (σ x)) = x)
    (hS : ∀ a, a ∈ S ↔ σ a = a) :
    (subfieldToPSL S).range = Sec11.fixedSub (psl2FieldAut F σ) := by
  ext x
  constructor
  · rintro ⟨A, rfl⟩
    rw [mem_fixedSub_iff, subfieldToPSL_apply]
    change psl2RingEquiv σ (QuotientGroup.mk' _ _) = _
    rw [psl2RingEquiv_mk]
    congr 1
    apply Subtype.ext
    ext i j
    exact (hS _).1 (A i j).2
  · intro hx
    obtain ⟨B, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(2, F)) x
    rw [mem_fixedSub_iff] at hx
    change psl2RingEquiv σ (QuotientGroup.mk' _ _) = _ at hx
    rw [psl2RingEquiv_mk] at hx
    have h2 := QuotientGroup.eq.1 hx
    obtain ⟨r, hr, hrB⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 h2
    have hr2 : r ^ 2 = 1 := by simpa using hr
    have hσr : σ r = r := by
      rcases sq_eq_one_iff.1 hr2 with h | h <;> simp [h]
    have hBeq : ∀ i j, B i j = σ (B i j) * r := by
      intro i j
      have h3 : (B : Matrix (Fin 2) (Fin 2) F) =
          ((Matrix.SpecialLinearGroup.map σ.toRingHom B : SL(2, F)) :
            Matrix (Fin 2) (Fin 2) F) * Matrix.scalar (Fin 2) r := by
        rw [hrB, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
      have h4 := congrFun (congrFun h3 i) j
      rw [Matrix.scalar_apply, Matrix.mul_diagonal] at h4
      exact h4
    have hfix : ∀ i j, σ (B i j) = B i j := by
      intro i j
      have e1 : σ (B i j) = B i j * r := by
        calc σ (B i j) = σ (B i j) * (r * r) := by rw [← sq, hr2, mul_one]
          _ = (σ (B i j) * r) * r := by rw [mul_assoc]
          _ = B i j * r := by rw [← hBeq]
      have e2 : σ (σ (B i j)) = B i j := by
        rw [e1, map_mul, hσr, e1]
        calc B i j * r * r = B i j * (r * r) := by rw [mul_assoc]
          _ = B i j := by rw [← sq, hr2, mul_one]
      have e3 := hσ3 (B i j)
      rw [e2] at e3
      exact e3
    let M : Matrix (Fin 2) (Fin 2) S := Matrix.of fun i j => ⟨B i j, (hS _).2 (hfix i j)⟩
    have hMmap : M.map S.subtype = (B : Matrix (Fin 2) (Fin 2) F) := by
      ext i j
      rfl
    have hdet : M.det = 1 := by
      apply S.subtype.injective
      rw [RingHom.map_det, map_one]
      have : S.subtype.mapMatrix M = (B : Matrix (Fin 2) (Fin 2) F) := hMmap
      rw [this]
      exact B.2
    let A : SL(2, S) := ⟨M, hdet⟩
    refine ⟨A, ?_⟩
    have hAB : Matrix.SpecialLinearGroup.map S.subtype A = B := Subtype.ext hMmap
    rw [subfieldToPSL_apply, hAB]

theorem nonempty_psl2_equiv_fixedSub (S : Subfield F) (σ : F ≃+* F)
    (hσ3 : ∀ x, σ (σ (σ x)) = x) (hS : ∀ a, a ∈ S ↔ σ a = a) :
    Nonempty (PSL2 S ≃* Sec11.fixedSub (psl2FieldAut F σ)) :=
  ⟨((QuotientGroup.quotientMulEquivOfEq (ker_subfieldToPSL S).symm).trans
      (QuotientGroup.quotientKerEquivRange (subfieldToPSL S))).trans
    (MulEquiv.subgroupCongr (range_subfieldToPSL S σ hσ3 hS))⟩

end Fixed

theorem nonempty_fixedSub_equiv_of_compat {X Y : Type*} [Group X] [Group Y] (ψ : X ≃* Y)
    (α : MulAut X) (β : MulAut Y) (h : ∀ x, β (ψ x) = ψ (α x)) :
    Nonempty (Sec11.fixedSub α ≃* Sec11.fixedSub β) :=
  ⟨{ toFun := fun x => ⟨ψ x.1, by
        rw [mem_fixedSub_iff, h, (mem_fixedSub_iff α x.1).1 x.2]⟩
     invFun := fun y => ⟨ψ.symm y.1, by
        rw [mem_fixedSub_iff]
        apply ψ.injective
        rw [← h, MulEquiv.apply_symm_apply]
        exact y.2⟩
     left_inv := fun x => Subtype.ext (ψ.symm_apply_apply x.1)
     right_inv := fun y => Subtype.ext (ψ.apply_symm_apply y.1)
     map_mul' := fun x y => Subtype.ext (map_mul ψ x.1 y.1) }⟩

end CFSG.RankThree.PartTwo.Sec11.SimsR1.FieldCent.L2
