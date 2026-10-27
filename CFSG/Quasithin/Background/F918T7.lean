module

public import CFSG.Quasithin.Background.F918T6

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.Quasithin.B5.Ln (mat dmat)
open scoped Matrix

private def unitri5Mat (f : {p : Fin 5 × Fin 5 // p.1 < p.2} → ZMod 2) :
    Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  fun i j => if h : i < j then f ⟨(i, j), h⟩ else if i = j then 1 else 0

private theorem unitri5Mat_upper (f : {p : Fin 5 × Fin 5 // p.1 < p.2} → ZMod 2) :
    (unitri5Mat f).IsUpperTriangular := by
  intro i j hji
  simp only [id] at hji
  simp [unitri5Mat, not_lt.2 hji.le, (ne_of_lt hji).symm]

private theorem det_unitri5Mat (f : {p : Fin 5 × Fin 5 // p.1 < p.2} → ZMod 2) :
    (unitri5Mat f).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (unitri5Mat_upper f)]
  simp [unitri5Mat]

private noncomputable def unitri5Of (f : {p : Fin 5 × Fin 5 // p.1 < p.2} → ZMod 2) :
    ↥(StatedSL 5 (ZMod 2)) :=
  B5.Ln.ofGL (Matrix.nonsingInvUnit (unitri5Mat f) (by rw [det_unitri5Mat]; exact isUnit_one))

private theorem mat_unitri5Of (f : {p : Fin 5 × Fin 5 // p.1 < p.2} → ZMod 2) :
    mat (unitri5Of f) = unitri5Mat f := rfl

private theorem unitri5Of_mem (f : {p : Fin 5 × Fin 5 // p.1 < p.2} → ZMod 2) :
    unitri5Of f ∈ unitri5 := fun i j hji => by
  rw [mat_unitri5Of]
  exact unitri5Mat_upper f hji

private theorem mat_diag_eq_one_of_mem_unitri5 {g : ↥(StatedSL 5 (ZMod 2))} (hg : g ∈ unitri5)
    (i : Fin 5) : mat g i i = 1 := by
  have hT : (mat g).IsUpperTriangular := fun i j hji => hg i j hji
  have hdet : (mat g).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det (B5.Ln.mat_mul_inv g)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  rw [Matrix.det_of_isUpperTriangular hT] at hdet
  have hi : mat g i i ≠ 0 := Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ i)
  have h01 : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  exact h01 _ hi

private noncomputable def unitri5Equiv :
    ↥unitri5 ≃ ({p : Fin 5 × Fin 5 // p.1 < p.2} → ZMod 2) where
  toFun g p := mat (g : ↥(StatedSL 5 (ZMod 2))) p.1.1 p.1.2
  invFun f := ⟨unitri5Of f, unitri5Of_mem f⟩
  left_inv g := by
    apply Subtype.ext
    apply B5.Ln.mat_injective
    rw [mat_unitri5Of]
    funext i j
    simp only [unitri5Mat]
    rcases lt_trichotomy i j with h | h | h
    · rw [dite_eq_left h]
    · subst h
      rw [dite_eq_right (lt_irrefl i), ite_eq_left rfl, mat_diag_eq_one_of_mem_unitri5 g.2 i]
    · rw [dite_eq_right (not_lt.2 h.le), ite_eq_right (ne_of_lt h).symm, g.2 i j h]
  right_inv f := by
    funext p
    show unitri5Mat f p.1.1 p.1.2 = f p
    simp only [unitri5Mat, dite_eq_left p.2]

theorem card_unitri5 : Nat.card ↥unitri5 = 2 ^ 10 := by
  rw [Nat.card_congr unitri5Equiv, Nat.card_fun, Nat.card_zmod]
  congr 1
  rw [Nat.card_eq_fintype_card]
  decide

private theorem card_statedSL5 : Nat.card ↥(StatedSL 5 (ZMod 2)) = 9999360 :=
  CFSG.Open.StatedAPI.card_statedSL_five_zmod_two

open scoped Pointwise in
theorem exists_conj_le_unitri5 {E : Subgroup ↥(StatedSL 5 (ZMod 2))} (hE : IsPGroup 2 ↥E) :
    ∃ g : ↥(StatedSL 5 (ZMod 2)), ∀ x ∈ E, g * x * g⁻¹ ∈ unitri5 := by
  have hU : IsPGroup 2 ↥unitri5 := IsPGroup.of_card card_unitri5
  have hidx : unitri5.index = 9765 := by
    have h := unitri5.card_mul_index
    rw [card_unitri5, card_statedSL5] at h
    omega
  have hodd : ¬ 2 ∣ unitri5.index := by rw [hidx]; decide
  obtain ⟨Q, hEQ⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(StatedSL 5 (ZMod 2)) Q (hU.toSylow hodd)
  refine ⟨g, fun x hx => ?_⟩
  have h1 : MulAut.conj g • x ∈ MulAut.conj g • (Q : Subgroup ↥(StatedSL 5 (ZMod 2))) :=
    Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) _ (hEQ hx)
  rw [← Sylow.coe_subgroup_smul, hg, MulAut.smul_def, MulAut.conj_apply] at h1
  exact h1

end CFSG.Quasithin
