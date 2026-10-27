module

public import CFSG.RankThree.PartTwo.Sec15.KL3Sub2ProofAbs
public import CFSG.RankThree.PartTwo.Sec16.Item166Res6ProofE9L
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
public import CFSG.CharacterTheory.Semidihedral.FixedFieldData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec15

namespace KL3Sub2Proof

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartTwo.Sec16.Proof166Res6

variable {K : Type} [Field K]

theorem ringEquiv_eq_one_of_card_prime {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r)
    (σ : K ≃+* K) : σ = 1 := by
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    CFSG.Semidihedral.FixedFieldData.finite_field_automorphism_fixed_field_cardinality r 1 hr
      le_rfl K (by rw [pow_one]; exact hK)
  have : Subsingleton (K ≃+* K) := (Nat.card_eq_one_iff_unique.mp hcard).1
  exact Subsingleton.elim _ _

theorem dualAut_apply_of_mem_fourPSL {v : projectiveSL 3 K} (hv : v ∈ fourPSL (K := K)) :
    dualAut 3 K v = v := by
  obtain ⟨g, hg, rfl⟩ := hv
  rw [dualAut_proj]
  congr 1
  have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_right (mul_self_of_mem_fourSL hg)
  rw [hinv]
  obtain ⟨u, -, rfl⟩ := hg
  apply sl_ext
  rw [Matrix.SpecialLinearGroup.coe_transpose, coe_diagSL, diagonal_transpose]

theorem conjAut_diagFirst_apply_of_mem_fourPSL (d : Kˣ) {v : projectiveSL 3 K}
    (hv : v ∈ fourPSL (K := K)) : conjAut 3 K (diagFirst d) v = v := by
  obtain ⟨g, hg, rfl⟩ := hv
  rw [conjAut_proj]
  congr 1
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
  obtain ⟨u, -, rfl⟩ := hg
  have hc : diagFirst d * Matrix.SpecialLinearGroup.toGL (diagSL u) =
      Matrix.SpecialLinearGroup.toGL (diagSL u) * diagFirst d := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    change diagonal ![(d : K), 1, 1] * diagonal (diagVec u) =
      diagonal (diagVec u) * diagonal ![(d : K), 1, 1]
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  rw [hc, mul_inv_cancel_right]

theorem diagFirst_inv (d : Kˣ) : (diagFirst d)⁻¹ = diagFirst d⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  rw [Units.val_mul, coe_diagFirst, coe_diagFirst, diagonal_mul_diagonal, Units.val_one,
    ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem inverseTranspose_diagFirst (d : Kˣ) :
    Matrix.GeneralLinearGroup.inverseTranspose (diagFirst d) = (diagFirst d)⁻¹ := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_inverseTranspose, diagFirst_inv, coe_diagFirst,
    diagonal_transpose]

theorem det_diagFirst (d : Kˣ) : Matrix.GeneralLinearGroup.det (diagFirst d) = d := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_diagFirst, det_diagonal, Fin.prod_univ_three]
  simp

theorem det_scalar_three (u : Kˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 3) u) = u ^ 3 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, det_diagonal, Fin.prod_univ_three, Units.val_pow_eq_pow_val]
  ring

theorem aut_cases_projectiveSL [Finite K] (hσ : ∀ σ : K ≃+* K, σ = 1)
    (α : MulAut (projectiveSL 3 K)) :
    (∃ y, α ^ 3 = MulAut.conj y) ∨
      ∃ y, ((MulAut.conj y)⁻¹ * α) ^ 2 = 1 ∧
        (∀ v ∈ fourPSL (K := K), ((MulAut.conj y)⁻¹ * α) v = v) ∧
        ∀ z, (MulAut.conj y)⁻¹ * α ≠ MulAut.conj z := by
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 α
  rw [hσ σ, map_one, mul_one]
  set d := Matrix.GeneralLinearGroup.det A with hd
  interval_cases ε
  ·
    left
    rw [pow_zero, mul_one]
    set Y : GL (Fin 3) K := A ^ 3 * (Matrix.GeneralLinearGroup.scalar (Fin 3) d)⁻¹ with hYdef
    have hY : (Y : Matrix (Fin 3) (Fin 3) K).det = 1 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, hYdef, map_mul, map_inv, det_scalar_three,
        map_pow, ← hd, mul_inv_cancel, Units.val_one]
    obtain ⟨Y', hY'⟩ : ∃ Y' : Matrix.SpecialLinearGroup (Fin 3) K,
        Matrix.SpecialLinearGroup.toGL Y' = Y := ⟨⟨Y, hY⟩, Units.ext rfl⟩
    refine ⟨proj 3 K Y', ?_⟩
    have hYA : A ^ 3 = Matrix.SpecialLinearGroup.toGL Y' *
        Matrix.GeneralLinearGroup.scalar (Fin 3) d := by
      rw [hY', hYdef, inv_mul_cancel_right]
    rw [← map_pow, hYA, map_mul, conjAut_scalar, mul_one, LinearFlag.conjAut_toGL]
  ·
    right
    rw [pow_one]
    set B : GL (Fin 3) K := diagFirst d with hB
    set X₀ : GL (Fin 3) K := A * B⁻¹ with hX₀
    have hX : (X₀ : Matrix (Fin 3) (Fin 3) K).det = 1 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, hX₀, map_mul, map_inv, hB, det_diagFirst,
        ← hd, mul_inv_cancel, Units.val_one]
    obtain ⟨X', hXgl⟩ : ∃ X' : Matrix.SpecialLinearGroup (Fin 3) K,
        Matrix.SpecialLinearGroup.toGL X' = X₀ := ⟨⟨X₀, hX⟩, Units.ext rfl⟩
    refine ⟨proj 3 K X', ?_⟩
    have hβ : (MulAut.conj (proj 3 K X'))⁻¹ * (conjAut 3 K A * dualAut 3 K) =
        conjAut 3 K B * dualAut 3 K := by
      rw [← LinearFlag.conjAut_toGL, hXgl, ← map_inv, ← mul_assoc, ← map_mul, hX₀,
        _root_.mul_inv_rev, inv_inv, inv_mul_cancel_right]
    rw [hβ]
    have htrans := standard_automorphism_transport (K := K) (n := 3)
    refine ⟨?_, fun v hv => ?_, fun z hz => ?_⟩
    ·
      rw [pow_two, mul_assoc, ← mul_assoc (dualAut 3 K) (conjAut 3 K B) (dualAut 3 K),
        htrans.2.2.2.2.1 B, ← map_mul, hB, inverseTranspose_diagFirst, mul_inv_cancel, map_one]
    · rw [MulAut.mul_apply, dualAut_apply_of_mem_fourPSL hv, hB,
        conjAut_diagFirst_apply_of_mem_fourPSL d hv]
    ·
      obtain ⟨Z, rfl⟩ := proj_surjective 3 K z
      rw [← LinearFlag.conjAut_toGL] at hz
      apply ProjectivePlane.dualAut_not_mem_semilinearAutGroup (K := K) (n := 3) le_rfl
      have hδ : dualAut 3 K = conjAut 3 K B⁻¹ * conjAut 3 K (Matrix.SpecialLinearGroup.toGL Z) := by
        rw [← hz, map_inv, inv_mul_cancel_left]
      rw [hδ, ← map_mul]
      exact linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup _)

theorem card_rootsOfUnity_two [Finite K] {p : ℕ} [CharP K p] (hp : p ≠ 2) :
    Nat.card (rootsOfUnity 2 K) = 2 :=
  (IsPrimitiveRoot.neg_one p hp).card_rootsOfUnity

theorem card_fourPSL [Finite K] {p : ℕ} [CharP K p] (hp : p ≠ 2) :
    Nat.card (fourPSL (K := K)) = 4 := by
  have hV : Nat.card (fourSL (K := K)) = 4 := by
    rw [fourSL, card_diagSub, card_rootsOfUnity_two hp]
    norm_num
  have hinj : Function.Injective ((proj 3 K).comp (fourSL (K := K)).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨g, hg⟩ hker
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, proj_eq_one_iff,
      mem_scalars] at hker
    obtain ⟨c, -, hc⟩ := hker
    rw [Subgroup.mem_bot]
    obtain ⟨u, hu, rfl⟩ := hg
    have h0 := congrFun (congrFun hc 0) 0
    have h1 := congrFun (congrFun hc 1) 1
    have h2 := congrFun (congrFun hc 2) 2
    simp only [coe_diagSL, diagonal_apply_eq, diagVec, scalar_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
    have hu1 : u.1 = c := Units.ext h0
    have hu2 : u.2 = c := Units.ext h1
    have hu12 : (u.1 * u.2)⁻¹ = c := Units.ext h2
    have hc2 : c ^ 2 = 1 := by rw [← hu1]; exact (mem_rootsOfUnity 2 u.1).mp hu.1
    have hc1 : c = 1 := by
      rw [hu1, hu2, ← pow_two, hc2, inv_one] at hu12
      exact hu12.symm
    apply Subtype.ext
    change diagSL u = 1
    rw [show u = 1 from Prod.ext (hu1.trans hc1) (hu2.trans hc1), map_one]
  have hmap : (fourSL (K := K)).map (proj 3 K) =
      ((proj 3 K).comp (fourSL (K := K)).subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [fourPSL, hmap, ← hV]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem mul_self_of_mem_fourPSL {v : projectiveSL 3 K} (hv : v ∈ fourPSL (K := K)) :
    v * v = 1 := by
  obtain ⟨g, hg, rfl⟩ := hv
  rw [← map_mul, mul_self_of_mem_fourSL hg, map_one]

end KL3Sub2Proof

end CFSG.RankThree.PartTwo.Sec15
