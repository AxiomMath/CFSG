module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeTableZDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.TwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.RankThree.PartOne.KE.E7FiveBlock

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.PerfectCover CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

private theorem tzNine_nine_dvd_two_pow_three_mul_add_one {n : ℕ} (h3 : 3 ∣ 2 ^ n + 1) :
    9 ∣ 2 ^ (3 * n) + 1 := by
  obtain ⟨k, hk⟩ := h3
  generalize ha : 2 ^ n = a at hk
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      omega
    · exact hkpos
  obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hb : a = 3 * m + 2 := by omega
  have hpow : 2 ^ (3 * n) = a ^ 3 := by rw [← ha, mul_comm 3 n, pow_mul]
  rw [hpow, hb]
  exact ⟨3 * m ^ 3 + 6 * m ^ 2 + 4 * m + 1, by ring⟩

open CFSG.HardMathSupport.Timmesfeld.CrossChar in
theorem tableZ_exists_diag_nine
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {n : ℕ} (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1)
    (σQ : L ≃+* L) (hσQ : ∀ c, σQ c = c ^ (2 ^ (3 * n))) :
    ∃ ζ : Lˣ, ζ ^ 9 = 1 ∧ ζ ^ 3 ≠ 1 ∧
      ∃ c : ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := 3) σQ)),
        ((c : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
          Matrix.diagonal ![(ζ : L), ((ζ ^ 2)⁻¹ : Lˣ), (ζ : L)] := by
  have h9ne : ((9 : ℕ) : L) ≠ 0 := by
    intro h
    have hd : 2 ∣ 9 := (CharP.cast_eq_zero_iff L 2 9).1 h
    norm_num at hd
  haveI : NeZero ((9 : ℕ) : L) := ⟨h9ne⟩
  obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 9
  have hu : IsUnit ζ0 := hζ0.isUnit (by norm_num)
  let ζ : Lˣ := hu.unit
  have hζ : IsPrimitiveRoot ζ 9 := by
    refine IsPrimitiveRoot.coe_units_iff.1 ?_
    simpa only [ζ, IsUnit.unit_spec] using hζ0
  have hζ9 : ζ ^ 9 = 1 := hζ.pow_eq_one
  have hζ3 : ζ ^ 3 ≠ 1 := by
    intro h
    have hd : 9 ∣ 3 := (hζ.pow_eq_one_iff_dvd 3).1 h
    norm_num at hd
  have h9dvd : 9 ∣ 2 ^ (3 * n) + 1 := tzNine_nine_dvd_two_pow_three_mul_add_one h3
  have hζQ : ζ ^ (2 ^ (3 * n) + 1) = 1 := (hζ.pow_eq_one_iff_dvd _).2 h9dvd
  have haQ : (ζ : L) ^ (2 ^ (3 * n) + 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζQ, Units.val_one]
  have hζne : (ζ : L) ≠ 0 := ζ.ne_zero
  have hmul1 : (ζ : L) ^ (2 ^ (3 * n)) * (ζ : L) = 1 := by
    rw [← pow_succ, haQ]
  have hmul2 : (ζ : L) ^ (2 ^ (3 * n) * 2) * (ζ : L) ^ 2 = 1 := by
    rw [← pow_add, show 2 ^ (3 * n) * 2 + 2 = (2 ^ (3 * n) + 1) * 2 by ring, pow_mul, haQ,
      one_pow]
  have h0 : (σQ.toRingHom (ζ : L))⁻¹ = (ζ : L) := by
    change (σQ (ζ : L))⁻¹ = (ζ : L)
    rw [hσQ]
    exact (mul_eq_one_iff_inv_eq₀ (pow_ne_zero _ hζne)).1 hmul1
  have h2 : (σQ.toRingHom (((ζ : L) ^ 2)⁻¹))⁻¹ = (((ζ : L) ^ 2)⁻¹) := by
    rw [map_inv₀ (σQ.toRingHom), inv_inv, map_pow (σQ.toRingHom)]
    rw [show σQ.toRingHom (ζ : L) = (ζ : L) ^ (2 ^ (3 * n)) from hσQ (ζ : L)]
    rw [← pow_mul]
    exact (mul_eq_one_iff_eq_inv₀ (pow_ne_zero 2 hζne)).1 hmul2
  let v : Fin 3 → L := ![(ζ : L), ((ζ ^ 2)⁻¹ : Lˣ), (ζ : L)]
  have hv1 : (((ζ ^ 2)⁻¹ : Lˣ) : L) = (((ζ : L)) ^ 2)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
  have hdet : Matrix.det (Matrix.diagonal v) = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp only [v, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons, hv1]
    rw [show (ζ : L) * (((ζ : L)) ^ 2)⁻¹ * (ζ : L) =
      ((ζ : L)) ^ 2 * (((ζ : L)) ^ 2)⁻¹ by ring]
    exact mul_inv_cancel₀ (pow_ne_zero 2 hζne)
  have hσne : ∀ x : L, σQ x = 0 → x = 0 := by
    intro x hx
    have hx' : σQ x = σQ 0 := by rw [hx, map_zero]
    exact σQ.injective hx'
  have hv_ne : ∀ i, v i ≠ 0 := by
    intro i
    fin_cases i <;>
      simp only [v, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons, hv1]
    · exact hζne
    · exact inv_ne_zero (pow_ne_zero 2 hζne)
    · exact hζne
  let X : SL(3, L) := ⟨Matrix.diagonal v, hdet⟩
  have hXval : (X : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal v :=
    Matrix.SpecialLinearGroup.coe_mk (Matrix.diagonal v) hdet
  have hfix : stdUnitary σQ.toRingHom X = X := by
    apply Subtype.ext
    rw [coe_stdUnitary]
    rw [hXval, Matrix.diagonal_map (map_zero σQ.toRingHom)]
    have hinv : (Matrix.diagonal fun i => σQ.toRingHom (v i))⁻¹ =
        Matrix.diagonal (fun i => (σQ.toRingHom (v i))⁻¹) := by
      refine Matrix.inv_eq_right_inv ?_
      rw [Matrix.diagonal_mul_diagonal,
        show (fun i => σQ.toRingHom (v i) * (σQ.toRingHom (v i))⁻¹) = (1 : Fin 3 → L) from
          funext fun i => mul_inv_cancel₀ fun h => hv_ne i (hσne (v i) h)]
      exact Matrix.diagonal_one
    rw [hinv, Matrix.diagonal_transpose, Matrix.diagonal_injective.eq_iff]
    funext i
    fin_cases i <;>
      simp only [v, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons, hv1]
    · exact h0
    · exact h2
    · exact h0
  refine ⟨ζ, hζ9, hζ3, ⟨⟨X, ?_⟩, ?_⟩⟩
  · rw [CFSG.RankThree.Classical2.mem_fixSubgroup, stdUnitaryEquiv_apply]
    exact hfix
  · rw [hXval]

end CFSG.StandardType.TablePThreeKG

end
