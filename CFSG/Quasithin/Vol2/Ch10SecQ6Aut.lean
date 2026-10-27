module

public import CFSG.Quasithin.Vol2.Ch10SecDFacts33
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.LocalAnalysis.ComponentInitial LinearFlag Matrix

namespace C10P06

variable {n : ℕ}

theorem units_zmod_two_eq_one (c : (ZMod 2)ˣ) : c = 1 := by
  revert c
  decide

theorem scalars_zmod_two_eq_bot : scalars n (ZMod 2) = ⊥ := by
  rw [eq_bot_iff]
  rintro A ⟨c, -, hA⟩
  rw [Subgroup.mem_bot]
  ext i j
  rw [hA, units_zmod_two_eq_one c, Units.val_one, scalar_apply, diagonal_apply]
  simp [one_apply]

theorem proj_bijective : Function.Bijective (proj n (ZMod 2)) := by
  refine ⟨?_, proj_surjective n (ZMod 2)⟩
  rw [← MonoidHom.ker_eq_bot_iff]
  show (QuotientGroup.mk' (scalars n (ZMod 2))).ker = ⊥
  rw [QuotientGroup.ker_mk', scalars_zmod_two_eq_bot]

@[expose] noncomputable def slEquivProj :
    SpecialLinearGroup (Fin n) (ZMod 2) ≃* projectiveSL n (ZMod 2) :=
  MulEquiv.ofBijective (proj n (ZMod 2)) proj_bijective

theorem center_sl_zmod_two_eq_bot :
    Subgroup.center (SpecialLinearGroup (Fin n) (ZMod 2)) = ⊥ := by
  rw [← scalars_eq_center, scalars_zmod_two_eq_bot]

theorem conj_injective :
    Function.Injective (MulAut.conj : projectiveSL n (ZMod 2) →* MulAut _) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  obtain ⟨g, rfl⟩ := slEquivProj.surjective x
  have hg : g ∈ Subgroup.center (SpecialLinearGroup (Fin n) (ZMod 2)) := by
    rw [Subgroup.mem_center_iff]
    intro h
    apply slEquivProj.injective
    have h1 := congrArg (fun α : MulAut (projectiveSL n (ZMod 2)) => α (slEquivProj h)) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    rw [map_mul, map_mul]
    conv_lhs => rw [← h1]
    group
  rw [center_sl_zmod_two_eq_bot, Subgroup.mem_bot] at hg
  rw [hg, map_one, Subgroup.mem_bot]

theorem conjAut_eq_conj_of_coe {K : Type*} [Field K] (A : GL (Fin n) K)
    (g : SpecialLinearGroup (Fin n) K)
    (hAg : (A : Matrix (Fin n) (Fin n) K) = (g : Matrix (Fin n) (Fin n) K)) :
    conjAut n K A = MulAut.conj (proj n K g) := by
  ext x
  obtain ⟨h, rfl⟩ := proj_surjective n K x
  rw [conjAut_proj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  have hinv : ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    refine left_inv_eq_right_inv (a := (A : Matrix (Fin n) (Fin n) K)) ?_ ?_
    · rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    · rw [hAg, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [coe_slConjugation, hinv, hAg, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]

theorem det_eq_one (A : GL (Fin n) (ZMod 2)) : (A : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 := by
  have h := units_zmod_two_eq_one (Matrix.GeneralLinearGroup.det A)
  have h' := congrArg Units.val h
  rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h'

theorem conjAut_eq_conj (A : GL (Fin n) (ZMod 2)) :
    ∃ x : projectiveSL n (ZMod 2), conjAut n (ZMod 2) A = MulAut.conj x :=
  ⟨proj n (ZMod 2) ⟨A, det_eq_one A⟩, conjAut_eq_conj_of_coe A ⟨A, det_eq_one A⟩ rfl⟩

variable (n) in
abbrev innP : Subgroup (MulAut (projectiveSL n (ZMod 2))) :=
  (MulAut.conj : projectiveSL n (ZMod 2) →* MulAut _).range

theorem innP_le_semilinear : innP n ≤ semilinearAutGroup n (ZMod 2) := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨g, rfl⟩ := proj_surjective n (ZMod 2) x
  rw [← conjAut_eq_conj_of_coe (Matrix.SpecialLinearGroup.toGL g) g rfl]
  exact linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup _)

theorem dualAut_not_mem_innP (hn : 3 ≤ n) : dualAut n (ZMod 2) ∉ innP n :=
  fun h => ProjectivePlane.dualAut_not_mem_semilinearAutGroup hn (innP_le_semilinear h)

theorem mem_innP_or_mul_mem_innP (hn : 3 ≤ n) (α : MulAut (projectiveSL n (ZMod 2))) :
    α ∈ innP n ∨ α * dualAut n (ZMod 2) ∈ innP n := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := ZMod 2) hn
  have hδδ : dualAut n (ZMod 2) * dualAut n (ZMod 2) = 1 :=
    (standard_automorphism_transport (K := ZMod 2) (n := n)).2.2.2.1
  obtain ⟨A, σ, ε, hε, rfl⟩ := hgen α
  have hσ : σ = 1 := RingEquiv.ext fun x =>
    congrArg (fun f : ZMod 2 →+* ZMod 2 => f x) (Subsingleton.elim σ.toRingHom (RingHom.id _))
  obtain ⟨x, hx⟩ := conjAut_eq_conj A
  rw [hσ, map_one, mul_one, hx]
  interval_cases ε
  · left
    rw [pow_zero, mul_one]
    exact ⟨x, rfl⟩
  · right
    rw [pow_one, mul_assoc, hδδ, mul_one]
    exact ⟨x, rfl⟩

theorem index_innP_eq_two (hn : 3 ≤ n) : (innP n).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨dualAut n (ZMod 2), fun b => ?_⟩
  have key : b ∈ innP n → b * dualAut n (ZMod 2) ∈ innP n → False := fun h h' =>
    dualAut_not_mem_innP hn (by
      have h2 := (innP n).mul_mem ((innP n).inv_mem h) h'
      rwa [inv_mul_cancel_left] at h2)
  rcases mem_innP_or_mul_mem_innP hn b with h | h
  · exact Or.inr ⟨h, key h⟩
  · exact Or.inl ⟨h, fun h' => key h' h⟩

theorem card_innP : Nat.card (innP n) = Nat.card (projectiveSL n (ZMod 2)) :=
  (Nat.card_congr (MonoidHom.ofInjective conj_injective).toEquiv).symm

theorem card_mulAut_sl_two (hn : 3 ≤ n) :
    Nat.card (MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) =
      2 * Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  rw [Nat.card_congr (MulAut.congr slEquivProj).toEquiv, Nat.card_congr slEquivProj.toEquiv,
    ← Subgroup.card_mul_index (innP n), card_innP, index_innP_eq_two hn, mul_comm]

end C10P06

theorem factAutSL : FactAutSL := by
  rintro k (rfl | rfl)
  · exact C10P06.card_mulAut_sl_two (by norm_num)
  · exact C10P06.card_mulAut_sl_two (by norm_num)

end CFSG.Quasithin.Vol2.Ch10.SecD
