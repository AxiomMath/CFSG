module

public import CFSG.RankThree.PartTwo.Census.OddClassical.Component
public import CFSG.RankThree.PartTwo.Census.OddClassical.SymplecticWitness
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Assembly.RankThreeEven CFSG.RankThree.Classical
  Matrix
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def planePair (X Y : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks (diagonal ![X 0 0, Y 0 0]) (diagonal ![X 0 1, Y 0 1]) (diagonal ![X 1 0, Y 1 0])
    (diagonal ![X 1 1, Y 1 1])

theorem planePair_mul (X Y X' Y' : Matrix (Fin 2) (Fin 2) K) :
    planePair X Y * planePair X' Y' = planePair (X * X') (Y * Y') := by
  rw [planePair, planePair, planePair, fromBlocks_multiply]
  simp only [diagonal_mul_diagonal, diagonal_add]
  congr 1 <;> congr 1 <;> ext i <;> fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem planePair_one : planePair (1 : Matrix (Fin 2) (Fin 2) K) 1 = 1 := by
  rw [planePair, ← fromBlocks_one]
  congr 1 <;> rw [← diagonal_one] <;> try rw [← diagonal_zero]
  all_goals congr 1; ext i; fin_cases i <;> simp

theorem planePair_injective {X Y X' Y' : Matrix (Fin 2) (Fin 2) K}
    (h : planePair X Y = planePair X' Y') : X = X' ∧ Y = Y' := by
  rw [planePair, planePair] at h
  obtain ⟨h1, h2, h3, h4⟩ := Matrix.fromBlocks_inj.mp h
  have e1 := diagonal_injective h1
  have e2 := diagonal_injective h2
  have e3 := diagonal_injective h3
  have e4 := diagonal_injective h4
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j
  · exact congrFun e1 0
  · exact congrFun e2 0
  · exact congrFun e3 0
  · exact congrFun e4 0
  · exact congrFun e1 1
  · exact congrFun e2 1
  · exact congrFun e3 1
  · exact congrFun e4 1

theorem planePair_symplectic {X Y : Matrix (Fin 2) (Fin 2) K} (hX : X.det = 1) (hY : Y.det = 1) :
    (planePair X Y)ᵀ * fromBlocks 0 1 (-1) 0 * planePair X Y = fromBlocks 0 1 (-1) 0 := by
  rw [det_fin_two] at hX hY
  ext a b
  rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [planePair, Matrix.mul_apply, Fintype.sum_sum_type, diagonal_apply] <;>
    first | ring1 | linear_combination hX | linear_combination -hX | linear_combination hY |
      linear_combination -hY

@[expose] noncomputable def spPlaneSL (K : Type) [Field K] :
    SL(2, K) →* StatedSp 2 K where
  toFun X := ⟨⟨planePair (X : Matrix (Fin 2) (Fin 2) K) 1,
      planePair ((X⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1, by
        rw [planePair_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one, planePair_one], by
        rw [planePair_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one, planePair_one]⟩,
    Subgroup.subset_closure (planePair_symplectic X.2 det_one)⟩
  map_one' := Subtype.ext (Units.ext (by
    change planePair ((1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 = 1
    rw [Matrix.SpecialLinearGroup.coe_one, planePair_one]))
  map_mul' X Y := Subtype.ext (Units.ext (by
    change planePair ((X * Y : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 =
      planePair (X : Matrix (Fin 2) (Fin 2) K) 1 * planePair (Y : Matrix (Fin 2) (Fin 2) K) 1
    rw [planePair_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_one]))

theorem coe_spPlaneSL (X : SL(2, K)) :
    (((spPlaneSL K X : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = planePair (X : Matrix (Fin 2) (Fin 2) K) 1 :=
  rfl

theorem spPlaneSL_injective : Function.Injective (spPlaneSL K) := by
  intro X Y h
  have h' := congrArg (fun g : StatedSp 2 K => ((g : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h
  simp only [coe_spPlaneSL] at h'
  exact Subtype.ext (planePair_injective h').1

theorem coe_planeInvolution_two :
    (((planeInvolution 2 K : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = planePair (-1) 1 := by
  rw [coe_planeInvolution, planePair]
  congr 1 <;> try rw [← diagonal_zero]
  all_goals congr 1; ext i; fin_cases i <;> simp [planeSign]

theorem exists_planePair_of_comm (h2 : (2 : K) ≠ 0) {g : StatedSp 2 K}
    (hg : g * planeInvolution 2 K = planeInvolution 2 K * g) :
    ∃ X Y, ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      planePair X Y := by
  set M := ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
  have hM : M * planePair (-1) 1 = planePair (-1) 1 * M := by
    have := congrArg (fun x : StatedSp 2 K => ((x : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hg
    simpa only [Subgroup.coe_mul, Units.val_mul, coe_planeInvolution_two] using this
  have hd : planePair (-1 : Matrix (Fin 2) (Fin 2) K) 1 =
      diagonal (Sum.elim ![-1, 1] ![-1, 1]) := by
    rw [planePair, ← fromBlocks_diagonal]
    congr 1 <;> try rw [← diagonal_zero]
    all_goals congr 1; ext i; fin_cases i <;> simp
  rw [hd] at hM
  have hz : ∀ a b, (Sum.elim ![-1, 1] ![-1, 1] a : K) ≠ Sum.elim ![-1, 1] ![-1, 1] b →
      M a b = 0 := by
    intro a b hab
    have := congrFun (congrFun hM a) b
    rw [mul_diagonal, diagonal_mul] at this
    have h' : M a b * (Sum.elim ![-1, 1] ![-1, 1] b - Sum.elim ![-1, 1] ![-1, 1] a) = 0 := by
      linear_combination this
    exact (mul_eq_zero.mp h').resolve_right (sub_ne_zero.mpr (Ne.symm hab))
  have hne : (-1 : K) ≠ 1 := fun h => h2 (by linear_combination -h)
  refine ⟨!![M (.inl 0) (.inl 0), M (.inl 0) (.inr 0); M (.inr 0) (.inl 0), M (.inr 0) (.inr 0)],
    !![M (.inl 1) (.inl 1), M (.inl 1) (.inr 1); M (.inr 1) (.inl 1), M (.inr 1) (.inr 1)], ?_⟩
  ext a b
  rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
    simp only [planePair, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, diagonal_apply_eq] <;>
    first
      | rfl
      | (simp; done)
      | exact hz _ _ (by simpa using hne)
      | exact hz _ _ (by simpa using hne.symm)

theorem conj_mem_range_spPlaneSL (h2 : (2 : K) ≠ 0) {g : StatedSp 2 K}
    (hg : g * planeInvolution 2 K = planeInvolution 2 K * g) (B : SL(2, K)) :
    g * spPlaneSL K B * g⁻¹ ∈ (spPlaneSL K).range := by
  have hg' : g⁻¹ * planeInvolution 2 K = planeInvolution 2 K * g⁻¹ := (Commute.inv_left hg).eq
  obtain ⟨X, Y, hXY⟩ := exists_planePair_of_comm h2 hg
  obtain ⟨X', Y', hXY'⟩ := exists_planePair_of_comm h2 hg'
  have hone : planePair (X * X') (Y * Y') = planePair 1 1 := by
    rw [← planePair_mul, ← hXY, ← hXY', planePair_one, ← Units.val_mul, ← Subgroup.coe_mul,
      mul_inv_cancel, Subgroup.coe_one, Units.val_one]
  obtain ⟨hX, hY⟩ := planePair_injective hone
  have hdet : (X * (B : Matrix (Fin 2) (Fin 2) K) * X').det = 1 := by
    rw [det_mul, det_mul, B.2, mul_one, ← det_mul, hX, det_one]
  refine ⟨⟨X * B * X', hdet⟩, Subtype.ext (Units.ext ?_)⟩
  change planePair (X * (B : Matrix (Fin 2) (Fin 2) K) * X') 1 =
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      planePair (B : Matrix (Fin 2) (Fin 2) K) 1 *
      ((g⁻¹ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K)
  rw [hXY, hXY', planePair_mul, planePair_mul, Matrix.mul_one, hY]

theorem statedScalars_le_center :
    (StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K) ≤
      Subgroup.center (StatedSp 2 K) := by
  rintro x ⟨u, hu⟩
  have hc : (x : GL (Fin 2 ⊕ Fin 2) K) ∈ Subgroup.center (GL (Fin 2 ⊕ Fin 2) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨u, hu⟩
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (Subgroup.mem_center_iff.mp hc (y : GL (Fin 2 ⊕ Fin 2) K))

theorem not_isCharTwoType_PSp_two [Finite K] (h4 : 4 ≤ Nat.card K) (hodd : Odd (Nat.card K)) :
    ¬ IsCharTwoType (StatedProj (StatedSp 2 K)) := by
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  refine not_isCharTwoType_of_sl2_component _ statedScalars_le_center
    (planeInvolution_not_mem h2 le_rfl)
    (by rw [planeInvolution_sq]; exact Subgroup.one_mem _) (J := (spPlaneSL K).range)
    ?_ ?_ ?_ h4 hodd (MonoidHom.ofInjective spPlaneSL_injective).symm
  · rintro _ ⟨B, rfl⟩
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_spPlaneSL,
      coe_planeInvolution_two, planePair_mul, planePair_mul]
    simp
  · rintro g hg _ ⟨B, rfl⟩
    exact conj_mem_range_spPlaneSL h2 hg B
  · rw [eq_bot_iff]
    rintro _ hx
    obtain ⟨⟨B, rfl⟩, ⟨u, hu⟩⟩ := Subgroup.mem_inf.mp hx
    have hu' := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) K => (g : Matrix (Fin 2 ⊕ Fin 2)
      (Fin 2 ⊕ Fin 2) K)) hu
    change Matrix.scalar _ (u : K) = planePair (B : Matrix (Fin 2) (Fin 2) K) 1 at hu'
    have e1 : (u : K) = 1 := by
      simpa [planePair] using congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K =>
        M (Sum.inl 1) (Sum.inl 1)) hu'
    rw [e1, map_one, ← planePair_one] at hu'
    have hB : B = 1 := Subtype.ext (planePair_injective hu'.symm).1
    rw [hB, map_one]
    exact Subgroup.one_mem _

theorem excluded433_B2_odd (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.B 2 q).Valid)
    (hq : q.p ≠ 2) : Excluded433 (.lie ⟨.B 2 q, hv⟩) := by
  intro G _ _ hG e
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hdup := (TauCeti.LieTypeIndex.isDuplicateRepresentative_iff _).not.mp
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).2
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.B 2 q, hv⟩
  have hcard :
      Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩) = q.p ^ q.exponent := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField]
    simp [TauCeti.ValidLieTypeIndex.fieldOrder]
  have hodd : Odd (q.p ^ q.exponent) := (Nat.Prime.odd_of_ne_two q.prime_p hq).pow
  have h3 : q.p ^ q.exponent ≠ 3 := by
    intro h
    apply hdup
    simp [h]
  have h1 : 2 ≤ q.p ^ q.exponent := (Nat.one_lt_pow q.exponent_pos.ne' q.prime_p.one_lt)
  refine hG.false_of_not_isCharTwoType
    (e.trans (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv))
    (not_isCharTwoType_PSp_two (by rw [hcard]; obtain ⟨k, hk⟩ := hodd; omega) (by rwa [hcard]))

end CFSG.RankThree.PartTwo.Census
