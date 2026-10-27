module

public import CFSG.RankThree.PartTwo.Sec21.Item2130Res4ProofU4Cent
public import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2130Res4Proof

open Matrix CFSG CFSG.RankThree CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof

section Swaps

variable {F : Type} [Field F]

@[expose] def swap01 : Matrix (Fin 3) (Fin 3) F := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

@[expose] def swap12 : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 0, 0, 1; 0, 1, 0]

theorem eq_of_commute_blk3_swap01 {μ : Fin 4 → F}
    (h : diagonal μ * blk3 swap01 = blk3 swap01 * diagonal μ) : μ 0 = μ 1 := by
  have e := congrFun (congrFun h 0) 1
  simpa [blk3, swap01, diagonal_mul, mul_diagonal] using e

theorem eq_of_commute_blk3_swap12 {μ : Fin 4 → F}
    (h : diagonal μ * blk3 swap12 = blk3 swap12 * diagonal μ) : μ 1 = μ 2 := by
  have e := congrFun (congrFun h 1) 2
  simpa [blk3, swap12, diagonal_mul, mul_diagonal] using e

end Swaps

section Unitary

variable {f : ℕ} {K : Type} [Field K] [Finite K] [Fact (Nat.Prime 2)] [CharP K 2]
variable (h : UnitaryFieldData 2 f K)

omit [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] in
theorem exists_mem_blk3SU {A : Matrix (Fin 3) (Fin 3) K} (hdet : A.det = 1)
    (hiso : (A.map h.bar)ᵀ * A = 1) : ∃ g ∈ blk3SU h, (g : Matrix (Fin 4) (Fin 4) K) = blk3 A := by
  have hu : IsUnit A.det := by rw [hdet]; exact isUnit_one
  refine ⟨iota3 h ⟨Matrix.nonsingInvUnit A hu, mem_gramSU.mpr ⟨?_, hdet⟩⟩, ⟨_, rfl⟩, rfl⟩
  rw [Units.val_one, Matrix.mul_one]
  exact hiso

omit [Finite K] [Fact (Nat.Prime 2)] in
theorem swap_mem (A : Matrix (Fin 3) (Fin 3) K) (hA : A = swap01 ∨ A = swap12) :
    A.det = 1 ∧ (A.map h.bar)ᵀ * A = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rcases hA with rfl | rfl
  · refine ⟨?_, ?_⟩
    · rw [Matrix.det_fin_three]
      simp [swap01]
      linear_combination -h2
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [swap01, Matrix.mul_apply, Fin.sum_univ_three]
  · refine ⟨?_, ?_⟩
    · rw [Matrix.det_fin_three]
      simp [swap12]
      linear_combination -h2
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [swap12, Matrix.mul_apply, Fin.sum_univ_three]

omit [Finite K] [Fact (Nat.Prime 2)] in
theorem eq_of_le_centralizer_blk3SU {y : GL (Fin 4) K} {μ : Fin 4 → K}
    (hy : (y : Matrix (Fin 4) (Fin 4) K) = diagonal μ)
    (hle : blk3SU h ≤ Subgroup.centralizer ({y} : Set (GL (Fin 4) K))) :
    μ 0 = μ 1 ∧ μ 1 = μ 2 := by
  have key : ∀ A : Matrix (Fin 3) (Fin 3) K, A = swap01 ∨ A = swap12 →
      diagonal μ * blk3 A = blk3 A * diagonal μ := by
    intro A hA
    obtain ⟨hdet, hiso⟩ := swap_mem h A hA
    obtain ⟨g, hg, hgA⟩ := exists_mem_blk3SU h hdet hiso
    have e := congrArg (fun z : GL (Fin 4) K => (z : Matrix (Fin 4) (Fin 4) K))
      (Subgroup.mem_centralizer_singleton_iff.mp (hle hg))
    simp only [Units.val_mul, hy, hgA] at e
    exact e.symm
  exact ⟨eq_of_commute_blk3_swap01 (key _ (Or.inl rfl)),
    eq_of_commute_blk3_swap12 (key _ (Or.inr rfl))⟩

@[expose] noncomputable def radGL {X : Fin 4 → K} (hX : (uF h 4).β X X = 0) :
    Subgroup (GL (Fin 4) K) where
  carrier := {g | (g : Matrix (Fin 4) (Fin 4) K) *ᵥ X = X ∧
    (∀ v, (uF h 4).β X v = 0 → ∃ t : K, (g : Matrix (Fin 4) (Fin 4) K) *ᵥ v - v = t • X) ∧
    ∀ v, (uF h 4).β X ((g : Matrix (Fin 4) (Fin 4) K) *ᵥ v - v) = 0}
  mul_mem' {g k} hg hk := by
    obtain ⟨hg1, hg2, hg3⟩ := hg
    obtain ⟨hk1, hk2, hk3⟩ := hk
    simp only [Set.mem_ofPred_eq, Units.val_mul, ← Matrix.mulVec_mulVec]
    refine ⟨by rw [hk1, hg1], fun v hv => ?_, fun v => ?_⟩
    · obtain ⟨t, ht⟩ := hk2 v hv
      have hkv : (uF h 4).β X ((k : Matrix (Fin 4) (Fin 4) K) *ᵥ v) = 0 := by
        have e : (k : Matrix (Fin 4) (Fin 4) K) *ᵥ v = v + t • X := by rw [← ht]; abel
        rw [e, (uF h 4).add_right, (uF h 4).smul_right, hv, hX, mul_zero, add_zero]
      obtain ⟨t', ht'⟩ := hg2 _ hkv
      refine ⟨t' + t, ?_⟩
      rw [add_smul, ← ht', ← ht]
      abel
    · have e : (g : Matrix (Fin 4) (Fin 4) K) *ᵥ ((k : Matrix (Fin 4) (Fin 4) K) *ᵥ v) - v =
          ((g : Matrix (Fin 4) (Fin 4) K) *ᵥ ((k : Matrix (Fin 4) (Fin 4) K) *ᵥ v) -
            (k : Matrix (Fin 4) (Fin 4) K) *ᵥ v) + ((k : Matrix (Fin 4) (Fin 4) K) *ᵥ v - v) := by
        abel
      rw [e, (uF h 4).add_right, hg3, hk3, add_zero]
  one_mem' := by
    simp only [Set.mem_ofPred_eq, Units.val_one, Matrix.one_mulVec, sub_self]
    exact ⟨trivial, fun _ _ => ⟨0, by rw [zero_smul]⟩, fun _ => (uF h 4).β_zero_right X⟩
  inv_mem' {g} hg := by
    obtain ⟨hg1, hg2, hg3⟩ := hg
    set M := (g : Matrix (Fin 4) (Fin 4) K) with hM
    set Mi := ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hMi
    have hinv : ∀ w, M *ᵥ (Mi *ᵥ w) = w := by
      intro w
      rw [Matrix.mulVec_mulVec, hM, hMi, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    have hinv' : ∀ w, Mi *ᵥ (M *ᵥ w) = w := by
      intro w
      rw [Matrix.mulVec_mulVec, hM, hMi, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    have hβu : ∀ v, (uF h 4).β X (Mi *ᵥ v) = (uF h 4).β X v := by
      intro v
      have e := hg3 (Mi *ᵥ v)
      rw [hinv, (uF h 4).β_sub_right] at e
      exact (sub_eq_zero.mp e).symm
    refine ⟨?_, fun v hv => ?_, fun v => ?_⟩
    · conv_lhs => rw [← hg1]
      exact hinv' X
    · obtain ⟨t, ht⟩ := hg2 _ ((hβu v).trans hv)
      rw [hinv] at ht
      refine ⟨-t, ?_⟩
      rw [neg_smul, ← ht]
      abel
    · rw [(uF h 4).β_sub_right, hβu, sub_self]

theorem isPGroup_radGL {X : Fin 4 → K} (hX : (uF h 4).β X X = 0) :
    IsPGroup 2 (radGL h hX) := by
  intro g
  refine ⟨2, ?_⟩
  obtain ⟨hg1, hg2, hg3⟩ := g.2
  set N := ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) - 1 with hN
  have hNv : ∀ v, N *ᵥ v = ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v - v := by
    intro v
    rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hN3 : N ^ 3 = 0 := by
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.zero_mulVec, pow_succ, pow_succ,
      pow_one, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 : (uF h 4).β X (N *ᵥ v) = 0 := by rw [hNv]; exact hg3 v
    obtain ⟨t, ht⟩ := hg2 _ h1
    rw [← hNv] at ht
    rw [ht, Matrix.mulVec_smul, hNv, hg1, sub_self, smul_zero]
  have hg4 : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ^ 2 ^ 2 = 1 := by
    have e : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 + N := by rw [hN]; abel
    rw [e, add_pow_char_pow_of_commute 2 2 (Commute.one_left N), one_pow,
      show (2 : ℕ) ^ 2 = 3 + 1 by norm_num, pow_succ, hN3, zero_mul, add_zero]
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hg4, Subgroup.coe_one, Units.val_one]

theorem exists_two_subgroup_blk3SU (hf1 : 1 < f) {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hωbar : h.bar ω = ω⁻¹) {Y₀ : GL (Fin 4) K}
    (hY₀ : (Y₀ : Matrix (Fin 4) (Fin 4) K) = diagonal ![ω, 1, 1, ω ^ 2]) :
    ∃ U : Subgroup (GL (Fin 4) K), U ≤ blk3SU h ∧ IsPGroup 2 U ∧
      Y₀ ∈ Subgroup.normalizer (U : Set (GL (Fin 4) K)) ∧
      ¬ U ≤ Subgroup.centralizer ({Y₀} : Set (GL (Fin 4) K)) := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω3
  have hωω : ω ^ 2 + ω + 1 = 0 := by
    have e : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr hω1)
  have hbar1 : h.bar (1 : K) = 1 := map_one _
  have hbar0 : h.bar (0 : K) = 0 := map_zero _
  have hbarω2 : h.bar (ω ^ 2) = (ω ^ 2)⁻¹ := by rw [map_pow, hωbar, inv_pow]
  set X : Fin 4 → K := ![0, 1, 1, 0] with hXdef
  set e0 : Fin 4 → K := ![1, 0, 0, 0] with he0
  have hβ : ∀ u v : Fin 4 → K, (uF h 4).β u v =
      h.bar (u 0) * v 0 + h.bar (u 1) * v 1 + h.bar (u 2) * v 2 + h.bar (u 3) * v 3 := by
    intro u v
    rw [uF_β, Fin.sum_univ_four]
    simp only [UnitaryFieldData.bar_apply]
  have hXX : (uF h 4).β X X = 0 := by
    rw [hβ]
    simp [hXdef, hbar0, hbar1]
    linear_combination h2
  have hXe0 : (uF h 4).β X e0 = 0 := by rw [hβ]; simp [hXdef, he0, hbar0]
  have he0e0 : (uF h 4).β e0 e0 = 1 := by rw [hβ]; simp [he0, hbar0, hbar1]
  have hc : ω + unitaryInvolution K 2 f ω =
      -(unitaryForm 2 f (card_sq_of_unitary h) 4).β e0 e0 := by
    change ω + unitaryInvolution K 2 f ω = -(uF h 4).β e0 e0
    rw [he0e0, unitaryInvolution_apply, ← UnitaryFieldData.bar_apply h, hωbar]
    have e : ω⁻¹ = ω ^ 2 :=
      (eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hω3)).symm
    rw [e]
    linear_combination hωω
  obtain ⟨T, hTS, hT⟩ := exists_mem_statedSU_eichler (card_sq_of_unitary h) hXX hXe0 hc
  change ∀ v, (T : Matrix (Fin 4) (Fin 4) K) *ᵥ v =
    v + (uF h 4).β X v • (e0 + ω • X) - (uF h 4).β e0 v • X at hT
  have hTuS : T ∈ uS h 4 := statedSU_eq_uS h 4 ▸ hTS
  have he0X : (uF h 4).β e0 X = 0 := by rw [hβ]; simp [hXdef, he0, hbar0, hbar1]
  have hTrad : T ∈ radGL h hXX := by
    refine ⟨?_, fun v hv => ⟨-(uF h 4).β e0 v, ?_⟩, fun v => ?_⟩
    · rw [hT, hXX, he0X, zero_smul, zero_smul, add_zero, sub_zero]
    · rw [hT, hv, zero_smul, add_zero, neg_smul]
      abel
    · rw [hT, add_sub_assoc, add_sub_cancel_left, (uF h 4).β_sub_right, (uF h 4).smul_right,
        (uF h 4).smul_right, (uF h 4).add_right, (uF h 4).smul_right, hXe0, hXX]
      ring
  have hTcol : ∀ i : Fin 4, (T : Matrix (Fin 4) (Fin 4) K) i 3 = if i = 3 then 1 else 0 := by
    intro i
    have e := congrFun (hT (Pi.single 3 1)) i
    rw [Matrix.mulVec_single_one] at e
    rw [Matrix.col_apply] at e
    rw [e]
    fin_cases i <;> simp [hβ, hXdef, he0, hbar0, hbar1]
  have hTrow : ∀ j : Fin 4, (T : Matrix (Fin 4) (Fin 4) K) 3 j = if j = 3 then 1 else 0 := by
    intro j
    have e := congrFun (hT (Pi.single j 1)) 3
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at e
    rw [e]
    have hX3 : X 3 = 0 := rfl
    have he03 : e0 3 = 0 := rfl
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hX3, he03, mul_zero,
      add_zero, sub_zero, Pi.single_apply]
    by_cases hj : j = 3
    · rw [ite_eq_left hj.symm, ite_eq_left hj]
    · rw [ite_eq_right (Ne.symm hj), ite_eq_right hj]
  have hTblk : T ∈ blk3SU h := by
    refine mem_blk3SU_of h hTuS ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
    · rw [hTcol]; rfl
    · rw [hTcol]; rfl
    · rw [hTcol]; rfl
    · rw [hTrow]; rfl
    · rw [hTrow]; rfl
    · rw [hTrow]; rfl
    · rw [hTcol]; rfl
  have hY₀S : Y₀ ∈ uS h 4 := by
    refine mem_gramSU.mpr ⟨?_, ?_⟩
    · rw [Units.val_one, Matrix.mul_one, hY₀, Matrix.diagonal_map hbar0,
        Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      ext i
      fin_cases i <;> simp [hωbar, hbarω2, hω0]
    · rw [hY₀, Matrix.det_diagonal, Fin.prod_univ_four]
      simp
      rw [← pow_succ', hω3]
  have hY₀X : (Y₀ : Matrix (Fin 4) (Fin 4) K) *ᵥ X = X := by
    rw [hY₀]
    ext i
    fin_cases i <;> simp [hXdef, Matrix.mulVec_diagonal]
  have hY₀Xinv : ((Y₀⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ X = X := by
    conv_lhs => rw [← hY₀X]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hiso := uF_isometry_of_mem h hY₀S
  have hisoinv := uF_isometry_of_mem h ((uS h 4).inv_mem hY₀S)
  have hY₀rad : Y₀ ∈ Subgroup.normalizer ((radGL h hXX : Subgroup (GL (Fin 4) K)) :
      Set (GL (Fin 4) K)) := by
    have key : ∀ (y : GL (Fin 4) K), y ∈ uS h 4 →
        (y : Matrix (Fin 4) (Fin 4) K) *ᵥ X = X →
        ∀ g ∈ radGL h hXX, y * g * y⁻¹ ∈ radGL h hXX := by
      intro y hyS hyX g hg
      obtain ⟨hg1, hg2, hg3⟩ := hg
      have hyiso := uF_isometry_of_mem h hyS
      set My := (y : Matrix (Fin 4) (Fin 4) K) with hMy
      set Myi := ((y⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hMyi
      set Mg := (g : Matrix (Fin 4) (Fin 4) K) with hMg
      have hyy : ∀ w, My *ᵥ (Myi *ᵥ w) = w := by
        intro w
        rw [Matrix.mulVec_mulVec, hMy, hMyi, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec]
      have hyy' : ∀ w, Myi *ᵥ (My *ᵥ w) = w := by
        intro w
        rw [Matrix.mulVec_mulVec, hMy, hMyi, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]
      have hyinvX : Myi *ᵥ X = X := by
        conv_lhs => rw [← hyX]
        exact hyy' X
      have hβinv : ∀ w, (uF h 4).β X (Myi *ᵥ w) = (uF h 4).β X w := by
        intro w
        have e := hyiso X (Myi *ᵥ w)
        rw [hyX, hyy] at e
        exact e.symm
      have hcoe : ((y * g * y⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = My * Mg * Myi := by
        rw [Units.val_mul, Units.val_mul]
      have hconj : ∀ w, ((y * g * y⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ w - w =
          My *ᵥ (Mg *ᵥ (Myi *ᵥ w) - Myi *ᵥ w) := by
        intro w
        rw [Matrix.mulVec_sub, hyy, hcoe, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      refine ⟨?_, fun w hw => ?_, fun w => ?_⟩
      · rw [hcoe, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hyinvX, hg1, hyX]
      · obtain ⟨t, ht⟩ := hg2 _ ((hβinv w).trans hw)
        refine ⟨t, ?_⟩
        rw [hconj, ht, Matrix.mulVec_smul, hyX]
      · rw [hconj]
        have e := hyiso X (Mg *ᵥ (Myi *ᵥ w) - Myi *ᵥ w)
        rw [hyX] at e
        rw [e]
        exact hg3 _
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · exact key Y₀ hY₀S hY₀X g
    · intro hg
      have := key Y₀⁻¹ ((uS h 4).inv_mem hY₀S) hY₀Xinv _ hg
      rwa [inv_inv, show Y₀⁻¹ * (Y₀ * g * Y₀⁻¹) * Y₀ = g by group] at this
  set D : GL (Fin 4) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagonal ![ω, ω, ω, 1])
    (by
      rw [Matrix.det_diagonal, Fin.prod_univ_four]
      simp [hω0]) with hDdef
  have hD : (D : Matrix (Fin 4) (Fin 4) K) = diagonal ![ω, ω, ω, 1] := rfl
  have hY₀C : Y₀ ∈ uS h 4 ⊓ Subgroup.centralizer ({D} : Set (GL (Fin 4) K)) := by
    refine ⟨hY₀S, Subgroup.mem_centralizer_singleton_iff.mpr (Units.ext ?_)⟩
    rw [Units.val_mul, Units.val_mul, hY₀, hD, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    exact mul_comm _ _
  have hY₀blk : Y₀ ∈ Subgroup.normalizer ((blk3SU h : Subgroup (GL (Fin 4) K)) :
      Set (GL (Fin 4) K)) := by
    rw [← perfectResidual_blk3SU h hf1 hω1 hD]
    exact GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _
      (Subgroup.le_normalizer hY₀C)
  refine ⟨radGL h hXX ⊓ blk3SU h, inf_le_right, (isPGroup_radGL h hXX).to_le inf_le_left,
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hY₀rad, hY₀blk⟩, fun hle => ?_⟩
  have hTY := Subgroup.mem_centralizer_singleton_iff.mp (hle ⟨hTrad, hTblk⟩)
  have e := congrArg (fun z : GL (Fin 4) K => ((z : Matrix (Fin 4) (Fin 4) K) *ᵥ e0) 1) hTY
  simp only [Units.val_mul, ← Matrix.mulVec_mulVec] at e
  have hY₀e0 : (Y₀ : Matrix (Fin 4) (Fin 4) K) *ᵥ e0 = ω • e0 := by
    rw [hY₀]
    ext i
    fin_cases i <;> simp [he0, Matrix.mulVec_diagonal]
  rw [hY₀e0, Matrix.mulVec_smul, hT, he0e0, hXe0] at e
  rw [hY₀] at e
  simp [Matrix.mulVec_diagonal, hXdef, he0] at e
  exact hω1 e

end Unitary

end CFSG.RankThree.PartTwo.Sec21.Item2130Res4Proof
