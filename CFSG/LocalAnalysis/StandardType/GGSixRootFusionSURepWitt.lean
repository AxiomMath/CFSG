module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepBlock
public import CFSG.LocalAnalysis.StandardType.GGInvolutionClassSU

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 Matrix
open CFSG.SectionRank.OddCover (diagHom coe_diagHom det_diagHom diagHom_injective)
open CFSG.RankThree.Classical (permGL)
open CFSG.RankThree.Classical2 (permGL_mul_diagHom_mul_inv diagHom_unitary unitary_mul
  permGL_unitary det_permGL diagHom_commute)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr conjTr_mul conjTr_one SUid conjEquiv
  SUid_eq_statedSU det_antidiag_ne_zero antidiag_mul_self)
open CFSG.LieType.Universal.Unitary.SUExtras (mat mat_apply mat_injective)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)

namespace SURep

section Witt

variable {n : ℕ} {F : Type} [Field F]

@[expose] def ggPairInv (n l : ℕ) (a : Fin n) : Fin n :=
  if (a : ℕ) < l ∨ (Fin.rev a : ℕ) < l then Fin.rev a else a

theorem ggPairInv_involutive (n l : ℕ) : Function.Involutive (ggPairInv n l) := by
  intro a
  unfold ggPairInv
  by_cases ha : (a : ℕ) < l ∨ (Fin.rev a : ℕ) < l
  · rw [ite_eq_left ha, ite_eq_left (by rw [Fin.rev_rev]; tauto), Fin.rev_rev]
  · rw [ite_eq_right ha, ite_eq_right ha]

@[expose] def ggPairPerm (n l : ℕ) : Equiv.Perm (Fin n) :=
  Function.Involutive.toPerm (ggPairInv n l) (ggPairInv_involutive n l)

theorem ggPairPerm_apply (n l : ℕ) (a : Fin n) : ggPairPerm n l a = ggPairInv n l a := rfl

theorem ggPairPerm_inv (n l : ℕ) : (ggPairPerm n l)⁻¹ = ggPairPerm n l :=
  Function.Involutive.toPerm_symm _

@[expose] def wittA (n : ℕ) (γ : F) (c : Fin n) : F :=
  if (c : ℕ) + c + 1 < n then γ else 1

@[expose] def wittB (n : ℕ) (γ : F) (c : Fin n) : F :=
  if (c : ℕ) + c + 1 < n then γ + 1 else if n < (c : ℕ) + c + 1 then 1 else 0

@[expose] def wittMat (n : ℕ) (γ : F) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun r c => (if r = c then wittA n γ c else 0) +
    (if r = Fin.rev c then wittB n γ c else 0)

theorem wittMat_apply (γ : F) (r c : Fin n) :
    wittMat n γ r c = (if r = c then wittA n γ c else 0) +
      (if r = Fin.rev c then wittB n γ c else 0) :=
  rfl

theorem conjTr_wittMat_mul_apply (σ : F ≃+* F) (γ : F) (a b : Fin n) :
    (conjTr σ (wittMat n γ) * wittMat n γ) a b =
      ((if b = a then σ (wittA n γ a) * wittA n γ b else 0) +
        if b = Fin.rev a then σ (wittB n γ a) * wittA n γ b else 0) +
      ((if Fin.rev b = a then σ (wittA n γ a) * wittB n γ b else 0) +
        if Fin.rev b = Fin.rev a then σ (wittB n γ a) * wittB n γ b else 0) := by
  rw [Matrix.mul_apply]
  simp only [conjTr, transpose_apply, map_apply, wittMat_apply, map_add, apply_ite σ, map_zero,
    add_mul, mul_add, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem conjTr_wittMat_mul [CharP F 2] (σ : F ≃+* F) {γ : F} (hγ : σ γ + γ = 1) :
    conjTr σ (wittMat n γ) * wittMat n γ = antidiag n := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext a b
  rw [conjTr_wittMat_mul_apply]
  simp only [antidiag, of_apply]
  have ha := a.isLt
  have hb := b.isLt
  by_cases hab : b = a
  · rw [hab]
    by_cases hm : (a : ℕ) + a + 1 = n
    · have hr : a = Fin.rev a := Fin.ext (by rw [Fin.val_rev]; omega)
      rw [ite_eq_left rfl, ite_eq_left hr, ite_eq_left hr.symm, ite_eq_left rfl, ite_eq_left hr]
      simp only [wittA, wittB]
      split_ifs <;> first | (exfalso; omega) | simp
    · have hr : ¬ a = Fin.rev a := fun h => hm (by
        have := congrArg Fin.val h
        rw [Fin.val_rev] at this
        omega)
      rw [ite_eq_left rfl, ite_eq_right hr, ite_eq_right (fun h => hr h.symm), ite_eq_left rfl,
        ite_eq_right hr]
      simp only [wittA, wittB]
      by_cases h1 : (a : ℕ) + a + 1 < n
      · simp only [h1, ite_true, map_add, map_one]
        linear_combination hγ + (σ γ * γ + 1) * h2
      · simp only [h1, show n < (a : ℕ) + a + 1 by omega, ite_true, ite_false, map_one]
        linear_combination h2
  · by_cases h2' : b = Fin.rev a
    · rw [h2']
      have hr : ¬ Fin.rev a = a := fun h => hab (h2'.trans h)
      rw [ite_eq_right hr, ite_eq_left rfl, ite_eq_left (Fin.rev_rev a),
        ite_eq_right (fun h => hr (by rw [Fin.rev_rev] at h; exact h.symm)), ite_eq_left rfl]
      have hm : ¬ (a : ℕ) + a + 1 = n := fun h => hr (Fin.ext (by rw [Fin.val_rev]; omega))
      simp only [wittA, wittB, Fin.val_rev]
      by_cases h1 : (a : ℕ) + a + 1 < n
      · split_ifs <;> first | (exfalso; omega) |
          (simp only [map_add, map_one]; linear_combination σ γ * h2)
      · split_ifs <;> first | (exfalso; omega) |
          (simp only [map_one]; linear_combination γ * h2)
    · have h3 : ¬ Fin.rev b = a := fun h => h2' (by rw [← h, Fin.rev_rev])
      have h4 : ¬ Fin.rev b = Fin.rev a := fun h => hab (Fin.rev_injective h)
      rw [ite_eq_right hab, ite_eq_right h2', ite_eq_right h3, ite_eq_right h4, ite_eq_right h2']
      ring

theorem permGL_mul_apply (π : Equiv.Perm (Fin n)) (M : Matrix (Fin n) (Fin n) F) (r c : Fin n) :
    (((permGL π : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * M) r c = M (π⁻¹ r) c := by
  rw [Matrix.mul_apply]
  simp only [TableBUE.permGL_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

theorem mul_ggInvUMatrix_apply {l : ℕ} (hl : 2 * l ≤ n) (M : Matrix (Fin n) (Fin n) F)
    (r c : Fin n) :
    (M * ggInvUMatrix n l F) r c = M r c + if (c : ℕ) < l then M r (Fin.rev c) else 0 := by
  rw [ggInvUMatrix, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  have hc := c.isLt
  split_ifs with hcl
  · rw [Finset.sum_eq_single (Fin.rev c)]
    · rw [ggInvUNil_apply, ite_eq_left ⟨hcl, by simp only [Fin.val_rev]; omega,
        by simp only [Fin.val_rev]; omega⟩, mul_one]
    · intro k _ hk
      rw [ggInvUNil_apply, ite_eq_right (fun h => hk (Fin.ext (by
        simp only [Fin.val_rev]
        omega))), mul_zero]
    · simp
  · refine Finset.sum_eq_zero fun k _ => ?_
    rw [ggInvUNil_apply, ite_eq_right (fun h => hcl h.1), mul_zero]

theorem permGL_ggPairPerm_mul_wittMat [CharP F 2] {l : ℕ} (hl : 2 * l ≤ n) (γ : F) :
    ((permGL (ggPairPerm n l) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * wittMat n γ =
      wittMat n γ * ggInvUMatrix n l F := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext r c
  rw [permGL_mul_apply, mul_ggInvUMatrix_apply hl, ggPairPerm_inv]
  have hinv : ∀ x y : Fin n, ggPairPerm n l x = y ↔ x = ggPairPerm n l y := fun x y => by
    constructor
    · rintro rfl
      exact ((ggPairInv_involutive n l) x).symm
    · rintro rfl
      exact (ggPairInv_involutive n l) y
  have hc := c.isLt
  simp only [wittMat_apply, hinv, Fin.rev_rev]
  by_cases hcl : (c : ℕ) < l
  · have hcrc : c ≠ Fin.rev c := fun h => by
      have := congrArg Fin.val h
      rw [Fin.val_rev] at this
      omega
    have hπc : ggPairPerm n l c = Fin.rev c := by
      rw [ggPairPerm_apply, ggPairInv, ite_eq_left (Or.inl hcl)]
    have hπrc : ggPairPerm n l (Fin.rev c) = c := by
      rw [ggPairPerm_apply, ggPairInv, ite_eq_left (Or.inr (by rw [Fin.rev_rev]; exact hcl)),
        Fin.rev_rev]
    have hA : wittA n γ c = γ := ite_eq_left (by omega)
    have hB : wittB n γ c = γ + 1 := ite_eq_left (by omega)
    have hArc : wittA n γ (Fin.rev c) = 1 := ite_eq_right (by rw [Fin.val_rev]; omega)
    have hBrc : wittB n γ (Fin.rev c) = 1 := by
      rw [wittB, ite_eq_right (by rw [Fin.val_rev]; omega),
        ite_eq_left (by rw [Fin.val_rev]; omega)]
    rw [hπc, hπrc, ite_eq_left hcl, hA, hB, hArc, hBrc]
    by_cases hr1 : r = c
    · rw [ite_eq_right (fun h => hcrc (hr1.symm.trans h)), ite_eq_left hr1, ite_eq_left hr1,
        ite_eq_right (fun h => hcrc (hr1.symm.trans h)),
        ite_eq_right (fun h => hcrc (hr1.symm.trans h)), ite_eq_left hr1]
      ring
    · by_cases hr2 : r = Fin.rev c
      · rw [ite_eq_left hr2, ite_eq_right hr1, ite_eq_right hr1, ite_eq_left hr2, ite_eq_left hr2,
          ite_eq_right hr1]
        linear_combination (-1 : F) * h2
      · rw [ite_eq_right hr2, ite_eq_right hr1, ite_eq_right hr1, ite_eq_right hr2,
          ite_eq_right hr2, ite_eq_right hr1]
        ring
  · rw [ite_eq_right hcl]
    by_cases hrcl : (Fin.rev c : ℕ) < l
    · have hπc : ggPairPerm n l c = Fin.rev c := by
        rw [ggPairPerm_apply, ggPairInv, ite_eq_left (Or.inr hrcl)]
      have hπrc : ggPairPerm n l (Fin.rev c) = c := by
        rw [ggPairPerm_apply, ggPairInv, ite_eq_left (Or.inl hrcl), Fin.rev_rev]
      have hA : wittA n γ c = 1 := ite_eq_right (by rw [Fin.val_rev] at hrcl; omega)
      have hB : wittB n γ c = 1 := by
        rw [wittB, ite_eq_right (by rw [Fin.val_rev] at hrcl; omega),
          ite_eq_left (by rw [Fin.val_rev] at hrcl; omega)]
      rw [hπc, hπrc, hA, hB]
      ring
    · have hπc : ggPairPerm n l c = c := by
        rw [ggPairPerm_apply, ggPairInv, ite_eq_right (by tauto)]
      have hπrc : ggPairPerm n l (Fin.rev c) = Fin.rev c := by
        rw [ggPairPerm_apply, ggPairInv, ite_eq_right (by rw [Fin.rev_rev]; tauto)]
      rw [hπc, hπrc]
      ring

end Witt

section Conj

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_SU_conj_of_isometry {σ : F ≃+* F} (hn : 2 ≤ n) {l : ℕ} (hl : 2 * l ≤ n)
    {A : Matrix (Fin n) (Fin n) F} (hAiso : conjTr σ A * antidiag n * A = antidiag n)
    {u : SU σ n} (hUA : mat σ n u * A = A * ggInvUMatrix n l F) :
    ∃ a : SU σ n, u = a * ggInvSU σ n l * a⁻¹ := by
  have hdetJ := det_antidiag_ne_zero (F := F) n
  set d := A.det with hd
  have hσd : σ d * d = 1 := by
    have h := congrArg Matrix.det hAiso
    have hmap : (A.map σ).det = σ A.det := (RingHom.map_det (σ : F →+* F) A).symm
    rw [Matrix.det_mul, Matrix.det_mul, conjTr, Matrix.det_transpose, hmap] at h
    have h' : (σ d * d - 1) * (antidiag n : Matrix (Fin n) (Fin n) F).det = 0 := by
      change σ d * (antidiag n : Matrix (Fin n) (Fin n) F).det * d =
        (antidiag n : Matrix (Fin n) (Fin n) F).det at h
      linear_combination h
    rcases mul_eq_zero.mp h' with h'' | h''
    · linear_combination h''
    · exact absurd h'' hdetJ
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hσd
    exact zero_ne_one hσd
  obtain ⟨μ, hμ⟩ := isSquare_of_charTwo' d⁻¹
  have hσμ : σ μ * μ = 1 := by
    refine eq_of_mul_self_eq_mul_self_charTwo ?_
    calc σ μ * μ * (σ μ * μ) = σ (μ * μ) * (μ * μ) := by rw [map_mul]; ring
      _ = σ d⁻¹ * d⁻¹ := by rw [← hμ]
      _ = (σ d * d)⁻¹ := by rw [map_inv₀, mul_inv]
      _ = 1 * 1 := by rw [hσd, inv_one, one_mul]
  set e : Fin n → F := Pi.mulSingle (⟨0, by omega⟩ : Fin n) μ *
    Pi.mulSingle (Fin.rev (⟨0, by omega⟩ : Fin n)) μ with he
  have he_val : ∀ x : Fin n, e x = if (x : ℕ) = 0 ∨ (x : ℕ) = n - 1 then μ else 1 := by
    intro x
    have := x.isLt
    simp only [he, Pi.mul_apply, Pi.mulSingle_apply, Fin.ext_iff, Fin.val_rev]
    split_ifs <;> first | (exfalso; omega) | simp
  have hprod : ∏ x, e x = μ * μ := by
    simp only [he, Pi.mul_apply, Finset.prod_mul_distrib, Finset.prod_pi_mulSingle',
      Finset.mem_univ, ite_true]
  have hDiso : conjTr σ (Matrix.diagonal e) * antidiag n * Matrix.diagonal e = antidiag n := by
    ext a b
    have ha := a.isLt
    rw [conjTr, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.mul_diagonal,
      Matrix.diagonal_mul]
    simp only [antidiag, of_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    split_ifs with hab
    · subst hab
      rw [he_val, he_val]
      simp only [Fin.val_rev]
      split_ifs <;> first | (exfalso; omega) | simp [hσμ]
    · rfl
  have hDcomm : ggInvUMatrix n l F * Matrix.diagonal e =
      Matrix.diagonal e * ggInvUMatrix n l F := by
    ext a b
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [ggInvUMatrix, Matrix.add_apply, Matrix.one_apply, ggInvUNil_apply]
    by_cases hab : a = b
    · subst hab
      ring
    · rw [ite_eq_right hab, zero_add]
      split_ifs with h
      · rw [one_mul, mul_one, he_val, he_val]
        have := a.isLt
        split_ifs <;> first | rfl | (exfalso; omega)
      · rw [mul_zero, zero_mul]
  have hADdet : (A * Matrix.diagonal e).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_diagonal, hprod, ← hμ, ← hd, mul_inv_cancel₀ hd0]
  have hADiso : conjTr σ (A * Matrix.diagonal e) * antidiag n * (A * Matrix.diagonal e) =
      antidiag n := by
    rw [conjTr_mul]
    calc conjTr σ (Matrix.diagonal e) * conjTr σ A * antidiag n * (A * Matrix.diagonal e) =
        conjTr σ (Matrix.diagonal e) * (conjTr σ A * antidiag n * A) * Matrix.diagonal e := by
          simp only [Matrix.mul_assoc]
      _ = antidiag n := by rw [hAiso, hDiso]
  let g : GL (Fin n) F := Matrix.GeneralLinearGroup.mkOfDetNeZero (A * Matrix.diagonal e)
    (by rw [hADdet]; exact one_ne_zero)
  have hg : g ∈ SU σ n := ⟨hADdet, hADiso⟩
  let a : SU σ n := ⟨g, hg⟩
  refine ⟨a, ?_⟩
  have hua : u * a = a * ggInvSU σ n l := by
    apply mat_injective
    rw [map_mul, map_mul]
    change mat σ n u * (A * Matrix.diagonal e) = A * Matrix.diagonal e * mat σ n (ggInvSU σ n l)
    rw [mat_apply (ggInvSU σ n l), coe_ggInvSU σ hl, ← Matrix.mul_assoc, hUA, Matrix.mul_assoc,
      Matrix.mul_assoc, hDcomm]
  calc u = u * a * a⁻¹ := by group
    _ = a * ggInvSU σ n l * a⁻¹ := by rw [hua]

end Conj

section Frame

variable {G : Type} [Group G] {n f : ℕ} {F : Type} [Field F] [Finite F] [Fact (Nat.Prime 2)]
  [CharP F 2]

@[expose] noncomputable def ggFrameEquiv (hF : Nat.card F = (2 ^ f) ^ 2) (P : GL (Fin n) F)
    (hP : conjTr (unitaryInvolution F 2 f) (P : Matrix (Fin n) (Fin n) F) *
      (P : Matrix (Fin n) (Fin n) F) = antidiag n) :
    SU (unitaryInvolution F 2 f) n ≃* ↥(unitarySU 2 f F n) :=
  (conjEquiv P hP).trans (MulEquiv.subgroupCongr (SUid_eq_statedSU hF n))

theorem coe_ggFrameEquiv_symm (hF : Nat.card F = (2 ^ f) ^ 2) (P : GL (Fin n) F)
    (hP : conjTr (unitaryInvolution F 2 f) (P : Matrix (Fin n) (Fin n) F) *
      (P : Matrix (Fin n) (Fin n) F) = antidiag n) (s : ↥(unitarySU 2 f F n)) :
    (((ggFrameEquiv hF P hP).symm s : SU (unitaryInvolution F 2 f) n) : GL (Fin n) F) =
      P⁻¹ * s * P :=
  rfl

@[expose] noncomputable def ggFrameU (hF : Nat.card F = (2 ^ f) ^ 2)
    (ψ : SU (unitaryInvolution F 2 f) n →* G) (P : GL (Fin n) F)
    (hP : conjTr (unitaryInvolution F 2 f) (P : Matrix (Fin n) (Fin n) F) *
      (P : Matrix (Fin n) (Fin n) F) = antidiag n) : ↥(unitarySU 2 f F n) →* G :=
  ψ.comp (ggFrameEquiv hF P hP).symm.toMonoidHom

variable (hF : Nat.card F = (2 ^ f) ^ 2) (ψ : SU (unitaryInvolution F 2 f) n →* G)
  (P : GL (Fin n) F)
  (hP : conjTr (unitaryInvolution F 2 f) (P : Matrix (Fin n) (Fin n) F) *
    (P : Matrix (Fin n) (Fin n) F) = antidiag n)

theorem ggFrameU_apply (s : ↥(unitarySU 2 f F n)) :
    ggFrameU hF ψ P hP s = ψ ((ggFrameEquiv hF P hP).symm s) :=
  rfl

theorem range_ggFrameU : (ggFrameU hF ψ P hP).range = ψ.range := by
  rw [ggFrameU, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (ggFrameEquiv hF P hP).symm.surjective, ← MonoidHom.range_eq_map]

theorem ker_ggFrameU_le (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) n)) :
    (ggFrameU hF ψ P hP).ker ≤ Subgroup.center ↥(unitarySU 2 f F n) := by
  intro z hz
  set E := ggFrameEquiv hF P hP with hE
  have hz' : E.symm z ∈ Subgroup.center (SU (unitaryInvolution F 2 f) n) := hker hz
  rw [Subgroup.mem_center_iff] at hz' ⊢
  intro g
  apply E.symm.injective
  rw [map_mul, map_mul]
  exact hz' (E.symm g)

theorem ggFrameKer_ggFrameU (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2))
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) n)) :
    GGFrameKer (ggFrameU hF ψ P hP) :=
  ggFrameKer_of_ker_le_center hF hn hnq (ker_ggFrameU_le hF ψ P hP hker)

omit [Finite F] [Fact (Nat.Prime 2)] in
theorem permGL_mem_unitarySU (h : UnitaryFieldData 2 f F) (π : Equiv.Perm (Fin n)) :
    (permGL π : GL (Fin n) F) ∈ unitarySU 2 f F n := by
  rw [mem_unitarySU_iff h]
  refine ⟨?_, permGL_unitary h π⟩
  rw [det_permGL]
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hs | hs <;> simp [hs, CharTwo.neg_eq]

omit [Finite F] [Fact (Nat.Prime 2)] [CharP F 2] in
theorem conjTr_eq_bar [Finite F] [Fact (Nat.Prime 2)] [CharP F 2] (h : UnitaryFieldData 2 f F)
    (M : Matrix (Fin n) (Fin n) F) :
    conjTr (unitaryInvolution F 2 f) M = (M.map h.bar)ᵀ := by
  rw [conjTr]
  congr 1

theorem exists_conj_ggInvSU_frame (h : UnitaryFieldData 2 f F) (hn : 2 ≤ n) {l : ℕ}
    (hl : 2 * l ≤ n) (ρ : Equiv.Perm (Fin n)) :
    ∃ w : SU (unitaryInvolution F 2 f) n,
      ggFrameU hF ψ P hP ⟨permGL (ρ * ggPairPerm n l * ρ⁻¹), permGL_mem_unitarySU h _⟩ =
        ψ (w * ggInvSU (unitaryInvolution F 2 f) n l * w⁻¹) := by
  set σ := unitaryInvolution F 2 f with hσ
  obtain ⟨γ, hγ⟩ :=
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hF).trace_surj 1
      (map_one σ)
  have hγ' : σ γ + γ = 1 := by rw [add_comm]; exact hγ
  set W := wittMat n γ with hWdef
  have hW : conjTr σ W * W = antidiag n := conjTr_wittMat_mul σ hγ'
  set v : ↥(unitarySU 2 f F n) := ⟨permGL (ρ * ggPairPerm n l * ρ⁻¹), permGL_mem_unitarySU h _⟩
    with hv
  set u := (ggFrameEquiv hF P hP).symm v with hu
  set Pm := (P : Matrix (Fin n) (Fin n) F) with hPm
  set Pi := ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hPi
  set R := ((permGL ρ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hR
  set A := Pi * R * W with hA
  have hPPi : Pm * Pi = 1 := by rw [hPm, hPi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPiP : Pi * Pm = 1 := by rw [hPm, hPi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hPJ : conjTr σ Pi * antidiag n * Pi = 1 := by
    rw [← hP]
    calc conjTr σ Pi * (conjTr σ Pm * Pm) * Pi = conjTr σ (Pm * Pi) * (Pm * Pi) := by
          simp only [conjTr_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hPPi, conjTr_one, Matrix.one_mul]
  have hRR : conjTr σ R * R = 1 := by rw [conjTr_eq_bar h]; exact permGL_unitary h ρ
  have hAiso : conjTr σ A * antidiag n * A = antidiag n := by
    rw [hA]
    calc conjTr σ (Pi * R * W) * antidiag n * (Pi * R * W) =
        conjTr σ W * (conjTr σ R * (conjTr σ Pi * antidiag n * Pi) * R) * W := by
          simp only [conjTr_mul, Matrix.mul_assoc]
      _ = antidiag n := by rw [hPJ, Matrix.mul_one, hRR, Matrix.mul_one, hW]
  have hUA : mat σ n u * A = A * ggInvUMatrix n l F := by
    have hmat : mat σ n u = Pi * (R * ((permGL (ggPairPerm n l) : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) * (((permGL ρ)⁻¹ : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F)) * Pm := by
      rw [mat_apply, hu, coe_ggFrameEquiv_symm, hv]
      simp only [map_mul, map_inv, Units.val_mul]
      rfl
    have hRi : (((permGL ρ)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * R = 1 := by
      rw [hR, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [hmat, hA]
    calc Pi * (R * ((permGL (ggPairPerm n l) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          (((permGL ρ)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) * Pm * (Pi * R * W) =
        Pi * R * (((permGL (ggPairPerm n l) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          ((((permGL ρ)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ((Pm * Pi) * R)) * W) := by
          simp only [Matrix.mul_assoc]
      _ = Pi * R * (((permGL (ggPairPerm n l) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * W) := by
          rw [hPPi, Matrix.one_mul, hRi, Matrix.mul_one]
      _ = Pi * R * W * ggInvUMatrix n l F := by
          rw [permGL_ggPairPerm_mul_wittMat hl γ, ← Matrix.mul_assoc]
  obtain ⟨a, ha⟩ := exists_SU_conj_of_isometry hn hl hAiso hUA
  exact ⟨a, by rw [ggFrameU_apply, ← hu, ha]⟩

end Frame

section Beta

variable {G : Type} [Group G]

theorem ggRootFusionWitnessAlt_of_conj_commU {U : Type*} [Group U] (ψ : U →* G) {p : ℕ}
    {Bs D E G₀ M : Subgroup G} {t : StatedLieTag} {e : ℕ} {r : G} {u w : U} {b : G}
    (hcomm : b * ψ (w * u * w⁻¹) = ψ (w * u * w⁻¹) * b) (hwM : ψ w ∈ M)
    (hW : GGSixFusionWitness p Bs D E G₀ t e b) :
    GGRootFusionWitnessAlt p Bs D E G₀ M t e r (ψ u) := by
  refine Or.inr (Or.inl ⟨(ψ w)⁻¹ * b * ψ w, ?_, ψ w, hwM, ?_⟩)
  · have h : b * (ψ w * ψ u * (ψ w)⁻¹) = (ψ w * ψ u * (ψ w)⁻¹) * b := by
      simpa only [map_mul, map_inv] using hcomm
    calc (ψ w)⁻¹ * b * ψ w * ψ u = (ψ w)⁻¹ * (b * (ψ w * ψ u * (ψ w)⁻¹)) * ψ w := by group
      _ = (ψ w)⁻¹ * ((ψ w * ψ u * (ψ w)⁻¹) * b) * ψ w := by rw [h]
      _ = ψ u * ((ψ w)⁻¹ * b * ψ w) := by group
  · have he : ψ w * ((ψ w)⁻¹ * b * ψ w) * (ψ w)⁻¹ = b := by group
    rw [he]
    exact hW

variable {n f : ℕ} {F : Type} [Field F] [Finite F] [Fact (Nat.Prime 2)] [CharP F 2]

omit [Finite F] [Fact (Nat.Prime 2)] in
theorem conjU_permGL_eq_self (h : UnitaryFieldData 2 f F) {τ : Fin n → Fˣ}
    (hτ : ∀ i, (τ i : F) ^ (2 ^ f + 1) = 1) {π : Equiv.Perm (Fin n)}
    (hπ : ∀ a, τ (π a) = τ a) :
    conjU h hτ ⟨permGL π, permGL_mem_unitarySU h π⟩ = ⟨permGL π, permGL_mem_unitarySU h π⟩ := by
  apply Subtype.ext
  rw [coe_conjU]
  have h1 := permGL_mul_diagHom_mul_inv (K := F) π τ
  have h2 : τ ∘ ⇑π.symm = τ := by
    funext a
    simp only [Function.comp_apply]
    have := hπ (π.symm a)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  rw [h2] at h1
  change diagHom n τ * permGL π * (diagHom n τ)⁻¹ = permGL π
  calc diagHom n τ * permGL π * (diagHom n τ)⁻¹ =
      (permGL π * diagHom n τ * (permGL π)⁻¹) * permGL π * (diagHom n τ)⁻¹ := by rw [h1]
    _ = permGL π := by group

theorem ggRootFusionWitnessAlt_of_frameU (hF : Nat.card F = (2 ^ f) ^ 2)
    (h : UnitaryFieldData 2 f F) (hn : 2 ≤ n) {l : ℕ} (hl : 2 * l ≤ n)
    {ψ : SU (unitaryInvolution F 2 f) n →* G} {P : GL (Fin n) F}
    {hP : conjTr (unitaryInvolution F 2 f) (P : Matrix (Fin n) (Fin n) F) *
      (P : Matrix (Fin n) (Fin n) F) = antidiag n}
    {p : ℕ} {Bs D E G₀ M : Subgroup G} {t : StatedLieTag} {e : ℕ} {r : G} (hle : ψ.range ≤ M)
    {b : G} {τ : Fin n → Fˣ} (hb : GGFrameActs (ggFrameU hF ψ P hP) b τ)
    (hW : GGSixFusionWitness p Bs D E G₀ t e b) (ρ : Equiv.Perm (Fin n))
    (hpair : ∀ c : Fin n, (c : ℕ) < l → τ (ρ c) = τ (ρ (Fin.rev c))) :
    GGRootFusionWitnessAlt p Bs D E G₀ M t e r (ψ (ggInvSU (unitaryInvolution F 2 f) n l)) := by
  obtain ⟨w, hw⟩ := exists_conj_ggInvSU_frame hF ψ P hP h hn hl ρ
  have hπ : ∀ a, τ ((ρ * ggPairPerm n l * ρ⁻¹) a) = τ a := by
    intro a
    obtain ⟨c, rfl⟩ := ρ.surjective a
    have hc' : ρ⁻¹ (ρ c) = c := Equiv.Perm.inv_eq_iff_eq.mpr rfl
    simp only [Equiv.Perm.mul_apply, hc', ggPairPerm_apply, ggPairInv]
    split_ifs with hc
    · rcases hc with hc | hc
      · exact (hpair c hc).symm
      · have := hpair (Fin.rev c) hc
        rw [Fin.rev_rev] at this
        exact this
    · rfl
  have hfix := conjU_permGL_eq_self h hb.1 hπ
  have hcomm : b * ggFrameU hF ψ P hP ⟨permGL (ρ * ggPairPerm n l * ρ⁻¹),
      permGL_mem_unitarySU h _⟩ = ggFrameU hF ψ P hP ⟨permGL (ρ * ggPairPerm n l * ρ⁻¹),
      permGL_mem_unitarySU h _⟩ * b := by
    have h1 := hb.apply h ⟨permGL (ρ * ggPairPerm n l * ρ⁻¹), permGL_mem_unitarySU h _⟩
    rw [hfix] at h1
    calc b * ggFrameU hF ψ P hP ⟨permGL (ρ * ggPairPerm n l * ρ⁻¹), permGL_mem_unitarySU h _⟩ =
        b * ggFrameU hF ψ P hP ⟨permGL (ρ * ggPairPerm n l * ρ⁻¹), permGL_mem_unitarySU h _⟩ *
          b⁻¹ * b := by group
      _ = _ := by rw [h1]
  rw [hw] at hcomm
  exact ggRootFusionWitnessAlt_of_conj_commU ψ hcomm (hle ⟨w, rfl⟩) hW

end Beta

end SURep

end CFSG.StandardType
