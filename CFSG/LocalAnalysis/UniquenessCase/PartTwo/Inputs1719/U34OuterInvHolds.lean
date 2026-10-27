module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U34OuterInvolution
public import CFSG.RankThree.PartTwo.KFacts.KS21U34
public import CFSG.GH74.Uniqueness.Bender.AutFixed
import CFSG.CGT.T75A.Lemma21

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.GH74.KGroups Matrix CFSG.LieType.Universal.Unitary
open CFSG.RankThree.PartTwo.KFacts.KS21.U34 CFSG.GH74.Uniqueness.Bender

theorem u34outer_mem_centralizer_autFixed {G : Type*} [Group G] {σ τ : MulAut G}
    (hτσ : τ * σ = σ * τ) {z : G} (hz : z ∈ Subgroup.centralizer (autFixed σ : Set G)) :
    τ z ∈ Subgroup.centralizer (autFixed σ : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hz ⊢
  intro f hf
  have h1 : σ * τ⁻¹ = τ⁻¹ * σ := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hτσ, ← mul_assoc, inv_mul_cancel, one_mul]
  have hf2 : σ f = f := hf
  have hf' : τ⁻¹ f ∈ autFixed σ := by
    rw [mem_autFixed_iff, ← MulAut.mul_apply, h1, MulAut.mul_apply, hf2]
  calc f * τ z = τ (τ⁻¹ f) * τ z := by rw [MulAut.apply_inv_self]
    _ = τ (τ⁻¹ f * z) := by rw [map_mul]
    _ = τ (z * τ⁻¹ f) := by rw [hz _ hf']
    _ = τ z * f := by rw [map_mul, MulAut.apply_inv_self]

theorem u34outer_transport {G H : Type*} [Group G] [Group H] (ψ : G ≃* H) {σ : MulAut G}
    {σ' : MulAut H} (hψ : MulAut.congr ψ σ = σ') {x' : H}
    (h : orderOf x' = 5 ∧ σ' x' = x'⁻¹ ∧
      ∀ τ' : MulAut H, τ' * σ' = σ' * τ' → τ' x' ∈ Subgroup.zpowers x') :
    ∃ x : G, orderOf x = 5 ∧ σ x = x⁻¹ ∧
      ∀ τ : MulAut G, τ * σ = σ * τ → τ x ∈ Subgroup.zpowers x := by
  obtain ⟨h5, hinv, hτ⟩ := h
  have hc : ∀ (α : MulAut G) (y : H), α (ψ.symm y) = ψ.symm (MulAut.congr ψ α y) := by
    intro α y
    simp [MulAut.congr_apply]
  refine ⟨ψ.symm x', by rw [MulEquiv.orderOf_eq, h5], by rw [hc, hψ, hinv, map_inv],
    fun τ hτσ => ?_⟩
  have hcomm : MulAut.congr ψ τ * σ' = σ' * MulAut.congr ψ τ := by
    rw [← hψ, ← map_mul, ← map_mul, hτσ]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hτ _ hcomm)
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [← map_zpow, hk, hc]

theorem u34outer_σ16_σ16 (c : GF16) : σ16 (σ16 c) = c := by
  rw [σ16_apply, σ16_apply]
  revert c
  decide

theorem u34outer_map_antidiag : (antidiag 3 : Mat3).map σ16 = antidiag 3 := by
  rw [antidiag_three_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J3]

theorem u34outer_map_mem {g : GL (Fin 3) GF16} (hg : g ∈ Y) :
    Matrix.GeneralLinearGroup.map σ16.toRingHom g ∈ Y := by
  obtain ⟨hdet, hU⟩ := mem_SU.mp hg
  refine mem_SU.mpr ⟨?_, ?_⟩
  · change ((g : Mat3).map σ16).det = 1
    rw [← RingEquiv.mapMatrix_apply, ← RingEquiv.map_det, hdet, map_one]
  · change conjTr σ16 ((g : Mat3).map σ16) * antidiag 3 * (g : Mat3).map σ16 = antidiag 3
    have hc : conjTr σ16 ((g : Mat3).map σ16) = (conjTr σ16 (g : Mat3)).map σ16 := by
      ext i j
      rfl
    rw [hc, ← u34outer_map_antidiag, ← RingEquiv.mapMatrix_apply, ← RingEquiv.mapMatrix_apply,
      ← RingEquiv.mapMatrix_apply, ← map_mul, ← map_mul, hU]

@[expose] def u34outer_frobHom : Y →* Y :=
  ((Matrix.GeneralLinearGroup.map σ16.toRingHom).comp Y.subtype).codRestrict Y
    fun y => u34outer_map_mem y.2

theorem u34outer_mat_frobHom (y : Y) : mat (u34outer_frobHom y) = (mat y).map σ16 := rfl

theorem u34outer_frobHom_frobHom (y : Y) : u34outer_frobHom (u34outer_frobHom y) = y := by
  apply mat_injective
  rw [u34outer_mat_frobHom, u34outer_mat_frobHom]
  ext i j
  exact u34outer_σ16_σ16 _

@[expose] def u34outer_frob : MulAut Y :=
  u34outer_frobHom.toMulEquiv u34outer_frobHom (MonoidHom.ext u34outer_frobHom_frobHom)
    (MonoidHom.ext u34outer_frobHom_frobHom)

theorem u34outer_mat_frob (y : Y) : mat (u34outer_frob y) = (mat y).map σ16 := rfl

theorem u34outer_frob_mul_self : u34outer_frob * u34outer_frob = 1 :=
  MulEquiv.ext u34outer_frobHom_frobHom

theorem u34outer_frob_eq_of_entries {y : Y} (h : ∀ i j, frob4 (mat y i j) = mat y i j) :
    u34outer_frob y = y := by
  apply mat_injective
  ext i j
  rw [u34outer_mat_frob, Matrix.map_apply, σ16_apply, h]

theorem u34outer_entries_of_frob_eq {y : Y} (hy : u34outer_frob y = y) (i j : Fin 3) :
    frob4 (mat y i j) = mat y i j := by
  have h := congrFun (congrFun (congrArg mat hy) i) j
  rwa [u34outer_mat_frob, Matrix.map_apply, σ16_apply] at h

@[expose] def u34outer_x0Mat : Mat3 :=
  !![GF16.ofNat' 8, 0, 0; 0, GF16.ofNat' 10, 0; 0, 0, GF16.ofNat' 8]

@[expose] def u34outer_x0InvMat : Mat3 :=
  !![GF16.ofNat' 15, 0, 0; 0, GF16.ofNat' 12, 0; 0, 0, GF16.ofNat' 15]

@[expose] def u34outer_x0GL : GL (Fin 3) GF16 :=
  ⟨u34outer_x0Mat, u34outer_x0InvMat, by decide +kernel, by decide +kernel⟩

@[expose] def u34outer_x0 : Y := ⟨u34outer_x0GL, (mem_Y_iff _).mpr (by decide +kernel)⟩

theorem u34outer_mat_x0 : mat u34outer_x0 = u34outer_x0Mat := rfl

theorem u34outer_mat_pow (y : Y) (n : ℕ) : mat (y ^ n) = mat y ^ n := by
  change (((y ^ n : Y) : GL (Fin 3) GF16) : Mat3) = _
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]

theorem u34outer_x0_pow_five : u34outer_x0 ^ 5 = 1 := by
  apply mat_injective
  rw [u34outer_mat_pow, u34outer_mat_x0, mat_one]
  decide +kernel

theorem u34outer_x0_ne_one : u34outer_x0 ≠ 1 := fun h => by
  have h' := congrArg mat h
  rw [u34outer_mat_x0, mat_one] at h'
  exact absurd h' (by decide +kernel)

theorem u34outer_orderOf_x0 : orderOf u34outer_x0 = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime u34outer_x0_pow_five u34outer_x0_ne_one

theorem u34outer_frob_x0 : u34outer_frob u34outer_x0 = u34outer_x0⁻¹ := by
  apply mat_injective
  rw [u34outer_mat_frob, u34outer_mat_x0]
  change u34outer_x0Mat.map σ16 = u34outer_x0InvMat
  ext i j
  rw [Matrix.map_apply, σ16_apply]
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem u34outer_x0_inv_ne : u34outer_x0⁻¹ ≠ u34outer_x0 := fun h => by
  have h' := congrArg mat h
  change u34outer_x0InvMat = u34outer_x0Mat at h'
  exact absurd h' (by decide +kernel)

@[expose] def u34outer_t0GL : GL (Fin 3) GF16 :=
  ⟨t0Mat, t0Mat * t0Mat, by decide +kernel, by decide +kernel⟩

@[expose] def u34outer_t0 : Y := ⟨u34outer_t0GL, (mem_Y_iff _).mpr (by decide +kernel)⟩

theorem u34outer_mat_t0 : mat u34outer_t0 = t0Mat := rfl

@[expose] def u34outer_s0GL : GL (Fin 3) GF16 :=
  ⟨sMat 1, sMat 1, by decide +kernel, by decide +kernel⟩

@[expose] def u34outer_s0 : Y := ⟨u34outer_s0GL, (mem_Y_iff _).mpr (by decide +kernel)⟩

theorem u34outer_mat_s0 : mat u34outer_s0 = sMat 1 := rfl

theorem u34outer_frob_t0 : u34outer_frob u34outer_t0 = u34outer_t0 :=
  u34outer_frob_eq_of_entries fun i j => by
    rw [u34outer_mat_t0]
    fin_cases i <;> fin_cases j <;> decide +kernel

theorem u34outer_frob_s0 : u34outer_frob u34outer_s0 = u34outer_s0 :=
  u34outer_frob_eq_of_entries fun i j => by
    rw [u34outer_mat_s0]
    fin_cases i <;> fin_cases j <;> decide +kernel

theorem u34outer_diag_of_comm (S : Mat3) (h : S * t0Mat = t0Mat * S) :
    S 0 1 = 0 ∧ S 0 2 = 0 ∧ S 1 0 = 0 ∧ S 1 2 = 0 ∧ S 2 0 = 0 ∧ S 2 1 = 0 := by
  rw [t0Mat_eq_diagonal] at h
  have key : ∀ i j, S i j * ![om, 1, om * om] j = ![om, 1, om * om] i * S i j := by
    intro i j
    have := congrFun (congrFun h i) j
    rwa [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
  exact ⟨eq_zero_of_mul_eq (key 0 1) (by decide), eq_zero_of_mul_eq (key 0 2) (by decide),
    eq_zero_of_mul_eq (key 1 0) (by decide), eq_zero_of_mul_eq (key 1 2) (by decide),
    eq_zero_of_mul_eq (key 2 0) (by decide), eq_zero_of_mul_eq (key 2 1) (by decide)⟩

@[expose] def u34outer_dMat (u z : GF16) : Mat3 := !![u, 0, 0; 0, z, 0; 0, 0, u]

theorem u34outer_dMat_check : ∀ u z : GF16, det3 (u34outer_dMat u z) = 1 →
    IsGU3 (u34outer_dMat u z) → ∃ k : Fin 5, u34outer_dMat u z = u34outer_x0Mat ^ (k : ℕ) := by
  decide +kernel

theorem u34outer_mem_zpowers {y : Y} (ht : y * u34outer_t0 = u34outer_t0 * y)
    (hs : y * u34outer_s0 = u34outer_s0 * y) : y ∈ Subgroup.zpowers u34outer_x0 := by
  have ht' : mat y * t0Mat = t0Mat * mat y := by
    rw [← u34outer_mat_t0, ← mat_mul, ← mat_mul, ht]
  have hs' : mat y * sMat 1 = sMat 1 * mat y := by
    rw [← u34outer_mat_s0, ← mat_mul, ← mat_mul, hs]
  obtain ⟨h01, h02, h10, h12, h20, h21⟩ := u34outer_diag_of_comm _ ht'
  have h22 : mat y 2 2 = mat y 0 0 := by
    have := congrFun (congrFun (eq_commMat_of_comm _ (by decide) hs') 2) 2
    simpa [commMat] using this
  have hy : mat y = u34outer_dMat (mat y 0 0) (mat y 1 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [u34outer_dMat, h01, h02, h10, h12, h20, h21, h22]
  obtain ⟨hdet, hgu⟩ := (mem_Y_iff _).mp y.2
  change det3 (mat y) = 1 at hdet
  change IsGU3 (mat y) at hgu
  rw [hy] at hdet hgu
  obtain ⟨k, hk⟩ := u34outer_dMat_check _ _ hdet hgu
  refine Subgroup.mem_zpowers_iff.mpr ⟨(k : ℕ), ?_⟩
  rw [zpow_natCast]
  apply mat_injective
  rw [u34outer_mat_pow, u34outer_mat_x0, hy, hk]

theorem u34outer_fixed_comm {y : Y} (hy : u34outer_frob y = y) :
    y * u34outer_x0 = u34outer_x0 * y := by
  have hA := u34outer_entries_of_frob_eq hy
  obtain ⟨hdet, hgu⟩ := (mem_Y_iff _).mp y.2
  change det3 (mat y) = 1 at hdet
  change IsGU3 (mat y) at hgu
  have e : ∀ i j, (ct3 (mat y) * J3 * mat y) i j = J3 i j := fun i j => by rw [hgu]
  have h2 : (2 : GF16) = 0 := by decide
  have e00 := e 0 0
  have e22 := e 2 2
  have e01 := e 0 1
  have e21 := e 2 1
  simp [ct3, J3, Matrix.mul_apply, Fin.sum_univ_three, hA] at e00 e22 e01 e21
  have h10 : mat y 1 0 = 0 := mul_self_eq_zero.mp (by
    linear_combination e00 - mat y 0 0 * mat y 2 0 * h2)
  have h12 : mat y 1 2 = 0 := mul_self_eq_zero.mp (by
    linear_combination e22 - mat y 0 2 * mat y 2 2 * h2)
  have hD : mat y 0 0 * mat y 2 2 - mat y 0 2 * mat y 2 0 ≠ 0 := by
    intro hD
    have hd : mat y 1 1 * (mat y 0 0 * mat y 2 2 - mat y 0 2 * mat y 2 0) = 1 := by
      rw [← hdet, det3, h10, h12]
      ring
    rw [hD, mul_zero] at hd
    exact zero_ne_one hd
  have h21 : mat y 2 1 = 0 := (mul_eq_zero.mp (by
    linear_combination mat y 2 2 * e01 - mat y 2 0 * e21 - mat y 1 1 * mat y 2 2 * h10 +
      mat y 1 1 * mat y 2 0 * h12 :
    (mat y 0 0 * mat y 2 2 - mat y 0 2 * mat y 2 0) * mat y 2 1 = 0)).resolve_left hD
  have h01 : mat y 0 1 = 0 := (mul_eq_zero.mp (by
    linear_combination mat y 0 0 * e21 - mat y 0 2 * e01 + mat y 0 2 * mat y 1 1 * h10 -
      mat y 0 0 * mat y 1 1 * h12 :
    (mat y 0 0 * mat y 2 2 - mat y 0 2 * mat y 2 0) * mat y 0 1 = 0)).resolve_left hD
  apply mat_injective
  rw [mat_mul, mat_mul, u34outer_mat_x0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u34outer_x0Mat, Matrix.mul_apply, Fin.sum_univ_three, h01, h10, h12, h21, mul_comm]

theorem u34outer_x0_mem_centralizer :
    u34outer_x0 ∈ Subgroup.centralizer (autFixed u34outer_frob : Set Y) :=
  Subgroup.mem_centralizer_iff.mpr fun _ hf => u34outer_fixed_comm hf

theorem u34outer_centralizer_autFixed :
    Subgroup.centralizer (autFixed u34outer_frob : Set Y) = Subgroup.zpowers u34outer_x0 := by
  refine le_antisymm (fun y hy => ?_) (Subgroup.zpowers_le.mpr u34outer_x0_mem_centralizer)
  have h := Subgroup.mem_centralizer_iff.mp hy
  exact u34outer_mem_zpowers (h _ u34outer_frob_t0).symm (h _ u34outer_frob_s0).symm

theorem u34outer_frob_not_mem : u34outer_frob ∉ (MulAut.conj : Y →* MulAut Y).range := by
  rintro ⟨g, hg⟩
  have hfix : ∀ y, u34outer_frob y = y → g * y = y * g := by
    intro y h1
    rw [← hg, MulAut.conj_apply] at h1
    calc g * y = g * y * g⁻¹ * g := by group
      _ = y * g := by rw [h1]
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp
    (u34outer_mem_zpowers (hfix _ u34outer_frob_t0) (hfix _ u34outer_frob_s0))
  have h2 : u34outer_frob u34outer_x0 = u34outer_x0 := by
    rw [← hg, MulAut.conj_apply]
    group
  rw [u34outer_frob_x0] at h2
  exact u34outer_x0_inv_ne h2

theorem u34outer_model :
    orderOf u34outer_x0 = 5 ∧ u34outer_frob u34outer_x0 = u34outer_x0⁻¹ ∧
      ∀ τ : MulAut Y, τ * u34outer_frob = u34outer_frob * τ →
        τ u34outer_x0 ∈ Subgroup.zpowers u34outer_x0 := by
  refine ⟨u34outer_orderOf_x0, u34outer_frob_x0, fun τ hτ => ?_⟩
  rw [← u34outer_centralizer_autFixed]
  exact u34outer_mem_centralizer_autFixed hτ u34outer_x0_mem_centralizer

theorem k_U34OuterInv_holds : K_U34OuterInv := by
  intro Q _ _ hQ σ hσσ hσout
  have hS := CFSG.Blueprint.LieModel.statedClassicalModel hQ (by decide)
  obtain ⟨eU⟩ := CFSG.CGT.Timmesfeld75.exists_psu3_of_statedClassicalModel le_rfl hS
  obtain ⟨e⟩ := nonempty_equiv_Y hS
  let eY : Y ≃* CFSG.Theory.Comparator.PSU3Model 2 := e.symm.trans (eU.trans
    (MulEquiv.subgroupCongr (show CFSG.Open.PSU3 2 2 = CFSG.Theory.Comparator.PSU3Model 2 from rfl)))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ1 : σ ≠ 1 := fun h => hσout ⟨1, by rw [map_one, h]⟩
  have hσY : orderOf (MulAut.congr e σ) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [sq, hσσ]) hσ1
  have hσYout : MulAut.congr e σ ∉ (MulAut.conj : Y →* MulAut Y).range := by
    rintro ⟨g, hg⟩
    refine hσout ⟨e.symm g, MulEquiv.ext fun q => e.injective ?_⟩
    have h1 := congrArg (fun φ : MulAut Y => φ (e q)) hg
    simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply] at h1
    simp [MulAut.conj_apply, h1]
  have hfrob1 : u34outer_frob ≠ 1 := fun h => u34outer_frob_not_mem ⟨1, by rw [map_one, h]⟩
  have hfrob : orderOf u34outer_frob = 2 :=
    orderOf_eq_prime (by rw [sq, u34outer_frob_mul_self]) hfrob1
  obtain ⟨β, hβ⟩ := isConj_iff.mp (CFSG.CGT.T75A.outer_involutions_conj_of_mulEquiv le_rfl eY
    hfrob hσY u34outer_frob_not_mem hσYout)
  refine u34outer_transport (e.trans β.symm) (MulEquiv.ext fun y => ?_) u34outer_model
  have h1 := congrArg (fun φ : MulAut Y => φ (β y)) hβ
  simp only [MulAut.mul_apply, MulAut.inv_apply_self] at h1
  simp only [MulAut.congr_apply, MulEquiv.trans_apply] at h1 ⊢
  rw [MulEquiv.symm_trans_apply, MulEquiv.symm_symm, ← h1, MulEquiv.symm_apply_apply]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
