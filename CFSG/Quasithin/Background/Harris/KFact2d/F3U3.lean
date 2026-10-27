module

public import CFSG.Quasithin.Background.Harris.KFact2d.Lin2
public import CFSG.Quasithin.Background.Harris.KFact2d.ModelU3
public import CFSG.Quasithin.Background.Harris.KFact2d.F1U3
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutMain
public import CFSG.ClassicalInvolution.AschTight.S19KUniIn
public import CFSG.Quasithin.Vol2.Ch3E213MOLA5
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP1Section6
public import CFSG.Quasithin.Vol2.Ch3E213MOLA4

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.Quasithin.E2P.Asc80 CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6
  CFSG.Quasithin.A312U3 CFSG.GH74.GLS.IVK.Proofs2 CFSG.ClassicalInvolution
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups Matrix


variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F] [CharP F p]

noncomputable def iotaU (hF : Nat.card F = p ^ 2) : Phan.Su F p 1 3 ≃* ↥(StatedSU 3 (p ^ 1) F) :=
  MulEquiv.subgroupCongr (SUid_eq_statedSU (p := p) (f := 1) (by simpa using hF) 3)

noncomputable def thetaU (hF : Nat.card F = p ^ 2) : Phan.Su F p 1 3 →* PSU3F p F :=
  (piU p F).comp (iotaU hF).toMonoidHom

theorem thetaU_surjective (hF : Nat.card F = p ^ 2) : Function.Surjective (thetaU hF) :=
  (piU_surjective (p := p) (F := F)).comp (iotaU hF).surjective

theorem thetaU_ker (hF : Nat.card F = p ^ 2) :
    (thetaU hF).ker ≤ Subgroup.center (Phan.Su F p 1 3) := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have h1 : (QuotientGroup.mk (iotaU hF x) : StatedProj (StatedSU 3 (p ^ 1) F)) = 1 := hx
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  have hc : ((x : Phan.Su F p 1 3) : GL (Fin 3) F) ∈ Subgroup.center (GL (Fin 3) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact h1
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro y
  exact Subtype.ext (hc y)


theorem exists_scU_of_central (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) {A : ↥(GU2Stated (p ^ 1) F)}
    (hcen : ∀ B : ↥(GU2Stated (p ^ 1) F), A * B = B * A) (hSU : ∃ c d : ↥(StatedSU 2 (p ^ 1) F),
      QuatPair c d) :
    ∃ (a : Fˣ) (ha : (a : F) ^ (p + 1) = 1), A = scU a ha := by
  obtain ⟨c, d, hQ⟩ := hSU
  have h2 : (2 : F) ≠ 0 := two_ne_zero_u hp2 hF
  have hQ' := hQ.map (StatedSU 2 (p ^ 1) F).subtype (StatedSU 2 (p ^ 1) F).subtype_injective
  obtain ⟨hC, hD, hDC⟩ := quat_relations h2 (det_of_mem_su2 hF c) hQ'
  have hYc : ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg (fun y : ↥(GU2Stated (p ^ 1) F) => ((y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
      (hcen (Subgroup.inclusion su2_le_gu2 c))
    simp only [Subgroup.coe_mul, Units.val_mul] at this
    exact this
  have hYd : ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((d : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((d : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg (fun y : ↥(GU2Stated (p ^ 1) F) => ((y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
      (hcen (Subgroup.inclusion su2_le_gu2 d))
    simp only [Subgroup.coe_mul, Units.val_mul] at this
    exact this
  have hnc : ((c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((d : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ≠
      ((d : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    intro h
    have h3 : ((c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((d : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 0 := by
      have h4 : (2 : F) • (((c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          ((d : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) = 0 := by
        rw [two_smul]
        have hDC' : ((d : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
            -(((c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((d : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) := hDC
        calc _ = ((c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((d : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) +
            ((d : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by rw [← h]
          _ = 0 := by rw [hDC']; simp
      rcases smul_eq_zero.mp h4 with h5 | h5
      · exact absurd h5 h2
      · exact h5
    have hdet := congrArg Matrix.det h3
    rw [Matrix.det_mul, det_of_mem_su2 hF c, det_of_mem_su2 hF d] at hdet
    simp at hdet
  obtain ⟨h01, h10, h00⟩ := CFSG.Quasithin.Ch3E213M.OLA.isScalar_of_commute_two hYc hYd hnc
  set Y := ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hYdef
  have hY : Y = Matrix.scalar (Fin 2) (Y 0 0) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, h01, h10, h00]
  have hdet : Y.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det Y).mp (A : GL (Fin 2) F).isUnit).ne_zero
  have a0 : Y 0 0 ≠ 0 := by
    intro h0
    apply hdet
    rw [hY, h0]
    simp
  have ha : ((Units.mk0 (Y 0 0) a0 : Fˣ) : F) ^ (p + 1) = 1 := by
    have hu : (Y.map (· ^ p))ᵀ * Y = 1 := unitary_eq hF A.2
    have e00 := congrFun (congrFun hu 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, zero_pow (Fact.out : p.Prime).ne_zero] at e00
    rw [pow_succ]
    simpa using e00
  refine ⟨Units.mk0 (Y 0 0) a0, ha, ?_⟩
  apply Subtype.ext
  apply Units.ext
  show Y = Matrix.scalar (Fin 2) (Y 0 0)
  exact hY


theorem blockzero_F (h2 : (2 : F) ≠ 0) {g : Matrix (Fin 3) (Fin 3) F}
    (h : g * CFSG.RankThree.Classical.negNegOneDiag F = CFSG.RankThree.Classical.negNegOneDiag F * g) :
    g 0 2 = 0 ∧ g 1 2 = 0 ∧ g 2 0 = 0 ∧ g 2 1 = 0 := by
  have e02 := congrFun (congrFun h 0) 2
  have e12 := congrFun (congrFun h 1) 2
  have e20 := congrFun (congrFun h 2) 0
  have e21 := congrFun (congrFun h 2) 1
  simp [CFSG.RankThree.Classical.negNegOneDiag, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply] at e02 e12 e20 e21
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (mul_eq_zero.mp (by linear_combination e02 : (2 : F) * g 0 2 = 0)).resolve_left h2
  · exact (mul_eq_zero.mp (by linear_combination e12 : (2 : F) * g 1 2 = 0)).resolve_left h2
  · exact (mul_eq_zero.mp (by linear_combination -e20 : (2 : F) * g 2 0 = 0)).resolve_left h2
  · exact (mul_eq_zero.mp (by linear_combination -e21 : (2 : F) * g 2 1 = 0)).resolve_left h2

theorem comm_diag3 {g : Matrix (Fin 3) (Fin 3) F}
    (h02 : g 0 2 = 0) (h12 : g 1 2 = 0) (h20 : g 2 0 = 0) (h21 : g 2 1 = 0) (u v : F) :
    g * !![u, 0, 0; 0, u, 0; 0, 0, v] = !![u, 0, 0; 0, u, 0; 0, 0, v] * g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, h02, h12, h20, h21] <;> ring

theorem matU_blkU_scU (hF : Nat.card F = p ^ 2) (a : Fˣ) (ha : (a : F) ^ (p + 1) = 1) :
    matU (Lemma41aU3.blkU (uniData hF) (scU a ha)) = !![(a : F), 0, 0; 0, (a : F), 0; 0, 0, ((a : F) ^ 2)⁻¹] := by
  rw [matU_blkU hF]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Lemma41aL3.blkMat, scU, coe_scF, Matrix.scalar_apply, Matrix.det_fin_two, Matrix.diagonal_apply,
      sq, mul_inv]


theorem f3_core_uni (hp4 : p % 4 = 1) (hF : Nat.card F = p ^ 2) {U : Subgroup (PSU3F p F)}
    (hU : SpecialSylowU hF U) (α : MulAut (PSU3F p F)) (hαα : α * α = 1)
    (hno : ∀ y : PSU3F p F, α ≠ MulAut.conj y) (hfix : ∀ w ∈ E2P.zOf U, α w = w)
    (a : Fˣ) (ha : (a : F) ^ (p + 1) = 1) : α (rhoU hF a ha) = (rhoU hF a ha)⁻¹ := by
  have hp2 : p ≠ 2 := by omega
  have hp5 : 5 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hcard' : Nat.card F = (p ^ 1) ^ 2 := by simpa using hF
  have h2 : (2 : F) ≠ 0 := two_ne_zero_u hp2 hF
  obtain ⟨α', g, φ, hα, hform, hiso, hφ⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.unitaryAutClassification_isometry_of_card
      (K := F) (p := p) (f := 1) hcard' hp2 (by simpa using hp5) (le_refl 3) (PSU3F p F)
      (thetaU hF) (thetaU_surjective hF) (thetaU_ker hF) α
  obtain ⟨hφc, -⟩ := hφ (fun x => by
    have := congrArg (fun f : MulAut (PSU3F p F) => f x) hαα
    simpa using this)
  obtain ⟨-, hUB, c, d, hQ, hc, hd⟩ := hU
  have hzU : zcU hF ∈ E2P.zOf U := by
    refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    · rw [zcU_eq_sq hp2 hF hQ]
      exact U.mul_mem hc hc
    · exact (zcU_comm_leviCU hF (hUB hu)).symm
  have hfixz : α (zcU hF) = zcU hF := hfix _ hzU
  set zt' : Phan.Su F p 1 3 := (iotaU hF).symm (CFSG.Quasithin.E2P.Asc80.tU hF) with hzt'
  have hθz : thetaU hF zt' = zcU hF := by
    show piU p F (iotaU hF ((iotaU hF).symm (CFSG.Quasithin.E2P.Asc80.tU hF))) = piU p F (CFSG.Quasithin.E2P.Asc80.tU hF)
    have hh := (iotaU hF).apply_symm_apply (CFSG.Quasithin.E2P.Asc80.tU hF)
    rw [hh]
  have hker : (zt')⁻¹ * α' zt' ∈ (thetaU hF).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hα, hθz, hfixz]
    exact inv_mul_cancel _
  obtain ⟨c0, hc03, hc0⟩ := exists_scalar_of_mem_ker hF (g := iotaU hF ((zt')⁻¹ * α' zt'))
    (MonoidHom.mem_ker.mpr (show piU p F (iotaU hF ((zt')⁻¹ * α' zt')) = 1 from hker))
  have hc0' : ((((zt')⁻¹ * α' zt' : Phan.Su F p 1 3) : GL (Fin 3) F)).1 = Matrix.scalar (Fin 3) c0 :=
    hc0
  have hmat : ((α' zt' : Phan.Su F p 1 3) : GL (Fin 3) F).1 =
      ((zt' : Phan.Su F p 1 3) : GL (Fin 3) F).1 * Matrix.scalar (Fin 3) c0 := by
    have h1 : ((α' zt' : Phan.Su F p 1 3) : GL (Fin 3) F).1 =
        ((zt' : Phan.Su F p 1 3) : GL (Fin 3) F).1 *
          ((((zt')⁻¹ * α' zt' : Phan.Su F p 1 3) : GL (Fin 3) F)).1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel_left]
    rw [h1, hc0']
  have hmatz : ((zt' : Phan.Su F p 1 3) : GL (Fin 3) F).1 = CFSG.RankThree.Classical.negNegOneDiag F := by
    have hh := (iotaU hF).apply_symm_apply (CFSG.Quasithin.E2P.Asc80.tU hF)
    calc ((zt' : Phan.Su F p 1 3) : GL (Fin 3) F).1
        = matU (iotaU hF zt') := rfl
      _ = matU (CFSG.Quasithin.E2P.Asc80.tU hF) := by rw [hzt', hh]
      _ = _ := matU_tU hF
  have hφZ : φ.mapMatrix (CFSG.RankThree.Classical.negNegOneDiag F) =
      CFSG.RankThree.Classical.negNegOneDiag F := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CFSG.RankThree.Classical.negNegOneDiag, RingEquiv.mapMatrix_apply, Matrix.diagonal_apply]
  have hconj : (g : Matrix (Fin 3) (Fin 3) F) * CFSG.RankThree.Classical.negNegOneDiag F *
      ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      CFSG.RankThree.Classical.negNegOneDiag F * Matrix.scalar (Fin 3) c0 := by
    have h1 := hform zt'
    rw [hmat, hmatz, hφZ] at h1
    exact h1.symm
  have htr : c0 = 1 := by
    have h1 := congrArg Matrix.trace hconj
    rw [Matrix.trace_units_conj] at h1
    simp [CFSG.RankThree.Classical.negNegOneDiag, Matrix.trace_fin_three, Matrix.scalar_apply,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply] at h1
    exact h1.symm
  have hcomm : (g : Matrix (Fin 3) (Fin 3) F) * CFSG.RankThree.Classical.negNegOneDiag F =
      CFSG.RankThree.Classical.negNegOneDiag F * (g : Matrix (Fin 3) (Fin 3) F) := by
    rw [htr, map_one, mul_one] at hconj
    have h1 := congrArg (fun M => M * (g : Matrix (Fin 3) (Fin 3) F)) hconj
    simp only [mul_assoc, Units.inv_mul, mul_one] at h1
    exact h1
  obtain ⟨h02, h12, h20, h21⟩ := blockzero_F h2 hcomm
  rcases hφc with hφ1 | hφ2
  · exfalso
    have hform0 : ∀ x : Phan.Su F p 1 3, ((α' x : Phan.Su F p 1 3) : GL (Fin 3) F).1 =
        (g : Matrix (Fin 3) (Fin 3) F) * ((x : Phan.Su F p 1 3) : GL (Fin 3) F).1 *
          ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      intro x
      rw [hform x, hφ1]
      have : (RingEquiv.refl F).mapMatrix (((x : Phan.Su F p 1 3) : GL (Fin 3) F).1) =
          ((x : Phan.Su F p 1 3) : GL (Fin 3) F).1 := by
        ext i j; simp [RingEquiv.mapMatrix_apply]
      rw [this]
    obtain ⟨y, hy⟩ := CFSG.ClassicalInvolution.Disconnected.AschTight.S19K.uni_inner hcard' hp2
      le_rfl (thetaU hF) (thetaU_surjective hF) (thetaU_ker hF) hα hform0 hiso hαα
    exact hno y hy
  · have hτ : ∀ c : F, φ c = c ^ p := by
      intro c
      rw [hφ2, unitaryInvolution_apply, pow_one]
    have hap : (a : F) ^ p = (a : F)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact ha)
    have ha' : (((a⁻¹ : Fˣ)) : F) ^ (p + 1) = 1 := by
      simp [Units.val_inv_eq_inv_val, inv_pow, ha]
    set x0 := Lemma41aU3.blkU (uniData hF) (scU a ha) with hx0
    set x1 := Lemma41aU3.blkU (uniData hF) (scU a⁻¹ ha') with hx1
    have hs : (scU a ha)⁻¹ = scU a⁻¹ ha' := by
      apply Subtype.ext
      show ((scF F a)⁻¹ : GL (Fin 2) F) = scF F a⁻¹
      rw [map_inv]
    have hinv : x0⁻¹ = x1 := by
      rw [hx0, hx1, ← hs, map_inv]
    set X : Phan.Su F p 1 3 := (iotaU hF).symm x0 with hX
    have hXm : ((X : Phan.Su F p 1 3) : GL (Fin 3) F).1 = matU x0 := by
      have hh := (iotaU hF).apply_symm_apply x0
      calc ((X : Phan.Su F p 1 3) : GL (Fin 3) F).1 = matU (iotaU hF X) := rfl
        _ = matU x0 := by rw [hX, hh]
    have hD : (φ.mapMatrix (matU x0)) = !![((a⁻¹ : Fˣ) : F), 0, 0; 0, ((a⁻¹ : Fˣ) : F), 0;
        0, 0, (((a⁻¹ : Fˣ) : F) ^ 2)⁻¹] := by
      rw [hx0, matU_blkU_scU hF a ha]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [RingEquiv.mapMatrix_apply, hτ, hap, inv_pow, Units.val_inv_eq_inv_val,
          zero_pow (Fact.out : p.Prime).ne_zero]
      all_goals (rw [← pow_mul, mul_comm 2 p, pow_mul, hap]; simp)
    have hM : ((α' X : Phan.Su F p 1 3) : GL (Fin 3) F).1 = matU x1 := by
      rw [hform X, hXm, hD, hx1, matU_blkU_scU hF a⁻¹ ha']
      rw [comm_diag3 h02 h12 h20 h21, mul_assoc, Units.mul_inv, mul_one]
    have hα'X : α' X = (iotaU hF).symm x1 := by
      apply Subtype.ext
      apply Units.ext
      rw [hM]
      rfl
    have hh : iotaU hF X = x0 := (iotaU hF).apply_symm_apply x0
    have hh1 : iotaU hF ((iotaU hF).symm x1) = x1 := (iotaU hF).apply_symm_apply x1
    calc α (rhoU hF a ha) = α (thetaU hF X) := by
          show α (piU p F x0) = α (piU p F (iotaU hF X))
          rw [hh]
      _ = thetaU hF (α' X) := (hα X).symm
      _ = piU p F x1 := by
          rw [hα'X]
          show piU p F (iotaU hF ((iotaU hF).symm x1)) = piU p F x1
          rw [hh1]
      _ = (rhoU hF a ha)⁻¹ := by
          rw [← hinv, map_inv]
          rfl


theorem exists_scU_of_mem_center (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2)
    {U : Subgroup (PSU3F p F)} (hU : SpecialSylowU hF U) {b : PSU3F p F}
    (hb1 : b ∈ Subgroup.centralizer (E2P.zOf U : Set (PSU3F p F)))
    (hb2 : b ∈ Subgroup.centralizer
      ((Subgroup.centralizer (E2P.zOf U : Set (PSU3F p F)) : Subgroup (PSU3F p F)) :
        Set (PSU3F p F))) :
    ∃ (a : Fˣ) (ha : (a : F) ^ (p + 1) = 1), b = rhoU hF a ha := by
  have hC : Subgroup.centralizer (E2P.zOf U : Set (PSU3F p F)) = leviCU hF :=
    centralizer_zOf_eq_leviCU hp2 hF hU.1 hU.2.1
  rw [hC] at hb1 hb2
  obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hb1
  obtain ⟨-, -, c, d, hQ, -, -⟩ := hU
  obtain ⟨a, ha, hA⟩ := exists_scU_of_central hp2 hF (A := A) (fun B =>
    (commute_of_piU_commute hF (A := B) (B := A)
      (Subgroup.mem_centralizer_iff.mp hb2 _ ⟨_, ⟨B, rfl⟩, rfl⟩)).symm) ⟨c, d, hQ⟩
  exact ⟨a, ha, by rw [hA]; rfl⟩

theorem f3At_special_u (hp4 : p % 4 = 1) (hF : Nat.card F = p ^ 2) {U : Subgroup (PSU3F p F)}
    (hU : SpecialSylowU hF U) : F3At (PSU3F p F) U := by
  have hp2 : p ≠ 2 := by omega
  intro α hαα hno hfix b ⟨hb1, hb2⟩ _
  obtain ⟨a, ha, rfl⟩ := exists_scU_of_mem_center hp2 hF hU hb1 hb2
  exact f3_core_uni hp4 hF hU α hαα hno hfix a ha

theorem f3_psu {X : Type} [Group X] [Finite X] {K S : Subgroup X}
    (hp4 : p % 4 = 1) (hK : IsPSU 3 p 1 ↥K) (hS : IsSylowTwoOf S K) (hKn : K.Normal)
    (hC : Subgroup.centralizer (K : Set X) = ⊥) {u : X} (huu : u * u = 1) (huK : u ∉ K)
    (huz : u ∈ Subgroup.centralizer (E2P.zOf S : Set X)) :
    ∀ b ∈ cenZ K S ⊓ Subgroup.centralizer (cenZ K S : Set X), Odd (orderOf b) →
      u * b * u⁻¹ = b⁻¹ := by
  obtain ⟨F, _, _, hF, e, U₀, hU₀, hmap⟩ := exists_equiv_special_u (p := p) (by omega) hK hS
  haveI : CharP F p := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := p) (f := 1)
    (by simpa using hF)
  have h := f3At_special_u hp4 hF hU₀
  rw [← hmap] at h
  exact f3_of_model hKn hC hS.1 (F3At.of_map e _ h) huu huK huz

end CFSG.Quasithin.Background.Harris.KFact2d
