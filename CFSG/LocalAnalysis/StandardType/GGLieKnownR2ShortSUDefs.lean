module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUSUStd
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieSpRad
public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.LieType.Universal.Unitary.Basic
public import CFSG.Timmesfeld.Transvection.ModelSUTorus
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Transvection.ModelRankSU
public import Certificates.Certificate43

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.StandardType CFSG.StandardType.ClassicalPosition CFSG.StandardType.GGOppRadSpU
  CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.QuasithinUnique.B113Lie.Sp
  CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.Transvection.ModelRank
open Matrix
open scoped Matrix

@[expose] noncomputable def suH {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) : ReflForm F (Fin n → F) :=
  suForm (unitaryInvolution F 2 f) (unitaryInvolution_involutive hc) n

@[expose] def suPair {F : Type} [Field F] (σ : F ≃+* F) (n : ℕ) (v w : Fin n → F) :
    Subgroup ↥(SU σ n) :=
  (unitPairGroup σ.toRingHom (antidiag n) v w).comap (SU σ n).subtype

@[expose] def SUFrame {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) (v w v' w' : Fin n → F) : Prop :=
  (suH hc n).β v w' = 1 ∧ (suH hc n).β w v' = 1 ∧
    ((suH hc n).β v v = 0 ∧ (suH hc n).β w w = 0 ∧ (suH hc n).β v' v' = 0 ∧
      (suH hc n).β w' w' = 0) ∧
    ((suH hc n).β v w = 0 ∧ (suH hc n).β v v' = 0 ∧ (suH hc n).β w w' = 0 ∧
      (suH hc n).β v' w' = 0)

@[expose] noncomputable def suStabRad {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) (A : Submodule F (Fin n → F))
    (hA : (suH hc n).IsTotallyIsotropic A) :
    Subgroup ↥(SU (unitaryInvolution F 2 f) n) :=
  rad (suH hc n) (natRep (SU (unitaryInvolution F 2 f) n)) A hA

@[expose] noncomputable def suStabFix {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) (A : Submodule F (Fin n → F))
    (hA : (suH hc n).IsTotallyIsotropic A) :
    Subgroup ↥(SU (unitaryInvolution F 2 f) n) where
  carrier := {g | g ∈ suStabRad hc n A hA ∧
    ∀ y ∈ (suH hc n).perp A, natRep (SU (unitaryInvolution F 2 f) n) g y = y}
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨mul_mem hg1 hh1, fun y hy => ?_⟩
    rw [map_mul, Module.End.mul_apply, hh2 y hy, hg2 y hy]
  one_mem' := by
    refine ⟨one_mem _, fun y hy => ?_⟩
    rw [map_one, Module.End.one_apply]
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨inv_mem hg1, fun y hy => ?_⟩
    have h1 : natRep (SU (unitaryInvolution F 2 f) n) g⁻¹
        (natRep (SU (unitaryInvolution F 2 f) n) g y) = y := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rwa [hg2 y hy] at h1

theorem suFrame_isTotallyIsotropic {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') :
    (suH hc n).IsTotallyIsotropic (Submodule.span F {v, w}) := by
  intro x hx y hy
  obtain ⟨h1, h2, hIsot, hOrth⟩ := hfr
  obtain ⟨h3, h4, h5, h6⟩ := hIsot
  obtain ⟨h7, h8, h9, h10⟩ := hOrth
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hy
  have hwv : (suH hc n).β w v = 0 := (suH hc n).refl v w h7
  simp only [ReflForm.add_left, ReflForm.add_right, ReflForm.smul_left, ReflForm.smul_right]
  rw [h3, h4, h7, hwv]
  ring

private theorem suH_symm {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} (u v : Fin n → F) :
    (suH hc n).β v u = unitaryInvolution F 2 f ((suH hc n).β u v) := by
  unfold suH
  exact suForm_symm (unitaryInvolution F 2 f) (unitaryInvolution_involutive hc) u v

private theorem suFrame_linearIndependent {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') : LinearIndependent F ![v, w, v', w'] := by
  obtain ⟨h1, h2, hIsot, hOrth⟩ := hfr
  obtain ⟨h3, h4, h5, h6⟩ := hIsot
  obtain ⟨h7, h8, h9, h10⟩ := hOrth
  have hwv : (suH hc n).β w v = 0 := (suH hc n).refl v w h7
  have hv'v : (suH hc n).β v' v = 0 := (suH hc n).refl v v' h8
  have hw'w : (suH hc n).β w' w = 0 := (suH hc n).refl w w' h9
  have hw'v' : (suH hc n).β w' v' = 0 := (suH hc n).refl v' w' h10
  have hw'v : (suH hc n).β w' v = 1 := by
    rw [suH_symm v w', h1, map_one]
  have hv'w : (suH hc n).β v' w = 1 := by
    rw [suH_symm w v', h2, map_one]
  have hv0 : ![v, w, v', w'] 0 = v := rfl
  have hv1 : ![v, w, v', w'] 1 = w := rfl
  have hv2 : ![v, w, v', w'] 2 = v' := rfl
  have hv3 : ![v, w, v', w'] 3 = w' := rfl
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hpair : ∀ y : Fin n → F,
      (∑ i, g i * (suH hc n).β y (![v, w, v', w'] i)) = 0 := by
    intro y
    let φ : (Fin n → F) →ₗ[F] F :=
      { toFun := fun z => (suH hc n).β y z
        map_add' := fun a b => (suH hc n).add_right y a b
        map_smul' := fun c a => (suH hc n).smul_right c y a }
    have h := congrArg φ hg
    simp only [map_sum, map_zero, map_smul, smul_eq_mul] at h
    simpa [φ] using h
  have h0 : g 0 = 0 := by
    have h := hpair w'
    rw [Fin.sum_univ_four] at h
    simp only [hv0, hv1, hv2, hv3, hw'v, hw'w, hw'v', h6, mul_one, mul_zero, add_zero,
      zero_add] at h
    exact h
  have h1' : g 1 = 0 := by
    have h := hpair v'
    rw [Fin.sum_univ_four] at h
    simp only [hv0, hv1, hv2, hv3, hv'v, hv'w, h5, h10, mul_one, mul_zero, add_zero,
      zero_add] at h
    exact h
  have h2' : g 2 = 0 := by
    have h := hpair w
    rw [Fin.sum_univ_four] at h
    simp only [hv0, hv1, hv2, hv3, hwv, h4, h2, h9, mul_one, mul_zero, add_zero,
      zero_add] at h
    exact h
  have h3' : g 3 = 0 := by
    have h := hpair v
    rw [Fin.sum_univ_four] at h
    simp only [hv0, hv1, hv2, hv3, h3, h7, h8, h1, mul_one, mul_zero, add_zero,
      zero_add] at h
    exact h
  intro k
  fin_cases k <;> assumption

theorem four_le_of_suFrame {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') : 4 ≤ n := by
  have h := (suFrame_linearIndependent hfr).fintype_card_le_finrank
  simpa [Module.finrank_fin_fun] using h

private def pairGenM1 {F : Type} [Field F] (σ : F →+* F) {n : ℕ} (v w : Fin n → F) :
    Matrix (Fin n) (Fin n) F :=
  Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (w i)) (antidiag n))

private def pairGenM2 {F : Type} [Field F] (σ : F →+* F) {n : ℕ} (v w : Fin n → F) :
    Matrix (Fin n) (Fin n) F :=
  Matrix.vecMulVec w (Matrix.vecMul (fun i => σ (v i)) (antidiag n))

private def pairGenE {F : Type} [Field F] (σ : F →+* F) {n : ℕ} (v w : Fin n → F) (c : F) :
    Matrix (Fin n) (Fin n) F :=
  c • pairGenM1 σ v w - σ c • pairGenM2 σ v w

private theorem pairGenE_eq {F : Type} [Field F] {n : ℕ} (σ : F →+* F) (v w : Fin n → F)
    (c : F) :
    1 + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (w i)) (antidiag n)) -
        σ c • Matrix.vecMulVec w (Matrix.vecMul (fun i => σ (v i)) (antidiag n)) =
      1 + pairGenE σ v w c := by
  rw [pairGenE, pairGenM1, pairGenM2, add_sub_assoc]

private theorem vecMul_antidiag_dotProduct {F : Type} [Field F] {n : ℕ} (σ : F →+* F)
    (w y : Fin n → F) :
    dotProduct (Matrix.vecMul (fun i => σ (w i)) (antidiag n)) y =
      ∑ i, σ (w i) * y (Fin.rev i) := by
  rw [← Matrix.dotProduct_mulVec, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by rw [antidiag_mulVec_apply]

private theorem vecMul_antidiag_dotProduct_suH {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (w y : Fin n → F) :
    dotProduct
      (Matrix.vecMul (fun i => (unitaryInvolution F 2 f).toRingHom (w i)) (antidiag n)) y =
      (suH hc n).β w y := by
  rw [vecMul_antidiag_dotProduct]
  change (∑ i, unitaryInvolution F 2 f (w i) * y (Fin.rev i)) =
    (suForm (unitaryInvolution F 2 f) (unitaryInvolution_involutive hc) n).β w y
  rw [suForm_β]

private theorem suForm_σ_symm {F : Type} [Field F] (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c)
    {n : ℕ} (u v : Fin n → F) :
    σ ((suForm σ hσ n).β v u) = (suForm σ hσ n).β u v := by
  rw [suForm_symm σ hσ u v, hσ]

private theorem suForm_β_comm_zero {F : Type} [Field F] (σ : F ≃+* F)
    (hσ : ∀ c, σ (σ c) = c) {n : ℕ} {u v : Fin n → F}
    (h : (suForm σ hσ n).β u v = 0) : (suForm σ hσ n).β v u = 0 := by
  rw [suForm_symm σ hσ u v, h, map_zero]

private theorem suH_β_comm_zero {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} {u v : Fin n → F}
    (h : (suH hc n).β u v = 0) : (suH hc n).β v u = 0 :=
  suForm_β_comm_zero (unitaryInvolution F 2 f) (unitaryInvolution_involutive hc) h

private theorem pairGenM1_mul_pairGenM1 {F : Type} [Field F] {n : ℕ} (σ : F →+* F)
    {v w : Fin n → F}
    (h : dotProduct (Matrix.vecMul (fun i => σ (w i)) (antidiag n)) v = 0) :
    pairGenM1 σ v w * pairGenM1 σ v w = 0 := by
  rw [pairGenM1, Matrix.vecMulVec_mul_vecMulVec, h, zero_smul, Matrix.vecMulVec_zero]

private theorem pairGenM1_mul_pairGenM2 {F : Type} [Field F] {n : ℕ} (σ : F →+* F)
    {v w : Fin n → F}
    (h : dotProduct (Matrix.vecMul (fun i => σ (w i)) (antidiag n)) w = 0) :
    pairGenM1 σ v w * pairGenM2 σ v w = 0 := by
  rw [pairGenM1, pairGenM2, Matrix.vecMulVec_mul_vecMulVec, h, zero_smul,
    Matrix.vecMulVec_zero]

private theorem pairGenM2_mul_pairGenM1 {F : Type} [Field F] {n : ℕ} (σ : F →+* F)
    {v w : Fin n → F}
    (h : dotProduct (Matrix.vecMul (fun i => σ (v i)) (antidiag n)) v = 0) :
    pairGenM2 σ v w * pairGenM1 σ v w = 0 := by
  rw [pairGenM1, pairGenM2, Matrix.vecMulVec_mul_vecMulVec, h, zero_smul,
    Matrix.vecMulVec_zero]

private theorem pairGenM2_mul_pairGenM2 {F : Type} [Field F] {n : ℕ} (σ : F →+* F)
    {v w : Fin n → F}
    (h : dotProduct (Matrix.vecMul (fun i => σ (v i)) (antidiag n)) w = 0) :
    pairGenM2 σ v w * pairGenM2 σ v w = 0 := by
  rw [pairGenM2, Matrix.vecMulVec_mul_vecMulVec, h, zero_smul, Matrix.vecMulVec_zero]

private theorem pairGenE_add {F : Type} [Field F] {n : ℕ} (σ : F →+* F) (v w : Fin n → F)
    (c d : F) : pairGenE σ v w c + pairGenE σ v w d = pairGenE σ v w (c + d) := by
  rw [pairGenE, pairGenE, pairGenE, map_add, add_smul, add_smul]
  abel

private theorem pairGenE_zero {F : Type} [Field F] {n : ℕ} (σ : F →+* F) (v w : Fin n → F) :
    pairGenE σ v w 0 = 0 := by
  rw [pairGenE, map_zero, zero_smul, zero_smul, sub_zero]

private theorem sub_eq_add_of_charTwo {F V : Type} [Field F] [CharP F 2] [AddCommGroup V]
    [Module F V] (x y : V) : x - y = x + y := by
  rw [sub_eq_add_neg]
  congr 1
  rw [neg_eq_iff_add_eq_zero, ← two_smul F y, CharTwo.two_eq_zero, zero_smul]

private theorem pairGenE_mulVec {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (v w : Fin n → F) (c : F) (y : Fin n → F) :
    Matrix.mulVec (pairGenE (unitaryInvolution F 2 f).toRingHom v w c) y =
      (c * (suH hc n).β w y) • v + (unitaryInvolution F 2 f c * (suH hc n).β v y) • w := by
  rw [pairGenE, pairGenM1, pairGenM2, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec]
  simp only [IsCentralScalar.op_smul_eq_smul]
  rw [vecMul_antidiag_dotProduct_suH hc w y, vecMul_antidiag_dotProduct_suH hc v y]
  simp only [smul_smul]
  rw [sub_eq_add_of_charTwo (F := F) (V := Fin n → F)]
  rfl

private theorem pairGenE_mul_pairGenE {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} {v w : Fin n → F}
    (hv : (suH hc n).β v v = 0) (hw : (suH hc n).β w w = 0) (hvw : (suH hc n).β v w = 0)
    (c d : F) :
    pairGenE (unitaryInvolution F 2 f).toRingHom v w c *
      pairGenE (unitaryInvolution F 2 f).toRingHom v w d = 0 := by
  have hwv : (suH hc n).β w v = 0 := suH_β_comm_zero hc hvw
  have h11 : pairGenM1 (unitaryInvolution F 2 f).toRingHom v w *
      pairGenM1 (unitaryInvolution F 2 f).toRingHom v w = 0 :=
    pairGenM1_mul_pairGenM1 ((unitaryInvolution F 2 f).toRingHom) (v := v) (w := w)
      (by rw [vecMul_antidiag_dotProduct_suH hc w v]; exact hwv)
  have h12 : pairGenM1 (unitaryInvolution F 2 f).toRingHom v w *
      pairGenM2 (unitaryInvolution F 2 f).toRingHom v w = 0 :=
    pairGenM1_mul_pairGenM2 ((unitaryInvolution F 2 f).toRingHom) (v := v) (w := w)
      (by rw [vecMul_antidiag_dotProduct_suH hc w w]; exact hw)
  have h21 : pairGenM2 (unitaryInvolution F 2 f).toRingHom v w *
      pairGenM1 (unitaryInvolution F 2 f).toRingHom v w = 0 :=
    pairGenM2_mul_pairGenM1 ((unitaryInvolution F 2 f).toRingHom) (v := v) (w := w)
      (by rw [vecMul_antidiag_dotProduct_suH hc v v]; exact hv)
  have h22 : pairGenM2 (unitaryInvolution F 2 f).toRingHom v w *
      pairGenM2 (unitaryInvolution F 2 f).toRingHom v w = 0 :=
    pairGenM2_mul_pairGenM2 ((unitaryInvolution F 2 f).toRingHom) (v := v) (w := w)
      (by rw [vecMul_antidiag_dotProduct_suH hc v w]; exact hvw)
  have hAC : (c • pairGenM1 (unitaryInvolution F 2 f).toRingHom v w) *
      (d • pairGenM1 (unitaryInvolution F 2 f).toRingHom v w) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, h11, smul_zero, smul_zero]
  have hAD : (c • pairGenM1 (unitaryInvolution F 2 f).toRingHom v w) *
      ((unitaryInvolution F 2 f).toRingHom d •
        pairGenM2 (unitaryInvolution F 2 f).toRingHom v w) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, h12, smul_zero, smul_zero]
  have hBC : ((unitaryInvolution F 2 f).toRingHom c •
        pairGenM2 (unitaryInvolution F 2 f).toRingHom v w) *
      (d • pairGenM1 (unitaryInvolution F 2 f).toRingHom v w) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, h21, smul_zero, smul_zero]
  have hBD : ((unitaryInvolution F 2 f).toRingHom c •
        pairGenM2 (unitaryInvolution F 2 f).toRingHom v w) *
      ((unitaryInvolution F 2 f).toRingHom d •
        pairGenM2 (unitaryInvolution F 2 f).toRingHom v w) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, h22, smul_zero, smul_zero]
  rw [pairGenE, pairGenE, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
    hAC, hAD, hBC, hBD]
  simp

private theorem one_add_pairGenE_mul {F : Type} [Field F] {n : ℕ} (σ : F →+* F)
    (v w : Fin n → F) (c d : F) (h : pairGenE σ v w c * pairGenE σ v w d = 0) :
    (1 + pairGenE σ v w c) * (1 + pairGenE σ v w d) = 1 + pairGenE σ v w (c + d) := by
  calc (1 + pairGenE σ v w c) * (1 + pairGenE σ v w d)
      = (1 + pairGenE σ v w c) * 1 +
          (1 + pairGenE σ v w c) * pairGenE σ v w d := by rw [Matrix.mul_add]
    _ = (1 + pairGenE σ v w c) +
          (1 * pairGenE σ v w d + pairGenE σ v w c * pairGenE σ v w d) := by
          rw [mul_one, Matrix.add_mul]
    _ = (1 + pairGenE σ v w c) + (pairGenE σ v w d + 0) := by
          rw [one_mul, h]
    _ = 1 + (pairGenE σ v w c + pairGenE σ v w d) := by abel
    _ = 1 + pairGenE σ v w (c + d) := by rw [pairGenE_add]

private theorem exists_suPair_Tc {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} {v w : Fin n → F}
    (hv : (suH hc n).β v v = 0) (hw : (suH hc n).β w w = 0) (hvw : (suH hc n).β v w = 0)
    (c : F) :
    ∃ g : ↥(SU (unitaryInvolution F 2 f) n),
      ∀ y : Fin n → F, natRep (SU (unitaryInvolution F 2 f) n) g y =
        y + (c * (suH hc n).β w y) • v +
          (unitaryInvolution F 2 f c * (suH hc n).β v y) • w := by
  let σ : F ≃+* F := unitaryInvolution F 2 f
  let hσ : ∀ x, σ (σ x) = x := unitaryInvolution_involutive hc
  have hv' : (suForm σ hσ n).β v v = 0 := hv
  have hw' : (suForm σ hσ n).β w w = 0 := hw
  have hvw' : (suForm σ hσ n).β v w = 0 := hvw
  have hwv' : (suForm σ hσ n).β w v = 0 := suForm_β_comm_zero σ hσ hvw'
  let N : Module.End F (Fin n → F) :=
    (suDual (σ := σ) (hσ := hσ) w).smulRight (c • v) +
      (suDual (σ := σ) (hσ := hσ) v).smulRight (σ c • w)
  have hNv : ∀ y, N y = (c * (suForm σ hσ n).β w y) • v +
      (σ c * (suForm σ hσ n).β v y) • w := by
    intro y
    change (((suDual (σ := σ) (hσ := hσ) w).smulRight (c • v) +
      (suDual (σ := σ) (hσ := hσ) v).smulRight (σ c • w)) y) = _
    rw [LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.smulRight_apply,
      suDual_apply, suDual_apply, smul_smul, smul_smul,
      mul_comm ((suForm σ hσ n).β w y) c, mul_comm ((suForm σ hσ n).β v y) (σ c)]
  have hNw : ∀ y, (suForm σ hσ n).β w (N y) = 0 := by
    intro y
    rw [hNv y, (suForm σ hσ n).add_right, (suForm σ hσ n).smul_right,
      (suForm σ hσ n).smul_right, hwv', hw', mul_zero, mul_zero, add_zero]
  have hNv0 : ∀ y, (suForm σ hσ n).β v (N y) = 0 := by
    intro y
    rw [hNv y, (suForm σ hσ n).add_right, (suForm σ hσ n).smul_right,
      (suForm σ hσ n).smul_right, hv', hvw', mul_zero, mul_zero, add_zero]
  have hcomm : ∀ u u', (suForm σ hσ n).β (N u) u' = (suForm σ hσ n).β u (N u') := by
    intro u u'
    simp only [hNv u, hNv u', (suForm σ hσ n).add_left, (suForm σ hσ n).add_right,
      (suForm σ hσ n).smul_left, (suForm σ hσ n).smul_right, suForm_σ, map_mul, hσ c,
      suForm_σ_symm σ hσ u w, suForm_σ_symm σ hσ u v]
    ring
  have hquad : ∀ u u', (suForm σ hσ n).β (N u) (N u') = 0 := by
    intro u u'
    simp only [hNv u, hNv u', (suForm σ hσ n).add_left, (suForm σ hσ n).add_right,
      (suForm σ hσ n).smul_left, (suForm σ hσ n).smul_right, suForm_σ, hv', hwv', hvw', hw',
      mul_zero, zero_mul, add_zero, zero_add]
  have hN2 : ∀ y, N (N y) = 0 := by
    intro y
    rw [hNv (N y), hNw y, hNv0 y]
    simp
  have hnil : IsNilpotent N := by
    refine ⟨2, ?_⟩
    rw [pow_two]
    exact LinearMap.ext hN2
  have hE : ∀ y, ((LinearMap.id + N : Module.End F (Fin n → F))) y =
      y + (c * (suForm σ hσ n).β w y) • v +
      (σ c * (suForm σ hσ n).β v y) • w := by
    intro y
    rw [LinearMap.add_apply, LinearMap.id_apply, hNv y, add_assoc]
  have hiso : ∀ u u', (suForm σ hσ n).β
        ((LinearMap.id + N : Module.End F (Fin n → F)) u)
        ((LinearMap.id + N : Module.End F (Fin n → F)) u') = (suForm σ hσ n).β u u' := by
    intro u u'
    have h1 : (LinearMap.id + N : Module.End F (Fin n → F)) u = u + N u := by
      rw [LinearMap.add_apply, LinearMap.id_apply]
    have h2 : (LinearMap.id + N : Module.End F (Fin n → F)) u' = u' + N u' := by
      rw [LinearMap.add_apply, LinearMap.id_apply]
    rw [h1, h2, (suForm σ hσ n).add_left, (suForm σ hσ n).add_right,
      (suForm σ hσ n).add_right, hcomm u u', hquad u u']
    rw [add_zero, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hdet : (LinearMap.toMatrix' (LinearMap.id + N : Module.End F (Fin n → F))).det = 1 :=
    det_toMatrix'_id_add hnil
  obtain ⟨g, hg⟩ := exists_SU_of_isometry σ hσ
    (LinearMap.id + N : Module.End F (Fin n → F)) hiso hdet
  refine ⟨g, fun y => ?_⟩
  rw [hg y, hE y]
  rfl

theorem mem_suPair_of_mulVec {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} {v w : Fin n → F}
    {g : ↥(SU (unitaryInvolution F 2 f) n)} (c : F)
    (h : ∀ y : Fin n → F, natRep (SU (unitaryInvolution F 2 f) n) g y =
      y + (c * (suH hc n).β w y) • v + (unitaryInvolution F 2 f c * (suH hc n).β v y) • w) :
    g ∈ suPair (unitaryInvolution F 2 f) n v w := by
  refine Subgroup.subset_closure ⟨c, ?_⟩
  rw [pairGenE_eq]
  apply Matrix.ext_of_mulVec_single
  intro j
  have hj := h (Pi.single j 1)
  rw [natRep_apply] at hj
  rw [Matrix.add_mulVec, Matrix.one_mulVec,
    pairGenE_mulVec hc v w c (Pi.single j 1)]
  rw [← add_assoc]
  exact hj

theorem exists_mem_suPair_mulVec {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} {v w : Fin n → F}
    (hv : (suH hc n).β v v = 0) (hw : (suH hc n).β w w = 0) (hvw : (suH hc n).β v w = 0)
    (c : F) :
    ∃ g ∈ suPair (unitaryInvolution F 2 f) n v w,
      ∀ y : Fin n → F, natRep (SU (unitaryInvolution F 2 f) n) g y =
        y + (c * (suH hc n).β w y) • v + (unitaryInvolution F 2 f c * (suH hc n).β v y) • w := by
  obtain ⟨g, hg⟩ := exists_suPair_Tc hc hv hw hvw c
  exact ⟨g, mem_suPair_of_mulVec hc c hg, hg⟩

theorem exists_mulVec_of_mem_suPair {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} {v w : Fin n → F}
    (hv : (suH hc n).β v v = 0) (hw : (suH hc n).β w w = 0) (hvw : (suH hc n).β v w = 0)
    {g : ↥(SU (unitaryInvolution F 2 f) n)}
    (hg : g ∈ suPair (unitaryInvolution F 2 f) n v w) :
    ∃ c : F, ∀ y : Fin n → F, natRep (SU (unitaryInvolution F 2 f) n) g y =
      y + (c * (suH hc n).β w y) • v + (unitaryInvolution F 2 f c * (suH hc n).β v y) • w := by
  have hg' : ((g : ↥(SU (unitaryInvolution F 2 f) n)) : GL (Fin n) F) ∈
      unitPairGroup (unitaryInvolution F 2 f).toRingHom (antidiag n) v w :=
    Subgroup.mem_comap.mp hg
  have hmem : ∃ c : F, (((g : ↥(SU (unitaryInvolution F 2 f) n)) : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) =
          1 + c • Matrix.vecMulVec v
              (Matrix.vecMul (fun i => (unitaryInvolution F 2 f).toRingHom (w i))
                (antidiag n)) -
            (unitaryInvolution F 2 f).toRingHom c • Matrix.vecMulVec w
              (Matrix.vecMul (fun i => (unitaryInvolution F 2 f).toRingHom (v i))
                (antidiag n)) := by
    refine Subgroup.closure_induction
      (p := fun (x : GL (Fin n) F) _ => ∃ c : F,
        (x : Matrix (Fin n) (Fin n) F) =
          1 + c • Matrix.vecMulVec v
              (Matrix.vecMul (fun i => (unitaryInvolution F 2 f).toRingHom (w i))
                (antidiag n)) -
            (unitaryInvolution F 2 f).toRingHom c • Matrix.vecMulVec w
              (Matrix.vecMul (fun i => (unitaryInvolution F 2 f).toRingHom (v i))
                (antidiag n))) ?_ ?_ ?_ ?_ hg'
    · rintro x ⟨c, hcx⟩
      exact ⟨c, hcx⟩
    · exact ⟨0, by rw [Units.val_one, map_zero, zero_smul, zero_smul, add_zero, sub_zero]⟩
    · rintro x y _ _ ⟨c, hcx⟩ ⟨d, hdy⟩
      refine ⟨c + d, ?_⟩
      rw [Units.val_mul, hcx, hdy, pairGenE_eq, pairGenE_eq, pairGenE_eq]
      exact one_add_pairGenE_mul (unitaryInvolution F 2 f).toRingHom v w c d
        (pairGenE_mul_pairGenE hc hv hw hvw c d)
    · rintro x _ ⟨c, hcx⟩
      refine ⟨c, ?_⟩
      have hxx : x * x = 1 := by
        apply Units.ext
        rw [Units.val_mul, hcx, Units.val_one, pairGenE_eq,
          one_add_pairGenE_mul (unitaryInvolution F 2 f).toRingHom v w c c
            (pairGenE_mul_pairGenE hc hv hw hvw c c),
          CharTwo.add_self_eq_zero, pairGenE_zero, add_zero]
      rw [inv_eq_of_mul_eq_one_right hxx]
      exact hcx
  obtain ⟨c, hmat⟩ := hmem
  exact ⟨c, fun y => by
    rw [natRep_apply, hmat, pairGenE_eq, Matrix.add_mulVec, Matrix.one_mulVec,
      pairGenE_mulVec hc v w c y, add_assoc]⟩

private noncomputable def suFrameZ {F : Type} [Field F] (σ : F ≃+* F) {n : ℕ}
    (v w v' w' x : Fin n → F) : Fin n → F :=
  x - (uForm σ w' x) • v - (uForm σ v' x) • w - (uForm σ w x) • v' - (uForm σ v x) • w'

private theorem suFrame_expand {F : Type} [Field F] {n : ℕ} (σ : F ≃+* F)
    (hσ : ∀ c, σ (σ c) = c) {v w v' w' : Fin n → F}
    (h1 : uForm σ v w' = 1) (h2 : uForm σ w v' = 1)
    (h3 : uForm σ v v = 0) (h4 : uForm σ w w = 0)
    (h5 : uForm σ v' v' = 0) (h6 : uForm σ w' w' = 0)
    (h7 : uForm σ v w = 0) (h8 : uForm σ v v' = 0)
    (h9 : uForm σ w w' = 0) (h10 : uForm σ v' w' = 0) (x y : Fin n → F) :
    uForm σ x y =
      σ (uForm σ w' x) * uForm σ v y + σ (uForm σ v' x) * uForm σ w y
      + σ (uForm σ w x) * uForm σ v' y + σ (uForm σ v x) * uForm σ w' y
      + uForm σ (suFrameZ σ v w v' w' x) (suFrameZ σ v w v' w' y) := by
  have hw'v : uForm σ w' v = 1 := by rw [← uForm_conj σ hσ v w', h1, map_one]
  have hv'w : uForm σ v' w = 1 := by rw [← uForm_conj σ hσ w v', h2, map_one]
  have hwv : uForm σ w v = 0 := by rw [← uForm_conj σ hσ v w, h7, map_zero]
  have hv'v : uForm σ v' v = 0 := by rw [← uForm_conj σ hσ v v', h8, map_zero]
  have hw'w : uForm σ w' w = 0 := by rw [← uForm_conj σ hσ w w', h9, map_zero]
  have hw'v' : uForm σ w' v' = 0 := by rw [← uForm_conj σ hσ v' w', h10, map_zero]
  have hxz_v : uForm σ v (suFrameZ σ v w v' w' x) = 0 := by
    rw [suFrameZ, uForm_sub_right, uForm_sub_right, uForm_sub_right, uForm_sub_right,
      uForm_smul_right, uForm_smul_right, uForm_smul_right, uForm_smul_right, h3, h7, h8, h1]
    ring
  have hxz_w : uForm σ w (suFrameZ σ v w v' w' x) = 0 := by
    rw [suFrameZ, uForm_sub_right, uForm_sub_right, uForm_sub_right, uForm_sub_right,
      uForm_smul_right, uForm_smul_right, uForm_smul_right, uForm_smul_right,
      hwv, h4, h2, h9]
    ring
  have hxz_v' : uForm σ v' (suFrameZ σ v w v' w' x) = 0 := by
    rw [suFrameZ, uForm_sub_right, uForm_sub_right, uForm_sub_right, uForm_sub_right,
      uForm_smul_right, uForm_smul_right, uForm_smul_right, uForm_smul_right,
      hv'v, hv'w, h5, h10]
    ring
  have hxz_w' : uForm σ w' (suFrameZ σ v w v' w' x) = 0 := by
    rw [suFrameZ, uForm_sub_right, uForm_sub_right, uForm_sub_right, uForm_sub_right,
      uForm_smul_right, uForm_smul_right, uForm_smul_right, uForm_smul_right,
      hw'v, hw'w, hw'v', h6]
    ring
  have hzx_v : uForm σ (suFrameZ σ v w v' w' x) v = 0 := by
    have h := uForm_conj σ hσ v (suFrameZ σ v w v' w' x)
    rw [hxz_v, map_zero] at h
    exact h.symm
  have hzx_w : uForm σ (suFrameZ σ v w v' w' x) w = 0 := by
    have h := uForm_conj σ hσ w (suFrameZ σ v w v' w' x)
    rw [hxz_w, map_zero] at h
    exact h.symm
  have hzx_v' : uForm σ (suFrameZ σ v w v' w' x) v' = 0 := by
    have h := uForm_conj σ hσ v' (suFrameZ σ v w v' w' x)
    rw [hxz_v', map_zero] at h
    exact h.symm
  have hzx_w' : uForm σ (suFrameZ σ v w v' w' x) w' = 0 := by
    have h := uForm_conj σ hσ w' (suFrameZ σ v w v' w' x)
    rw [hxz_w', map_zero] at h
    exact h.symm
  have hyz_v : uForm σ v (suFrameZ σ v w v' w' y) = 0 := by
    rw [suFrameZ, uForm_sub_right, uForm_sub_right, uForm_sub_right, uForm_sub_right,
      uForm_smul_right, uForm_smul_right, uForm_smul_right, uForm_smul_right, h3, h7, h8, h1]
    ring
  have hyz_w : uForm σ w (suFrameZ σ v w v' w' y) = 0 := by
    rw [suFrameZ, uForm_sub_right, uForm_sub_right, uForm_sub_right, uForm_sub_right,
      uForm_smul_right, uForm_smul_right, uForm_smul_right, uForm_smul_right,
      hwv, h4, h2, h9]
    ring
  have hyz_v' : uForm σ v' (suFrameZ σ v w v' w' y) = 0 := by
    rw [suFrameZ, uForm_sub_right, uForm_sub_right, uForm_sub_right, uForm_sub_right,
      uForm_smul_right, uForm_smul_right, uForm_smul_right, uForm_smul_right,
      hv'v, hv'w, h5, h10]
    ring
  have hyz_w' : uForm σ w' (suFrameZ σ v w v' w' y) = 0 := by
    rw [suFrameZ, uForm_sub_right, uForm_sub_right, uForm_sub_right, uForm_sub_right,
      uForm_smul_right, uForm_smul_right, uForm_smul_right, uForm_smul_right,
      hw'v, hw'w, hw'v', h6]
    ring
  have hzy_v : uForm σ (suFrameZ σ v w v' w' y) v = 0 := by
    have h := uForm_conj σ hσ v (suFrameZ σ v w v' w' y)
    rw [hyz_v, map_zero] at h
    exact h.symm
  have hzy_w : uForm σ (suFrameZ σ v w v' w' y) w = 0 := by
    have h := uForm_conj σ hσ w (suFrameZ σ v w v' w' y)
    rw [hyz_w, map_zero] at h
    exact h.symm
  have hzy_v' : uForm σ (suFrameZ σ v w v' w' y) v' = 0 := by
    have h := uForm_conj σ hσ v' (suFrameZ σ v w v' w' y)
    rw [hyz_v', map_zero] at h
    exact h.symm
  have hzy_w' : uForm σ (suFrameZ σ v w v' w' y) w' = 0 := by
    have h := uForm_conj σ hσ w' (suFrameZ σ v w v' w' y)
    rw [hyz_w', map_zero] at h
    exact h.symm
  have hx : x = uForm σ w' x • v + uForm σ v' x • w + uForm σ w x • v' + uForm σ v x • w'
      + suFrameZ σ v w v' w' x := by
    rw [suFrameZ]
    abel
  have hy : y = uForm σ w' y • v + uForm σ v' y • w + uForm σ w y • v' + uForm σ v y • w'
      + suFrameZ σ v w v' w' y := by
    rw [suFrameZ]
    abel
  conv_lhs => rw [hx]
  conv_lhs => rw [hy]
  simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hwv, hv'v, hw'w, hw'v', hw'v, hv'w,
    hxz_v, hxz_w, hxz_v', hxz_w', hyz_v, hyz_w, hyz_v', hyz_w',
    hzx_v, hzx_w, hzx_v', hzx_w', hzy_v, hzy_w, hzy_v', hzy_w',
    mul_zero, mul_one, zero_mul, add_zero, zero_add, sub_zero]
  ring

private theorem suTorus_of_frame {F : Type} [Field F] {m : ℕ}
    (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c) {v w v' w' : Fin m → F}
    (g1 : uForm σ v w' = 1) (g2 : uForm σ w v' = 1)
    (g3 : uForm σ v v = 0) (g4 : uForm σ w w = 0)
    (g5 : uForm σ v' v' = 0) (g6 : uForm σ w' w' = 0)
    (g7 : uForm σ v w = 0) (g8 : uForm σ v v' = 0)
    (g9 : uForm σ w w' = 0) (g10 : uForm σ v' w' = 0)
    {μ ν : F} (hμ : μ ≠ 0) (hν : ν ≠ 0) (hμν : σ (μ * ν) = μ * ν) :
    ∃ g : SU σ m, suMat σ m g *ᵥ v = μ • v ∧ suMat σ m g *ᵥ w = ν • w ∧
      suMat σ m g *ᵥ v' = (σ ν)⁻¹ • v' ∧ suMat σ m g *ᵥ w' = (σ μ)⁻¹ • w' ∧
      ∀ y, uForm σ v y = 0 → uForm σ w y = 0 → uForm σ v' y = 0 → uForm σ w' y = 0 →
        suMat σ m g *ᵥ y = y := by
  have hw'v : uForm σ w' v = 1 := by rw [← uForm_conj σ hσ v w', g1, map_one]
  have hv'w : uForm σ v' w = 1 := by rw [← uForm_conj σ hσ w v', g2, map_one]
  have hwv : uForm σ w v = 0 := by rw [← uForm_conj σ hσ v w, g7, map_zero]
  have hv'v : uForm σ v' v = 0 := by rw [← uForm_conj σ hσ v v', g8, map_zero]
  have hw'w : uForm σ w' w = 0 := by rw [← uForm_conj σ hσ w w', g9, map_zero]
  have hw'v' : uForm σ w' v' = 0 := by rw [← uForm_conj σ hσ v' w', g10, map_zero]
  set M : Matrix (Fin m) (Fin m) F :=
    (1 + (μ - 1) • vecMulVec v (uRow σ w')) *
      (1 + ((σ μ)⁻¹ - 1) • vecMulVec w' (uRow σ v)) *
      (1 + (ν - 1) • vecMulVec w (uRow σ v')) *
      (1 + ((σ ν)⁻¹ - 1) • vecMulVec v' (uRow σ w)) with hMdef
  have hM : ∀ x, M *ᵥ x = x + ((μ - 1) * uForm σ w' x) • v
      + (((σ μ)⁻¹ - 1) * uForm σ v x) • w' + ((ν - 1) * uForm σ v' x) • w
      + (((σ ν)⁻¹ - 1) * uForm σ w x) • v' := by
    intro x
    simp only [hMdef, ← mulVec_mulVec, one_add_smul_vecMulVec_uRow_mulVec, uForm_add_right,
      uForm_smul_right, g3, g4, g5, g6, g7, g8, g9, g10, hwv, hv'v, hw'w, hw'v', hw'v, hv'w,
      mul_zero, mul_one, add_zero]
    abel
  have hdet : M.det = 1 := by
    rw [hMdef, det_mul, det_mul, det_mul, det_one_add_smul_vecMulVec_uRow,
      det_one_add_smul_vecMulVec_uRow, det_one_add_smul_vecMulVec_uRow,
      det_one_add_smul_vecMulVec_uRow, hw'v, g1, hv'w, g2]
    rw [show (1 + (μ - 1) * 1) * (1 + ((σ μ)⁻¹ - 1) * 1) * (1 + (ν - 1) * 1) *
        (1 + ((σ ν)⁻¹ - 1) * 1) = μ * (σ μ)⁻¹ * ν * (σ ν)⁻¹ by ring]
    have hmain : μ * (σ μ)⁻¹ * ν * (σ ν)⁻¹ = 1 := by
      rw [show μ * (σ μ)⁻¹ * ν * (σ ν)⁻¹ = (μ * ν) * (σ (μ * ν))⁻¹ by
        rw [map_mul, mul_inv_rev (σ μ) (σ ν)]
        ring]
      rw [hμν]
      exact mul_inv_cancel₀ (mul_ne_zero hμ hν)
    exact hmain
  have hcoord : ∀ z, uForm σ w' (M *ᵥ z) = μ * uForm σ w' z ∧
      uForm σ v' (M *ᵥ z) = ν * uForm σ v' z ∧
      uForm σ w (M *ᵥ z) = (σ ν)⁻¹ * uForm σ w z ∧
      uForm σ v (M *ᵥ z) = (σ μ)⁻¹ * uForm σ v z := by
    intro z
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      · rw [hM z]
        simp only [uForm_add_right, uForm_smul_right, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10,
          hwv, hv'v, hw'w, hw'v', hw'v, hv'w, mul_zero, mul_one, add_zero]
        ring
  have hzcoord : ∀ z, suFrameZ σ v w v' w' (M *ᵥ z) = suFrameZ σ v w v' w' z := by
    intro z
    obtain ⟨hz1, hz2, hz3, hz4⟩ := hcoord z
    unfold suFrameZ
    rw [hz1, hz2, hz3, hz4, hM z]
    module
  have hiso : ∀ x y, uForm σ (M *ᵥ x) (M *ᵥ y) = uForm σ x y := by
    intro x y
    have hL := suFrame_expand σ hσ g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 (M *ᵥ x) (M *ᵥ y)
    have hR := suFrame_expand σ hσ g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 x y
    obtain ⟨a1, a2, a3, a4⟩ := hcoord x
    obtain ⟨b1, b2, b3, b4⟩ := hcoord y
    rw [hL, hR, a1, a2, a3, a4, b1, b2, b3, b4, hzcoord x, hzcoord y]
    rw [map_mul, map_mul, map_mul, map_mul, map_inv₀, map_inv₀, hσ, hσ]
    have hsμ : σ μ ≠ 0 := (map_ne_zero σ).mpr hμ
    have hsν : σ ν ≠ 0 := (map_ne_zero σ).mpr hν
    field_simp
  obtain ⟨g, hg⟩ := exists_SU_of_isometry σ hσ (Matrix.toLin' M)
    (fun x y => by
      rw [suForm_β_eq_uForm hσ, suForm_β_eq_uForm hσ, Matrix.toLin'_apply,
        Matrix.toLin'_apply, hiso])
    (by rw [LinearMap.toMatrix'_toLin', hdet])
  refine ⟨g, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hg v
    rw [natRep_apply] at h
    rw [suMat_apply, h, Matrix.toLin'_apply, hM v, hw'v, g3, hv'v, hwv]
    simp only [mul_one, mul_zero, zero_smul, add_zero]
    module
  · have h := hg w
    rw [natRep_apply] at h
    rw [suMat_apply, h, Matrix.toLin'_apply, hM w, hw'w, g7, hv'w, g4]
    simp only [mul_one, mul_zero, zero_smul, add_zero]
    module
  · have h := hg v'
    rw [natRep_apply] at h
    rw [suMat_apply, h, Matrix.toLin'_apply, hM v', hw'v', g8, g5, g2]
    simp only [mul_one, mul_zero, zero_smul, add_zero]
    module
  · have h := hg w'
    rw [natRep_apply] at h
    rw [suMat_apply, h, Matrix.toLin'_apply, hM w', g6, g1, g10, g9]
    simp only [mul_one, mul_zero, zero_smul, add_zero]
    module
  · intro y hy1 hy2 hy3 hy4
    have h := hg y
    rw [natRep_apply] at h
    rw [suMat_apply, h, Matrix.toLin'_apply, hM y, hy1, hy2, hy3, hy4]
    simp only [mul_zero, zero_smul, add_zero]

theorem exists_mem_SU_torus {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') {μ ν : F} (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (hμν : unitaryInvolution F 2 f (μ * ν) = μ * ν) :
    ∃ g : ↥(SU (unitaryInvolution F 2 f) n),
      natRep (SU (unitaryInvolution F 2 f) n) g v = μ • v ∧
      natRep (SU (unitaryInvolution F 2 f) n) g w = ν • w ∧
      natRep (SU (unitaryInvolution F 2 f) n) g v' = (unitaryInvolution F 2 f ν)⁻¹ • v' ∧
      natRep (SU (unitaryInvolution F 2 f) n) g w' = (unitaryInvolution F 2 f μ)⁻¹ • w' ∧
      ∀ y ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}),
        natRep (SU (unitaryInvolution F 2 f) n) g y = y := by
  obtain ⟨h1, h2, hIsot, hOrth⟩ := hfr
  obtain ⟨h3, h4, h5, h6⟩ := hIsot
  obtain ⟨h7, h8, h9, h10⟩ := hOrth
  have g1 : uForm (unitaryInvolution F 2 f) v w' = 1 := by
    rw [← suForm_β_eq_uForm (unitaryInvolution_involutive hc) v w']
    exact h1
  have g2 : uForm (unitaryInvolution F 2 f) w v' = 1 := by
    rw [← suForm_β_eq_uForm (unitaryInvolution_involutive hc) w v']
    exact h2
  have g3 : uForm (unitaryInvolution F 2 f) v v = 0 := by
    rw [← suForm_β_eq_uForm (unitaryInvolution_involutive hc) v v]
    exact h3
  have g4 : uForm (unitaryInvolution F 2 f) w w = 0 := by
    rw [← suForm_β_eq_uForm (unitaryInvolution_involutive hc) w w]
    exact h4
  have g5 : uForm (unitaryInvolution F 2 f) v' v' = 0 := by
    rw [← suForm_β_eq_uForm (unitaryInvolution_involutive hc) v' v']
    exact h5
  have g6 : uForm (unitaryInvolution F 2 f) w' w' = 0 := by
    rw [← suForm_β_eq_uForm (unitaryInvolution_involutive hc) w' w']
    exact h6
  have g7 : uForm (unitaryInvolution F 2 f) v w = 0 := by
    rw [← suForm_β_eq_uForm (unitaryInvolution_involutive hc) v w]
    exact h7
  have g8 : uForm (unitaryInvolution F 2 f) v v' = 0 := by
    rw [← suForm_β_eq_uForm (unitaryInvolution_involutive hc) v v']
    exact h8
  have g9 : uForm (unitaryInvolution F 2 f) w w' = 0 := by
    rw [← suForm_β_eq_uForm (unitaryInvolution_involutive hc) w w']
    exact h9
  have g10 : uForm (unitaryInvolution F 2 f) v' w' = 0 := by
    rw [← suForm_β_eq_uForm (unitaryInvolution_involutive hc) v' w']
    exact h10
  obtain ⟨g, hg1, hg2, hg3, hg4, hg5⟩ :=
    suTorus_of_frame (unitaryInvolution F 2 f) (unitaryInvolution_involutive hc)
      g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 hμ hν hμν
  refine ⟨g, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [natRep_apply, suMat_apply] using hg1
  · simpa only [natRep_apply, suMat_apply] using hg2
  · simpa only [natRep_apply, suMat_apply] using hg3
  · simpa only [natRep_apply, suMat_apply] using hg4
  · intro y hy
    have hv_ : uForm (unitaryInvolution F 2 f) v y = 0 := by
      rw [← suForm_β_eq_uForm (unitaryInvolution_involutive hc) v y]
      exact hy v (Submodule.subset_span (by simp))
    have hw_ : uForm (unitaryInvolution F 2 f) w y = 0 := by
      rw [← suForm_β_eq_uForm (unitaryInvolution_involutive hc) w y]
      exact hy w (Submodule.subset_span (by simp))
    have hv'_ : uForm (unitaryInvolution F 2 f) v' y = 0 := by
      rw [← suForm_β_eq_uForm (unitaryInvolution_involutive hc) v' y]
      exact hy v' (Submodule.subset_span (by simp))
    have hw'_ : uForm (unitaryInvolution F 2 f) w' y = 0 := by
      rw [← suForm_β_eq_uForm (unitaryInvolution_involutive hc) w' y]
      exact hy w' (Submodule.subset_span (by simp))
    simpa only [natRep_apply, suMat_apply] using hg5 y hv_ hw_ hv'_ hw'_

private theorem suSwap_of_frame {F : Type} [Field F] [CharP F 2] {m : ℕ}
    (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c) {v w v' w' : Fin m → F}
    (g1 : uForm σ v w' = 1) (g2 : uForm σ w v' = 1)
    (g3 : uForm σ v v = 0) (g4 : uForm σ w w = 0)
    (g5 : uForm σ v' v' = 0) (g6 : uForm σ w' w' = 0)
    (g7 : uForm σ v w = 0) (g8 : uForm σ v v' = 0)
    (g9 : uForm σ w w' = 0) (g10 : uForm σ v' w' = 0) :
    ∃ s : SU σ m, suMat σ m s *ᵥ v = w ∧ suMat σ m s *ᵥ w = v ∧
      suMat σ m s *ᵥ v' = w' ∧ suMat σ m s *ᵥ w' = v' ∧
      ∀ y, uForm σ v y = 0 → uForm σ w y = 0 → uForm σ v' y = 0 → uForm σ w' y = 0 →
        suMat σ m s *ᵥ y = y := by
  have hw'v : uForm σ w' v = 1 := by rw [← uForm_conj σ hσ v w', g1, map_one]
  have hv'w : uForm σ v' w = 1 := by rw [← uForm_conj σ hσ w v', g2, map_one]
  have hwv : uForm σ w v = 0 := by rw [← uForm_conj σ hσ v w, g7, map_zero]
  have hv'v : uForm σ v' v = 0 := by rw [← uForm_conj σ hσ v v', g8, map_zero]
  have hw'w : uForm σ w' w = 0 := by rw [← uForm_conj σ hσ w w', g9, map_zero]
  have hw'v' : uForm σ w' v' = 0 := by rw [← uForm_conj σ hσ v' w', g10, map_zero]
  let N : Module.End F (Fin m → F) :=
    ((suDual (σ := σ) (hσ := hσ) w' + suDual (σ := σ) (hσ := hσ) v').smulRight (v + w))
      + ((suDual (σ := σ) (hσ := hσ) w + suDual (σ := σ) (hσ := hσ) v).smulRight (v' + w'))
  have hNv : ∀ z, N z = (uForm σ w' z + uForm σ v' z) • (v + w) +
      (uForm σ w z + uForm σ v z) • (v' + w') := by
    intro z
    simp only [N, LinearMap.add_apply, LinearMap.smulRight_apply, suDual_apply,
      suForm_β_eq_uForm hσ]
  have hNvw : N (v + w) = 0 := by
    rw [hNv]
    have e1 : uForm σ w' (v + w) + uForm σ v' (v + w) = 0 := by
      rw [uForm_add_right, uForm_add_right, hw'v, hw'w, hv'v, hv'w]
      simp only [add_zero, zero_add]
      exact CharTwo.add_self_eq_zero 1
    have e2 : uForm σ w (v + w) + uForm σ v (v + w) = 0 := by
      rw [uForm_add_right, uForm_add_right, hwv, g4, g3, g7]
      ring
    rw [e1, e2, zero_smul, zero_smul, add_zero]
  have hNv'w' : N (v' + w') = 0 := by
    rw [hNv]
    have e1 : uForm σ w' (v' + w') + uForm σ v' (v' + w') = 0 := by
      rw [uForm_add_right, uForm_add_right, hw'v', g6, g5, g10]
      ring
    have e2 : uForm σ w (v' + w') + uForm σ v (v' + w') = 0 := by
      rw [uForm_add_right, uForm_add_right, g2, g9, g8, g1]
      simp only [add_zero, zero_add]
      exact CharTwo.add_self_eq_zero 1
    rw [e1, e2, zero_smul, zero_smul, add_zero]
  have hcomp : ∀ z, N (N z) = 0 := by
    intro z
    rw [hNv z, map_add, map_smul, map_smul]
    rw [hNvw, hNv'w', smul_zero, smul_zero, add_zero]
  have hN : IsNilpotent N := by
    refine ⟨2, ?_⟩
    rw [pow_two]
    refine LinearMap.ext fun z => ?_
    rw [Module.End.mul_apply, LinearMap.zero_apply]
    exact hcomp z
  let f : (Fin m → F) →ₗ[F] (Fin m → F) := LinearMap.id + N
  have hf : ∀ z, f z = z + N z := by intro z; simp [f]
  have hcoord : ∀ z, uForm σ w' (f z) = uForm σ v' z ∧
      uForm σ v' (f z) = uForm σ w' z ∧
      uForm σ w (f z) = uForm σ v z ∧ uForm σ v (f z) = uForm σ w z := by
    intro z
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hf z, hNv z, uForm_add_right, uForm_add_right, uForm_smul_right,
        uForm_smul_right, uForm_add_right, uForm_add_right]
      simp only [g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, hwv, hv'v, hw'w, hw'v', hw'v,
        hv'w, mul_one, mul_zero, add_zero, zero_add]
      linear_combination (uForm σ w' z) * (CharTwo.two_eq_zero : (2 : F) = 0)
    · rw [hf z, hNv z, uForm_add_right, uForm_add_right, uForm_smul_right,
        uForm_smul_right, uForm_add_right, uForm_add_right]
      simp only [g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, hwv, hv'v, hw'w, hw'v', hw'v,
        hv'w, mul_one, mul_zero, add_zero, zero_add]
      linear_combination (uForm σ v' z) * (CharTwo.two_eq_zero : (2 : F) = 0)
    · rw [hf z, hNv z, uForm_add_right, uForm_add_right, uForm_smul_right,
        uForm_smul_right, uForm_add_right, uForm_add_right]
      simp only [g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, hwv, hv'v, hw'w, hw'v', hw'v,
        hv'w, mul_one, mul_zero, add_zero, zero_add]
      linear_combination (uForm σ w z) * (CharTwo.two_eq_zero : (2 : F) = 0)
    · rw [hf z, hNv z, uForm_add_right, uForm_add_right, uForm_smul_right,
        uForm_smul_right, uForm_add_right, uForm_add_right]
      simp only [g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, hwv, hv'v, hw'w, hw'v', hw'v,
        hv'w, mul_one, mul_zero, add_zero, zero_add]
      linear_combination (uForm σ v z) * (CharTwo.two_eq_zero : (2 : F) = 0)
  have hzcoord : ∀ z, suFrameZ σ v w v' w' (f z) = suFrameZ σ v w v' w' z := by
    intro z
    obtain ⟨hz1, hz2, hz3, hz4⟩ := hcoord z
    unfold suFrameZ
    rw [hz1, hz2, hz3, hz4, hf z, hNv z]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, CharTwo.sub_eq_add]
    ring_nf
    rw [CharTwo.two_eq_zero]
    ring
  have hiso : ∀ x y, uForm σ (f x) (f y) = uForm σ x y := by
    intro x y
    have hL := suFrame_expand σ hσ g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 (f x) (f y)
    have hR := suFrame_expand σ hσ g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 x y
    obtain ⟨a1, a2, a3, a4⟩ := hcoord x
    obtain ⟨b1, b2, b3, b4⟩ := hcoord y
    rw [hL, hR, a1, a2, a3, a4, b1, b2, b3, b4, hzcoord x, hzcoord y]
    ring
  obtain ⟨s, hs⟩ := exists_SU_of_isometry σ hσ f
    (fun x y => by rw [suForm_β_eq_uForm hσ, suForm_β_eq_uForm hσ, hiso])
    (by rw [show f = LinearMap.id + N from rfl]; exact det_toMatrix'_id_add hN)
  refine ⟨s, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hs v
    rw [natRep_apply] at h
    rw [suMat_apply, h, LinearMap.add_apply, LinearMap.id_apply, hNv v]
    rw [hw'v, hv'v, hwv, g3]
    simp only [add_zero, zero_add, zero_smul, one_smul]
    rw [← add_assoc, ← two_smul F v, CharTwo.two_eq_zero, zero_smul, zero_add]
  · have h := hs w
    rw [natRep_apply] at h
    rw [suMat_apply, h, LinearMap.add_apply, LinearMap.id_apply, hNv w]
    rw [hw'w, hv'w, g4, g7]
    simp only [add_zero, zero_add, zero_smul, one_smul]
    rw [add_comm v w, ← add_assoc, ← two_smul F w, CharTwo.two_eq_zero, zero_smul, zero_add]
  · have h := hs v'
    rw [natRep_apply] at h
    rw [suMat_apply, h, LinearMap.add_apply, LinearMap.id_apply, hNv v']
    rw [hw'v', g5, g2, g8]
    simp only [add_zero, zero_add, zero_smul, one_smul]
    rw [← add_assoc, ← two_smul F v', CharTwo.two_eq_zero, zero_smul, zero_add]
  · have h := hs w'
    rw [natRep_apply] at h
    rw [suMat_apply, h, LinearMap.add_apply, LinearMap.id_apply, hNv w']
    rw [g6, g10, g9, g1]
    simp only [add_zero, zero_add, zero_smul, one_smul]
    rw [add_comm v' w', ← add_assoc, ← two_smul F w', CharTwo.two_eq_zero, zero_smul, zero_add]
  · intro y hy1 hy2 hy3 hy4
    have h := hs y
    rw [natRep_apply] at h
    rw [suMat_apply, h, LinearMap.add_apply, LinearMap.id_apply, hNv y]
    rw [hy1, hy2, hy3, hy4]
    simp only [add_zero, zero_smul, add_zero]

theorem exists_mem_SU_swap {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') :
    ∃ s : ↥(SU (unitaryInvolution F 2 f) n),
      natRep (SU (unitaryInvolution F 2 f) n) s v = w ∧
      natRep (SU (unitaryInvolution F 2 f) n) s w = v ∧
      natRep (SU (unitaryInvolution F 2 f) n) s v' = w' ∧
      natRep (SU (unitaryInvolution F 2 f) n) s w' = v' ∧
      ∀ y ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}),
        natRep (SU (unitaryInvolution F 2 f) n) s y = y := by
  obtain ⟨h1, h2, hIsot, hOrth⟩ := hfr
  obtain ⟨h3, h4, h5, h6⟩ := hIsot
  obtain ⟨h7, h8, h9, h10⟩ := hOrth
  have g1 : uForm (unitaryInvolution F 2 f) v w' = 1 := by
    rw [← suForm_β_eq_uForm (unitaryInvolution_involutive hc) v w']
    exact h1
  have g2 : uForm (unitaryInvolution F 2 f) w v' = 1 := by
    rw [← suForm_β_eq_uForm (unitaryInvolution_involutive hc) w v']
    exact h2
  have g3 : uForm (unitaryInvolution F 2 f) v v = 0 := by
    rw [← suForm_β_eq_uForm (unitaryInvolution_involutive hc) v v]
    exact h3
  have g4 : uForm (unitaryInvolution F 2 f) w w = 0 := by
    rw [← suForm_β_eq_uForm (unitaryInvolution_involutive hc) w w]
    exact h4
  have g5 : uForm (unitaryInvolution F 2 f) v' v' = 0 := by
    rw [← suForm_β_eq_uForm (unitaryInvolution_involutive hc) v' v']
    exact h5
  have g6 : uForm (unitaryInvolution F 2 f) w' w' = 0 := by
    rw [← suForm_β_eq_uForm (unitaryInvolution_involutive hc) w' w']
    exact h6
  have g7 : uForm (unitaryInvolution F 2 f) v w = 0 := by
    rw [← suForm_β_eq_uForm (unitaryInvolution_involutive hc) v w]
    exact h7
  have g8 : uForm (unitaryInvolution F 2 f) v v' = 0 := by
    rw [← suForm_β_eq_uForm (unitaryInvolution_involutive hc) v v']
    exact h8
  have g9 : uForm (unitaryInvolution F 2 f) w w' = 0 := by
    rw [← suForm_β_eq_uForm (unitaryInvolution_involutive hc) w w']
    exact h9
  have g10 : uForm (unitaryInvolution F 2 f) v' w' = 0 := by
    rw [← suForm_β_eq_uForm (unitaryInvolution_involutive hc) v' w']
    exact h10
  obtain ⟨s, hs1, hs2, hs3, hs4, hs5⟩ :=
    suSwap_of_frame (unitaryInvolution F 2 f) (unitaryInvolution_involutive hc)
      g1 g2 g3 g4 g5 g6 g7 g8 g9 g10
  refine ⟨s, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [natRep_apply, suMat_apply] using hs1
  · simpa only [natRep_apply, suMat_apply] using hs2
  · simpa only [natRep_apply, suMat_apply] using hs3
  · simpa only [natRep_apply, suMat_apply] using hs4
  · intro y hy
    have hv_ : uForm (unitaryInvolution F 2 f) v y = 0 := by
      rw [← suForm_β_eq_uForm (unitaryInvolution_involutive hc) v y]
      exact hy v (Submodule.subset_span (by simp))
    have hw_ : uForm (unitaryInvolution F 2 f) w y = 0 := by
      rw [← suForm_β_eq_uForm (unitaryInvolution_involutive hc) w y]
      exact hy w (Submodule.subset_span (by simp))
    have hv'_ : uForm (unitaryInvolution F 2 f) v' y = 0 := by
      rw [← suForm_β_eq_uForm (unitaryInvolution_involutive hc) v' y]
      exact hy v' (Submodule.subset_span (by simp))
    have hw'_ : uForm (unitaryInvolution F 2 f) w' y = 0 := by
      rw [← suForm_β_eq_uForm (unitaryInvolution_involutive hc) w' y]
      exact hy w' (Submodule.subset_span (by simp))
    simpa only [natRep_apply, suMat_apply] using hs5 y hv_ hw_ hv'_ hw'_

end CFSG.StandardType.LieKnownR2.Short
