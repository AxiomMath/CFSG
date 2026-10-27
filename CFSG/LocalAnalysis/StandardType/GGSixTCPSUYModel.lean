module

public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUNotDvd
public import CFSG.LieType.Steinberg.CentralExt.HermitianBasis
public import CFSG.Models.Transport
public import CFSG.Models.Blueprint
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.ClassicalPosition

section RankFactorization

theorem exists_rankFactorization_of_isIdempotentElem {F : Type} [Field F] {n : ℕ}
    {T : Matrix (Fin n) (Fin n) F} (hT : IsIdempotentElem T) :
    ∃ (P : Matrix (Fin n) (Fin (Matrix.rank T)) F) (R : Matrix (Fin (Matrix.rank T)) (Fin n) F),
      T = P * R ∧ R * P = 1 := by
  have hTT : T * T = T := hT
  have hfix : ∀ w : LinearMap.range T.mulVecLin,
      Matrix.mulVec T (w : Fin n → F) = (w : Fin n → F) := by
    intro w
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp w.2
    have hu' : Matrix.mulVec T u = (w : Fin n → F) := hu
    calc Matrix.mulVec T (w : Fin n → F) = Matrix.mulVec T (Matrix.mulVec T u) := by
          rw [hu']
      _ = Matrix.mulVec (T * T) u := by rw [Matrix.mulVec_mulVec]
      _ = Matrix.mulVec T u := by rw [hTT]
      _ = (w : Fin n → F) := hu'
  let b : Module.Basis (Fin (Matrix.rank T)) F (LinearMap.range T.mulVecLin) :=
    Module.finBasisOfFinrankEq F (LinearMap.range T.mulVecLin) rfl
  let f : (Fin n → F) →ₗ[F] LinearMap.range T.mulVecLin :=
    LinearMap.codRestrict (LinearMap.range T.mulVecLin) T.mulVecLin
      (fun v => LinearMap.mem_range_self T.mulVecLin v)
  let cL : (Fin n → F) →ₗ[F] (Fin (Matrix.rank T) → F) :=
    LinearMap.comp b.equivFun.toLinearMap f
  let pL : (Fin (Matrix.rank T) → F) →ₗ[F] (Fin n → F) :=
    LinearMap.comp (LinearMap.range T.mulVecLin).subtype b.equivFun.symm.toLinearMap
  refine ⟨LinearMap.toMatrix' pL, LinearMap.toMatrix' cL, ?_, ?_⟩
  · apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
    apply LinearMap.ext
    intro v
    simp [cL, pL, f, LinearMap.codRestrict_apply]
  · apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix', Matrix.toLin'_one]
    apply LinearMap.ext
    intro x
    have hw : f (pL x) = b.equivFun.symm x := by
      apply Subtype.ext
      exact hfix (b.equivFun.symm x)
    show b.equivFun (f (pL x)) = x
    rw [hw, LinearEquiv.apply_symm_apply]

end RankFactorization

section YEmbed

open CFSG.LieType.Universal.Unitary

variable {F : Type} [Field F] {n r : ℕ}

@[expose] def tcYEmb (P : Matrix (Fin n) (Fin r) F) (R : Matrix (Fin r) (Fin n) F)
    (u : Matrix (Fin r) (Fin r) F) : Matrix (Fin n) (Fin n) F :=
  1 + P * (u - 1) * R

theorem tcYEmb_one (P : Matrix (Fin n) (Fin r) F) (R : Matrix (Fin r) (Fin n) F) :
    tcYEmb P R 1 = 1 := by
  simp [tcYEmb]

theorem tcSandwich_mul {P : Matrix (Fin n) (Fin r) F} {R : Matrix (Fin r) (Fin n) F}
    (h : R * P = 1) (X Y : Matrix (Fin r) (Fin r) F) :
    (P * X * R) * (P * Y * R) = P * (X * Y) * R := by
  calc (P * X * R) * (P * Y * R) = P * X * (R * P) * Y * R := by simp only [Matrix.mul_assoc]
    _ = P * (X * Y) * R := by rw [h, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem tcSandwich_add (P : Matrix (Fin n) (Fin r) F) (R : Matrix (Fin r) (Fin n) F)
    (X Y : Matrix (Fin r) (Fin r) F) : P * X * R + P * Y * R = P * (X + Y) * R := by
  rw [Matrix.mul_add, Matrix.add_mul]

theorem tcYEmb_mul {P : Matrix (Fin n) (Fin r) F} {R : Matrix (Fin r) (Fin n) F} (h : R * P = 1)
    (u v : Matrix (Fin r) (Fin r) F) : tcYEmb P R u * tcYEmb P R v = tcYEmb P R (u * v) := by
  unfold tcYEmb
  have e1 : (1 + P * (u - 1) * R) * (1 + P * (v - 1) * R) =
      1 + (P * (u - 1) * R + P * (v - 1) * R + (P * (u - 1) * R) * (P * (v - 1) * R)) := by
    generalize P * (u - 1) * R = A
    generalize P * (v - 1) * R = B
    noncomm_ring
  rw [e1, tcSandwich_mul h, tcSandwich_add, tcSandwich_add]
  congr 3
  noncomm_ring

theorem det_tcYEmb {P : Matrix (Fin n) (Fin r) F} {R : Matrix (Fin r) (Fin n) F} (h : R * P = 1)
    (u : Matrix (Fin r) (Fin r) F) : (tcYEmb P R u).det = u.det := by
  unfold tcYEmb
  have e : 1 + P * (u - 1) * R = 1 + P * ((u - 1) * R) := by rw [Matrix.mul_assoc]
  rw [e, Matrix.det_one_add_mul_comm]
  have e2 : (u - 1) * R * P = u - 1 := by rw [Matrix.mul_assoc, h, Matrix.mul_one]
  rw [e2]
  simp

theorem tcYEmb_mul_one_sub {P : Matrix (Fin n) (Fin r) F} {R : Matrix (Fin r) (Fin n) F}
    (h : R * P = 1) (u : Matrix (Fin r) (Fin r) F) :
    tcYEmb P R u * (1 - P * R) = 1 - P * R := by
  unfold tcYEmb
  have e : (1 + P * (u - 1) * R) * (1 - P * R) =
      1 - P * R + (P * (u - 1) * R - (P * (u - 1) * R) * (P * R)) := by
    generalize P * (u - 1) * R = A
    generalize P * R = B
    noncomm_ring
  have e2 : (P * (u - 1) * R) * (P * R) = P * (u - 1) * R := by
    have := tcSandwich_mul h (u - 1) 1
    rw [Matrix.mul_one] at this
    simpa [Matrix.mul_assoc] using this
  rw [e, e2, sub_self, add_zero]

theorem tcYProj_tcYEmb {P : Matrix (Fin n) (Fin r) F} {R : Matrix (Fin r) (Fin n) F} (h : R * P = 1)
    (u : Matrix (Fin r) (Fin r) F) : R * tcYEmb P R u * P = u := by
  unfold tcYEmb
  have e : R * (1 + P * (u - 1) * R) * P = R * P + (R * P) * (u - 1) * (R * P) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [e, h]
  simp

theorem tcYEmb_tcYProj {P : Matrix (Fin n) (Fin r) F} {R : Matrix (Fin r) (Fin n) F} (h : R * P = 1)
    {y : Matrix (Fin n) (Fin n) F} (hy1 : y * (1 - P * R) = 1 - P * R)
    (hy2 : y * (P * R) = (P * R) * y) : tcYEmb P R (R * y * P) = y := by
  unfold tcYEmb
  have hT : (P * R) * (P * R) = P * R := by
    have := tcSandwich_mul h 1 1
    simpa [Matrix.mul_assoc] using this
  have hyT : y = (1 - P * R) + y * (P * R) := by
    have : y * (1 - P * R) = y - y * (P * R) := by rw [Matrix.mul_sub, Matrix.mul_one]
    rw [this] at hy1
    calc y = (y - y * (P * R)) + y * (P * R) := by abel
      _ = (1 - P * R) + y * (P * R) := by rw [hy1]
  have hTyT : P * (R * y * P) * R = y * (P * R) := by
    calc P * (R * y * P) * R = (P * R) * y * (P * R) := by simp only [Matrix.mul_assoc]
      _ = y * (P * R) * (P * R) := by rw [← hy2]
      _ = y * ((P * R) * (P * R)) := by rw [Matrix.mul_assoc]
      _ = y * (P * R) := by rw [hT]
  have : 1 + P * (R * y * P - 1) * R = 1 - P * R + P * (R * y * P) * R := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    generalize P * (R * y * P) * R = A
    generalize P * R = B
    noncomm_ring
  rw [this, hTyT]
  exact hyT.symm

@[expose] def tcConjTr {m k : Type} (σ : F ≃+* F) (A : Matrix m k F) : Matrix k m F :=
  Matrix.transpose (A.map σ)

theorem tcConjTr_mul {m k l : Type} [Fintype k] (σ : F ≃+* F) (A : Matrix m k F)
    (B : Matrix k l F) :
    tcConjTr σ (A * B) = tcConjTr σ B * tcConjTr σ A := by
  unfold tcConjTr
  rw [show (A * B).map σ = A.map σ * B.map σ from Matrix.map_mul (f := σ.toRingHom),
    Matrix.transpose_mul]

theorem tcConjTr_add {m k : Type} (σ : F ≃+* F) (A B : Matrix m k F) :
    tcConjTr σ (A + B) = tcConjTr σ A + tcConjTr σ B := by
  unfold tcConjTr
  ext i j
  simp

theorem tcConjTr_sub {m k : Type} (σ : F ≃+* F) (A B : Matrix m k F) :
    tcConjTr σ (A - B) = tcConjTr σ A - tcConjTr σ B := by
  unfold tcConjTr
  ext i j
  simp

theorem tcConjTr_one {m : Type} [DecidableEq m] (σ : F ≃+* F) :
    tcConjTr σ (1 : Matrix m m F) = 1 := by
  unfold tcConjTr
  ext i j
  simp [Matrix.one_apply, eq_comm]

theorem tcConjTr_tcConjTr {m k : Type} {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) (A : Matrix m k F) :
    tcConjTr σ (tcConjTr σ A) = A := by
  unfold tcConjTr
  ext i j
  simp [hσ]

theorem conjTr_eq_tcConjTr (σ : F ≃+* F) (A : Matrix (Fin n) (Fin n) F) :
    Unitary.conjTr σ A = tcConjTr σ A := rfl

theorem tcYEmb_unitary {σ : F ≃+* F} (_hσ : ∀ c, σ (σ c) = c) {P : Matrix (Fin n) (Fin r) F}
    {R : Matrix (Fin r) (Fin n) F} (_h : R * P = 1)
    (hgram : tcConjTr σ P * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * P =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F))
    (hadj : tcConjTr σ P * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F) * R)
    (hadj' : (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * P =
      tcConjTr σ R * (Unitary.antidiag r : Matrix (Fin r) (Fin r) F))
    {u : Matrix (Fin r) (Fin r) F}
    (hu : Unitary.conjTr σ u * (Unitary.antidiag r : Matrix (Fin r) (Fin r) F) * u =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F)) :
    Unitary.conjTr σ (tcYEmb P R u) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) *
      tcYEmb P R u = (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) := by
  set J : Matrix (Fin n) (Fin n) F := Unitary.antidiag n with hJ
  set Jr : Matrix (Fin r) (Fin r) F := Unitary.antidiag r with hJr
  set X : Matrix (Fin r) (Fin r) F := u - 1 with hX
  have hXs : tcConjTr σ X = Unitary.conjTr σ u - 1 := by
    rw [hX, tcConjTr_sub, tcConjTr_one]; rfl
  have h1 : Unitary.conjTr σ (tcYEmb P R u) = 1 + tcConjTr σ R * tcConjTr σ X * tcConjTr σ P := by
    rw [conjTr_eq_tcConjTr]
    unfold tcYEmb
    rw [tcConjTr_add, tcConjTr_one, tcConjTr_mul, tcConjTr_mul, ← hX]
    simp only [Matrix.mul_assoc]
  have e1 : (1 + tcConjTr σ R * tcConjTr σ X * tcConjTr σ P) * J * (1 + P * X * R) =
      J + (tcConjTr σ R * tcConjTr σ X * (tcConjTr σ P * J) + (J * P) * X * R +
        tcConjTr σ R * tcConjTr σ X * (tcConjTr σ P * J * P) * X * R) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    abel
  have e2 : tcConjTr σ R * tcConjTr σ X * (tcConjTr σ P * J) + (J * P) * X * R +
      tcConjTr σ R * tcConjTr σ X * (tcConjTr σ P * J * P) * X * R =
      tcConjTr σ R * (tcConjTr σ X * Jr + Jr * X + tcConjTr σ X * Jr * X) * R := by
    rw [hgram, hadj, hadj']
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have e3 : tcConjTr σ X * Jr + Jr * X + tcConjTr σ X * Jr * X = 0 := by
    rw [hXs, hX]
    have : Unitary.conjTr σ u * Jr * u = Jr := hu
    calc (Unitary.conjTr σ u - 1) * Jr + Jr * (u - 1) + (Unitary.conjTr σ u - 1) * Jr * (u - 1)
        = Unitary.conjTr σ u * Jr * u - Jr := by noncomm_ring
      _ = 0 := by rw [this, sub_self]
  rw [h1]
  unfold tcYEmb
  rw [← hX, e1, e2, e3]
  simp

end YEmbed

section YData

open CFSG.LieType.Universal.Unitary

variable {g n r : ℕ}

theorem exists_tcYData_of_factorization {T : Matrix (Fin n) (Fin n) (PSUF g)}
    (hTa : formAdj (PSUσ g).toRingHom (Unitary.antidiag n) T = T)
    {P₀ : Matrix (Fin n) (Fin r) (PSUF g)} {R₀ : Matrix (Fin r) (Fin n) (PSUF g)}
    (hT : T = P₀ * R₀) (hRP : R₀ * P₀ = 1) :
    ∃ (P : Matrix (Fin n) (Fin r) (PSUF g)) (R : Matrix (Fin r) (Fin n) (PSUF g)),
      T = P * R ∧ R * P = 1 ∧
      tcConjTr (PSUσ g) P * (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) * P =
        (Unitary.antidiag r : Matrix (Fin r) (Fin r) (PSUF g)) ∧
      tcConjTr (PSUσ g) P * (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) =
        (Unitary.antidiag r : Matrix (Fin r) (Fin r) (PSUF g)) * R ∧
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) * P =
        tcConjTr (PSUσ g) R * (Unitary.antidiag r : Matrix (Fin r) (Fin r) (PSUF g)) := by
  classical
  set σ : PSUF g ≃+* PSUF g := PSUσ g with hσdef
  set J : Matrix (Fin n) (Fin n) (PSUF g) := Unitary.antidiag n with hJ
  set Jr : Matrix (Fin r) (Fin r) (PSUF g) := Unitary.antidiag r with hJr
  have hσσ : ∀ c, σ (σ c) = c := PSUσ_involutive g
  have hdet : IsUnit J.det := PSUantidiag_isUnit_det n g
  have hJh : tcConjTr σ J = J := PSUantidiag_transpose_map n g
  have hJrh : tcConjTr σ Jr = Jr := PSUantidiag_transpose_map r g
  have hJinv : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hdet
  have hadjT : tcConjTr σ T * J = J * T := by
    have h1 := congrArg (fun M => J * M) hTa
    simp only [formAdj] at h1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJinv, Matrix.one_mul] at h1
    exact h1
  have hTP : T * P₀ = P₀ := by
    rw [hT, Matrix.mul_assoc, hRP, Matrix.mul_one]
  set G : Matrix (Fin r) (Fin r) (PSUF g) := tcConjTr σ P₀ * J * P₀ with hG
  have hGR : tcConjTr σ P₀ * J = G * R₀ := by
    have e1 : G * R₀ = tcConjTr σ P₀ * (J * T) := by
      rw [hG, hT]
      simp only [Matrix.mul_assoc]
    rw [e1, ← hadjT, ← Matrix.mul_assoc, ← tcConjTr_mul, hTP]
  have hGh : tcConjTr σ G = G := by
    rw [hG, tcConjTr_mul, tcConjTr_mul, hJh, tcConjTr_tcConjTr hσσ]
    simp only [Matrix.mul_assoc]
  have hGinv : G * (R₀ * J⁻¹ * tcConjTr σ R₀) = 1 := by
    calc G * (R₀ * J⁻¹ * tcConjTr σ R₀) = (G * R₀) * J⁻¹ * tcConjTr σ R₀ := by
          simp only [Matrix.mul_assoc]
      _ = tcConjTr σ P₀ * J * J⁻¹ * tcConjTr σ R₀ := by rw [← hGR]
      _ = tcConjTr σ P₀ * tcConjTr σ R₀ := by
          rw [Matrix.mul_assoc (tcConjTr σ P₀) J J⁻¹, hJinv, Matrix.mul_one]
      _ = 1 := by rw [← tcConjTr_mul, hRP, tcConjTr_one]
  have hGdet : G.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hGinv
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  obtain ⟨N, hN⟩ := CFSG.LieType.Steinberg.exists_conjTr_mul_mul_eq_one (F := PSUF g) (p := 2)
    (f := g + 1) (card_PSUF g) (n := r) (G := G) hGh hGdet
  obtain ⟨W, hW⟩ := Unitary.exists_wittMatrix (F := PSUF g) (p := 2) (f := g + 1)
    (card_PSUF g) r
  set M : GL (Fin r) (PSUF g) := N * W with hM
  set Mm : Matrix (Fin r) (Fin r) (PSUF g) := (M : Matrix (Fin r) (Fin r) (PSUF g)) with hMm
  set Mi : Matrix (Fin r) (Fin r) (PSUF g) := ((M⁻¹ : GL (Fin r) (PSUF g)) :
    Matrix (Fin r) (Fin r) (PSUF g)) with hMi
  have hMMi : Mm * Mi = 1 := by
    rw [hMm, hMi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMiM : Mi * Mm = 1 := by
    rw [hMm, hMi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hMG : tcConjTr σ Mm * G * Mm = Jr := by
    have hN' : tcConjTr σ (N : Matrix (Fin r) (Fin r) (PSUF g)) * G *
        (N : Matrix (Fin r) (Fin r) (PSUF g)) = 1 := hN
    have hW' : tcConjTr σ (W : Matrix (Fin r) (Fin r) (PSUF g)) *
        (W : Matrix (Fin r) (Fin r) (PSUF g)) = Jr := hW
    rw [hMm, hM, Units.val_mul, tcConjTr_mul]
    calc tcConjTr σ (W : Matrix (Fin r) (Fin r) (PSUF g)) *
          tcConjTr σ (N : Matrix (Fin r) (Fin r) (PSUF g)) *
          G * ((N : Matrix (Fin r) (Fin r) (PSUF g)) * (W : Matrix (Fin r) (Fin r) (PSUF g)))
        = tcConjTr σ (W : Matrix (Fin r) (Fin r) (PSUF g)) *
          (tcConjTr σ (N : Matrix (Fin r) (Fin r) (PSUF g)) * G *
            (N : Matrix (Fin r) (Fin r) (PSUF g))) *
          (W : Matrix (Fin r) (Fin r) (PSUF g)) := by simp only [Matrix.mul_assoc]
      _ = Jr := by rw [hN', Matrix.mul_one]; exact hW'
  have h4 : tcConjTr σ (P₀ * Mm) * J = Jr * (Mi * R₀) := by
    calc tcConjTr σ (P₀ * Mm) * J = tcConjTr σ Mm * (tcConjTr σ P₀ * J) := by
          rw [tcConjTr_mul]; simp only [Matrix.mul_assoc]
      _ = tcConjTr σ Mm * (G * R₀) := by rw [hGR]
      _ = (tcConjTr σ Mm * G * Mm) * (Mi * R₀) := by
          calc tcConjTr σ Mm * (G * R₀) = tcConjTr σ Mm * G * (Mm * Mi) * R₀ := by
                rw [hMMi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
            _ = (tcConjTr σ Mm * G * Mm) * (Mi * R₀) := by simp only [Matrix.mul_assoc]
      _ = Jr * (Mi * R₀) := by rw [hMG]
  refine ⟨P₀ * Mm, Mi * R₀, ?_, ?_, ?_, h4, ?_⟩
  · calc T = P₀ * R₀ := hT
      _ = P₀ * (Mm * Mi) * R₀ := by rw [hMMi, Matrix.mul_one]
      _ = P₀ * Mm * (Mi * R₀) := by simp only [Matrix.mul_assoc]
  · calc Mi * R₀ * (P₀ * Mm) = Mi * (R₀ * P₀) * Mm := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hRP, Matrix.mul_one, hMiM]
  · calc tcConjTr σ (P₀ * Mm) * J * (P₀ * Mm) = tcConjTr σ Mm * (tcConjTr σ P₀ * J * P₀) * Mm := by
          rw [tcConjTr_mul]; simp only [Matrix.mul_assoc]
      _ = Jr := by rw [← hG]; exact hMG
  · have h5 := congrArg (tcConjTr σ) h4
    rw [tcConjTr_mul σ (tcConjTr σ (P₀ * Mm)) J, tcConjTr_tcConjTr hσσ, hJh,
      tcConjTr_mul σ Jr (Mi * R₀), hJrh] at h5
    exact h5

end YData

section YIso

open CFSG.LieType.Universal.Unitary

variable {g n r : ℕ}

structure PSUYData (g n r : ℕ) (T : Matrix (Fin n) (Fin n) (PSUF g))
    (P : Matrix (Fin n) (Fin r) (PSUF g)) (R : Matrix (Fin r) (Fin n) (PSUF g)) : Prop where
  fac : T = P * R
  selfadj : formAdj (PSUσ g).toRingHom (Unitary.antidiag n) T = T
  rp : R * P = 1
  gram : tcConjTr (PSUσ g) P * (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) * P =
    (Unitary.antidiag r : Matrix (Fin r) (Fin r) (PSUF g))
  adj : tcConjTr (PSUσ g) P * (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) =
    (Unitary.antidiag r : Matrix (Fin r) (Fin r) (PSUF g)) * R
  adj' : (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) * P =
    tcConjTr (PSUσ g) R * (Unitary.antidiag r : Matrix (Fin r) (Fin r) (PSUF g))

@[expose] noncomputable def tcYEmbGL {F : Type} [Field F] {P : Matrix (Fin n) (Fin r) F}
    {R : Matrix (Fin r) (Fin n) F} (h : R * P = 1) : GL (Fin r) F →* GL (Fin n) F where
  toFun u := ⟨tcYEmb P R (u : Matrix (Fin r) (Fin r) F),
    tcYEmb P R ((u⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F),
    by rw [tcYEmb_mul h, ← Units.val_mul, mul_inv_cancel, Units.val_one, tcYEmb_one],
    by rw [tcYEmb_mul h, ← Units.val_mul, inv_mul_cancel, Units.val_one, tcYEmb_one]⟩
  map_one' := by
    ext1
    simp [tcYEmb_one]
  map_mul' u v := by
    ext1
    simp only [Units.val_mul]
    exact (tcYEmb_mul h _ _).symm

@[expose] noncomputable def tcYEmbSU {T : Matrix (Fin n) (Fin n) (PSUF g)}
    {P : Matrix (Fin n) (Fin r) (PSUF g)} {R : Matrix (Fin r) (Fin n) (PSUF g)}
    (hD : PSUYData g n r T P R) :
    ↥(Unitary.SU (PSUσ g) r) →* ↥(Unitary.SU (PSUσ g) n) :=
  ((tcYEmbGL hD.rp).comp (Unitary.SU (PSUσ g) r).subtype).codRestrict (Unitary.SU (PSUσ g) n)
    fun u => by
      refine ⟨?_, ?_⟩
      · change (tcYEmb P R ((u : GL (Fin r) (PSUF g)) : Matrix (Fin r) (Fin r) (PSUF g))).det = 1
        rw [det_tcYEmb hD.rp]
        exact u.2.1
      · exact tcYEmb_unitary (PSUσ_involutive g) hD.rp hD.gram hD.adj hD.adj' u.2.2

theorem coe_tcYEmbSU {T : Matrix (Fin n) (Fin n) (PSUF g)} {P : Matrix (Fin n) (Fin r) (PSUF g)}
    {R : Matrix (Fin r) (Fin n) (PSUF g)} (hD : PSUYData g n r T P R)
    (u : ↥(Unitary.SU (PSUσ g) r)) :
    (((tcYEmbSU hD u : ↥(Unitary.SU (PSUσ g) n)) : GL (Fin n) (PSUF g)) :
      Matrix (Fin n) (Fin n) (PSUF g)) =
      tcYEmb P R (((u : GL (Fin r) (PSUF g))) : Matrix (Fin r) (Fin r) (PSUF g)) := rfl

theorem tcYEmbSU_injective {T : Matrix (Fin n) (Fin n) (PSUF g)}
    {P : Matrix (Fin n) (Fin r) (PSUF g)} {R : Matrix (Fin r) (Fin n) (PSUF g)}
    (hD : PSUYData g n r T P R) : Function.Injective (tcYEmbSU hD) := by
  intro u v huv
  have h1 := congrArg (fun w : ↥(Unitary.SU (PSUσ g) n) =>
    R * (((w : GL (Fin n) (PSUF g))) : Matrix (Fin n) (Fin n) (PSUF g)) * P) huv
  simp only [coe_tcYEmbSU, tcYProj_tcYEmb hD.rp] at h1
  exact Subtype.ext (Units.ext h1)

theorem exists_PSUYData_of_factorization {T : Matrix (Fin n) (Fin n) (PSUF g)}
    (hTa : formAdj (PSUσ g).toRingHom (Unitary.antidiag n) T = T)
    {P₀ : Matrix (Fin n) (Fin r) (PSUF g)} {R₀ : Matrix (Fin r) (Fin n) (PSUF g)}
    (hT : T = P₀ * R₀) (hRP : R₀ * P₀ = 1) :
    ∃ (P : Matrix (Fin n) (Fin r) (PSUF g)) (R : Matrix (Fin r) (Fin n) (PSUF g)),
      PSUYData g n r T P R := by
  obtain ⟨P, R, h1, h2, h3, h4, h5⟩ := exists_tcYData_of_factorization hTa hT hRP
  exact ⟨P, R, ⟨h1, hTa, h2, h3, h4, h5⟩⟩

theorem PSUYsd_range_tcYEmbSU {T : Matrix (Fin n) (Fin n) (PSUF g)}
    {P : Matrix (Fin n) (Fin r) (PSUF g)} {R : Matrix (Fin r) (Fin n) (PSUF g)}
    (hD : PSUYData g n r T P R) : (tcYEmbSU hD).range = PSUYsd n g T := by
  have hσσ : ∀ c, PSUσ g (PSUσ g c) = c := PSUσ_involutive g
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    rw [mem_PSUYsd]
    change tcYEmb P R ((u : GL (Fin r) (PSUF g)) : Matrix (Fin r) (Fin r) (PSUF g)) * (1 - T) =
      1 - T
    rw [hD.fac]
    exact tcYEmb_mul_one_sub hD.rp _
  · intro hy
    set ym : Matrix (Fin n) (Fin n) (PSUF g) := ((y : GL (Fin n) (PSUF g)) :
      Matrix (Fin n) (Fin n) (PSUF g)) with hym
    have hy1 : ym * (1 - P * R) = 1 - P * R := by
      have := (mem_PSUYsd (T := T)).mp hy
      rw [hD.fac] at this
      exact this
    have hy2 : ym * (P * R) = (P * R) * ym := by
      have := PSUYsd.comm_T hD.selfadj hy
      rw [hD.fac] at this
      exact this
    have hyu : tcConjTr (PSUσ g) ym * (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) * ym =
        Unitary.antidiag n := y.2.2
    have hdety : ym.det = 1 := y.2.1
    set Um : Matrix (Fin r) (Fin r) (PSUF g) := R * ym * P with hUm
    have hyU : tcYEmb P R Um = ym := tcYEmb_tcYProj hD.rp hy1 hy2
    have hdetU : Um.det = 1 := by
      rw [← det_tcYEmb hD.rp Um, hyU, hdety]
    have hTP : P * R * P = P := by rw [Matrix.mul_assoc, hD.rp, Matrix.mul_one]
    have hUu : tcConjTr (PSUσ g) Um * (Unitary.antidiag r : Matrix (Fin r) (Fin r) (PSUF g)) * Um =
        Unitary.antidiag r := by
      have hRJR : tcConjTr (PSUσ g) R * (Unitary.antidiag r : Matrix (Fin r) (Fin r) (PSUF g)) * R =
          (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) * (P * R) := by
        rw [← hD.adj', Matrix.mul_assoc]
      calc tcConjTr (PSUσ g) Um * (Unitary.antidiag r : Matrix (Fin r) (Fin r) (PSUF g)) * Um
          = tcConjTr (PSUσ g) P * tcConjTr (PSUσ g) ym * (tcConjTr (PSUσ g) R *
              (Unitary.antidiag r : Matrix (Fin r) (Fin r) (PSUF g)) * R) * ym * P := by
            rw [hUm, tcConjTr_mul, tcConjTr_mul]; simp only [Matrix.mul_assoc]
        _ = tcConjTr (PSUσ g) P * tcConjTr (PSUσ g) ym *
              ((Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) * (P * R)) * ym * P := by
            rw [hRJR]
        _ = tcConjTr (PSUσ g) P * (tcConjTr (PSUσ g) ym *
              (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) * ym) * (P * R) * P := by
            have e : (P * R) * ym = ym * (P * R) := hy2.symm
            calc tcConjTr (PSUσ g) P * tcConjTr (PSUσ g) ym *
                ((Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) * (P * R)) * ym * P
                = tcConjTr (PSUσ g) P * tcConjTr (PSUσ g) ym *
                  (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) * ((P * R) * ym) * P := by
                  simp only [Matrix.mul_assoc]
              _ = tcConjTr (PSUσ g) P * tcConjTr (PSUσ g) ym *
                  (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) * (ym * (P * R)) * P := by
                  rw [e]
              _ = _ := by simp only [Matrix.mul_assoc]
        _ = tcConjTr (PSUσ g) P * (Unitary.antidiag n : Matrix (Fin n) (Fin n) (PSUF g)) *
              (P * R * P) := by
            rw [hyu]; simp only [Matrix.mul_assoc]
        _ = (Unitary.antidiag r : Matrix (Fin r) (Fin r) (PSUF g)) := by
            rw [hTP]; exact hD.gram
    let u : GL (Fin r) (PSUF g) :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero Um (by rw [hdetU]; exact one_ne_zero)
    have hu : u ∈ Unitary.SU (PSUσ g) r := ⟨hdetU, hUu⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [coe_tcYEmbSU]
    exact hyU

theorem exists_PSUYData {T : Matrix (Fin n) (Fin n) (PSUF g)} (hT : IsIdempotentElem T)
    (hTa : formAdj (PSUσ g).toRingHom (Unitary.antidiag n) T = T) :
    ∃ (P : Matrix (Fin n) (Fin (Matrix.rank T)) (PSUF g))
      (R : Matrix (Fin (Matrix.rank T)) (Fin n) (PSUF g)),
      PSUYData g n (Matrix.rank T) T P R := by
  obtain ⟨P₀, R₀, h1, h2⟩ := exists_rankFactorization_of_isIdempotentElem hT
  exact exists_PSUYData_of_factorization hTa h1 h2

theorem PSUYsd_mulEquiv {T : Matrix (Fin n) (Fin n) (PSUF g)} (hT : IsIdempotentElem T)
    (hTa : formAdj (PSUσ g).toRingHom (Unitary.antidiag n) T = T) :
    Nonempty (↥(PSUYsd n g T) ≃* ↥(Unitary.SU (PSUσ g) (Matrix.rank T))) := by
  obtain ⟨P, R, hD⟩ := exists_PSUYData hT hTa
  exact ⟨(MulEquiv.subgroupCongr (PSUYsd_range_tcYEmbSU hD).symm).trans
    (MonoidHom.ofInjective (tcYEmbSU_injective hD)).symm⟩

theorem isQuasisimple_PSUYsd {T : Matrix (Fin n) (Fin n) (PSUF g)} (hT : IsIdempotentElem T)
    (hTa : formAdj (PSUσ g).toRingHom (Unitary.antidiag n) T = T)
    (hr : 3 ≤ Matrix.rank T) (hrq : (Matrix.rank T, 2 ^ (g + 1)) ≠ (3, 2)) :
    CFSG.Assembly.IsQuasisimple ↥(PSUYsd n g T) := by
  obtain ⟨e⟩ := PSUYsd_mulEquiv hT hTa
  exact CFSG.Assembly.IsQuasisimple.of_mulEquiv e
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
      (Unitary.isQuasisimple_SU (F := PSUF g) (p := 2) (f := g + 1) (card_PSUF g) hr hrq))

theorem PSU_mem_classicalTags : (StatedLieTag.PSU) ∈ CFSG.Blueprint.classicalTags := by
  simp [CFSG.Blueprint.classicalTags]

theorem blueprintLieModel_PSU_of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    {r f : ℕ} (h : CFSG.Blueprint.LieModel G .PSU r 2 f) :
    CFSG.Blueprint.LieModel G' .PSU r 2 f :=
  CFSG.Models.LieModel.toBlueprint PSU_mem_classicalTags
    (CFSG.Models.LieModel.of_mulEquiv e
      (CFSG.Models.LieModel.of_blueprint PSU_mem_classicalTags h))

theorem lieModel_PSUYsd {T : Matrix (Fin n) (Fin n) (PSUF g)} (hT : IsIdempotentElem T)
    (hTa : formAdj (PSUσ g).toRingHom (Unitary.antidiag n) T = T)
    (hr : 3 ≤ Matrix.rank T) (hrq : (Matrix.rank T, 2 ^ (g + 1)) ≠ (3, 2)) :
    CFSG.Blueprint.LieModel (↥(PSUYsd n g T) ⧸ Subgroup.center ↥(PSUYsd n g T)) .PSU
      (Matrix.rank T) 2 (g + 1) := by
  obtain ⟨e⟩ := PSUYsd_mulEquiv hT hTa
  have hadm : StatedLieAdmissible .PSU (Matrix.rank T) 2 (g + 1) :=
    ⟨Nat.prime_two, by omega, hr, hrq⟩
  have hSU : CFSG.Blueprint.LieModel
      (↥(Unitary.SU (PSUσ g) (Matrix.rank T)) ⧸
        Subgroup.center ↥(Unitary.SU (PSUσ g) (Matrix.rank T))) .PSU (Matrix.rank T) 2 (g + 1) :=
    Or.inl ⟨PSU_mem_classicalTags, Unitary.statedClassicalModel_center_quotient (F := PSUF g)
      (p := 2) (f := g + 1) hadm (card_PSUF g)⟩
  exact blueprintLieModel_PSU_of_mulEquiv
    (QuotientGroup.congr (Subgroup.center ↥(Unitary.SU (PSUσ g) (Matrix.rank T)))
      (Subgroup.center ↥(PSUYsd n g T)) e.symm (Unitary.map_center_mulEquiv e.symm)) hSU

end YIso

end CFSG.StandardType.TableCRes
