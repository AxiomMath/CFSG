module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModel
public import CFSG.LocalAnalysis.StandardType.GGL45FixA2Comp

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix
open scoped commutatorElement

@[expose] def IsHeisRegU5Five {F : Type} [Field F] (M : GL (Fin 5) F) : Prop :=
  M ^ 5 ∈ LargeEvenScalars (Fin 5) F ∧ ∃ (N : GL (Fin 5) F) (ζ : F), ζ ≠ 1 ∧ ζ ^ 5 = 1 ∧
    (M : Matrix (Fin 5) (Fin 5) F) * N = ζ • ((N : Matrix (Fin 5) (Fin 5) F) * M)

theorem commute_of_regular_U5Five {F : Type} [Field F] {ζ : F} (hζ : IsPrimitiveRoot ζ 5)
    {M N : GL (Fin 5) F} (hM : M ^ 5 = 1)
    (hMN : (M : Matrix (Fin 5) (Fin 5) F) * N = ζ • ((N : Matrix (Fin 5) (Fin 5) F) * M))
    {X Y : GL (Fin 5) F} (hX : X * M = M * X) (hY : Y * M = M * Y) : X * Y = Y * X := by
  classical
  have : NeZero 5 := ⟨by norm_num⟩
  obtain ⟨A₀, hA₀⟩ := TypeA.PGLTor.exists_conj_diagonal hζ ({M} : Set (GL (Fin 5) F))
    (fun x hx y hy => by rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy])
    (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact hM)
  set δ : Fin 5 → F := fun i => TypeA.PGLTor.conjMatrix A₀ M i i with hδdef
  have hD : TypeA.PGLTor.conjMatrix A₀ M = diagonal δ :=
    TypeA.PGLTor.eq_diagonal_of_offDiag_eq_zero (hA₀ M rfl)
  have hδ5 : ∀ i, δ i ^ 5 = 1 := by
    intro i
    have h1 := TypeA.PGLTor.conjMatrix_pow A₀ M 5
    rw [hM, TypeA.PGLTor.conjMatrix_one, hD, diagonal_pow] at h1
    have h2 := congrFun (congrFun h1 i) i
    simpa [one_apply_eq] using h2.symm
  have hδ0 : ∀ i, δ i ≠ 0 := fun i h0 => by
    have := hδ5 i
    rw [h0, zero_pow (by norm_num)] at this
    exact zero_ne_one this
  set N' := TypeA.PGLTor.conjMatrix A₀ N with hN'
  have hDN : diagonal δ * N' = ζ • (N' * diagonal δ) := by
    rw [← hD, hN', ← TypeA.PGLTor.conjMatrix_mul, ← TypeA.PGLTor.conjMatrix_mul]
    simp only [TypeA.PGLTor.conjMatrix, Units.val_mul]
    rw [hMN, Matrix.mul_smul, Matrix.smul_mul]
  have hN'det : N'.det ≠ 0 := by
    have hu : IsUnit (N' : Matrix (Fin 5) (Fin 5) F) := by
      have : N' = ((A₀ * N * A₀⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) := by
        simp [hN', TypeA.PGLTor.conjMatrix]
      rw [this]
      exact Units.isUnit _
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  have hcol : ∀ j, ∃ i, N' i j ≠ 0 := by
    intro j
    by_contra hcon
    push Not at hcon
    exact hN'det (Matrix.det_eq_zero_of_column_eq_zero j hcon)
  choose s hs using hcol
  have hshift : ∀ j, δ (s j) = ζ * δ j := by
    intro j
    have h1 := congrFun (congrFun hDN (s j)) j
    rw [diagonal_mul, Matrix.smul_apply, mul_diagonal, smul_eq_mul] at h1
    apply mul_right_cancel₀ (hs j)
    rw [h1]
    ring
  have hiter : ∀ (k : ℕ) (j : Fin 5), δ (s^[k] j) = ζ ^ k * δ j := by
    intro k
    induction k with
    | zero => intro j; simp
    | succ k ih =>
      intro j
      rw [Function.iterate_succ_apply, ih, hshift, pow_succ]
      ring
  set g : Fin 5 → Fin 5 := fun k => s^[k.val] 0 with hg
  have hpow_inj : ∀ a b : Fin 5, ζ ^ a.val * δ 0 = ζ ^ b.val * δ 0 → a = b := by
    intro a b hab
    have h1 : ζ ^ a.val = ζ ^ b.val := mul_right_cancel₀ (hδ0 0) hab
    exact Fin.ext (hζ.pow_inj a.isLt b.isLt h1)
  have hginj : Function.Injective g := by
    intro a b hab
    apply hpow_inj
    rw [← hiter, ← hiter]
    exact congrArg δ hab
  have hgsurj : Function.Surjective g := Finite.injective_iff_surjective.mp hginj
  have hδinj : Function.Injective δ := by
    intro i j hij
    obtain ⟨a, rfl⟩ := hgsurj i
    obtain ⟨b, rfl⟩ := hgsurj j
    have h1 : ζ ^ a.val * δ 0 = ζ ^ b.val * δ 0 := by
      rw [← hiter, ← hiter]
      exact hij
    rw [hpow_inj a b h1]
  have hdiag : ∀ Z : GL (Fin 5) F, Z * M = M * Z →
      TypeA.PGLTor.conjMatrix A₀ Z =
        diagonal (fun i => TypeA.PGLTor.conjMatrix A₀ Z i i) := by
    intro Z hZ
    have hc : TypeA.PGLTor.conjMatrix A₀ Z * diagonal δ =
        diagonal δ * TypeA.PGLTor.conjMatrix A₀ Z := by
      rw [← hD, ← TypeA.PGLTor.conjMatrix_mul, ← TypeA.PGLTor.conjMatrix_mul, hZ]
    exact TypeA.PGLTor.eq_diagonal_of_offDiag_eq_zero fun i j hij =>
      TypeA.PGLTor.isBlockDiag_of_commute_diagonal hc i j (hδinj.ne hij)
  have hXY : TypeA.PGLTor.conjMatrix A₀ (X * Y) = TypeA.PGLTor.conjMatrix A₀ (Y * X) := by
    rw [TypeA.PGLTor.conjMatrix_mul, TypeA.PGLTor.conjMatrix_mul, hdiag X hX, hdiag Y hY,
      diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  have hinj : ∀ Z W : GL (Fin 5) F, TypeA.PGLTor.conjMatrix A₀ Z = TypeA.PGLTor.conjMatrix A₀ W →
      Z = W := by
    intro Z W hZW
    have hPQ : ((A₀⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) * (A₀ : Matrix _ _ F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    apply Units.ext
    have h1 := congrArg (fun T : Matrix (Fin 5) (Fin 5) F =>
      ((A₀⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) * T * (A₀ : Matrix _ _ F)) hZW
    simp only [TypeA.PGLTor.conjMatrix, ← Matrix.mul_assoc, hPQ, Matrix.one_mul] at h1
    simpa only [Matrix.mul_assoc, hPQ, Matrix.mul_one] using h1
  exact hinj _ _ hXY

theorem commute_of_regular_scalar_U5Five {F : Type} [Field F] {ζ : F} (hζ : IsPrimitiveRoot ζ 5)
    {A N : GL (Fin 5) F} {t : Fˣ} (hA : A ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) (t ^ 5))
    (hAN : (A : Matrix (Fin 5) (Fin 5) F) * N = ζ • ((N : Matrix (Fin 5) (Fin 5) F) * A))
    {X Y : GL (Fin 5) F} (hX : X * A = A * X) (hY : Y * A = A * Y) : X * Y = Y * X := by
  set c : GL (Fin 5) F := Matrix.GeneralLinearGroup.scalar (Fin 5) t⁻¹ with hc
  have hcomm : ∀ Z : GL (Fin 5) F, c * Z = Z * c := fun Z => TypeA.PGLTor.scalar_mul_comm t⁻¹ Z
  have hM5 : (c * A) ^ 5 = 1 := by
    have hc' : Commute c A := hcomm A
    rw [hc'.mul_pow, hA, hc, ← map_pow, ← map_mul, inv_pow, inv_mul_cancel, map_one]
  have hcmat : ((c * A : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) =
      ((t⁻¹ : Fˣ) : F) • (A : Matrix (Fin 5) (Fin 5) F) := by
    rw [Units.val_mul, hc, Matrix.GeneralLinearGroup.coe_scalar, TableBUD.scalar_mul_eq_smul]
  have hMN : ((c * A : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) * N =
      ζ • ((N : Matrix (Fin 5) (Fin 5) F) * (c * A : GL (Fin 5) F)) := by
    rw [hcmat, Matrix.smul_mul, hAN, Matrix.mul_smul, smul_comm]
  have hX' : X * (c * A) = (c * A) * X := by
    rw [← mul_assoc, ← hcomm X, mul_assoc, hX, ← mul_assoc]
  have hY' : Y * (c * A) = (c * A) * Y := by
    rw [← mul_assoc, ← hcomm Y, mul_assoc, hY, ← mul_assoc]
  exact commute_of_regular_U5Five hζ hM5 hMN hX' hY'

theorem isSolvable_ggFix_of_regular_U5Five {n : ℕ} {K : Type} [Field K] {A : GL (Fin 5) K}
    (hAnorm : A ∈ Subgroup.normalizer (LargeEvenSUGroup (Fin 5) K (2 ^ n) : Set (GL (Fin 5) K)))
    {t : Kˣ} (hA5 : A ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) (t ^ 5))
    {N : GL (Fin 5) K} {ζ : K} (hζ1 : ζ ≠ 1) (hζ5 : ζ ^ 5 = 1)
    (hAN : (A : Matrix (Fin 5) (Fin 5) K) * N = ζ • ((N : Matrix (Fin 5) (Fin 5) K) * A))
    {φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 5) K (2 ^ n)))}
    (hφ : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin 5) K (2 ^ n)))
      (fun h h' => (h' : GL (Fin 5) K) = A * h * A⁻¹) φ) :
    Group.IsSolvable (ggFix φ) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hζ : IsPrimitiveRoot ζ 5 := by
    have h := IsPrimitiveRoot.orderOf ζ
    rwa [orderOf_eq_prime hζ5 hζ1] at h
  set T : Subgroup (LargeEvenSUGroup (Fin 5) K (2 ^ n)) :=
    (ggFix φ).comap (LargeEvenProjMk (LargeEvenSUGroup (Fin 5) K (2 ^ n))) with hT
  have hcent : ∀ u : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 5) u ∈
      Subgroup.center (GL (Fin 5) K) := fun u =>
    Subgroup.mem_center_iff.mpr fun g => (TypeA.PGLTor.scalar_mul_comm u g).symm
  have hTz : ∀ h ∈ T, ∃ u : Kˣ,
      A * (h : GL (Fin 5) K) * A⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 5) u * h := by
    intro h hh
    have hmem : A * (h : GL (Fin 5) K) * A⁻¹ ∈ LargeEvenSUGroup (Fin 5) K (2 ^ n) :=
      (Subgroup.mem_normalizer_iff.mp hAnorm (h : GL (Fin 5) K)).mp h.2
    have e1 := hφ h ⟨_, hmem⟩ rfl
    have e2 : φ (LargeEvenProjMk (LargeEvenSUGroup (Fin 5) K (2 ^ n)) h) =
        LargeEvenProjMk (LargeEvenSUGroup (Fin 5) K (2 ^ n)) h := hh
    have e3 : (QuotientGroup.mk (⟨_, hmem⟩ : LargeEvenSUGroup (Fin 5) K (2 ^ n)) :
        LargeEvenProj (LargeEvenSUGroup (Fin 5) K (2 ^ n))) = QuotientGroup.mk h :=
      e1.symm.trans e2
    rw [QuotientGroup.eq] at e3
    have e4 := Subgroup.mem_subgroupOf.mp e3
    rw [Subgroup.coe_mul, Subgroup.coe_inv, largeEvenScalars_def] at e4
    obtain ⟨u, hu⟩ := e4
    refine ⟨u⁻¹, ?_⟩
    change Matrix.GeneralLinearGroup.scalar (Fin 5) u =
      (A * (h : GL (Fin 5) K) * A⁻¹)⁻¹ * h at hu
    have hc := TypeA.PGLTor.scalar_mul_comm u⁻¹ (h : GL (Fin 5) K)
    have hh' : A * (h : GL (Fin 5) K) * A⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 5) u = h := by
      rw [hu]
      group
    calc A * (h : GL (Fin 5) K) * A⁻¹
        = A * (h : GL (Fin 5) K) * A⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 5) u *
            Matrix.GeneralLinearGroup.scalar (Fin 5) u⁻¹ := by
          rw [mul_assoc _ (Matrix.GeneralLinearGroup.scalar (Fin 5) u), ← map_mul, mul_inv_cancel,
            map_one, mul_one]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 5) u⁻¹ * h := by rw [hh', hc]
  have hTcomm : ∀ h₁ ∈ T, ∀ h₂ ∈ T,
      A * ⁅(h₁ : GL (Fin 5) K), (h₂ : GL (Fin 5) K)⁆ =
        ⁅(h₁ : GL (Fin 5) K), (h₂ : GL (Fin 5) K)⁆ * A := by
    intro h₁ hh₁ h₂ hh₂
    obtain ⟨u₁, hu₁⟩ := hTz h₁ hh₁
    obtain ⟨u₂, hu₂⟩ := hTz h₂ hh₂
    have h1 : A * ⁅(h₁ : GL (Fin 5) K), (h₂ : GL (Fin 5) K)⁆ * A⁻¹ =
        ⁅A * (h₁ : GL (Fin 5) K) * A⁻¹, A * (h₂ : GL (Fin 5) K) * A⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [hu₁, hu₂, LineU.comm_mul_central (hcent u₁) (hcent u₂)] at h1
    calc A * ⁅(h₁ : GL (Fin 5) K), (h₂ : GL (Fin 5) K)⁆
        = A * ⁅(h₁ : GL (Fin 5) K), (h₂ : GL (Fin 5) K)⁆ * A⁻¹ * A := by group
      _ = ⁅(h₁ : GL (Fin 5) K), (h₂ : GL (Fin 5) K)⁆ * A := by rw [h1]
  set C : Subgroup T := (Subgroup.centralizer {A}).comap
    ((LargeEvenSUGroup (Fin 5) K (2 ^ n)).subtype.comp T.subtype) with hC
  have hmemC : ∀ x : T, x ∈ C ↔
      A * ((x : LargeEvenSUGroup (Fin 5) K (2 ^ n)) : GL (Fin 5) K) =
        ((x : LargeEvenSUGroup (Fin 5) K (2 ^ n)) : GL (Fin 5) K) * A := by
    intro x
    rw [hC, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    exact eq_comm
  have hcommC : commutator T ≤ C := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [hmemC]
    have e : (((⁅g₁, g₂⁆ : T) : LargeEvenSUGroup (Fin 5) K (2 ^ n)) : GL (Fin 5) K) =
        ⁅((g₁ : LargeEvenSUGroup (Fin 5) K (2 ^ n)) : GL (Fin 5) K),
          ((g₂ : LargeEvenSUGroup (Fin 5) K (2 ^ n)) : GL (Fin 5) K)⁆ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e]
    exact hTcomm g₁ g₁.2 g₂ g₂.2
  have hCab : ⁅C, C⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact commute_of_regular_scalar_U5Five hζ hA5 hAN ((hmemC x).mp hx).symm
      ((hmemC y).mp hy).symm
  have hTsol : Group.IsSolvable T := by
    refine ⟨⟨2, ?_⟩⟩
    rw [derivedSeries_succ, derivedSeries_one]
    exact eq_bot_iff.mpr ((Subgroup.commutator_mono hcommC hcommC).trans hCab.le)
  let f : T →* ggFix φ :=
    ((LargeEvenProjMk (LargeEvenSUGroup (Fin 5) K (2 ^ n))).comp T.subtype).codRestrict
      (ggFix φ) fun x => x.2
  have hf : Function.Surjective f := by
    rintro ⟨r, hr⟩
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective r
    exact ⟨⟨h, hr⟩, rfl⟩
  haveI := hTsol
  exact solvable_of_surjective hf

theorem not_isComponentOf_ggFix_of_regular_U5Five {n : ℕ} {K : Type} [Field K]
    {A : GL (Fin 5) K}
    (hAnorm : A ∈ Subgroup.normalizer (LargeEvenSUGroup (Fin 5) K (2 ^ n) : Set (GL (Fin 5) K)))
    {t : Kˣ} (hA5 : A ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) (t ^ 5))
    {N : GL (Fin 5) K} {ζ : K} (hζ1 : ζ ≠ 1) (hζ5 : ζ ^ 5 = 1)
    (hAN : (A : Matrix (Fin 5) (Fin 5) K) * N = ζ • ((N : Matrix (Fin 5) (Fin 5) K) * A))
    {φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 5) K (2 ^ n)))}
    (hφ : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin 5) K (2 ^ n)))
      (fun h h' => (h' : GL (Fin 5) K) = A * h * A⁻¹) φ)
    (J : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin 5) K (2 ^ n)))) :
    ¬ IsComponentOf J (ggFix φ) := fun hJ =>
  gffa2_false_of_solvable (isSolvable_ggFix_of_regular_U5Five hAnorm hA5 hζ1 hζ5 hAN hφ) hJ

end CFSG.StandardType

end
