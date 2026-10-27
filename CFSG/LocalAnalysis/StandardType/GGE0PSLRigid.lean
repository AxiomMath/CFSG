module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPSL
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompPSL
public import CFSG.LocalAnalysis.StandardType.GGSixBstarUniqueToralA
public import CFSG.LocalAnalysis.StandardType.GGE0PSLComp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepACore
public import CFSG.LocalAnalysis.StandardType.GGE0RigidCount

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.StandardType.ClassicalPosition

private theorem conjSL_of_isGLLift (m : ℕ) {F : Type} [Field F] {X : Type} [Group X]
    (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* X) {b : X} {A : GL (Fin (m + 1)) F}
    (hA : IsGLLift Matrix.SpecialLinearGroup.toGL ψ A b) :
    ∀ u, b⁻¹ * ψ u * b = ψ (InnerDiagA.conjSL A u) := by
  intro u
  obtain ⟨u', hu'j, hu'b⟩ := hA u
  rw [hu'b]
  congr 1
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [RootPlaneA.toGL_conjSL, hu'j]

private theorem isDiag_mul_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {A B : Matrix ι ι F} (hA : A.IsDiag) (hB : B.IsDiag) : A * B = B * A := by
  rw [← hA.diagonal_diag, ← hB.diagonal_diag, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

private theorem pow_conj_eq_scalar {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {A t : GL ι F} {p : ℕ} {μ : F}
    (htp : ((t ^ p : GL ι F) : Matrix ι ι F) = Matrix.scalar ι μ) :
    (((↑(A * t * A⁻¹ : GL ι F)) : Matrix ι ι F) ^ p = Matrix.scalar ι μ) := by
  have hcenter : t ^ p ∈ Subgroup.center (GL ι F) := by
    refine Subgroup.mem_center_iff.mpr (fun g => ?_)
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, htp]
    exact (Matrix.scalar_commute μ (fun _ => Commute.all _ _) ((g : GL ι F) : Matrix ι ι F)).eq.symm
  have hpow : ∀ k : ℕ, (A * t * A⁻¹ : GL ι F) ^ k = A * t ^ k * A⁻¹ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, pow_succ]; group
  have hfix : A * t ^ p * A⁻¹ = t ^ p := by
    have h1 := Subgroup.mem_center_iff.mp hcenter A⁻¹
    calc A * t ^ p * A⁻¹ = A * (t ^ p * A⁻¹) := by rw [mul_assoc]
      _ = A * (A⁻¹ * t ^ p) := by rw [h1]
      _ = t ^ p := by group
  rw [← Units.val_pow_eq_pow_val, hpow p, hfix]
  exact htp

private theorem exists_diagonal_lift (m : ℕ) (hm : 2 ≤ m) {F : Type} [Field F] [Finite F]
    [CharP F 2] {X : Type} [Group X] (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (hC : Subgroup.centralizer (ψ.range : Set X) = ⊥)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F - 1)
    {B₁ : Subgroup X} (hB₁ : ∀ b ∈ B₁, GGPsiInnerDiag (SpecialLinear.rootDatum m F) ψ b)
    (hab : IsElemAbelian p B₁) (h3 : p ^ 3 ≤ Nat.card B₁) (hN : p ^ (m - 1) ≤ Nat.card B₁)
    {z : X} (hz : z ∈ B₁) {t : GL (Fin (m + 1)) F}
    (ht : IsGLLift Matrix.SpecialLinearGroup.toGL ψ t z) :
    ∃ A₀ : GL (Fin (m + 1)) F,
      ((A₀ * t * A₀⁻¹ : GL (Fin (m + 1)) F) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag ∧
      ∀ b ∈ B₁, ∀ s : GL (Fin (m + 1)) F, IsGLLift Matrix.SpecialLinearGroup.toGL ψ s b →
        ((A₀ * s * A₀⁻¹ : GL (Fin (m + 1)) F) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag := by
  have hinn : ∀ b ∈ B₁, ∃ A : GL (Fin (m + 1)) F, ∀ u,
      b⁻¹ * ψ u * b = ψ (InnerDiagA.conjSL A u) :=
    fun b hb => RootPlaneA.exists_gl_of_psiInnerDiag hm hψ (hB₁ b hb)
  have hc1 : p ^ (m + 1 - 2) ≤ Nat.card B₁ := by
    rw [show m + 1 - 2 = m - 1 from by omega]
    exact hN
  obtain ⟨A₀, hA₀⟩ := RootPlaneA.ggBstarToralA_of_card (F := F) (ψ := ψ) hm hψ hC hab hinn
    hp hp2 hpq hc1 h3
  exact ⟨A₀, hA₀ z hz t (conjSL_of_isGLLift m ψ ht),
    fun b hb s hs => hA₀ b hb s (conjSL_of_isGLLift m ψ hs)⟩

private theorem mulVec_mul_val {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (u w : GL ι F)
    (x : ι → F) :
    (((u * w : GL ι F)) : Matrix ι ι F).mulVec x =
      ((u : GL ι F) : Matrix ι ι F).mulVec (((w : GL ι F) : Matrix ι ι F).mulVec x) := by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec]

private theorem isDiag_mulVec_single {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {D : Matrix ι ι F} (hD : D.IsDiag) (i : ι) :
    D.mulVec (Pi.single i 1) = D i i • Pi.single i 1 := by
  conv_lhs => rw [← hD.diagonal_diag]
  rw [Matrix.diagonal_mulVec_single]
  ext j
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

private def scalarOnCoordEigenspace {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (D : GL ι F) (lam : F) : Subgroup (GL ι F) where
  carrier := {g | Commute g D ∧ ∃ ν : F, ∀ v : ι → F,
    (D : Matrix ι ι F).mulVec v = lam • v → (g : Matrix ι ι F).mulVec v = ν • v}
  mul_mem' := by
    rintro g g' ⟨hg, ν, hν⟩ ⟨hg', ν', hν'⟩
    exact ⟨hg.symm.mul_right hg'.symm |>.symm, ν * ν', fun v hv => by
      rw [mulVec_mul_val, hν' v hv, Matrix.mulVec_smul, hν v hv, smul_smul, mul_comm]⟩
  one_mem' := ⟨Commute.one_left D, 1, fun v _ => by
    rw [Units.val_one, Matrix.one_mulVec, one_smul]⟩
  inv_mem' := by
    classical
    rintro g ⟨hg, ν, hν⟩
    have hginv : ∀ w : ι → F, ((g⁻¹ : GL ι F) : Matrix ι ι F).mulVec
        ((((g : GL ι F) : Matrix ι ι F).mulVec w)) = w := by
      intro w
      rw [← mulVec_mul_val, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    refine ⟨hg.symm.inv_right.symm, if h : ν = 0 then 0 else ν⁻¹, fun v hv => ?_⟩
    have hgv : ((g : GL ι F) : Matrix ι ι F).mulVec
        ((((g⁻¹ : GL ι F)) : Matrix ι ι F).mulVec v) = v := by
      rw [← mulVec_mul_val, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    by_cases h : ν = 0
    · have h0 : ((g : GL ι F) : Matrix ι ι F).mulVec v = 0 := by
        rw [hν v hv, h, zero_smul]
      have hv0 : v = 0 := by rw [← hginv v, h0, Matrix.mulVec_zero]
      rw [dif_pos h, hv0, Matrix.mulVec_zero, smul_zero]
    · rw [dif_neg h]
      have h2 : ((g : GL ι F) : Matrix ι ι F).mulVec (ν⁻¹ • v) = v := by
        rw [Matrix.mulVec_smul, hν v hv, smul_smul, inv_mul_cancel₀ h, one_smul]
      conv_lhs => rw [← h2]
      rw [← mulVec_mul_val, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

private theorem scalarOnCoordEigenspace_le_centralizer {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] (D : GL ι F) (lam : F) :
    scalarOnCoordEigenspace D lam ≤ Subgroup.centralizer ({D} : Set (GL ι F)) := by
  intro g hg h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  exact hg.1.symm.eq

private theorem mulVec_mem_eigenspace {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {D c : GL ι F} {lam : F} (hc : Commute c D) {v : ι → F}
    (hv : (D : Matrix ι ι F).mulVec v = lam • v) :
    (D : Matrix ι ι F).mulVec (((c : GL ι F) : Matrix ι ι F).mulVec v) = lam •
      (((c : GL ι F) : Matrix ι ι F).mulVec v) := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← hc.eq, Units.val_mul, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul]

private theorem mulVec_inv_mulVec {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (c : GL ι F) (v : ι → F) :
    ((c : GL ι F) : Matrix ι ι F).mulVec
      ((((c⁻¹ : GL ι F)) : Matrix ι ι F).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

private theorem conj_mem_scalarOnCoordEigenspace {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] {D g c : GL ι F} {lam : F}
    (hc : c ∈ Subgroup.centralizer ({D} : Set (GL ι F)))
    (hg : g ∈ scalarOnCoordEigenspace D lam) :
    c * g * c⁻¹ ∈ scalarOnCoordEigenspace D lam := by
  rw [Subgroup.mem_centralizer_iff] at hc
  have hcD : Commute c D := (hc D (Set.mem_singleton D)).symm
  have hDc : Commute D c := hcD.symm
  refine ⟨?_, ?_⟩
  · exact ((hDc.mul_right hg.1.symm).mul_right hDc.inv_right).symm
  obtain ⟨ν, hν⟩ := hg.2
  refine ⟨ν, fun v hv => ?_⟩
  have hcv : (D : Matrix ι ι F).mulVec
      ((((c⁻¹ : GL ι F)) : Matrix ι ι F).mulVec v) = lam •
        ((((c⁻¹ : GL ι F)) : Matrix ι ι F).mulVec v) :=
    mulVec_mem_eigenspace hcD.inv_left hv
  have hstep : ((g : GL ι F) : Matrix ι ι F).mulVec
      ((((c⁻¹ : GL ι F)) : Matrix ι ι F).mulVec v) = ν •
        ((((c⁻¹ : GL ι F)) : Matrix ι ι F).mulVec v) := hν _ hcv
  have hkey : ((c * g * c⁻¹ : GL ι F) : Matrix ι ι F) =
      ((c : GL ι F) : Matrix ι ι F) * ((g : GL ι F) : Matrix ι ι F) *
        ((c⁻¹ : GL ι F) : Matrix ι ι F) := by rw [Units.val_mul, Units.val_mul]
  have hv' : ((c * g * c⁻¹ : GL ι F) : Matrix ι ι F).mulVec v =
      ((c : GL ι F) : Matrix ι ι F).mulVec
        ((((g : GL ι F) : Matrix ι ι F).mulVec
          ((((c⁻¹ : GL ι F)) : Matrix ι ι F).mulVec v))) := by
    rw [hkey, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hv', hstep, Matrix.mulVec_smul, mulVec_inv_mulVec]

private theorem le_normalizer_scalarOnCoordEigenspace {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] (D : GL ι F) (lam : F) :
    Subgroup.centralizer ({D} : Set (GL ι F)) ≤
      Subgroup.normalizer ((scalarOnCoordEigenspace D lam : Subgroup (GL ι F)) :
        Set (GL ι F)) := by
  intro c hc
  rw [Subgroup.mem_set_normalizer_iff'']
  intro g
  constructor
  · intro hg
    have h := conj_mem_scalarOnCoordEigenspace (D := D) (g := g) (c := c⁻¹)
      ((Subgroup.centralizer ({D} : Set (GL ι F))).inv_mem hc) hg
    rwa [inv_inv] at h
  · intro hg
    have h := conj_mem_scalarOnCoordEigenspace (D := D) (g := c⁻¹ * g * c) (c := c) hc hg
    have heq : c * (c⁻¹ * g * c) * c⁻¹ = g := by group
    rwa [heq] at h

private theorem exists_not_le_scalarOnCoordEigenspace {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] {D : GL ι F} (hD : (D : Matrix ι ι F).IsDiag) {J : Subgroup (GL ι F)}
    (hJq : CFSG.Open.IsQuasisimple ↥J) :
    ∃ lam : F, ¬ J ≤ scalarOnCoordEigenspace D lam := by
  by_contra hcon
  have hcon' : ∀ lam, J ≤ scalarOnCoordEigenspace D lam := fun lam =>
    not_not.mp (not_exists.mp hcon lam)
  have hdiag : ∀ g ∈ J, (g : Matrix ι ι F).IsDiag := by
    intro g hg
    refine fun i j hij => ?_
    obtain ⟨-, ν, hν⟩ := hcon' (D j j) hg
    have hv : (D : Matrix ι ι F).mulVec (Pi.single j 1) = (D j j) • Pi.single j 1 :=
      isDiag_mulVec_single hD j
    have h := congrArg (fun w : ι → F => w i) (hν _ hv)
    simpa [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply,
      Pi.single_eq_of_ne hij] using h
  refine (CFSG.LieType.SemisimpleCentralizers.Held.not_isQuasisimple_of_comm
    (Γ := ↥J) ?_) hJq
  intro a b
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
  exact isDiag_mul_comm (hdiag a a.2) (hdiag b b.2)

private theorem commutator_eq_bot_of_not_le_scalarOnCoordEigenspace {ι F : Type} [Fintype ι]
    [DecidableEq ι] [Field F] [Finite F] {D : GL ι F} {J : Subgroup (GL ι F)} {lam : F}
    (hJ : IsComponentOf J (Subgroup.centralizer ({D} : Set (GL ι F))))
    (hlam : ¬ J ≤ scalarOnCoordEigenspace D lam) :
    ⁅J, scalarOnCoordEigenspace D lam⁆ = ⊥ := by
  have hsub : IsSubnormal (scalarOnCoordEigenspace D lam)
      (Subgroup.centralizer ({D} : Set (GL ι F))) :=
    IsSubnormal.step (scalarOnCoordEigenspace_le_centralizer D lam)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (scalarOnCoordEigenspace_le_centralizer D lam)).mpr
        (le_normalizer_scalarOnCoordEigenspace D lam))
      (IsSubnormal.refl _)
  rcases isComponentOf_le_or_commutator_eq_bot hJ hsub with h | h
  · exact absurd h hlam
  · exact h

private theorem map_centralizer_conj {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (A t : GL ι F) :
    (Subgroup.centralizer ({t} : Set (GL ι F))).map (MulAut.conj A).toMonoidHom =
      Subgroup.centralizer ({A * t * A⁻¹} : Set (GL ι F)) := by
  ext g
  constructor
  · rintro ⟨y, hy, rfl⟩
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    have h : t * y = y * t := hy t (Set.mem_singleton t)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc A * t * A⁻¹ * (A * y * A⁻¹) = A * (t * y) * A⁻¹ := by group
      _ = A * (y * t) * A⁻¹ := by rw [h]
      _ = (A * y * A⁻¹) * (A * t * A⁻¹) := by group
  · intro hg
    refine ⟨A⁻¹ * g * A, ?_, ?_⟩
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      have h : (A * t * A⁻¹) * g = g * (A * t * A⁻¹) := hg (A * t * A⁻¹) (Set.mem_singleton _)
      calc t * (A⁻¹ * g * A) = A⁻¹ * ((A * t * A⁻¹) * g) * A := by group
        _ = A⁻¹ * (g * (A * t * A⁻¹)) * A := by rw [h]
        _ = (A⁻¹ * g * A) * t := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

private theorem exists_scalar_commutator (m : ℕ) {F : Type} [Field F] [CharP F 2]
    {X : Type} [Group X] (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {p : ℕ} {c z : X} (hcz : Commute c z)
    {s t : GL (Fin (m + 1)) F}
    (hs : IsGLLift Matrix.SpecialLinearGroup.toGL ψ s c)
    (ht : IsGLLift Matrix.SpecialLinearGroup.toGL ψ t z)
    (htp : ∃ μ : F, ((t ^ p : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      Matrix.scalar (Fin (m + 1)) μ) :
    ∃ a : F, (((t * s)⁻¹ * (s * t) : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) = Matrix.scalar (Fin (m + 1)) a ∧ a ^ p = 1 := by
  have hst : IsGLLift Matrix.SpecialLinearGroup.toGL ψ (s * t) (z * c) := ht.mul hs
  have hts : IsGLLift Matrix.SpecialLinearGroup.toGL ψ (t * s) (c * z) := hs.mul ht
  rw [← hcz.eq] at hst
  obtain ⟨a, ha⟩ := isGLLift_unique_PSL m F ψ hψ hst hts
  exact ⟨a, ha, pow_eq_one_of_commutator_eq_scalar ha htp⟩

private theorem isDiag_pow_apply {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {D : Matrix ι ι F} (hD : D.IsDiag) (p : ℕ) (i : ι) {μ : F}
    (h : D ^ p = Matrix.scalar ι μ) : (Matrix.diag D i) ^ p = μ := by
  have hdiag : D = Matrix.diagonal (Matrix.diag D) := hD.diagonal_diag.symm
  have hpow : ∀ k : ℕ, (Matrix.diagonal (Matrix.diag D)) ^ k
      = Matrix.diagonal (fun j => (Matrix.diag D j) ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, ih, Matrix.diagonal_mul_diagonal]
        congr 1
        funext j
        rw [pow_succ]
  rw [hdiag, hpow p] at h
  have h1 := congrArg (fun M : Matrix ι ι F => M i i) h
  simpa using h1

private theorem isDiag_mul_apply {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {A : Matrix ι ι F} (hA : A.IsDiag) (B : Matrix ι ι F) (i : ι) :
    (A * B) i i = A i i * B i i := by
  conv_lhs => rw [← hA.diagonal_diag]
  rw [Matrix.diagonal_mul, Matrix.diag_apply]

private theorem isDiag_unit_apply_ne_zero {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {g : GL ι F} (hg : (g : Matrix ι ι F).IsDiag) (i : ι) : (g : Matrix ι ι F) i i ≠ 0 := by
  intro h0
  have h1 := congrArg (fun M : Matrix ι ι F => M i i) (Units.mul_inv g)
  rw [isDiag_mul_apply hg, h0, zero_mul, Matrix.one_apply_eq] at h1
  exact zero_ne_one h1

private theorem mem_scalarOnCoordEigenspace_of_isDiag {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] {D g : GL ι F} (hD : (D : Matrix ι ι F).IsDiag) (hg : (g : Matrix ι ι F).IsDiag)
    {lam ν : F} (hν : ∀ i, (D : Matrix ι ι F) i i = lam → (g : Matrix ι ι F) i i = ν) :
    g ∈ scalarOnCoordEigenspace D lam := by
  refine ⟨Units.ext (isDiag_mul_comm hg hD), ν, fun v hv => ?_⟩
  funext j
  have hDv := congrFun hv j
  rw [← hD.diagonal_diag, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul,
    Matrix.diag_apply] at hDv
  rw [← hg.diagonal_diag, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, Matrix.diag_apply]
  by_cases hj : (D : Matrix ι ι F) j j = lam
  · rw [hν j hj]
  · have h2 : ((D : Matrix ι ι F) j j - lam) * v j = 0 := by rw [sub_mul, hDv, sub_self]
    rw [(mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hj), mul_zero, mul_zero]

private theorem exists_commute_scalarOnCoordEigenspace {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [Finite F] {D : GL ι F} (hD : (D : Matrix ι ι F).IsDiag) {J : Subgroup (GL ι F)}
    (hJ : IsComponentOf J (Subgroup.centralizer ({D} : Set (GL ι F)))) :
    ∃ i₀ : ι, ∀ g ∈ scalarOnCoordEigenspace D ((D : Matrix ι ι F) i₀ i₀), ∀ y ∈ J,
      Commute g y := by
  obtain ⟨lam, hlam⟩ := exists_not_le_scalarOnCoordEigenspace hD hJ.2.2
  have hbot := commutator_eq_bot_of_not_le_scalarOnCoordEigenspace hJ hlam
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, (D : Matrix ι ι F) i₀ i₀ = lam := by
    by_contra hne
    rw [not_exists] at hne
    refine hlam fun g hg => ⟨Subgroup.mem_centralizer_singleton_iff.mp (hJ.1 hg), 1,
      fun v hv => ?_⟩
    have hv0 : v = 0 := by
      funext j
      have hDv := congrFun hv j
      rw [← hD.diagonal_diag, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul,
        Matrix.diag_apply] at hDv
      have h2 : ((D : Matrix ι ι F) j j - lam) * v j = 0 := by rw [sub_mul, hDv, sub_self]
      exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (hne j))
    rw [hv0, Matrix.mulVec_zero, smul_zero]
  refine ⟨i₀, fun g hg y hy => ?_⟩
  rw [hi₀] at hg
  have h := Subgroup.commutator_mem_commutator hy hg
  rw [hbot, Subgroup.mem_bot] at h
  exact (commutatorElement_eq_one_iff_commute.mp h).symm

private theorem mem_centralizer_map_of_isGLLift (m : ℕ) {F : Type} [Field F] {X : Type}
    [Group X] (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* X)
    {J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) F)} {b : X}
    {u : GL (Fin (m + 1)) F} (hu : IsGLLift Matrix.SpecialLinearGroup.toGL ψ u b)
    (hcomm : ∀ x ∈ J', Commute u (Matrix.SpecialLinearGroup.toGL x)) :
    b ∈ Subgroup.centralizer ((J'.map ψ : Subgroup X) : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨x', hx'j, hx'b⟩ := hu x
  have hx' : x' = x := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [hx'j, (hcomm x hx).eq, mul_inv_cancel_right]
  rw [hx'] at hx'b
  calc ψ x * b = b * (b⁻¹ * ψ x * b) := by group
    _ = b * ψ x := by rw [hx'b]

private theorem exists_entry_mem_centralizer_of_lift (m : ℕ) {F : Type} [Field F] [Finite F]
    {X : Type} [Group X] [Finite X] (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {z : X} {t : GL (Fin (m + 1)) F}
    (ht : IsGLLift Matrix.SpecialLinearGroup.toGL ψ t z) {L' : Subgroup X}
    (hL' : IsComponentOf L' (ψ.range ⊓ Subgroup.centralizer {z})) {A₀ : GL (Fin (m + 1)) F}
    (hD : ((A₀ * t * A₀⁻¹ : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag) :
    ∃ i₀ : Fin (m + 1), ∀ (b : X) (u : GL (Fin (m + 1)) F),
      IsGLLift Matrix.SpecialLinearGroup.toGL ψ u b →
      A₀ * u * A₀⁻¹ ∈ scalarOnCoordEigenspace (A₀ * t * A₀⁻¹)
        (((A₀ * t * A₀⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i₀ i₀) →
      b ∈ Subgroup.centralizer (L' : Set X) := by
  obtain ⟨J', -, hJ, hJ'map⟩ := ggE0Comp_PSL m ψ hψ ht hL'
  have hJ₁ : IsComponentOf ((J'.map Matrix.SpecialLinearGroup.toGL).map
      (MulAut.conj A₀).toMonoidHom)
      (Subgroup.centralizer ({A₀ * t * A₀⁻¹} : Set (GL (Fin (m + 1)) F))) := by
    rw [← map_centralizer_conj]
    exact CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hJ _
      (MulEquiv.injective _)
  obtain ⟨i₀, hi₀⟩ := exists_commute_scalarOnCoordEigenspace hD hJ₁
  refine ⟨i₀, fun b u hu hW => ?_⟩
  rw [← hJ'map]
  refine mem_centralizer_map_of_isGLLift m ψ hu (fun x hx => ?_)
  have h := hi₀ _ hW _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  exact (Commute.conj_iff A₀).mp h

private theorem diag_pow_eq_of_isGLLift (m : ℕ) {F : Type} [Field F] [CharP F 2] {X : Type}
    [Group X] (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {p : ℕ} {b : X} (hbp : b ^ p = 1)
    {A₀ s : GL (Fin (m + 1)) F} (hs : IsGLLift Matrix.SpecialLinearGroup.toGL ψ s b)
    (hdiag : ((A₀ * s * A₀⁻¹ : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag) (i j : Fin (m + 1)) :
    ((A₀ * s * A₀⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i ^ p =
      ((A₀ * s * A₀⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) j j ^ p := by
  have h1 := hs.pow p
  rw [hbp] at h1
  obtain ⟨μ, hμ⟩ := isGLLift_unique_PSL m F ψ hψ h1 isGLLift_one
  have hμ' : ((s ^ p : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      Matrix.scalar (Fin (m + 1)) μ := by simpa using hμ
  have h2 := pow_conj_eq_scalar (A := A₀) hμ'
  exact (isDiag_pow_apply hdiag p i h2).trans (isDiag_pow_apply hdiag p j h2).symm

private theorem inv_mul_mem_centralizer_of_ratio (m : ℕ) {F : Type} [Field F] [Finite F]
    {X : Type} [Group X] (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* X)
    {B₁ L' : Subgroup X} {A₀ D : GL (Fin (m + 1)) F}
    (hD : (D : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag) {lam : F}
    (hdiag : ∀ b ∈ B₁, ∀ s : GL (Fin (m + 1)) F,
      IsGLLift Matrix.SpecialLinearGroup.toGL ψ s b →
      ((A₀ * s * A₀⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag)
    (hK : ∀ (b : X) (u : GL (Fin (m + 1)) F), IsGLLift Matrix.SpecialLinearGroup.toGL ψ u b →
      A₀ * u * A₀⁻¹ ∈ scalarOnCoordEigenspace D lam → b ∈ Subgroup.centralizer (L' : Set X))
    {b b' : X} (hb : b ∈ B₁) (hb' : b' ∈ B₁) {s s' : GL (Fin (m + 1)) F}
    (hs : IsGLLift Matrix.SpecialLinearGroup.toGL ψ s b)
    (hs' : IsGLLift Matrix.SpecialLinearGroup.toGL ψ s' b') {ν : F}
    (hν : ∀ i, (D : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i = lam →
      ((A₀ * s' * A₀⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i =
        ν * ((A₀ * s * A₀⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i) :
    b⁻¹ * b' ∈ Subgroup.centralizer (L' : Set X) := by
  have hu : IsGLLift Matrix.SpecialLinearGroup.toGL ψ (s' * s⁻¹) (b⁻¹ * b') :=
    (hs.inv_of_injective Matrix.SpecialLinearGroup.toGL_injective).mul hs'
  have hgd := hdiag _ (B₁.mul_mem (B₁.inv_mem hb) hb') _ hu
  refine hK _ _ hu (mem_scalarOnCoordEigenspace_of_isDiag hD hgd (ν := ν) (fun i hi => ?_))
  have hprod : A₀ * (s' * s⁻¹) * A₀⁻¹ * (A₀ * s * A₀⁻¹) = A₀ * s' * A₀⁻¹ := by group
  have h1 := congrArg (fun x : GL (Fin (m + 1)) F =>
    (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i) hprod
  rw [Units.val_mul (A₀ * (s' * s⁻¹) * A₀⁻¹), isDiag_mul_apply hgd, hν i hi] at h1
  exact mul_right_cancel₀ (isDiag_unit_apply_ne_zero (hdiag b hb s hs) i) h1

private theorem exists_ratio_function {B ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {e : B → ι → F} {i₀ : ι} {p : ℕ} {I : Finset ι} (hi₀ : i₀ ∈ I)
    (he0 : ∀ b i, e b i ≠ 0) (hep : ∀ b i, e b i ^ p = e b i₀ ^ p) :
    ∃ f : B → ι → F,
      (∀ b, f b i₀ = 1) ∧ (∀ b i, i ∉ I → f b i = 1) ∧
      (∀ b i, i ∈ I → f b i ^ p = 1) ∧
      (∀ b b', f b = f b' → ∀ i, i ∈ I → e b' i = e b' i₀ / e b i₀ * e b i) := by
  classical
  refine ⟨fun b i => if i ∈ I then e b i / e b i₀ else 1, ?_, ?_, ?_, ?_⟩
  · intro b
    change (if i₀ ∈ I then e b i₀ / e b i₀ else 1) = 1
    rw [if_pos hi₀]
    exact div_self (he0 b i₀)
  · intro b i hi
    simp [hi]
  · intro b i hi
    simp only [if_pos hi]
    rw [div_pow, hep b i, div_self (pow_ne_zero _ (he0 b i₀))]
  · intro b b' hbb' i hi
    have h := congrFun hbb' i
    simp only [if_pos hi] at h
    rw [div_eq_div_iff (he0 b i₀) (he0 b' i₀)] at h
    rw [div_mul_eq_mul_div, eq_div_iff (he0 b i₀), ← h, mul_comm]

private theorem card_le_card_centralizer_mul_pow (m : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] [DecidableEq F] {X : Type} [Group X] [Finite X]
    (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* X) (hψ : ψ.ker ≤ Subgroup.center _)
    {p : ℕ} (hp : p.Prime) {B₁ : Subgroup X}
    (hB₁N : B₁ ≤ Subgroup.normalizer (ψ.range : Set X))
    (hB₁ : ∀ b ∈ B₁, GGPsiInnerDiag (SpecialLinear.rootDatum m F) ψ b)
    (hab : IsElemAbelian p B₁) {L' : Subgroup X} {A₀ D : GL (Fin (m + 1)) F}
    (hD : (D : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag) (i₀ : Fin (m + 1))
    (hdiag : ∀ b ∈ B₁, ∀ s : GL (Fin (m + 1)) F,
      IsGLLift Matrix.SpecialLinearGroup.toGL ψ s b →
      ((A₀ * s * A₀⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag)
    (hK : ∀ (b : X) (u : GL (Fin (m + 1)) F), IsGLLift Matrix.SpecialLinearGroup.toGL ψ u b →
      A₀ * u * A₀⁻¹ ∈ scalarOnCoordEigenspace D
        ((D : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i₀ i₀) →
      b ∈ Subgroup.centralizer (L' : Set X)) :
    Nat.card B₁ ≤ Nat.card ↥(B₁ ⊓ Subgroup.centralizer (L' : Set X)) *
      p ^ ((Finset.univ.filter fun i => (D : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i =
        (D : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i₀ i₀).card - 1) := by
  have hlift : ∀ b : ↥B₁, ∃ s : GL (Fin (m + 1)) F,
      IsGLLift Matrix.SpecialLinearGroup.toGL ψ s (b : X) :=
    fun b => exists_isGLLift_PSL m F ψ hψ (hB₁N b.2) (hB₁ b b.2)
  choose L hL using hlift
  let e : ↥B₁ → Fin (m + 1) → F := fun b i =>
    ((A₀ * L b * A₀⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i
  have hdb : ∀ b : ↥B₁, ((A₀ * L b * A₀⁻¹ : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag := fun b => hdiag b b.2 (L b) (hL b)
  have he0 : ∀ b i, e b i ≠ 0 := fun b i => isDiag_unit_apply_ne_zero (hdb b) i
  have hep : ∀ b i, e b i ^ p = e b i₀ ^ p := fun b i =>
    diag_pow_eq_of_isGLLift m ψ hψ (hab.2 b b.2) (hL b) (hdb b) i i₀
  obtain ⟨f, hf₀, hfI, hfp, hrat⟩ := exists_ratio_function
    (I := Finset.univ.filter fun i => (D : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i =
      (D : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i₀ i₀)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩) he0 hep
  refine card_le_card_inf_mul_pow_of_fibres B₁ _ hp.pos (i₀ := i₀)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩) f hf₀ hfI hfp (fun b b' hbb' => ?_)
  refine inv_mul_mem_centralizer_of_ratio m ψ hD hdiag hK b.2 b'.2 (hL b) (hL b')
    (ν := e b' i₀ / e b i₀) (fun i hi => hrat b b' hbb' i ?_)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩

private theorem mul_conj_eq_smul_of_commutator_eq_scalar {ι F : Type} [Fintype ι]
    [DecidableEq ι] [Field F] {s t A : GL ι F} {a : F}
    (ha : (((t * s)⁻¹ * (s * t) : GL ι F) : Matrix ι ι F) = Matrix.scalar ι a) :
    ((A * s * A⁻¹ : GL ι F) : Matrix ι ι F) * ((A * t * A⁻¹ : GL ι F) : Matrix ι ι F) =
      a • (((A * t * A⁻¹ : GL ι F) : Matrix ι ι F) * ((A * s * A⁻¹ : GL ι F) : Matrix ι ι F)) := by
  have hζA : Commute ((t * s)⁻¹ * (s * t)) A := commute_of_val_eq_scalar ⟨a, ha⟩ A
  have hgrp : (A * s * A⁻¹) * (A * t * A⁻¹) =
      (A * t * A⁻¹) * (A * s * A⁻¹) * ((t * s)⁻¹ * (s * t)) := by
    calc (A * s * A⁻¹) * (A * t * A⁻¹)
        = A * (t * s) * (((t * s)⁻¹ * (s * t)) * A⁻¹) := by group
      _ = A * (t * s) * (A⁻¹ * ((t * s)⁻¹ * (s * t))) := by rw [hζA.inv_right.eq]
      _ = (A * t * A⁻¹) * (A * s * A⁻¹) * ((t * s)⁻¹ * (s * t)) := by group
  rw [← Units.val_mul, ← Units.val_mul, hgrp, Units.val_mul _ ((t * s)⁻¹ * (s * t)), ha,
    Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal]

private theorem exists_pow_eq_scalar_of_isGLLift (m : ℕ) {F : Type} [Field F] [CharP F 2]
    {X : Type} [Group X] (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {p : ℕ} {B₁ : Subgroup X} (hab : IsElemAbelian p B₁)
    {z : X} (hz : z ∈ B₁) {t : GL (Fin (m + 1)) F}
    (ht : IsGLLift Matrix.SpecialLinearGroup.toGL ψ t z) :
    ∃ μ : F, ((t ^ p : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      Matrix.scalar (Fin (m + 1)) μ := by
  have h1 := ht.pow p
  rw [hab.2 z hz] at h1
  obtain ⟨μ, hμ⟩ := isGLLift_unique_PSL m F ψ hψ h1 isGLLift_one
  exact ⟨μ, by simpa using hμ⟩

private theorem exists_card_fiber_eq_mul_of_diagonal_commutator {ι F : Type} [Fintype ι]
    [DecidableEq ι] [Field F] [DecidableEq F] {p : ℕ} (hp : p.Prime) {a : F}
    (hprim : IsPrimitiveRoot a p) {s t A₀ : GL ι F} {i₀ : ι}
    (hD : ((A₀ * t * A₀⁻¹ : GL ι F) : Matrix ι ι F).IsDiag)
    (htp : ∃ μ : F, ((t ^ p : GL ι F) : Matrix ι ι F) = Matrix.scalar ι μ)
    (ha : (((t * s)⁻¹ * (s * t) : GL ι F) : Matrix ι ι F) = Matrix.scalar ι a) :
    ∃ k : ℕ, 1 ≤ k ∧ (Finset.univ.filter fun i => ((A₀ * t * A₀⁻¹ : GL ι F) :
      Matrix ι ι F) i i = ((A₀ * t * A₀⁻¹ : GL ι F) : Matrix ι ι F) i₀ i₀).card = k ∧
      Fintype.card ι = p * k := by
  obtain ⟨μ, hμ⟩ := htp
  have hdμ : ∀ i, ((A₀ * t * A₀⁻¹ : GL ι F) : Matrix ι ι F) i i ^ p = μ :=
    fun i => isDiag_pow_apply hD p i (pow_conj_eq_scalar hμ)
  have hcomm := mul_conj_eq_smul_of_commutator_eq_scalar (A := A₀) ha
  rw [← hD.diagonal_diag] at hcomm
  have hdim := card_eq_mul_card_fiber_of_mul_diagonal_eq_smul hp hprim
    (Matrix.diag ((A₀ * t * A₀⁻¹ : GL ι F) : Matrix ι ι F)) i₀
    (isDiag_unit_apply_ne_zero hD i₀) (fun i => (hdμ i).trans (hdμ i₀).symm)
    (Units.isUnit (A₀ * s * A₀⁻¹)) hcomm
  refine ⟨(Finset.univ.filter fun i => ((A₀ * t * A₀⁻¹ : GL ι F) : Matrix ι ι F) i i =
    ((A₀ * t * A₀⁻¹ : GL ι F) : Matrix ι ι F) i₀ i₀).card, ?_, rfl, hdim⟩
  exact Finset.card_pos.mpr ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

private theorem false_of_pow_bounds {p m k B : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hB : B ≤ p ^ (k + 1)) (hN : p ^ (m - 1) ≤ B) (h3 : p ^ 3 ≤ B)
    (hk : m + 1 = p * k) : False := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h1 : m - 1 ≤ k + 1 := (pow_le_pow_iff_right₀ hp.one_lt).mp (hN.trans hB)
  have h2 : 3 ≤ k + 1 := (pow_le_pow_iff_right₀ hp.one_lt).mp (h3.trans hB)
  have h4 : 3 * k ≤ p * k := Nat.mul_le_mul_right k hp3
  omega

theorem isGLLift_commute_of_rigid_PSL (m : ℕ) (hm : 2 ≤ m) {F : Type} [Field F] [Finite F]
    [CharP F 2] {X : Type} [Group X] [Finite X]
    (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (hC : Subgroup.centralizer (ψ.range : Set X) = ⊥)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F - 1)
    {B₁ : Subgroup X} (hB₁N : B₁ ≤ Subgroup.normalizer (ψ.range : Set X))
    (hB₁ : ∀ b ∈ B₁, GGPsiInnerDiag (SpecialLinear.rootDatum m F) ψ b)
    (hab : IsElemAbelian p B₁) (h3 : p ^ 3 ≤ Nat.card B₁) (hN : p ^ (m - 1) ≤ Nat.card B₁)
    {z : X} (hz : z ∈ B₁) {L' : Subgroup X}
    (hL' : IsComponentOf L' (ψ.range ⊓ Subgroup.centralizer {z}))
    (hcent : Nat.card ↥(B₁ ⊓ Subgroup.centralizer (L' : Set X)) ≤ p ^ 2)
    {c : X} (hcz : Commute c z) {s t : GL (Fin (m + 1)) F}
    (hs : IsGLLift Matrix.SpecialLinearGroup.toGL ψ s c)
    (ht : IsGLLift Matrix.SpecialLinearGroup.toGL ψ t z) : Commute s t := by
  classical
  obtain ⟨μ, htp⟩ := exists_pow_eq_scalar_of_isGLLift m ψ hψ hab hz ht
  obtain ⟨a, ha, hap⟩ := exists_scalar_commutator m ψ hψ hcz hs ht ⟨μ, htp⟩
  by_contra hst
  have ha1 : a ≠ 1 := by
    rintro rfl
    refine hst (inv_mul_eq_one.mp (Units.ext ?_)).symm
    rw [ha, map_one, Units.val_one]
  have : Fact p.Prime := ⟨hp⟩
  have hprim : IsPrimitiveRoot a p := by
    rw [← orderOf_eq_prime hap ha1]
    exact IsPrimitiveRoot.orderOf a
  obtain ⟨A₀, hD, hdiag⟩ := exists_diagonal_lift m hm ψ hψ hC hp hp2 hpq hB₁ hab h3 hN hz ht
  obtain ⟨i₀, hK⟩ := exists_entry_mem_centralizer_of_lift m ψ hψ ht hL' hD
  have hcount := card_le_card_centralizer_mul_pow m ψ hψ hp hB₁N hB₁ hab hD i₀ hdiag hK
  obtain ⟨k, hk1, hk, hdim⟩ := exists_card_fiber_eq_mul_of_diagonal_commutator
    (i₀ := i₀) hp hprim hD ⟨μ, htp⟩ ha
  rw [Fintype.card_fin] at hdim
  have hB : Nat.card B₁ ≤ p ^ (k + 1) := by
    rw [hk] at hcount
    calc Nat.card B₁ ≤ Nat.card ↥(B₁ ⊓ Subgroup.centralizer (L' : Set X)) * p ^ (k - 1) :=
          hcount
      _ ≤ p ^ 2 * p ^ (k - 1) := Nat.mul_le_mul_right _ hcent
      _ = p ^ (k + 1) := by rw [← pow_add]; congr 1; omega
  exact false_of_pow_bounds hp hp2 hB hN h3 hdim

end CFSG.StandardType
