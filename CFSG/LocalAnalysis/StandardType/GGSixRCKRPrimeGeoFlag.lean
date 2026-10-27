module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Defs
public import CFSG.Open.StatedAPI
public import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
public import CFSG.LocalAnalysis.StandardType.UnitaryCenterScalar
public import CFSG.ClassicalGroups.Symplectic.DiagonalTorusRank

public section

namespace CFSG.StandardType.RCKRP

open CFSG.LieType.Universal CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition

@[expose] def GLGeoFlag {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (B : Option ((ι → F) → (ι → F) → F)) (R : Subgroup (GL ι F)) : Prop :=
  ∃ W H : Submodule F (ι → F), W ≤ H ∧
    (∀ x ∈ R, x ≠ 1 →
      LinearMap.range (Matrix.toLin' ((x : Matrix ι ι F) - 1)) = W ∧
      LinearMap.ker (Matrix.toLin' ((x : Matrix ι ι F) - 1)) = H) ∧
    ∀ b ∈ B, (∀ x ∈ R, ∀ m : ι → F, b m (((x : Matrix ι ι F) - 1).mulVec m) = 0) ∨
      Module.finrank F W = 1

abbrev spForm (n : ℕ) (F : Type) [Field F] :
    Option (((Fin n ⊕ Fin n) → F) → ((Fin n ⊕ Fin n) → F) → F) :=
  some fun u v => u ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec v)

theorem flagAt_of_glGeoFlag {U X ι F : Type} [Group U] [Group X] [Fintype ι] [DecidableEq ι]
    [Field F] {j : U →* GL ι F} (hj : Function.Injective j)
    {B : Option ((ι → F) → (ι → F) → F)} {φ : U →* X} {K R : Subgroup X} (hφr : φ.range = K)
    (hφk : φ.ker ≤ Subgroup.center U) {R' : Subgroup U} (hR : R'.map φ = R)
    (hinj : ∀ v ∈ R', φ v = 1 → v = 1) (hflag : GLGeoFlag B (R'.map j)) : FlagAt j B K R := by
  obtain ⟨W, H, hWH, hflag, hform⟩ := hflag
  refine ⟨φ, R', W, H, hφr, hφk, hR, hinj, hWH, ?_, ?_⟩
  · intro v hv hv1
    have hmem : j v ∈ R'.map j := Subgroup.mem_map_of_mem j hv
    have hj1 : j v ≠ 1 := by
      intro h
      exact hv1 (hj (by simpa using h))
    exact hflag (j v) hmem hj1
  · intro b hb
    rcases hform b hb with hB | hdim
    · left
      intro x hx m
      have hx' : j x ∈ R'.map j := Subgroup.mem_map_of_mem j hx
      exact hB (j x) hx' m
    · exact Or.inr hdim

private theorem rckRPgf_scalar_of_commute_transvections {F : Type} [Field F]
    (Z : Matrix (Fin 2) (Fin 2) F)
    (h0 : Z * !![1, 1; 0, 1] = !![1, 1; 0, 1] * Z)
    (h1 : Z * !![1, 0; 1, 1] = !![1, 0; 1, 1] * Z) :
    Z = Matrix.scalar (Fin 2) (Z 0 0) := by
  rw [Matrix.eta_fin_two Z] at h0 h1
  have hZ10 : Z 1 0 = 0 := by
    have e := congrFun (congrFun h0 0) 0
    simp [Matrix.mul_fin_two] at e
    linear_combination e
  have hZeq : Z 0 0 = Z 1 1 := by
    have e := congrFun (congrFun h0 0) 1
    simp [Matrix.mul_fin_two] at e
    linear_combination e
  have hZ01 : Z 0 1 = 0 := by
    have e := congrFun (congrFun h1 0) 0
    simp [Matrix.mul_fin_two] at e
    linear_combination e
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar_apply, hZ10, hZ01, hZeq]

private theorem rckRPgf_eq_one_of_center_SU_two {g : ℕ} (hg : 1 ≤ g)
    {z : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * g)) 2 g) 2)}
    (hz : z ∈ Subgroup.center _) (hz2 : z * z = 1) : z = 1 := by
  let F := GaloisField 2 (2 * g)
  let σ := CFSG.LieType.BorelTits.unitaryInvolution F 2 g
  have h1t : (1 : F) + σ 1 = 0 := by
    rw [map_one, CharTwo.add_self_eq_zero]
  let c1 : Multiplicative (Unitary.traceZero σ) :=
    Multiplicative.ofAdd ⟨1, by rw [Unitary.mem_traceZero]; exact h1t⟩
  let L0 : ↥(Unitary.SU σ 2) := Unitary.longRootHom σ (i := (0 : Fin 2)) (by decide) c1
  let L1 : ↥(Unitary.SU σ 2) := Unitary.longRootHom σ (i := (1 : Fin 2)) (by decide) c1
  have hL0 : ((L0 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1] := by
    rw [Unitary.coe_longRootHom]
    have hc : ((Multiplicative.toAdd c1 : Unitary.traceZero σ) : F) = 1 := rfl
    rw [hc]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Unitary.longRootMatrix]
  have hL1 : ((L1 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 1, 1] := by
    rw [Unitary.coe_longRootHom]
    have hc : ((Multiplicative.toAdd c1 : Unitary.traceZero σ) : F) = 1 := rfl
    rw [hc]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Unitary.longRootMatrix]
  have hM0 : ((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * !![1, 1; 0, 1]
      = !![1, 1; 0, 1] * ((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    have hcomm0 : z * L0 = L0 * z := (Subgroup.mem_center_iff.mp hz L0).symm
    have hgl := congrArg (fun w : ↥(Unitary.SU σ 2) =>
      ((w : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) hcomm0
    simpa [hL0] using hgl
  have hM1 : ((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * !![1, 0; 1, 1]
      = !![1, 0; 1, 1] * ((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    have hcomm1 : z * L1 = L1 * z := (Subgroup.mem_center_iff.mp hz L1).symm
    have hgl := congrArg (fun w : ↥(Unitary.SU σ 2) =>
      ((w : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) hcomm1
    simpa [hL1] using hgl
  have hzscalar : ((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.scalar (Fin 2) (((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0) :=
    rckRPgf_scalar_of_commute_transvections _ hM0 hM1
  have hz2mat : ((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      ((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have hgl : (z : GL (Fin 2) F) * (z : GL (Fin 2) F) = 1 := by
      simpa using congrArg Subtype.val hz2
    simpa using congrArg (fun w : GL (Fin 2) F => (w : Matrix (Fin 2) (Fin 2) F)) hgl
  have hp2 : (((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0) *
      (((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0) = 1 := by
    have e := congrFun (congrFun hz2mat 0) 0
    rw [hzscalar] at e
    simpa [Matrix.scalar_apply, Matrix.diagonal_mul_diagonal] using e
  have hp1 : (((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0) = 1 :=
    CFSG.LieType.Chevalley.eq_one_of_mul_self_eq_one_of_two_eq_zero
      (CharP.cast_eq_zero F 2) hp2
  have hzmat1 : ((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [hzscalar, hp1, Matrix.scalar_apply, Matrix.diagonal_one]
  exact Subtype.ext (Units.ext hzmat1)

theorem eq_one_of_mem_center_SU_of_mul_self {n g : ℕ} (hg : 1 ≤ g)
    {z : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * g)) 2 g) n)}
    (hz : z ∈ Subgroup.center _) (hz2 : z * z = 1) : z = 1 := by
  rcases lt_or_ge n 3 with hn | hn
  · interval_cases n
    ·
      apply Subtype.ext
      apply Units.ext
      apply Matrix.ext
      intro i j
      exact i.elim0
    ·
      apply Subtype.ext
      apply Units.ext
      apply Matrix.ext
      intro i j
      fin_cases i
      fin_cases j
      have hdet := (Unitary.mem_SU (σ := CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * g)) 2 g)).mp z.2 |>.1
      rw [Matrix.det_fin_one] at hdet
      simpa using hdet
    ·
      exact rckRPgf_eq_one_of_center_SU_two hg hz hz2
  ·
    let F := GaloisField 2 (2 * g)
    have hF : Nat.card F = (2 ^ g) ^ 2 := by
      rw [show Nat.card F = 2 ^ (2 * g) from GaloisField.card 2 (2 * g) (by omega),
        ← pow_mul, mul_comm]
    obtain ⟨c, hc, -, -⟩ :=
      CFSG.StandardType.UnitaryCenter.exists_scalar_of_mem_center
        (F := F) (f := g) (n := n) hF hg hn hz
    have hz2mat : ((z : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        ((z : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
      have hgl : (z : GL (Fin n) F) * (z : GL (Fin n) F) = 1 := by
        simpa using congrArg Subtype.val hz2
      simpa using congrArg (fun w : GL (Fin n) F => (w : Matrix (Fin n) (Fin n) F)) hgl
    let i : Fin n := ⟨0, by omega⟩
    have hcc : (c : F) * (c : F) = 1 := by
      have e := congrArg (fun M : Matrix (Fin n) (Fin n) F => M i i) hz2mat
      rw [hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_mul_diagonal] at e
      simpa using e
    have hc1 : (c : F) = 1 :=
      CFSG.LieType.Chevalley.eq_one_of_mul_self_eq_one_of_two_eq_zero
        (CharP.cast_eq_zero F 2) hcc
    have hzmat1 : ((z : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
      rw [hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hc1,
        Matrix.diagonal_one]
    exact Subtype.ext (Units.ext hzmat1)

private theorem rckRPgf_mul_self_of_range_le_ker {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [CharP F 2] {X : Matrix ι ι F}
    (hle : LinearMap.range (Matrix.toLin' (X - 1)) ≤ LinearMap.ker (Matrix.toLin' (X - 1))) :
    X * X = 1 := by
  have hA2 : (Matrix.toLin' (X - 1)).comp (Matrix.toLin' (X - 1)) = 0 :=
    LinearMap.range_le_ker_iff.mp hle
  have hmat2 : (X - 1) * (X - 1) = 0 := by
    apply Matrix.toLin'.injective
    have hzero : Matrix.toLin' (0 : Matrix ι ι F) = 0 := by
      rw [Matrix.toLin'_apply', Matrix.mulVecLin_zero]
    rw [Matrix.toLin'_mul, hzero]
    exact hA2
  have e : X * X = 1 + ((X - 1) + (X - 1)) + (X - 1) * (X - 1) := by
    noncomm_ring
  rw [hmat2, add_zero] at e
  have hself : (X - 1) + (X - 1) = 0 := by
    ext i j
    simp [CharTwo.add_self_eq_zero]
  rw [hself, add_zero] at e
  exact e

theorem eq_one_of_mem_center_SL_of_mul_self {n F : Type} [Fintype n] [DecidableEq n] [Field F]
    [CharP F 2] {z : Matrix.SpecialLinearGroup n F}
    (hz : z ∈ Subgroup.center (Matrix.SpecialLinearGroup n F)) (hz2 : z * z = 1) : z = 1 := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i⟩⟩
  · exact Subsingleton.elim z 1
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have hz2mat : (z : Matrix n n F) * (z : Matrix n n F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hz2, Matrix.SpecialLinearGroup.coe_one]
  have hrr : r * r = 1 := by
    have e := congrArg (fun M : Matrix n n F => M i i) hz2mat
    rw [← hr, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal] at e
    simpa using e
  have hr1 : r = 1 :=
    CFSG.LieType.Chevalley.eq_one_of_mul_self_eq_one_of_two_eq_zero (CharP.cast_eq_zero F 2) hrr
  apply Subtype.ext
  rw [← hr, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem ggRootPosFlag_of_glGeoFlag_PSL {X : Type} [Group X] {m g : ℕ} (hg : 1 ≤ g)
    (φ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g) →* X) {K R : Subgroup X}
    (hφr : φ.range = K) (hφk : φ.ker ≤ Subgroup.center _)
    {R' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g))}
    (hR : R'.map φ = R) (hflag : GLGeoFlag none (R'.map Matrix.SpecialLinearGroup.toGL)) :
    GGRootPosFlag K R := by
  refine Or.inl ⟨m, g, hg, ?_⟩
  refine flagAt_of_glGeoFlag (j := Matrix.SpecialLinearGroup.toGL) (B := none) (φ := φ)
    (K := K) (R := R) (R' := R') Matrix.SpecialLinearGroup.toGL_injective hφr hφk hR ?_ hflag
  intro v hvR hvphi
  by_contra hvne
  have hvcenter : v ∈ Subgroup.center _ := hφk (MonoidHom.mem_ker.mpr hvphi)
  obtain ⟨W, H, hWH, hrange, -⟩ := hflag
  have hvmap : Matrix.SpecialLinearGroup.toGL v ∈ R'.map Matrix.SpecialLinearGroup.toGL :=
    Subgroup.mem_map_of_mem _ hvR
  have hvneGL : Matrix.SpecialLinearGroup.toGL v ≠ 1 := fun h =>
    hvne (Matrix.SpecialLinearGroup.toGL_injective (h.trans (map_one _).symm))
  obtain ⟨hW, hH⟩ := hrange _ hvmap hvneGL
  have hle : LinearMap.range (Matrix.toLin' (((Matrix.SpecialLinearGroup.toGL v :
        GL (Fin (m + 1)) (GaloisField 2 g)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)) - 1)) ≤
      LinearMap.ker (Matrix.toLin' (((Matrix.SpecialLinearGroup.toGL v :
        GL (Fin (m + 1)) (GaloisField 2 g)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)) - 1)) := by
    rw [hW, hH]
    exact hWH
  have hvv : (v : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)) * v = 1 :=
    rckRPgf_mul_self_of_range_le_ker hle
  have hv2 : v * v = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, hvv, Matrix.SpecialLinearGroup.coe_one]
  exact hvne (eq_one_of_mem_center_SL_of_mul_self hvcenter hv2)

theorem ggRootPosFlag_of_glGeoFlag_PSp {X : Type} [Group X] {n f : ℕ} (hf : 1 ≤ f)
    (φ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →* X) {K R : Subgroup X} (hφr : φ.range = K)
    (hφk : φ.ker ≤ Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    {R' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))} (hR : R'.map φ = R)
    (hflag : GLGeoFlag (spForm n (GaloisField 2 f))
      (R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype)) :
    GGRootPosFlag K R := by
  refine Or.inr (Or.inr (Or.inl ⟨n, f, hf, ?_⟩))
  let F := GaloisField 2 f
  refine flagAt_of_glGeoFlag (j := (CFSG.Open.StatedSp n F).subtype)
    (B := spForm n F) (φ := φ) (K := K) (R := R) (R' := R')
    (Subgroup.subtype_injective _) hφr hφk hR ?_ hflag
  intro v hvR hvphi
  have hc : v ∈ Subgroup.center ↥(CFSG.Open.StatedSp n F) :=
    hφk (MonoidHom.mem_ker.mpr hvphi)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hv1 : v = 1 := by
      apply Subtype.ext
      apply Units.ext
      apply Matrix.ext
      intro i j
      rcases i with i | i <;> exact i.elim0
    exact hv1
  · have hcenter : Subgroup.center ↥(CFSG.Open.StatedSp n F) = ⊥ :=
      CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two
        (m := n) (F := F) hn
    rwa [hcenter, Subgroup.mem_bot] at hc

private abbrev rckRPgfF (g : ℕ) : Type := GaloisField 2 (2 * g)

theorem ggRootPosFlag_of_glGeoFlag_PSU {X : Type} [Group X] {n g : ℕ} (hg : 1 ≤ g)
    (φ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * g)) 2 g) n) →*
      X)
    {K R : Subgroup X} (hφr : φ.range = K) (hφk : φ.ker ≤ Subgroup.center _)
    {R' : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * g)) 2 g) n)} (hR : R'.map φ = R)
    (hflag : GLGeoFlag none (R'.map (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * g)) 2 g) n).subtype)) :
    GGRootPosFlag K R := by
  refine Or.inr (Or.inl ⟨n, g, hg, ?_⟩)
  let σ := CFSG.LieType.BorelTits.unitaryInvolution (rckRPgfF g) 2 g
  refine flagAt_of_glGeoFlag (j := (Unitary.SU σ n).subtype)
    (B := none) (φ := φ) (K := K) (R := R) (R' := R')
    (Subgroup.subtype_injective _) hφr hφk hR ?_ hflag
  intro v hvR hvphi
  by_contra hvne
  have hvcenter : v ∈ Subgroup.center ↥(Unitary.SU σ n) :=
    hφk (MonoidHom.mem_ker.mpr hvphi)
  obtain ⟨W, H, hWH, hrange, -⟩ := hflag
  have hvmap : (v : GL (Fin n) (rckRPgfF g)) ∈ R'.map (Unitary.SU σ n).subtype :=
    Subgroup.mem_map_of_mem _ hvR
  have hvneGL : (v : GL (Fin n) (rckRPgfF g)) ≠ 1 := by
    intro h
    exact hvne (Subtype.ext h)
  obtain ⟨hW, hH⟩ := hrange (v : GL (Fin n) (rckRPgfF g)) hvmap hvneGL
  have hle : LinearMap.range (Matrix.toLin' (((v : GL (Fin n) (rckRPgfF g)) :
        Matrix (Fin n) (Fin n) (rckRPgfF g)) - 1)) ≤
      LinearMap.ker (Matrix.toLin' (((v : GL (Fin n) (rckRPgfF g)) :
        Matrix (Fin n) (Fin n) (rckRPgfF g)) - 1)) := by
    rw [hW, hH]
    exact hWH
  have hv2 : v * v = 1 := Subtype.ext (Units.ext (rckRPgf_mul_self_of_range_le_ker hle))
  exact hvne (eq_one_of_mem_center_SU_of_mul_self hg hvcenter hv2)

private theorem rckRPgf_range_comp_conj {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (e : V ≃ₗ[F] V) (f : V →ₗ[F] V) :
    LinearMap.range (e.toLinearMap.comp (f.comp e.symm.toLinearMap)) =
      (LinearMap.range f).map e.toLinearMap := by
  rw [LinearMap.range_comp, LinearEquiv.range_comp]

private theorem rckRPgf_ker_comp_conj {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (e : V ≃ₗ[F] V) (f : V →ₗ[F] V) :
    LinearMap.ker (e.toLinearMap.comp (f.comp e.symm.toLinearMap)) =
      (LinearMap.ker f).map e.toLinearMap := by
  rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot, LinearMap.ker_comp,
    Submodule.comap_equiv_eq_map_symm]
  exact congrArg (fun g : V ≃ₗ[F] V => Submodule.map (g : V →ₗ[F] V) (LinearMap.ker f))
    (LinearEquiv.symm_symm e)

theorem glGeoFlag_map_conj {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {B : Option ((ι → F) → (ι → F) → F)} {R : Subgroup (GL ι F)} (hR : GLGeoFlag B R)
    (y : GL ι F)
    (hy : ∀ b ∈ B, ∀ m m' : ι → F,
      b ((y : Matrix ι ι F).mulVec m) ((y : Matrix ι ι F).mulVec m') = b m m') :
    GLGeoFlag B (R.map (MulAut.conj y).toMonoidHom) := by
  obtain ⟨W, H, hWH, hrange, hform⟩ := hR
  let Y : Matrix ι ι F := (y : Matrix ι ι F)
  let Z : Matrix ι ι F := ((y⁻¹ : GL ι F) : Matrix ι ι F)
  have hYZ : Y * Z = 1 := by
    dsimp [Y, Z]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hZY : Z * Y = 1 := by
    dsimp [Y, Z]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  let e : (ι → F) ≃ₗ[F] (ι → F) :=
    LinearEquiv.ofLinearMap (Matrix.toLin' Y) (Matrix.toLin' Z)
      (by rw [← Matrix.toLin'_mul, hYZ, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, hZY, Matrix.toLin'_one])
  have he : e.toLinearMap = Matrix.toLin' Y := rfl
  have he' : e.symm.toLinearMap = Matrix.toLin' Z := rfl
  have hstep : ∀ x : GL ι F,
      (((MulEquiv.toMonoidHom (MulAut.conj y)) x : GL ι F) : Matrix ι ι F) - 1 =
      Y * ((x : Matrix ι ι F) - 1) * Z := by
    intro x
    have hcoe : (((MulEquiv.toMonoidHom (MulAut.conj y)) x : GL ι F) : Matrix ι ι F) =
        Y * (x : Matrix ι ι F) * Z := by
      change ((MulAut.conj y x : GL ι F) : Matrix ι ι F) = Y * (x : Matrix ι ι F) * Z
      rw [MulAut.conj_apply]
      simp [Y, Z]
    rw [hcoe, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hYZ]
  refine ⟨W.map e.toLinearMap, H.map e.toLinearMap, Submodule.map_mono hWH, ?_, ?_⟩
  · intro x' hx' hx'ne
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hx'
    have hxne : x ≠ 1 := by
      intro h1
      apply hx'ne
      simp [h1]
    obtain ⟨hW, hH⟩ := hrange x hx hxne
    have hlin : Matrix.toLin'
        ((((MulEquiv.toMonoidHom (MulAut.conj y)) x : GL ι F) : Matrix ι ι F) - 1) =
        e.toLinearMap.comp
          ((Matrix.toLin' (((x : GL ι F) : Matrix ι ι F) - 1)).comp e.symm.toLinearMap) := by
      rw [hstep x, Matrix.toLin'_mul, Matrix.toLin'_mul, he, he', LinearMap.comp_assoc]
    constructor
    · rw [hlin, rckRPgf_range_comp_conj, hW]
    · rw [hlin, rckRPgf_ker_comp_conj, hH]
  · intro b hb
    rcases hform b hb with hB | hdim
    · left
      intro x' hx' m
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hx'
      rw [hstep x, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      have hm : Y.mulVec (Z.mulVec m) = m := by
        rw [Matrix.mulVec_mulVec, hYZ, Matrix.one_mulVec]
      calc b m (Y.mulVec (((x : Matrix ι ι F) - 1).mulVec (Z.mulVec m)))
          = b (Y.mulVec (Z.mulVec m))
              (Y.mulVec (((x : Matrix ι ι F) - 1).mulVec (Z.mulVec m))) := by rw [hm]
        _ = b (Z.mulVec m) (((x : Matrix ι ι F) - 1).mulVec (Z.mulVec m)) := by
              rw [hy b hb]
        _ = 0 := hB x hx (Z.mulVec m)
    · right
      exact (LinearEquiv.finrank_map_eq e W).trans hdim

theorem glGeoFlag_polar_of_isotropic {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {Q : QuadraticForm F (ι → F)} {R : Subgroup (GL ι F)} {W H : Submodule F (ι → F)}
    (hWH : W ≤ H) (hW : ∀ w ∈ W, Q w = 0)
    (hQ : ∀ x ∈ R, ∀ m, Q ((x : Matrix ι ι F).mulVec m) = Q m)
    (hflag : ∀ x ∈ R, x ≠ 1 →
      LinearMap.range (Matrix.toLin' ((x : Matrix ι ι F) - 1)) = W ∧
      LinearMap.ker (Matrix.toLin' ((x : Matrix ι ι F) - 1)) = H) :
    GLGeoFlag (some (QuadraticMap.polar Q)) R := by
  refine ⟨W, H, hWH, hflag, ?_⟩
  intro b hb
  left
  rw [Option.mem_some_iff] at hb
  subst hb
  intro x hx m
  by_cases hx1 : x = 1
  · subst hx1
    simp [QuadraticMap.polar]
  · have hmem : ((x : Matrix ι ι F) - 1).mulVec m ∈ W := by
      rw [← (hflag x hx hx1).1]
      exact ⟨m, by rw [Matrix.toLin'_apply]⟩
    have hQv : Q (((x : Matrix ι ι F) - 1).mulVec m) = 0 := hW _ hmem
    have hxm : m + ((x : Matrix ι ι F) - 1).mulVec m = (x : Matrix ι ι F).mulVec m := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
    rw [QuadraticMap.polar, hxm, hQ x hx, hQv]
    simp

theorem spForm_isometry (n : ℕ) (F : Type) [Field F] (y : GL (Fin n ⊕ Fin n) F)
    (hy : y ∈ CFSG.Open.StatedSp n F) :
    ∀ b ∈ spForm n F, ∀ m m' : (Fin n ⊕ Fin n) → F,
      b ((y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec m)
        ((y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec m') = b m m' := by
  intro b hb m m'
  simp only [spForm, Option.mem_def, Option.some.injEq] at hb
  subst b
  change ((y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec m) ⬝ᵥ
      ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec
        ((y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec m')) =
    m ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec m')
  have hJ : Matrix.transpose (y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      (Matrix.fromBlocks 0 1 (-1) 0 * (y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) =
      Matrix.fromBlocks 0 1 (-1) 0 := by
    rw [← Matrix.mul_assoc]
    exact (CFSG.Open.StatedAPI.mem_statedSp_iff.mp hy)
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, hJ, ← Matrix.dotProduct_mulVec]

end CFSG.StandardType.RCKRP
