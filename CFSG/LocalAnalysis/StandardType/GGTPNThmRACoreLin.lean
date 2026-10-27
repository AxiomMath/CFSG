module

public import CFSG.LocalAnalysis.StandardType.GGTPNThmRABase
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRADescent
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeALift
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab
public import CFSG.LocalAnalysis.StandardType.GGTPNI1TypeAHelp
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearFieldType
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.PrimaryConjScalar
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzB2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDLinProj
public import CFSG.LocalAnalysis.StandardType.GGPGLTorality
public import CFSG.RankThree.PartOne.KC.LinearCommutantFactors
public import CFSG.RankThree.PartOne.S15K.CommonEigen
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearNative

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Solomon.Coordinator
open Polynomial CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.RankThree.PartOne.KCPrimary CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.RankThree.CALinearPrimary

theorem raLin_ggInducedAut_trans {X : Type} [Group X] {R R' : Type} [Group R]
    [Group R'] (θ : X ⧸ Subgroup.center X ≃* R) (e : R ≃* R') (a : MulAut X) :
    ggInducedAut (θ.trans e) a = MulAut.congr e (ggInducedAut θ a) := by
  show MulAut.congr (θ.trans e) (centerQuotAut X a) =
    MulAut.congr e (MulAut.congr θ (centerQuotAut X a))
  rw [MulAut.congr_apply, MulAut.congr_apply, MulAut.congr_apply]
  ext x
  rfl

theorem raLin_model {p : ℕ} (hp : p.Prime) {X : Type} [Group X] [Finite X]
    {A : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hloc : GGTPNLocalCore p A σ J) {labX : LargeEvenLabel}
    (hA : labX.tag = .A) (hm : GGTPNMarked p (fun _ lab => lab = labX) A) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = 2 ^ labX.n ∧
      ∃ θ : X ⧸ Subgroup.center X ≃* projectiveSL (labX.rank + 1) K,
        (∀ a ∈ A, ∃ B : GL (Fin (labX.rank + 1)) K,
          ∀ l : X, conjAut (labX.rank + 1) K B (θ (l : X ⧸ Subgroup.center X)) =
            θ ((a l : X) : X ⧸ Subgroup.center X)) ∧
        ∃ g : GL (Fin (labX.rank + 1)) K,
          (∃ c : Kˣ, g ^ p = Matrix.GeneralLinearGroup.scalar (Fin (labX.rank + 1)) c) ∧
          (∀ l : X, conjAut (labX.rank + 1) K g (θ (l : X ⧸ Subgroup.center X)) =
            θ ((σ l : X) : X ⧸ Subgroup.center X)) ∧
          commutator X = ⊤ := by
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hm
  obtain ⟨R₀, _, I₀, F₀, -, -, θ₀, hP⟩ := largeEvenRawDatum_exists hraw
  have hlab_eq : lab = labX := hP.1
  rw [hlab_eq] at hraw
  obtain ⟨t, r, n⟩ := labX
  simp only at hA
  subst hA
  dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
  obtain ⟨K, hFld, hFin, hKcard, hQR⟩ := hraw
  letI : Field K := hFld
  haveI : Finite K := hFin
  obtain ⟨-, -, θ, -, -, hind⟩ := hQR
  refine ⟨K, hFld, hFin, hKcard, ?_⟩
  let e := TypeA.recipeEquiv (r + 1) K
  refine ⟨θ.trans e, ?_, ?_⟩
  · intro a ha
    have hmem : ggInducedAut θ a ∈
        LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (r + 1)) K)) Set.univ :=
      hind a ha
    have hmem' : MulAut.congr e (ggInducedAut θ a) ∈ Set.range (conjAut (r + 1) K) :=
      TypeA.congr_recipeEquiv_mem hmem
    obtain ⟨B, hB⟩ := hmem'
    refine ⟨B, fun l => ?_⟩
    have h1 := ggInducedAut_apply (θ.trans e) a l
    rw [raLin_ggInducedAut_trans θ e a, ← hB] at h1
    exact h1
  · have hσA : σ ∈ A := hloc.2.1
    have hmem : ggInducedAut θ σ ∈
        LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (r + 1)) K)) Set.univ :=
      hind σ hσA
    have hmem' : MulAut.congr e (ggInducedAut θ σ) ∈ Set.range (conjAut (r + 1) K) :=
      TypeA.congr_recipeEquiv_mem hmem
    let g := Classical.choose hmem'
    have hg : MulAut.congr e (ggInducedAut θ σ) = conjAut (r + 1) K g :=
      (Classical.choose_spec hmem').symm
    have hconj : conjAut (r + 1) K g = ggInducedAut (θ.trans e) σ := by
      rw [raLin_ggInducedAut_trans θ e σ, hg]
    have hσpow : σ ^ p = 1 := hloc.1.2 σ hσA
    have hgpow : conjAut (r + 1) K (g ^ p) = 1 := by
      rw [map_pow, hconj, ← map_pow, hσpow, map_one]
    obtain ⟨c, hc⟩ := TypeA.exists_scalar_of_conjAut_eq_one (A := g ^ p) hgpow
    obtain ⟨u, hu⟩ := TypeA.exists_unit_of_scalar (by omega : 0 < r + 1) hc
    refine ⟨g, ⟨u, hu⟩, ?_, hcomm⟩
    intro l
    rw [hconj]
    simpa only using ggInducedAut_apply (θ.trans e) σ l

theorem raLin_nonSplit_component {p N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpk : (p : K) ≠ 0) {g : GL (Fin N) K} {c : Kˣ}
    (hg : g ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    (hc : ∀ b : K, b ^ p ≠ (c : K))
    {T : Subgroup (projectiveSL N K)}
    (hT : CFSG.Open.IsComponentOf T (fixSubgroup (conjAut N K g))) :
    2 ≤ N / p ∧
      ∃ (E : Type) (_ : Field E) (_ : Fintype E), Nat.card E = Nat.card K ^ p ∧
        Nonempty (↥T ⧸ Subgroup.center ↥T ≃* projectiveSL (N / p) E) := by
  obtain ⟨hpN, hp2, -, E, hEfld, hEfin, hEcard, f, hfsurj, hfker⟩ :=
    LieComp.linear_fieldType_component (n := N) (k := K) hp hpk hg hc hT
  letI : Field E := hEfld
  haveI : Fintype E := hEfin
  have hE4 : 4 ≤ Nat.card E := by
    rw [hEcard]
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hK2 : 2 ≤ Nat.card K := Nat.succ_le_iff.mpr Finite.one_lt_card
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ Nat.card K ^ 3 := Nat.pow_le_pow_left hK2 3
      _ ≤ Nat.card K ^ p := Nat.pow_le_pow_right (Nat.card_pos (α := K)) hp3
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin (N / p)) E) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_perfect (N / p) E hp2
      (Or.inr (by intro h; have := hE4; omega))
      (Or.inr (by intro h; have := hE4; omega))
  obtain ⟨e1⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10F.quotEquiv_of_perfect_central f hfsurj
    hperf hfker
  let e2 : (Matrix.SpecialLinearGroup (Fin (N / p)) E ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (N / p)) E)) ≃*
      projectiveSL (N / p) E :=
    QuotientGroup.quotientMulEquivOfEq (scalars_eq_center (N / p) E).symm
  exact ⟨hp2, E, hEfld, hEfin, hEcard, ⟨e1.symm.trans e2⟩⟩

theorem raLin_card_le_nonSplit {p N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) (hN : 0 < N)
    {g : GL (Fin N) K} {c : Kˣ}
    (hg : g ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    (hc : ∀ b : K, b ^ p ≠ (c : K))
    {G : Subgroup (MulAut (projectiveSL N K))} (hG : IsElemAbelian p G)
    (hGr : ∀ x ∈ G, x ∈ Set.range (conjAut N K))
    (hgG : conjAut N K g ∈ G) :
    Nat.card G ≤ p ^ (N / p + 1) := by
  have hGp : TypeA.PGLTor.IsProjElem p (G.comap (conjAut N K)) :=
    TypeA.isProjElem_comap hN hG
  rcases TypeA.PGLTor.toral_or_card_le hp hp2 hpq hGp with htor | hbound
  ·
    exfalso
    obtain ⟨A₀, hA₀⟩ := htor
    have hgG' : g ∈ G.comap (conjAut N K) := hgG
    set D : GL (Fin N) K := A₀ * g * A₀⁻¹ with hD
    have hDdiag : (D : Matrix (Fin N) (Fin N) K) =
        diagonal (fun i => (D : Matrix (Fin N) (Fin N) K) i i) :=
      CFSG.RankThree.CALinearPlane.eq_diagonal_of_offDiag (hA₀ g hgG')
    have hDp : D ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) c := by
      rw [hD, conj_pow, hg, ← TypeA.PGLTor.scalar_mul_comm c A₀, mul_inv_cancel_right]
    have h1 := congrArg (fun M : GL (Fin N) K => (M : Matrix (Fin N) (Fin N) K)) hDp
    have h2 := congrArg (fun M : Matrix (Fin N) (Fin N) K => M ⟨0, hN⟩ ⟨0, hN⟩) h1
    rw [Units.val_pow_eq_pow_val, hDdiag, diagonal_pow, GeneralLinearGroup.coe_scalar,
      scalar_apply, diagonal_apply_eq, Pi.pow_apply] at h2
    exact hc ((D : Matrix (Fin N) (Fin N) K) ⟨0, hN⟩ ⟨0, hN⟩) h2
  ·
    have hXI : (G : Set (MulAut (projectiveSL N K))) ⊆ Set.range (conjAut N K) := hGr
    rw [TypeA.card_comap_eq hN hXI, Fintype.card_fin] at hbound
    have hK1 : 0 < Nat.card K - 1 := by
      have := Finite.one_lt_card (α := K)
      omega
    exact Nat.le_of_mul_le_mul_right hbound hK1



section Split

variable {N : ℕ} {K : Type} [Field K] [Finite K]

theorem raLin_specialFactor_triv {D : GL (Fin N) K} {f : K[X]}
    (x : ↥(specialFactor D f)) {j : K[X]}
    (hj : j ∈ primaryFactors (glA D : Module.End K (Fin N → K))) (hjf : j ≠ f)
    {v : Fin N → K} (hv : v ∈ primaryComponent (glA D : Module.End K (Fin N → K)) j) :
    (slGL N K (x : Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K)) v = v :=
  (mem_linearSpecialBlock.mp (Subgroup.mem_comap.mp x.2)).2.1 j hj hjf v hv

theorem raLin_specialFactor_mul_apply_scalar {D : GL (Fin N) K} {f : K[X]}
    (hcon : ∀ (x : ↥(specialFactor D f))
      (v : ↥(primaryComponent (glA D : Module.End K (Fin N → K)) f)),
      ∃ c : K, (slGL N K (x : Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K))
        (v : Fin N → K) = c • (v : Fin N → K))
    {x y : ↥(specialFactor D f)}
    (v : ↥(primaryComponent (glA D : Module.End K (Fin N → K)) f)) :
    (slGL N K ((x * y : ↥(specialFactor D f)) : Matrix.SpecialLinearGroup (Fin N) K) :
        Module.End K (Fin N → K)) (v : Fin N → K) =
      (slGL N K ((y * x : ↥(specialFactor D f)) : Matrix.SpecialLinearGroup (Fin N) K) :
        Module.End K (Fin N → K)) (v : Fin N → K) := by
  obtain ⟨cx, hx⟩ := hcon x v
  obtain ⟨cy, hy⟩ := hcon y v
  have hxy : (slGL N K ((x * y : ↥(specialFactor D f)) :
      Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K)) (v : Fin N → K) =
      (cx * cy) • (v : Fin N → K) := by
    have hxy2 : (slGL N K ((x * y : ↥(specialFactor D f)) :
        Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K)) =
        (slGL N K (x : Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K)) *
        (slGL N K (y : Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K)) := by
      rw [show ((x * y : ↥(specialFactor D f)) : Matrix.SpecialLinearGroup (Fin N) K) =
        (x : Matrix.SpecialLinearGroup (Fin N) K) * (y : Matrix.SpecialLinearGroup (Fin N) K)
        from rfl, map_mul]
      rfl
    rw [hxy2]
    change ((slGL N K (x : Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K)) *
      (slGL N K (y : Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K)))
        (v : Fin N → K) = _
    rw [Module.End.mul_apply, hy, LinearMap.map_smul, hx, smul_smul, Subtype.coe_mk, mul_comm]
  have hyx : (slGL N K ((y * x : ↥(specialFactor D f)) :
      Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K)) (v : Fin N → K) =
      (cy * cx) • (v : Fin N → K) := by
    have hyx2 : (slGL N K ((y * x : ↥(specialFactor D f)) :
        Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K)) =
        (slGL N K (y : Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K)) *
        (slGL N K (x : Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K)) := by
      rw [show ((y * x : ↥(specialFactor D f)) : Matrix.SpecialLinearGroup (Fin N) K) =
        (y : Matrix.SpecialLinearGroup (Fin N) K) * (x : Matrix.SpecialLinearGroup (Fin N) K)
        from rfl, map_mul]
      rfl
    rw [hyx2]
    change ((slGL N K (y : Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K)) *
      (slGL N K (x : Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K)))
        (v : Fin N → K) = _
    rw [Module.End.mul_apply, hx, LinearMap.map_smul, hy, smul_smul, Subtype.coe_mk, mul_comm]
  rw [hxy, hyx, mul_comm]

theorem raLin_specialFactor_commutative_of_scalar {D : GL (Fin N) K}
    (hsq : Squarefree (minpoly K (glA D : Module.End K (Fin N → K))))
    {f : K[X]} (hf : f ∈ primaryFactors (glA D : Module.End K (Fin N → K)))
    (hcon : ∀ (x : ↥(specialFactor D f))
      (v : ↥(primaryComponent (glA D : Module.End K (Fin N → K)) f)),
      ∃ c : K, (slGL N K (x : Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K))
        (v : Fin N → K) = c • (v : Fin N → K)) :
    ∀ x y : ↥(specialFactor D f), x * y = y * x := by
  intro x y
  apply Subtype.ext
  apply slGL_injective
  apply Units.ext
  apply ext_primaryComponent hsq
  intro j hj v hv
  by_cases hjf : j = f
  · have hmemf : v ∈ primaryComponent (glA D : Module.End K (Fin N → K)) f := hjf ▸ hv
    have h1 := raLin_specialFactor_mul_apply_scalar hcon (x := x) (y := y) ⟨v, hmemf⟩
    simpa using h1
  · have hxy2 : (slGL N K ((x * y : ↥(specialFactor D f)) :
        Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K)) =
        (slGL N K (x : Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K)) *
        (slGL N K (y : Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K)) := by
      rw [show ((x * y : ↥(specialFactor D f)) : Matrix.SpecialLinearGroup (Fin N) K) =
        (x : Matrix.SpecialLinearGroup (Fin N) K) * (y : Matrix.SpecialLinearGroup (Fin N) K)
        from rfl, map_mul]
      rfl
    have hyx2 : (slGL N K ((y * x : ↥(specialFactor D f)) :
        Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K)) =
        (slGL N K (y : Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K)) *
        (slGL N K (x : Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K)) := by
      rw [show ((y * x : ↥(specialFactor D f)) : Matrix.SpecialLinearGroup (Fin N) K) =
        (y : Matrix.SpecialLinearGroup (Fin N) K) * (x : Matrix.SpecialLinearGroup (Fin N) K)
        from rfl, map_mul]
      rfl
    rw [hxy2, hyx2]
    change ((slGL N K (x : Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K)) *
      (slGL N K (y : Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K)))
        (v : Fin N → K) =
        ((slGL N K (y : Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K)) *
          (slGL N K (x : Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K)))
          (v : Fin N → K)
    rw [Module.End.mul_apply, Module.End.mul_apply]
    change (slGL N K (x : Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K))
      ((slGL N K (y : Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K))
        (v : Fin N → K)) =
      (slGL N K (y : Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K))
        ((slGL N K (x : Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K))
          (v : Fin N → K))
    simp only [raLin_specialFactor_triv x hj hjf hv, raLin_specialFactor_triv y hj hjf hv]

theorem raLin_exists_nonScalarOn {D : GL (Fin N) K}
    (hsq : Squarefree (minpoly K (glA D : Module.End K (Fin N → K))))
    {f : K[X]} (hf : f ∈ primaryFactors (glA D : Module.End K (Fin N → K)))
    (hgood : IsGoodFactor D f) :
    ∃ x : ↥(specialFactor D f), ∃ v : primaryComponent (glA D : Module.End K (Fin N → K)) f,
      ∀ c : K, (slGL N K (x : Matrix.SpecialLinearGroup (Fin N) K) : Module.End K (Fin N → K))
        (v : Fin N → K) ≠ c • (v : Fin N → K) := by
  by_contra hcon
  push Not at hcon
  have hcomm := raLin_specialFactor_commutative_of_scalar hsq hf hcon
  have hbot : commutator ↥(specialFactor D f) = ⊥ := by
    rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hcomm y x
  have hq := isQuasisimple_specialFactor hsq hf hgood
  haveI := CFSG.LocalCores.isQuasisimple_nontrivial hq
  exact (bot_ne_top : (⊥ : Subgroup ↥(specialFactor D f)) ≠ ⊤)
    (hbot.symm.trans hq.1.commutator_eq_top)

theorem raLin_components_ne {D : GL (Fin N) K}
    (hsq : Squarefree (minpoly K (glA D : Module.End K (Fin N → K))))
    {j f : K[X]} (hj : j ∈ primaryFactors (glA D : Module.End K (Fin N → K)))
    (hf : f ∈ primaryFactors (glA D : Module.End K (Fin N → K))) (hjf : j ≠ f)
    (hgood : IsGoodFactor D f) :
    (specialFactor D j).map (proj N K) ≠ (specialFactor D f).map (proj N K) := by
  intro heq
  obtain ⟨x, v, hx⟩ := raLin_exists_nonScalarOn hsq hf hgood
  have hximg : proj N K (x : Matrix.SpecialLinearGroup (Fin N) K) ∈
      (specialFactor D j).map (proj N K) := by
    rw [heq]
    exact Subgroup.mem_map_of_mem _ x.2
  obtain ⟨y, hymem, hyx⟩ := Subgroup.mem_map.mp hximg
  have hscal : (y⁻¹ * (x : Matrix.SpecialLinearGroup (Fin N) K)) ∈ scalars N K :=
    (proj_eq_proj_iff).mp hyx
  obtain ⟨c, -, hcmat⟩ := mem_scalars.mp hscal
  have hxeq : (x : Matrix.SpecialLinearGroup (Fin N) K) =
      y * (y⁻¹ * (x : Matrix.SpecialLinearGroup (Fin N) K)) := by group
  have hcx : (slGL N K (x : Matrix.SpecialLinearGroup (Fin N) K) :
      Module.End K (Fin N → K)) (v : Fin N → K) = (c : K) • (v : Fin N → K) := by
    have hz : (slGL N K (y⁻¹ * (x : Matrix.SpecialLinearGroup (Fin N) K)) :
        Module.End K (Fin N → K)) (v : Fin N → K) = (c : K) • (v : Fin N → K) := by
      rw [coe_slGL, hcmat]
      simp [Matrix.toLin'_apply, Matrix.mulVec_diagonal]
    have hyv : (slGL N K y : Module.End K (Fin N → K)) (v : Fin N → K) = v :=
      (mem_linearSpecialBlock.mp (Subgroup.mem_comap.mp hymem)).2.1 f hf hjf.symm v v.2
    rw [hxeq, map_mul]
    change (slGL N K y : Module.End K (Fin N → K))
      ((slGL N K (y⁻¹ * (x : Matrix.SpecialLinearGroup (Fin N) K)) :
        Module.End K (Fin N → K)) (v : Fin N → K)) = _
    rw [hz]
    exact (LinearMap.map_smul (slGL N K y : Module.End K (Fin N → K)) (c : K)
      (v : Fin N → K)).trans (by rw [hyv])
  exact hx c hcx

theorem raLin_dvd_card_specialFactor {p : ℕ} (hp : p.Prime) {D : GL (Fin N) K}
    (hsq : Squarefree (minpoly K (glA D : Module.End K (Fin N → K))))
    {a : K[X]} (ha : a ∈ primaryFactors (glA D : Module.End K (Fin N → K)))
    (hdeg : a.natDegree = 1)
    (hm2 : 2 ≤ primaryMultiplicity (glA D : Module.End K (Fin N → K)) a)
    (hpq : p ∣ Nat.card K - 1) :
    p ∣ Nat.card (specialFactor D a) := by
  haveI : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
  obtain ⟨eSL⟩ := nonempty_mulEquiv_specialFactor (A := D) hsq ha
  rw [← Nat.card_congr eSL.toEquiv]
  have hE : Nat.card (AdjoinRoot a) = Nat.card K := by
    rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot, hdeg, pow_one]
  have hcard := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq
    (K := AdjoinRoot a) (n := primaryMultiplicity (glA D : Module.End K (Fin N → K)) a)
    (by omega)
  rw [hcard]
  have hmem : 2 ∈ Finset.Icc 2 (primaryMultiplicity (glA D : Module.End K (Fin N → K)) a) :=
    Finset.mem_Icc.mpr ⟨le_rfl, hm2⟩
  have hq : p ∣ Nat.card (AdjoinRoot a) - 1 := hE ▸ hpq
  have hq2 : p ∣ Nat.card (AdjoinRoot a) ^ 2 - 1 :=
    hq.trans (Nat.sub_one_dvd_pow_sub_one (Nat.card (AdjoinRoot a)) 2)
  refine Dvd.dvd.mul_left ?_ _
  exact hq2.trans (Finset.dvd_prod_of_mem (fun j => Nat.card (AdjoinRoot a) ^ j - 1) hmem)


theorem raLin_conjAut_eq_one_of_single_primaryFactor {g : GL (Fin N) K}
    (hsq : Squarefree (minpoly K (glA g : Module.End K (Fin N → K)))) {h : K[X]} {ε : K}
    (hh : h ∈ primaryFactors (glA g : Module.End K (Fin N → K))) (hlin : h = X - C ε)
    (hε0 : ε ≠ 0)
    (hSe : primaryFactors (glA g : Module.End K (Fin N → K)) = {h}) :
    conjAut N K g = 1 := by
  have hdeg : h.natDegree = 1 := by rw [hlin]; simp
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hsum := finrank_eq_sum_degree_mul_multiplicity (x := (glA g : Module.End K (Fin N → K)))
    hsq
  have hfinN : Module.finrank K (Fin N → K) = N := by simp
  have huniv : (Finset.univ : Finset ↥(primaryFactors (glA g : Module.End K (Fin N → K)))) =
      {⟨h, by rw [hSe]; exact Finset.mem_singleton_self h⟩} := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    apply Subtype.ext
    have hx : (x : K[X]) ∈ ({h} : Finset K[X]) := by rw [← hSe]; exact x.2
    simpa using hx
  rw [hfinN, huniv, Finset.sum_singleton] at hsum
  have hm : primaryMultiplicity (glA g : Module.End K (Fin N → K)) h = N := by
    rw [hdeg, one_mul] at hsum
    simpa using hsum.symm
  have hfr : Module.finrank K (primaryComponent (glA g : Module.End K (Fin N → K)) h) = N := by
    rw [finrank_primaryComponent, hdeg, one_mul]
    exact hm
  have htop : primaryComponent (glA g : Module.End K (Fin N → K)) h = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [hfr, hfinN])
  have hgl : Matrix.GeneralLinearGroup.toLin g = (ε : K) • (1 : Module.End K (Fin N → K)) := by
    apply ext_primaryComponent (x := (glA g : Module.End K (Fin N → K))) hsq
    intro a ha v hv
    have hae : a = h := by rw [hSe] at ha; simpa using ha
    subst hae
    have hv' : v ∈ primaryComponent (glA g : Module.End K (Fin N → K)) (X - C ε) := by
      rwa [hlin] at hv
    have := (CFSG.RankThree.PartOne.KCUnitaryScalar.mem_primaryComponent_X_sub_C).mp hv'
    simpa using this
  have hg_eq : g = Matrix.GeneralLinearGroup.scalar (Fin N) (Units.mk0 ε hε0) := by
    apply Matrix.GeneralLinearGroup.toLin.injective
    apply Units.ext
    rw [hgl]
    ext v i
    simp [Matrix.GeneralLinearGroup.toLin, Matrix.toLin'_apply,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.mulVec_diagonal]
  rw [hg_eq, conjAut_scalar]

theorem raLin_split_factor {p N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpk : (p : K) ≠ 0) (hpq : p ∣ Nat.card K - 1)
    {g : GL (Fin N) K} (hg : g ^ p = 1)
    {T : Subgroup (projectiveSL N K)}
    (hT : CFSG.Open.IsComponentOf T (fixSubgroup (conjAut N K g))) :
    ∃ (h : K[X]) (ε : K),
      h ∈ primaryFactors (glA g : Module.End K (Fin N → K)) ∧ IsGoodFactor g h ∧
      h = X - C ε ∧ ε ≠ 0 ∧ h.natDegree = 1 ∧
      (∀ a ∈ primaryFactors (glA g : Module.End K (Fin N → K)), a.natDegree = 1) ∧
      Nat.card (AdjoinRoot h) = Nat.card K ∧ 4 ≤ Nat.card K ∧
      2 ≤ primaryMultiplicity (glA g : Module.End K (Fin N → K)) h ∧
      T = (specialFactor g h).map (proj N K) := by
  classical
  have hg' : g ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) (1 : Kˣ) := by simpa using hg
  obtain ⟨ω, hω⟩ := CFSG.RankThree.PartOne.S15K.exists_isPrimitiveRoot_of_dvd hp hpq
  obtain ⟨h, hTeq⟩ := linear_inner_components (n := N) (k := K) hpk hg' T hT
  obtain ⟨⟨hmem, hmemP⟩, hgood⟩ := h
  obtain ⟨ε, hform, -, hε0⟩ :=
    eq_X_sub_C_of_mem_primaryFactors_of_pow_eq_one hp.ne_zero hω hg' hmemP
  have hdeg : hmem.natDegree = 1 := by rw [hform]; simp
  have hdegS : ∀ a ∈ primaryFactors (glA g : Module.End K (Fin N → K)), a.natDegree = 1 := by
    intro a ha
    obtain ⟨μ, hμ, -⟩ :=
      eq_X_sub_C_of_mem_primaryFactors_of_pow_eq_one hp.ne_zero hω hg' ha
    rw [hμ]; simp
  haveI : Fact (Irreducible hmem) := ⟨irreducible_of_mem_primaryFactors hmemP⟩
  have hEcard : Nat.card (AdjoinRoot hmem) = Nat.card K := by
    rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot, hdeg, pow_one]
  have hK4 : 4 ≤ Nat.card K := by
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hpos : 0 < Nat.card K - 1 := by have := Finite.one_lt_card (α := K); omega
    have hle : p ≤ Nat.card K - 1 := Nat.le_of_dvd hpos hpq
    have hle' : Nat.card K - 1 ≤ Nat.card K := Nat.sub_le _ _
    omega
  have hm2 : 2 ≤ primaryMultiplicity (glA g : Module.End K (Fin N → K)) hmem := by
    have hgood' : IsGoodFactor g hmem := hgood
    rcases hgood' with h3 | ⟨h2, -⟩
    · omega
    · exact h2
  exact ⟨hmem, ε, hmemP, hgood, hform, hε0, hdeg, hdegS, hEcard, hK4, hm2, hTeq⟩

theorem raLin_split_centralQuot {p N : ℕ} {K : Type} [Field K] [Finite K]
    (hpk : (p : K) ≠ 0) {g : GL (Fin N) K} (hg : g ^ p = 1)
    {T : Subgroup (projectiveSL N K)}
    {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors (glA g : Module.End K (Fin N → K)))
    (hgood : IsGoodFactor g h) (hdeg : h.natDegree = 1)
    (hTeq : T = (specialFactor g h).map (proj N K)) :
    Nat.card (AdjoinRoot h) = Nat.card K ∧
      2 ≤ primaryMultiplicity (glA g : Module.End K (Fin N → K)) h ∧
      Nonempty (↥T ⧸ Subgroup.center ↥T ≃*
        projectiveSL (primaryMultiplicity (glA g : Module.End K (Fin N → K)) h)
          (AdjoinRoot h)) := by
  classical
  have hsq : Squarefree (minpoly K (glA g : Module.End K (Fin N → K))) :=
    squarefree_minpoly_glA hpk (c := 1) (by simpa using hg)
  have hEcard : Nat.card (AdjoinRoot h) = Nat.card K := by
    rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot, hdeg, pow_one]
  have hm2 : 2 ≤ primaryMultiplicity (glA g : Module.End K (Fin N → K)) h := by
    rcases hgood with h3 | ⟨h2, -⟩
    · omega
    · exact h2
  obtain ⟨eSL⟩ := nonempty_mulEquiv_specialFactor (A := g) hsq hh
  obtain ⟨f, hfsurj, hfker⟩ :=
    exists_surjective_ker_le_center_map_proj (n := N) (k := K) (S := specialFactor g h) eSL
  let eC : ↥T ≃* ↥((specialFactor g h).map (proj N K)) := MulEquiv.subgroupCongr hTeq
  let f' : Matrix.SpecialLinearGroup
      (Fin (primaryMultiplicity (glA g : Module.End K (Fin N → K)) h)) (AdjoinRoot h) →* ↥T :=
    eC.symm.toMonoidHom.comp f
  have hf'surj : Function.Surjective f' := eC.symm.surjective.comp hfsurj
  have hf'ker : f'.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup
      (Fin (primaryMultiplicity (glA g : Module.End K (Fin N → K)) h)) (AdjoinRoot h)) := by
    rw [show f' = eC.symm.toMonoidHom.comp f from rfl, TypeA.ker_comp_mulEquiv]
    exact hfker
  have hqF := isQuasisimple_specialFactor hsq hh hgood
  have hperfSL : Group.IsPerfect (Matrix.SpecialLinearGroup
      (Fin (primaryMultiplicity (glA g : Module.End K (Fin N → K)) h)) (AdjoinRoot h)) :=
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv eSL.symm hqF).1
  obtain ⟨e1⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10F.quotEquiv_of_perfect_central f' hf'surj
    hperfSL hf'ker
  let e2 : (Matrix.SpecialLinearGroup
        (Fin (primaryMultiplicity (glA g : Module.End K (Fin N → K)) h)) (AdjoinRoot h) ⧸
        Subgroup.center (Matrix.SpecialLinearGroup
          (Fin (primaryMultiplicity (glA g : Module.End K (Fin N → K)) h)) (AdjoinRoot h))) ≃*
      projectiveSL (primaryMultiplicity (glA g : Module.End K (Fin N → K)) h) (AdjoinRoot h) :=
    QuotientGroup.quotientMulEquivOfEq
      (scalars_eq_center (primaryMultiplicity (glA g : Module.End K (Fin N → K)) h)
        (AdjoinRoot h)).symm
  exact ⟨hEcard, hm2, ⟨e1.symm.trans e2⟩⟩

theorem raLin_split_mult_one {p N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hpq : p ∣ Nat.card K - 1)
    {g : GL (Fin N) K} (hsq : Squarefree (minpoly K (glA g : Module.End K (Fin N → K))))
    {T : Subgroup (projectiveSL N K)}
    (hTonly : ∀ Q : Subgroup (projectiveSL N K),
      CFSG.Open.IsComponentOf Q (fixSubgroup (conjAut N K g)) → p ∣ Nat.card Q → Q = T)
    {h : K[X]} (hh : h ∈ primaryFactors (glA g : Module.End K (Fin N → K)))
    (hgood : IsGoodFactor g h) (hTeq : T = (specialFactor g h).map (proj N K))
    (hdegS : ∀ a ∈ primaryFactors (glA g : Module.End K (Fin N → K)), a.natDegree = 1)
    (hK4 : 4 ≤ Nat.card K) :
    ∀ a ∈ primaryFactors (glA g : Module.End K (Fin N → K)), a ≠ h →
      primaryMultiplicity (glA g : Module.End K (Fin N → K)) a = 1 := by
  classical
  intro a haS hane
  haveI : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors haS⟩
  have hpos : 0 < primaryMultiplicity (glA g : Module.End K (Fin N → K)) a := by
    have hne := primaryComponent_ne_bot hsq haS
    haveI : Nontrivial ↥(primaryComponent (glA g : Module.End K (Fin N → K)) a) :=
      Submodule.nontrivial_iff_ne_bot.mpr hne
    exact Module.finrank_pos
  by_contra hne1
  have hm2a : 2 ≤ primaryMultiplicity (glA g : Module.End K (Fin N → K)) a := by omega
  have hdega : a.natDegree = 1 := hdegS a haS
  have hgooda : IsGoodFactor g a := by
    refine Or.inr ⟨hm2a, ?_⟩
    haveI : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors haS⟩
    calc 4 ≤ Nat.card K := hK4
      _ ≤ Nat.card (AdjoinRoot a) := Nat.card_le_card_of_injective _
        (algebraMap K (AdjoinRoot a)).injective
  have hpF : p ∣ Nat.card (specialFactor g a) :=
    raLin_dvd_card_specialFactor hp hsq haS hdega hm2a hpq
  have hpcenter := CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin.dvd_card_centerQuot_map_of_dvd
    (n := N) hsq haS hgooda hp hpF
  have hpJ : p ∣ Nat.card ((specialFactor g a).map (proj N K)) :=
    hpcenter.trans (Subgroup.card_quotient_dvd_card _)
  have hcompa : CFSG.Open.IsComponentOf ((specialFactor g a).map (proj N K))
      (fixSubgroup (conjAut N K g)) :=
    CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin.isComponentOf_map_specialFactor hsq haS hgooda
  have heqa : (specialFactor g a).map (proj N K) = T := hTonly _ hcompa hpJ
  exact (raLin_components_ne hsq haS hh hane hgood) (heqa.trans hTeq)

theorem raLin_split_card_primaryFactors {p N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hpq : p ∣ Nat.card K - 1)
    {g : GL (Fin N) K} (hg : g ^ p = 1)
    (hsq : Squarefree (minpoly K (glA g : Module.End K (Fin N → K)))) :
    Nat.card (primaryFactors (glA g : Module.End K (Fin N → K))) ≤ p := by
  have hxp : (glA g : Module.End K (Fin N → K)) ^ p = 1 := by
    have h1 : (glA g : LinearMap.GeneralLinearGroup K (Fin N → K)) ^ p = 1 := by
      rw [← map_pow, hg, map_one]
    simpa using congrArg (fun u : LinearMap.GeneralLinearGroup K (Fin N → K) =>
      (u : Module.End K (Fin N → K))) h1
  have hpq' : ¬ p ∣ Nat.card K := by
    intro hd
    have hn1 : 1 ≤ Nat.card K := Nat.card_pos
    have h1 : p ∣ Nat.card K - (Nat.card K - 1) := Nat.dvd_sub hd hpq
    rw [Nat.sub_sub_self hn1] at h1
    exact hp.not_dvd_one h1
  have hle := CFSG.RankThree.PartOne.KCLinComm.card_primaryFactors_le hp hsq hxp hpq'
  have hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 1 := by
    have hn1 : 1 ≤ Nat.card K := Nat.card_pos
    have h0 : ((Nat.card K - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpq
    rw [Nat.cast_sub hn1, Nat.cast_one, sub_eq_zero] at h0
    rw [h0, orderOf_one]
  rw [hord, Nat.div_one] at hle
  have hp1 : 1 ≤ p := hp.one_le
  omega

theorem raLin_split_finrank {N : ℕ} {K : Type} [Field K] [Finite K]
    {g : GL (Fin N) K}
    (hsq : Squarefree (minpoly K (glA g : Module.End K (Fin N → K))))
    {h : K[X]} (hh : h ∈ primaryFactors (glA g : Module.End K (Fin N → K)))
    (hdeg : h.natDegree = 1)
    (hdegS : ∀ a ∈ primaryFactors (glA g : Module.End K (Fin N → K)), a.natDegree = 1)
    (hmult1 : ∀ a ∈ primaryFactors (glA g : Module.End K (Fin N → K)), a ≠ h →
      primaryMultiplicity (glA g : Module.End K (Fin N → K)) a = 1) :
    N = primaryMultiplicity (glA g : Module.End K (Fin N → K)) h +
      ((primaryFactors (glA g : Module.End K (Fin N → K))).card - 1) := by
  classical
  have hsum := finrank_eq_sum_degree_mul_multiplicity (x := (glA g : Module.End K (Fin N → K))) hsq
  have hfinN : Module.finrank K (Fin N → K) = N := by simp
  rw [hfinN] at hsum
  have hsplit : (∑ a : ↥(primaryFactors (glA g : Module.End K (Fin N → K))),
        (a : K[X]).natDegree * primaryMultiplicity (glA g : Module.End K (Fin N → K)) a) =
      primaryMultiplicity (glA g : Module.End K (Fin N → K)) h +
        ((primaryFactors (glA g : Module.End K (Fin N → K))).card - 1) := by
    rw [Finset.sum_coe_sort (primaryFactors (glA g : Module.End K (Fin N → K)))
      (fun a => a.natDegree * primaryMultiplicity (glA g : Module.End K (Fin N → K)) a)]
    rw [← Finset.sum_erase_add (s := primaryFactors (glA g : Module.End K (Fin N → K)))
      (f := fun a => a.natDegree * primaryMultiplicity (glA g : Module.End K (Fin N → K)) a) hh]
    have hcard : ((primaryFactors (glA g : Module.End K (Fin N → K))).erase h).card =
        (primaryFactors (glA g : Module.End K (Fin N → K))).card - 1 :=
      Finset.card_erase_of_mem hh
    have herase : (∑ a ∈ (primaryFactors (glA g : Module.End K (Fin N → K))).erase h,
        (a.natDegree * primaryMultiplicity (glA g : Module.End K (Fin N → K)) a)) =
        ((primaryFactors (glA g : Module.End K (Fin N → K))).erase h).card := by
      have h1 : ∀ a ∈ (primaryFactors (glA g : Module.End K (Fin N → K))).erase h,
          a.natDegree * primaryMultiplicity (glA g : Module.End K (Fin N → K)) a = 1 := by
        intro a ha
        rw [hdegS a (Finset.mem_of_mem_erase ha),
          hmult1 a (Finset.mem_of_mem_erase ha) (Finset.ne_of_mem_erase ha), mul_one]
      rw [Finset.sum_congr rfl h1]
      simp
    rw [herase, hcard, hdeg]
    omega
  rw [hsplit] at hsum
  exact hsum

theorem raLin_split_card_ge_two {N : ℕ} {K : Type} [Field K] [Finite K]
    {g : GL (Fin N) K}
    (hsq : Squarefree (minpoly K (glA g : Module.End K (Fin N → K))))
    {h : K[X]} (hh : h ∈ primaryFactors (glA g : Module.End K (Fin N → K)))
    {ε : K} (hform : h = X - C ε) (hε0 : ε ≠ 0) (hgne : conjAut N K g ≠ 1) :
    2 ≤ (primaryFactors (glA g : Module.End K (Fin N → K))).card := by
  classical
  by_contra hlt
  have hpos : 0 < (primaryFactors (glA g : Module.End K (Fin N → K))).card :=
    Finset.card_pos.mpr ⟨h, hh⟩
  have hcard1 : (primaryFactors (glA g : Module.End K (Fin N → K))).card = 1 := by omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard1
  have hmem : h ∈ ({a} : Finset K[X]) := by rw [← ha]; exact hh
  have hha : h = a := by simpa using hmem
  exact hgne (raLin_conjAut_eq_one_of_single_primaryFactor hsq hh hform hε0 (by rw [ha, hha]))

theorem raLin_split_structure {p N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpk : (p : K) ≠ 0) (hpq : p ∣ Nat.card K - 1)
    {g : GL (Fin N) K} (hg : g ^ p = 1) (hgne : conjAut N K g ≠ 1)
    {T : Subgroup (projectiveSL N K)}
    (hT : CFSG.Open.IsComponentOf T (fixSubgroup (conjAut N K g)))
    (hTonly : ∀ Q : Subgroup (projectiveSL N K),
      CFSG.Open.IsComponentOf Q (fixSubgroup (conjAut N K g)) → p ∣ Nat.card Q → Q = T) :
    ∃ (a : ℕ) (ds : List ℕ) (E : Type) (_ : Field E) (_ : Fintype E),
      Nat.card E = Nat.card K ∧ 2 ≤ a ∧ N = a + ds.sum ∧ ds ≠ [] ∧ ds.length < p ∧
      (∀ x ∈ ds, x = 1) ∧
      Nonempty (↥T ⧸ Subgroup.center ↥T ≃* projectiveSL a E) := by
  classical
  have hsq : Squarefree (minpoly K (glA g : Module.End K (Fin N → K))) :=
    squarefree_minpoly_glA hpk (c := 1) (by simpa using hg)
  obtain ⟨h, ε, hh, hgood, hform, hε0, hdeg, hdegS, -, hK4, -, hTeq⟩ :=
    raLin_split_factor hp hp2 hpk hpq hg hT
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  obtain ⟨hEcard, hm2, ⟨eT⟩⟩ := raLin_split_centralQuot hpk hg hh hgood hdeg hTeq
  have hmult1 := raLin_split_mult_one hp hpq hsq hTonly hh hgood hTeq hdegS hK4
  have hS_card := raLin_split_card_primaryFactors hp hpq hg hsq
  have hN := raLin_split_finrank hsq hh hdeg hdegS hmult1
  have hcard2 := raLin_split_card_ge_two hsq hh hform hε0 hgne
  haveI hEfin : Finite (AdjoinRoot h) := Module.finite_of_finite K
  refine ⟨primaryMultiplicity (glA g : Module.End K (Fin N → K)) h,
    List.replicate ((primaryFactors (glA g : Module.End K (Fin N → K))).card - 1) 1,
    AdjoinRoot h, inferInstance, Fintype.ofFinite (AdjoinRoot h), hEcard, hm2, ?_, ?_, ?_, ?_,
    ⟨eT⟩⟩
  · rw [List.sum_replicate, smul_eq_mul, mul_one]
    exact hN
  · intro hnil
    have h0 : (primaryFactors (glA g : Module.End K (Fin N → K))).card - 1 = 0 := by
      simpa using congrArg List.length hnil
    omega
  · rw [List.length_replicate]
    have hSc : Nat.card ↥(primaryFactors (glA g : Module.End K (Fin N → K))) =
        (primaryFactors (glA g : Module.End K (Fin N → K))).card := by simp
    rw [hSc] at hS_card
    omega
  · intro x hx
    simp only [List.mem_replicate] at hx
    exact hx.2

end Split

theorem raLin_arith {p n : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hKcard : Nat.card K = 2 ^ n) (hpq2 : p ∣ 2 ^ n - 1) :
    p ≠ 2 ∧ (p : K) ≠ 0 ∧ 1 ≤ n ∧ p ∣ Nat.card K - 1 := by
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, pow_zero] at hKcard
      have : 2 ≤ Nat.card K := Nat.succ_le_iff.mpr Finite.one_lt_card
      omega
    · exact h
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hodd : 2 ∣ 2 ^ n - 1 := hpq2
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h1 : 2 ∣ 2 ^ n - (2 ^ n - 1) := Nat.dvd_sub h2 hodd
    have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [Nat.sub_sub_self hpos] at h1
    omega
  haveI hchar : CharP K 2 := charP_two_of_card hKcard
  have hpk : (p : K) ≠ 0 := by
    intro h0
    have h2dvd : 2 ∣ p := (CharP.cast_eq_zero_iff K 2 p).mp h0
    have hp_eq : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2dvd
    exact hp2 hp_eq.symm
  refine ⟨hp2, hpk, hn1, ?_⟩
  rw [hKcard]
  exact hpq2

theorem raLin_two_le_n {p n : ℕ} (hp : p.Prime) (hn1 : 1 ≤ n)
    (hpq : p ∣ 2 ^ n - 1) : 2 ≤ n := by
  by_contra h
  have hn1' : n = 1 := by omega
  rw [hn1', pow_one] at hpq
  have hle := Nat.le_of_dvd (by norm_num) hpq
  have hp2 : 2 ≤ p := hp.two_le
  omega

theorem raLin_conjAut_ne_one {p : ℕ} {X : Type} [Group X] [Finite X]
    {A : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hloc : GGTPNLocalCore p A σ J) {N : ℕ} {K : Type} [Field K]
    {θ : X ⧸ Subgroup.center X ≃* projectiveSL N K} {g : GL (Fin N) K}
    (hcomm : commutator X = ⊤) (hσbar : ggInducedAut θ σ = conjAut N K g) :
    conjAut N K g ≠ 1 := by
  intro h1
  have hσ1 : ggInducedAut θ σ = 1 := hσbar.trans h1
  have hinj := ggInducedAut_injective_of_perfect hcomm θ
  exact hloc.2.2.1 (hinj (by rw [hσ1, map_one]))

theorem raLin_descent {p : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X]
    {σ : MulAut X} {J : Subgroup X}
    (hcomm : commutator X = ⊤) (hJ : IsComponentOf J (ggAutFixedSubgroup σ))
    (h8 : GGTPNOnlyComp p σ J) {N : ℕ} {K : Type} [Field K] [Finite K]
    {θ : X ⧸ Subgroup.center X ≃* projectiveSL N K} {g : GL (Fin N) K}
    (hσbar : ggInducedAut θ σ = conjAut N K g) :
    ∃ Jbar : Subgroup (projectiveSL N K),
      CFSG.Open.IsComponentOf Jbar (fixSubgroup (conjAut N K g)) ∧
      (∀ Q : Subgroup (projectiveSL N K),
        CFSG.Open.IsComponentOf Q (fixSubgroup (conjAut N K g)) → p ∣ Nat.card Q → Q = Jbar) ∧
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥Jbar ⧸ Subgroup.center ↥Jbar) := by
  obtain ⟨hJbar, huniq, hequiv⟩ :=
    ggTPNOnlyComp_map_proj (p := p) hcomm hJ h8 (R := projectiveSL N K) θ
  refine ⟨J.map (TablePThreeKG.proj θ), ?_, ?_, hequiv⟩
  · have h1 : CFSG.Assembly.IsComponentOf (J.map (TablePThreeKG.proj θ))
        (ggAutFixedSubgroup (ggInducedAut θ σ)) := hJbar
    have h2 := CFSG.Assembly.isComponentOf_iff_open.mp h1
    rwa [hσbar] at h2
  · intro Q hQ hpQ
    refine huniq Q ?_ hpQ
    have h2 : CFSG.Assembly.IsComponentOf Q (ggAutFixedSubgroup (ggInducedAut θ σ)) := by
      rw [hσbar]
      exact CFSG.Assembly.isComponentOf_iff_open.mpr hQ
    exact h2

theorem raLin_rescale {p N : ℕ} {K : Type} [Field K] {g : GL (Fin N) K} {u : Kˣ}
    (hp : p.Prime) (hg : g ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) u)
    (hb : ∃ b : K, b ^ p = (u : K)) :
    ∃ g' : GL (Fin N) K, g' ^ p = 1 ∧ conjAut N K g' = conjAut N K g := by
  obtain ⟨b, hb⟩ := hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    have h0 : (0 : K) ^ p = (u : K) := hb
    rw [zero_pow hp.ne_zero] at h0
    exact u.ne_zero h0.symm
  let bu : Kˣ := Units.mk0 b hb0
  have hbu : (bu : K) = b := rfl
  refine ⟨(Matrix.GeneralLinearGroup.scalar (Fin N) bu)⁻¹ * g, ?_, ?_⟩
  · have hc : Commute (Matrix.GeneralLinearGroup.scalar (Fin N) bu) g :=
      TypeA.PGLTor.scalar_mul_comm bu g
    have hu' : (Matrix.GeneralLinearGroup.scalar (Fin N) bu) ^ p =
        Matrix.GeneralLinearGroup.scalar (Fin N) u := by
      rw [← map_pow]
      congr 1
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hbu, hb]
    rw [Commute.mul_pow hc.inv_left, inv_pow, hu', hg, inv_mul_cancel]
  · rw [map_mul, map_inv, conjAut_scalar, inv_one, one_mul]

theorem raLin_split_label {N : ℕ} {K : Type} [Field K] [Finite K]
    {X : Type} [Group X] {J : Subgroup X} {Jbar : Subgroup (projectiveSL N K)}
    {labX : LargeEvenLabel} {a : ℕ} (hn1 : 1 ≤ labX.n) (hn2 : 2 ≤ labX.n) (ha2 : 2 ≤ a)
    {E : Type} [Field E] [Finite E] (hE : Nat.card E = 2 ^ labX.n)
    (eJZ : ↥J ⧸ Subgroup.center ↥J ≃* ↥Jbar ⧸ Subgroup.center ↥Jbar)
    (eT : ↥Jbar ⧸ Subgroup.center ↥Jbar ≃* projectiveSL a E) :
    LargeEvenInLambda2 ⟨.A, a - 1, labX.n⟩ ∧
      GGHasLabel ⟨.A, a - 1, labX.n⟩ (↥J ⧸ Subgroup.center ↥J) := by
  have ha1 : 1 ≤ a := by omega
  have hsub : a - 1 + 1 = a := Nat.sub_add_cancel ha1
  have hΛ : LargeEvenInLambda2 ⟨.A, a - 1, labX.n⟩ := by
    refine ⟨hn1, ?_, ?_⟩
    · show 1 ≤ a - 1
      omega
    · show a - 1 = 1 → 2 ≤ labX.n
      intro _
      exact hn2
  refine ⟨hΛ, ?_⟩
  rw [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum]
  simp only [LargeEvenRecipeLinear]
  rw [hsub]
  exact ⟨E, inferInstance, inferInstance, hE,
    ⟨(eJZ.trans eT).trans (TypeA.recipeEquiv a E).symm⟩⟩

theorem raLin_split_case {p N : ℕ} {X : Type} [Group X] [Finite X]
    {J : Subgroup X} {K : Type} [Field K] [Finite K] {labX : LargeEvenLabel}
    (hA : labX.tag = .A) (hn1 : 1 ≤ labX.n) (hn2 : 2 ≤ labX.n)
    (hKcard : Nat.card K = 2 ^ labX.n)
    {g : GL (Fin N) K} {u : Kˣ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpk : (p : K) ≠ 0) (hpq : p ∣ Nat.card K - 1)
    (hgu : g ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) u)
    (hb : ∃ b : K, b ^ p = (u : K))
    {Jbar : Subgroup (projectiveSL N K)}
    (hJbarOpen : CFSG.Open.IsComponentOf Jbar (fixSubgroup (conjAut N K g)))
    (huniq : ∀ Q : Subgroup (projectiveSL N K),
      CFSG.Open.IsComponentOf Q (fixSubgroup (conjAut N K g)) → p ∣ Nat.card Q → Q = Jbar)
    (hgne : conjAut N K g ≠ 1)
    (hequiv : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥Jbar ⧸ Subgroup.center ↥Jbar)) :
    ∃ (a : ℕ) (ds : List ℕ), N = a + ds.sum ∧ ds ≠ [] ∧ ds.length < p ∧
      (∀ x ∈ ds, x = 1) ∧ LargeEvenInLambda2 ⟨.A, a - 1, labX.n⟩ ∧
      GGHasLabel ⟨.A, a - 1, labX.n⟩ (↥J ⧸ Subgroup.center ↥J) := by
  obtain ⟨g', hgp', hconj'⟩ := raLin_rescale hp hgu hb
  have hgne' : conjAut N K g' ≠ 1 := by rw [hconj']; exact hgne
  have hJbarOpen' : CFSG.Open.IsComponentOf Jbar (fixSubgroup (conjAut N K g')) := by
    rw [hconj']; exact hJbarOpen
  have huniq' : ∀ Q : Subgroup (projectiveSL N K),
      CFSG.Open.IsComponentOf Q (fixSubgroup (conjAut N K g')) → p ∣ Nat.card Q → Q = Jbar := by
    rw [hconj']; exact huniq
  obtain ⟨a, ds, E, hEfld, hEfin, hEcard, ha2, hN, hdsne, hdslt, hds1, ⟨eT⟩⟩ :=
    raLin_split_structure (N := N) hp hp2 hpk hpq hgp' hgne' hJbarOpen' huniq'
  letI : Field E := hEfld
  haveI : Fintype E := hEfin
  have hEcard' : Nat.card E = 2 ^ labX.n := by rw [hEcard, hKcard]
  obtain ⟨eJZ⟩ := hequiv
  obtain ⟨hΛ, hlabJ⟩ := raLin_split_label (J := J) (Jbar := Jbar) hn1 hn2 ha2 hEcard' eJZ eT
  exact ⟨a, ds, hN, hdsne, hdslt, hds1, hΛ, hlabJ⟩

theorem raLin_nonSplit_bound {p N : ℕ} {K : Type} [Field K] [Finite K]
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hloc : GGTPNLocalCore p A σ J) (hp : p.Prime) (hp2 : p ≠ 2) (hN : 0 < N)
    (hpq : p ∣ Nat.card K - 1) {g : GL (Fin N) K} {u : Kˣ}
    (hgu : g ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) u)
    (hc : ∀ b : K, b ^ p ≠ (u : K))
    {θ : X ⧸ Subgroup.center X ≃* projectiveSL N K}
    (hAll : ∀ a ∈ A, ∃ B : GL (Fin N) K, ∀ l : X,
      conjAut N K B (θ (l : X ⧸ Subgroup.center X)) = θ ((a l : X) : X ⧸ Subgroup.center X))
    (hcomm : commutator X = ⊤) (hσbar : ggInducedAut θ σ = conjAut N K g) :
    Nat.card A ≤ p ^ (N / p + 1) := by
  have hXcard : Nat.card (A.map (ggInducedAut θ)) = Nat.card A :=
    Subgroup.card_map_of_injective (ggInducedAut_injective_of_perfect hcomm θ)
  have hXeab : IsElemAbelian p (A.map (ggInducedAut θ)) :=
    tpta_isElemAbelian_map_ggInducedAut θ hloc.1
  have hXr : ∀ x ∈ A.map (ggInducedAut θ), x ∈ Set.range (conjAut N K) := by
    intro x hx
    obtain ⟨af, haf, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨B, hB⟩ := hAll af haf
    refine ⟨B, ?_⟩
    ext y
    obtain ⟨z, rfl⟩ := θ.surjective y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    rw [ggInducedAut_apply]
    exact hB l
  have hgG : conjAut N K g ∈ A.map (ggInducedAut θ) := by
    rw [← hσbar]
    exact Subgroup.mem_map_of_mem _ hloc.2.1
  have h := raLin_card_le_nonSplit (N := N) hp hp2 hpq hN hgu hc hXeab hXr hgG
  rwa [hXcard] at h

theorem raLin_nonSplit_label {p N : ℕ} {K : Type} [Field K] [Finite K]
    {X : Type} [Group X] {J : Subgroup X} {Jbar : Subgroup (projectiveSL N K)}
    {labX : LargeEvenLabel} (hn1 : 1 ≤ labX.n) (hp : p.Prime) (hpN2 : 2 ≤ N / p)
    {E : Type} [Field E] [Finite E] (hE : Nat.card E = 2 ^ (p * labX.n))
    (eJZ : ↥J ⧸ Subgroup.center ↥J ≃* ↥Jbar ⧸ Subgroup.center ↥Jbar)
    (eT : ↥Jbar ⧸ Subgroup.center ↥Jbar ≃* projectiveSL (N / p) E) :
    LargeEvenInLambda2 ⟨.A, N / p - 1, p * labX.n⟩ ∧
      GGHasLabel ⟨.A, N / p - 1, p * labX.n⟩ (↥J ⧸ Subgroup.center ↥J) := by
  have hsub : N / p - 1 + 1 = N / p := Nat.sub_add_cancel (by omega)
  have h1n : 1 ≤ p * labX.n := by
    have := Nat.mul_pos hp.pos hn1
    omega
  have hrnk : 1 ≤ N / p - 1 := by omega
  have hΛ : LargeEvenInLambda2 ⟨.A, N / p - 1, p * labX.n⟩ := by
    refine ⟨h1n, hrnk, ?_⟩
    show N / p - 1 = 1 → 2 ≤ p * labX.n
    intro _
    calc 2 ≤ p := hp.two_le
      _ = p * 1 := (mul_one p).symm
      _ ≤ p * labX.n := Nat.mul_le_mul_left p hn1
  refine ⟨hΛ, ?_⟩
  rw [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum]
  simp only [LargeEvenRecipeLinear]
  rw [hsub]
  exact ⟨E, inferInstance, inferInstance, hE,
    ⟨(eJZ.trans eT).trans (TypeA.recipeEquiv (N / p) E).symm⟩⟩

theorem raLin_nonSplit_case {p N : ℕ} {X : Type} [Group X] [Finite X]
    {A : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    {K : Type} [Field K] [Finite K] {labX : LargeEvenLabel} (hn1 : 1 ≤ labX.n)
    (hKcard : Nat.card K = 2 ^ labX.n)
    {g : GL (Fin N) K} {u : Kˣ}
    (hloc : GGTPNLocalCore p A σ J) (hp : p.Prime) (hp2 : p ≠ 2) (hN : 0 < N)
    (hpk : (p : K) ≠ 0) (hpq : p ∣ Nat.card K - 1)
    (hgu : g ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) u)
    (hc : ∀ b : K, b ^ p ≠ (u : K))
    {θ : X ⧸ Subgroup.center X ≃* projectiveSL N K}
    (hAll : ∀ a ∈ A, ∃ B : GL (Fin N) K, ∀ l : X,
      conjAut N K B (θ (l : X ⧸ Subgroup.center X)) = θ ((a l : X) : X ⧸ Subgroup.center X))
    (hcomm : commutator X = ⊤) (hσbar : ggInducedAut θ σ = conjAut N K g)
    {Jbar : Subgroup (projectiveSL N K)}
    (hJbarOpen : CFSG.Open.IsComponentOf Jbar (fixSubgroup (conjAut N K g)))
    (hequiv : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥Jbar ⧸ Subgroup.center ↥Jbar)) :
    2 ≤ N / p ∧ Nat.card A ≤ p ^ (N / p + 1) ∧
      LargeEvenInLambda2 ⟨.A, N / p - 1, p * labX.n⟩ ∧
      GGHasLabel ⟨.A, N / p - 1, p * labX.n⟩ (↥J ⧸ Subgroup.center ↥J) := by
  obtain ⟨hpN2, E, hEfld, hEfin, hEcard, ⟨eT⟩⟩ :=
    raLin_nonSplit_component (N := N) hp hp2 hpk hgu hc hJbarOpen
  letI : Field E := hEfld
  haveI : Fintype E := hEfin
  have hEcard' : Nat.card E = 2 ^ (p * labX.n) := by
    rw [hEcard, hKcard, ← pow_mul, Nat.mul_comm]
  obtain ⟨eJZ⟩ := hequiv
  obtain ⟨hΛ, hlabJ⟩ := raLin_nonSplit_label (J := J) (Jbar := Jbar) hn1 hp hpN2 hEcard' eJZ eT
  exact ⟨hpN2, raLin_nonSplit_bound hloc hp hp2 hN hpq hgu hc hAll hcomm hσbar, hΛ, hlabJ⟩

theorem split_or_fieldType_of_ggKacRA_linear {p : ℕ} (hp : p.Prime) {X : Type} [Group X] [Finite X]
    {A : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hloc : GGTPNLocalCore p A σ J) (h8 : GGTPNOnlyComp p σ J) {labX : LargeEvenLabel}
    (hA : labX.tag = .A) (hRA : GGKacRA labX p) (hm : GGTPNMarked p (fun _ lab => lab = labX) A) :
    (∃ (a : ℕ) (ds : List ℕ), labX.rank + 1 = a + ds.sum ∧ ds ≠ [] ∧ ds.length < p ∧
        (∀ x ∈ ds, x = 1 ∨ (labX.tag = .twA ∧ labX.n = 1 ∧ (x = 2 ∨ x = 3))) ∧
        ((LargeEvenInLambda2 ⟨labX.tag, a - 1, labX.n⟩ ∧
            GGHasLabel ⟨labX.tag, a - 1, labX.n⟩ (↥J ⧸ Subgroup.center ↥J)) ∨
          (labX.tag = .twA ∧ a = 2 ∧ LargeEvenInLambda2 ⟨.A, 1, labX.n⟩ ∧
            GGHasLabel ⟨.A, 1, labX.n⟩ (↥J ⧸ Subgroup.center ↥J)))) ∨
    (2 ≤ (labX.rank + 1) / p ∧ Nat.card A ≤ p ^ ((labX.rank + 1) / p + 1) ∧
      (((labX.tag = .A ∨ (labX.rank + 1) / p = 2) ∧
          LargeEvenInLambda2 ⟨.A, (labX.rank + 1) / p - 1, p * labX.n⟩ ∧
          GGHasLabel ⟨.A, (labX.rank + 1) / p - 1, p * labX.n⟩ (↥J ⧸ Subgroup.center ↥J)) ∨
        (labX.tag = .twA ∧ 3 ≤ (labX.rank + 1) / p ∧
          LargeEvenInLambda2 ⟨.twA, (labX.rank + 1) / p - 1, p * labX.n⟩ ∧
          GGHasLabel ⟨.twA, (labX.rank + 1) / p - 1, p * labX.n⟩
            (↥J ⧸ Subgroup.center ↥J)))) := by
  classical
  obtain ⟨K, hFld, hFin, hKcard, θ, hAll, g, ⟨u, hgu⟩, hgl, hcomm⟩ := raLin_model hp hloc hA hm
  letI : Field K := hFld
  haveI : Finite K := hFin
  let N : ℕ := labX.rank + 1
  rcases hRA with ⟨-, hpN, hpq2⟩ | ⟨htw, -⟩
  · obtain ⟨hp2, hpk, hn1, hpq⟩ := raLin_arith (K := K) hp hKcard hpq2
    have hn2 := raLin_two_le_n hp hn1 hpq2
    haveI : Fact p.Prime := ⟨hp⟩
    have hJcomp : IsComponentOf J (ggAutFixedSubgroup σ) := hloc.2.2.2.1
    have hσbar : ggInducedAut θ σ = conjAut N K g := by
      ext x
      obtain ⟨z, rfl⟩ := θ.surjective x
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
      rw [ggInducedAut_apply, hgl]
    have hgne := raLin_conjAut_ne_one (N := N) hloc hcomm hσbar
    obtain ⟨Jbar, hJbarOpen, huniq, hequiv⟩ :=
      raLin_descent (p := p) hcomm hJcomp h8 (N := N) hσbar
    by_cases hsplit : ∃ b : K, b ^ p = (u : K)
    · obtain ⟨a, ds, hN, hdsne, hdslt, hds1, hΛ, hlabJ⟩ :=
        raLin_split_case (N := N) (J := J) hA hn1 hn2 hKcard hp hp2 hpk hpq hgu hsplit
          hJbarOpen huniq hgne hequiv
      refine Or.inl ⟨a, ds, ?_, hdsne, hdslt, ?_, Or.inl ?_⟩
      · rw [show labX.rank + 1 = N from rfl]
        exact hN
      · intro x hx
        exact Or.inl (hds1 x hx)
      · rw [hA]
        exact ⟨hΛ, hlabJ⟩
    · have hc : ∀ b : K, b ^ p ≠ (u : K) := fun b hb => hsplit ⟨b, hb⟩
      obtain ⟨hpN2, hbound, hΛ, hlabJ⟩ :=
        raLin_nonSplit_case (N := N) (A := A) (J := J) hn1 hKcard hloc hp hp2
          (Nat.succ_pos labX.rank) hpk hpq hgu hc hAll hcomm hσbar hJbarOpen hequiv
      refine Or.inr ⟨?_, ?_, Or.inl ⟨Or.inl hA, ?_, ?_⟩⟩
      · rw [show labX.rank + 1 = N from rfl]
        exact hpN2
      · rw [show labX.rank + 1 = N from rfl]
        exact hbound
      · rw [show labX.rank + 1 = N from rfl]
        exact hΛ
      · rw [show labX.rank + 1 = N from rfl]
        exact hlabJ
  · rw [hA] at htw
    exact absurd htw (by simp)

end CFSG.StandardType

end
