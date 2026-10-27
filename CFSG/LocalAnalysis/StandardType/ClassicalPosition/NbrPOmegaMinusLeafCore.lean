module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Position
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualPOmegaMinus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualTwoPOmegaMinus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelDualPairPOmegaMinus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoRootConversePOmegaMinus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockRankDvd
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepACore
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPOmegaMinus
public import CFSG.LieType.Universal.Spin.Twisted.Datum
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompPOmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2POmegaPosDefs

public section

namespace CFSG.StandardType.ClassicalPosition.NbrLeaf

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.ClassicalPosition

open scoped commutatorElement

local notation "Ix" n:max => (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
local notation "Mx" n:max f:max => Matrix (Ix n) (Ix n) (GaloisField 2 f)
set_option quotPrecheck false in
local notation "UK" n:max f:max => (ggU .POmegaMinus n f).K
set_option quotPrecheck false in
local notation "ρm" n:max f:max => Spin.spinMatrix
  (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
set_option quotPrecheck false in
local notation "Gm" n:max f:max => LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin
  (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))
local notation "AdS" f:max S:max => Algebra.adjoin (GaloisField 2 f) (Units.val '' S)
local notation "Fadj" n:max f:max e:max => formAdj (RingHom.id (GaloisField 2 f)) (Gm n f) e
local notation "BlkC" n:max f:max S:max ε:max =>
  (glBlockCentralizer (ρm n f) S ε : Subgroup (UK n f))
local notation "rk" f:max e:max =>
  Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e))

section Vocabulary

@[expose] def SetD {X : Type} [Group X] (n f : ℕ) (ψ : UK n f →* X) (J : Subgroup X)
    (S : Set (GL (Ix n) (GaloisField 2 f))) (J' : Subgroup (UK n f)) : Prop :=
  (∀ s ∈ S, s ∈ (ρm n f).range) ∧ (∀ s ∈ S, ∀ s' ∈ S, Commute s s') ∧
    (∀ s ∈ S, Odd (orderOf s)) ∧ IsComponentOf J' ((Subgroup.centralizer S).comap (ρm n f)) ∧
    J'.map ψ = J
@[expose] def FullD {X : Type} [Group X] (n f : ℕ) (ψ : UK n f →* X) (D : Subgroup X)
    (S : Set (GL (Ix n) (GaloisField 2 f))) : Prop :=
  ∀ s : GL (Ix n) (GaloisField 2 f), s ∈ (ρm n f).range →
    (∃ d ∈ D, IsGLLift (ρm n f) ψ s d) → s ∈ S
@[expose] def EpsD (n f : ℕ) (S : Set (GL (Ix n) (GaloisField 2 f))) (J' : Subgroup (UK n f))
    (ε : Mx n f) : Prop :=
  IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f)) (Gm n f) (AdS f S) ε ∧
    IsComponentOf J' ⁅BlkC n f S ε, BlkC n f S ε⁆
@[expose] def SplitD (n f : ℕ) (ε e : Mx n f) : Prop :=
  e = ε ∨ (e ≠ ε ∧ Fadj n f e ≠ e ∧ ε = e + Fadj n f e)
@[expose] def OrthOut {X : Type} [Group X] (f : ℕ) (K R : Subgroup X) (a : ℕ) : Prop :=
  ∃ (t : StatedLieTag) (m : ℕ) (β : Fin (ggU t m f).D.rank → ℤ),
    (t = .POmegaPlus ∨ t = .POmegaMinus) ∧ 3 ≤ m ∧ a ≤ m ∧ β ∈ (ggU t m f).D.roots ∧
    GGLongRoot (ggU t m f).D β ∧ GGRootVia (ggU t m f) K R β

end Vocabulary

lemma nbrpom_isUnit_det {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) :
    IsUnit (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).det := by
  have h1 : (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) =
      LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q) := rfl
  rw [h1]
  exact isUnit_iff_ne_zero.mpr (Matrix.nondegenerate_iff_det_ne_zero.mp
    ((LinearMap.BilinForm.nondegenerate_toMatrix'_iff).mpr hnd))

lemma nbrpom_polar_matrix_transpose_eq {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] (Q : QuadraticForm F (ι → F)) :
    Matrix.transpose (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) =
      LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q) := by
  ext i j
  simp only [Matrix.transpose_apply, LinearMap.toMatrix₂'_apply,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]

lemma nbrpom_spinMatrix_gram {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [CharP F 2] (Q : QuadraticForm F (ι → F)) (g : spinGroup Q) :
    Matrix.transpose ((Spin.spinMatrix Q g) : Matrix ι ι F) *
      LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q) *
      ((Spin.spinMatrix Q g) : Matrix ι ι F) =
        LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q) := by
  let B : LinearMap.BilinForm F (ι → F) := QuadraticMap.polarBilin Q
  let l : (ι → F) →ₗ[F] (ι → F) := ((Spin.spinAction Q g) : (ι → F) →ₗ[F] (ι → F))
  have h1 : (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) =
      LinearMap.BilinForm.toMatrix' B := rfl
  have h2 : ((Spin.spinMatrix Q g) : Matrix ι ι F) = LinearMap.toMatrix' l :=
    Spin.coe_spinMatrix Q g
  rw [h1, h2]
  have hisom : B.comp l l = B := by
    apply LinearMap.ext; intro x
    apply LinearMap.ext; intro y
    change LinearMap.BilinForm.comp B l l x y = B x y
    rw [LinearMap.BilinForm.comp_apply]
    exact Spin.polar_spinAction Q g x y
  have h := LinearMap.BilinForm.toMatrix'_comp B l l
  rw [hisom] at h
  exact h.symm

lemma nbrpom_rank_le_two_of_mulVec_mem {ι : Type} [Fintype ι] {F : Type} [Field F]
    [DecidableEq F]
    (A : Matrix ι ι F) (a₁ a₂ : ι → F)
    (h : ∀ x, Matrix.mulVec A x ∈ Submodule.span F ({a₁, a₂} : Set (ι → F))) :
    Matrix.rank A ≤ 2 := by
  have hrange : A.mulVecLin.range ≤ Submodule.span F ({a₁, a₂} : Set (ι → F)) := by
    rintro y ⟨x, rfl⟩
    simpa [Matrix.mulVecLin_apply] using h x
  have h1 : Module.finrank F ↥(A.mulVecLin.range) ≤
      Module.finrank F ↥(Submodule.span F ({a₁, a₂} : Set (ι → F))) :=
    Submodule.finrank_mono hrange
  have h2 : Module.finrank F ↥(Submodule.span F ({a₁, a₂} : Set (ι → F))) ≤ 2 := by
    have hc := finrank_span_le_card (R := F) ({a₁, a₂} : Set (ι → F))
    refine le_trans hc ?_
    rw [show ({a₁, a₂} : Set (ι → F)).toFinset = ({a₁, a₂} : Finset (ι → F)) by simp]
    exact le_trans (Finset.card_insert_le a₁ {a₂}) (by simp)
  rw [Matrix.rank]
  exact le_trans h1 h2

lemma nbrpom_rank_pos {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {M : Matrix ι ι F} (hM : M ≠ 1) : 1 ≤ Matrix.rank (M - 1) := by
  have hAne : M - 1 ≠ 0 := by
    intro h0; exact hM (sub_eq_zero.mp h0)
  have hrange_ne : (M - 1).mulVecLin.range ≠ ⊥ := by
    intro hbot
    apply hAne
    ext i j
    have hmem : (M - 1).mulVec (Pi.single j 1) ∈ (M - 1).mulVecLin.range :=
      LinearMap.mem_range.mpr ⟨Pi.single j 1, rfl⟩
    rw [hbot] at hmem
    have hz : (M - 1).mulVec (Pi.single j 1) = 0 := by simpa using hmem
    have := congrFun hz i
    simpa [Matrix.mulVec_single_one, Matrix.col_apply] using this
  rw [Matrix.rank, Nat.one_le_iff_ne_zero]
  intro hzero
  exact hrange_ne (Submodule.finrank_eq_zero.mp hzero)

@[expose] def nbrpom_HasShortElm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (R' : Subgroup (spinGroup Q)) : Prop :=
  ∃ g ∈ R', g ≠ 1 ∧
    Matrix.rank (((Spin.spinMatrix Q g) : Matrix ι ι F) - 1) ≤ 2

lemma nbrpom_eichler_ne_one {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [CharP F 2] (Q : QuadraticForm F (ι → F))
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (a₁ a₂ : ι → F) (ha₁ : a₁ ≠ 0) (hli : LinearIndependent F ![a₁, a₂])
    (hQ₁ : Q a₁ = 0) (hQ₂ : Q a₂ = 0)
    (horth : QuadraticMap.polar Q a₁ a₂ = 0) :
    CFSG.ClassicalGroups.Orthogonal.eichler Q a₁ a₂ ≠ 1 := by
  intro h1
  have hker : LinearMap.ker (QuadraticMap.polarBilin Q) = ⊥ :=
    LinearMap.BilinForm.Nondegenerate.ker_eq_bot hnd
  have hx : ∃ x, QuadraticMap.polar Q x a₁ ≠ 0 := by
    by_contra h
    push Not at h
    have hmem : a₁ ∈ LinearMap.ker (QuadraticMap.polarBilin Q) := by
      rw [LinearMap.mem_ker]
      apply LinearMap.ext; intro y
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
      exact h y
    have hzero : a₁ = 0 := by
      have hbot : a₁ ∈ (⊥ : Submodule F (ι → F)) := hker ▸ hmem
      simpa using hbot
    exact ha₁ hzero
  obtain ⟨x, hx⟩ := hx
  have hxeq : CFSG.ClassicalGroups.Orthogonal.eichler Q a₁ a₂ x = x := by rw [h1]; rfl
  rw [CFSG.ClassicalGroups.Orthogonal.eichler_apply hQ₁ horth x] at hxeq
  simp only [hQ₂, zero_mul, add_zero] at hxeq
  have hsub : QuadraticMap.polar Q x a₁ • a₂ - QuadraticMap.polar Q x a₂ • a₁ = 0 := by
    have h2 : x + (QuadraticMap.polar Q x a₁ • a₂ -
        QuadraticMap.polar Q x a₂ • a₁) = x + 0 := by
      rw [add_zero]
      conv_rhs => rw [← hxeq]
      abel
    exact add_left_cancel h2
  have hAB : QuadraticMap.polar Q x a₁ • a₂ = QuadraticMap.polar Q x a₂ • a₁ :=
    sub_eq_zero.mp hsub
  have hzero : QuadraticMap.polar Q x a₂ • a₁ + QuadraticMap.polar Q x a₁ • a₂ = 0 := by
    rw [hAB]
    rw [← add_smul, CharTwo.add_self_eq_zero (QuadraticMap.polar Q x a₂), zero_smul]
  have hcon := (LinearIndependent.pair_iff.mp hli) (QuadraticMap.polar Q x a₂)
    (QuadraticMap.polar Q x a₁) hzero
  exact hx hcon.2

theorem nbrpom_siegel_shortElm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [CharP F 2] (Q : QuadraticForm F (ι → F))
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (R' : Subgroup (spinGroup Q)) (a₁ a₂ : ι → F)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (hli : LinearIndependent F ![a₁, a₂])
    (hQ₁ : Q a₁ = 0) (hQ₂ : Q a₂ = 0)
    (horth : QuadraticMap.polar Q a₁ a₂ = 0)
    (hm : siegelGroup Q a₁ a₂ ≤ R'.map (Spin.spinAction Q)) :
    nbrpom_HasShortElm Q R' := by
  classical
  let g₀ := CFSG.ClassicalGroups.Orthogonal.eichler Q a₁ a₂
  have hg₀mem : g₀ ∈ siegelGroup Q a₁ a₂ := by
    refine Subgroup.subset_closure ⟨1, ?_⟩
    rw [one_smul]
  have hg₀R : g₀ ∈ R'.map (Spin.spinAction Q) := hm hg₀mem
  obtain ⟨g, hgR, hgval⟩ := Subgroup.mem_map.mp hg₀R
  have hgne : g ≠ 1 := by
    intro hg1
    apply nbrpom_eichler_ne_one Q hnd a₁ a₂ ha₁ hli hQ₁ hQ₂ horth
    have h := hgval
    rw [hg1, map_one] at h
    exact h.symm
  refine ⟨g, hgR, hgne, ?_⟩
  apply nbrpom_rank_le_two_of_mulVec_mem _ a₁ a₂
  intro x
  have hx : (((Spin.spinMatrix Q g) : Matrix ι ι F)).mulVec x = g₀ x := by
    rw [Spin.spinMatrix_mulVec, hgval]
  have hsub : ((((Spin.spinMatrix Q g) : Matrix ι ι F) - 1)).mulVec x = g₀ x - x := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hx]
  rw [hsub]
  obtain ⟨a, b, hab⟩ := CFSG.ClassicalGroups.Orthogonal.eichler_apply_eq_add (Q := Q) a₁ a₂ x
  have hg₀eq : g₀ = CFSG.ClassicalGroups.Orthogonal.eichler Q a₁ a₂ := rfl
  rw [hg₀eq, hab]
  have hmove : x + a • a₂ + b • a₁ - x = a • a₂ + b • a₁ := by abel
  rw [hmove]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

lemma nbrpom_formAdj_id {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (G a : Matrix ι ι F) : formAdj (RingHom.id F) G a = G⁻¹ * a.transpose * G := by
  unfold formAdj
  rw [show a.map (⇑(RingHom.id F)) = a from by ext i j; rfl]

lemma nbrpom_formAdj_neg {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (σ : F →+* F) (G a : Matrix ι ι F) : formAdj σ G (-a) = -formAdj σ G a := by
  have h : formAdj σ G (-a) + formAdj σ G a = 0 := by
    rw [← Geo.formAdj_add, neg_add_cancel]
    unfold formAdj
    rw [Matrix.map_zero σ (map_zero σ), Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul]
  exact eq_neg_of_add_eq_zero_left h

lemma nbrpom_polar_eq_dot {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (x y : ι → F) :
    QuadraticMap.polar Q x y =
      dotProduct x ((LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).mulVec y) := by
  have h1 : (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) =
      LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q) := rfl
  rw [h1]
  rw [← Matrix.toBilin'_apply' (LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q)) x y,
    Matrix.toBilin'_toMatrix', QuadraticMap.polarBilin_apply_apply]

lemma nbrpom_dotProduct_mulVec_transpose {ι F : Type} [Fintype ι] [CommSemiring F]
    (M : Matrix ι ι F) (x y : ι → F) :
    dotProduct (M.mulVec x) y = dotProduct x (M.transpose.mulVec y) := by
  exact ((Matrix.dotProduct_mulVec x M.transpose y).trans
    (by rw [Matrix.vecMul_transpose])).symm

lemma nbrpom_formAdj_mulVec {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {G a : Matrix ι ι F} (hG : IsUnit G.det) (y : ι → F) :
    G.mulVec ((formAdj (RingHom.id F) G a).mulVec y) = a.transpose.mulVec (G.mulVec y) := by
  have hmat : G * (G⁻¹ * a.transpose * G) = a.transpose * G := by
    rw [← Matrix.mul_assoc G (G⁻¹ * a.transpose) G,
      ← Matrix.mul_assoc G G⁻¹ a.transpose, Matrix.mul_nonsing_inv G hG, Matrix.one_mul]
  rw [nbrpom_formAdj_id, Matrix.mulVec_mulVec, hmat, Matrix.mulVec_mulVec]

lemma nbrpom_formAdj_apply {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F))
    (hG : IsUnit (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).det)
    (a : Matrix ι ι F) (x y : ι → F) :
    QuadraticMap.polar Q (a.mulVec x) y =
      QuadraticMap.polar Q x ((formAdj (RingHom.id F)
        (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) a).mulVec y) := by
  rw [nbrpom_polar_eq_dot Q, nbrpom_polar_eq_dot Q,
    nbrpom_dotProduct_mulVec_transpose a x
      ((LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).mulVec y),
    nbrpom_formAdj_mulVec hG y]

lemma nbrpom_polar_selfAdjoint {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F))
    (hG : IsUnit (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).det)
    {E : Matrix ι ι F}
    (hE : formAdj (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) E = E) (x y : ι → F) :
    QuadraticMap.polar Q (E.mulVec x) y = QuadraticMap.polar Q x (E.mulVec y) := by
  rw [nbrpom_formAdj_apply Q hG E x y, hE]

lemma nbrpom_spinMatrix_injective (n f : ℕ) :
    Function.Injective (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  exact Spin.ker_spinMatrix_quadMinus_eq_bot (minusCoeffs_irr 2 f) CharTwo.two_eq_zero

lemma nbrpom_spinAction_injective (n f : ℕ) :
    Function.Injective (Spin.spinAction (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) := by
  have hinj := nbrpom_spinMatrix_injective n f
  have hcomp : (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
        (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) :
      ↥(spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
        (minusCoeffs 2 f).2)) →*
      GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f)) =
      ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv
        (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f)).symm.toMonoidHom.comp
        (Spin.spinAction (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
          (minusCoeffs 2 f).2))) := Spin.spinMatrix_eq_comp _
  intro x y hxy
  apply hinj
  rw [hcomp, MonoidHom.comp_apply, MonoidHom.comp_apply, hxy]

lemma nbrpom_map_spinAction_injective {n f : ℕ}
    {A B : Subgroup (spinGroup (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))}
    (h : A.map (Spin.spinAction (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) =
      B.map (Spin.spinAction (Spin.quadMinus n (GaloisField 2 f)
        (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) : A = B :=
  Subgroup.map_injective (nbrpom_spinAction_injective n f) h

lemma nbrpom_center_bot (n f : ℕ) (hn : 4 ≤ n) :
    Subgroup.center ↥(spinGroup (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) = ⊥ :=
  CFSG.StandardType.PsiDiag.SpinM.center_eq_bot (minusCoeffs_irr 2 f) hn

lemma nbrpom_lift_to_mem {X : Type} [Group X] (n f : ℕ)
    (ψ : spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2) →* X) {b : X}
    {s : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f)}
    (hsj : s ∈ (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).range)
    (hs : IsGLLift (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) ψ s b) :
    ∃ s₀ : spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
        (minusCoeffs 2 f).2),
      (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
        (minusCoeffs 2 f).2)) s₀ = s ∧
        ∀ u, b⁻¹ * ψ u * b = ψ (s₀ * u * s₀⁻¹) := by
  obtain ⟨s₀, hs₀⟩ := hsj
  refine ⟨s₀, hs₀, fun u => ?_⟩
  obtain ⟨u', hu'j, hu'ψ⟩ := hs u
  have heq : u' = s₀ * u * s₀⁻¹ := by
    apply nbrpom_spinMatrix_injective n f
    rw [hu'j, ← hs₀]
    simp only [map_mul, map_inv]
  rw [hu'ψ, heq]

lemma nbrpom_lift_inv {X : Type} [Group X] (n f : ℕ)
    (ψ : spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2) →* X) {b : X}
    {s : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f)}
    (hsj : s ∈ (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).range)
    (hs : IsGLLift (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) ψ s b) :
    IsGLLift (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) ψ s⁻¹ b⁻¹ := by
  obtain ⟨s₀, hs₀, hsl₀⟩ := nbrpom_lift_to_mem n f ψ hsj hs
  intro u
  refine ⟨s₀⁻¹ * u * s₀, ?_, ?_⟩
  · change (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
        (minusCoeffs 2 f).2)) (s₀⁻¹ * u * s₀) =
      s⁻¹ * (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
        (minusCoeffs 2 f).2)) u * s
    rw [map_mul, map_mul, map_inv, hs₀]
  · have h := hsl₀ (s₀⁻¹ * u * s₀)
    have h1 : s₀ * (s₀⁻¹ * u * s₀) * s₀⁻¹ = u := by group
    rw [h1] at h
    rw [inv_inv]
    calc b * ψ u * b⁻¹ = b * (b⁻¹ * ψ (s₀⁻¹ * u * s₀) * b) * b⁻¹ := by rw [h]
      _ = ψ (s₀⁻¹ * u * s₀) := by group

lemma nbrpom_lift_zpow {X : Type} [Group X] (n f : ℕ)
    (ψ : spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2) →* X) {b : X}
    {s : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f)}
    (hsj : s ∈ (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).range)
    (hs : IsGLLift (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) ψ s b) (k : ℤ) :
    IsGLLift (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) ψ (s ^ k) (b ^ k) := by
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg k
  · rw [hm]; simpa using hs.pow m
  · rw [hm]
    rw [show s ^ (-(m : ℤ)) = (s ^ m)⁻¹ by rw [zpow_neg, zpow_natCast],
        show b ^ (-(m : ℤ)) = (b ^ m)⁻¹ by rw [zpow_neg, zpow_natCast]]
    exact nbrpom_lift_inv n f ψ (Subgroup.pow_mem _ hsj m) (hs.pow m)

lemma nbrpom_lift_unique {X : Type} [Group X] (n f : ℕ) (hn : 4 ≤ n)
    (ψ : spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2) →* X)
    (hψ : ψ.ker ≤ Subgroup.center ↥(spinGroup (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) {b : X}
    {s s' : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f)}
    (hsj : s ∈ (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).range)
    (hs'j : s' ∈ (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).range)
    (hs : IsGLLift (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) ψ s b)
    (hs' : IsGLLift (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) ψ s' b) : s = s' := by
  obtain ⟨s₀, hs₀, hsl₀⟩ := nbrpom_lift_to_mem n f ψ hsj hs
  obtain ⟨s₁, hs₁, hsl₁⟩ := nbrpom_lift_to_mem n f ψ hs'j hs'
  have hconj : ∀ u, ψ (s₀ * u * s₀⁻¹) = ψ (s₁ * u * s₁⁻¹) := by
    intro u
    rw [← hsl₀ u, ← hsl₁ u]
  have hEq : s₀ = s₁ :=
    conj_eq_unique_POmegaMinus n (minusCoeffs_irr 2 f) hn ψ hψ hconj
  calc s = (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
        (minusCoeffs 2 f).2)) s₀ := hs₀.symm
    _ = (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
        (minusCoeffs 2 f).2)) s₁ := by rw [hEq]
    _ = s' := hs₁

lemma nbrpom_injective {X : Type} [Group X] (n f : ℕ) (hn : 4 ≤ n)
    (ψ : spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2) →* X)
    (hψ : ψ.ker ≤ Subgroup.center ↥(spinGroup (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) :
    Function.Injective ψ := by
  have hker : ψ.ker = ⊥ := le_bot_iff.mp (hψ.trans (le_of_eq (nbrpom_center_bot n f hn)))
  exact (MonoidHom.ker_eq_bot_iff ψ).mp hker

theorem nbrpom_L1
    {X : Type} [Group X] (n f p : ℕ) (hn : 4 ≤ n)
    (ψ : (ggU .POmegaMinus n f).K →* X) (R Rm : Subgroup X)
    (hR0 : GGRootPosG0 .POmegaMinus n f p ψ R Rm) :
    ∃ R' : Subgroup (ggU .POmegaMinus n f).K,
      R'.map ψ = R ∧
      (∃ a₁ a₂ : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) → GaloisField 2 f,
        a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
        LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ = 0 ∧
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₂ = 0 ∧
        QuadraticMap.polar (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
          (minusCoeffs 2 f).2) a₁ a₂ = 0 ∧
        R'.map (Spin.spinAction (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
          (minusCoeffs 2 f).2)) = siegelGroup (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ a₂) := by
  obtain ⟨β, -, hlong_or, u, hRu, -⟩ := hR0
  have hlong : GGLongRoot (ggU .POmegaMinus n f).D β := by
    rcases hlong_or with h | hshort
    · exact h
    · rcases hshort with h | hshort
      · exact absurd h (by decide)
      · rcases hshort with h | ⟨h, -⟩
        · exact absurd h (by decide)
        · rcases h with h | h <;> exact absurd h (by decide)
  let R' : Subgroup (ggU .POmegaMinus n f).K :=
    ((ggU .POmegaMinus n f).D.rootGroup β).map (MulAut.conj u).toMonoidHom
  refine ⟨R', ?_, ?_⟩
  · rw [hRu]; rfl
  · obtain ⟨a₁, a₂, ha₁, ha₂, hli, hQ₁, hQ₂, horth, heq⟩ :=
      exists_siegelGroup_eq_rootGroup_POmegaMinus n f hn hlong u
    exact ⟨a₁, a₂, ha₁, ha₂, hli, hQ₁, hQ₂, horth, heq⟩

theorem nbrpom_L3
    (n f : ℕ) (hn : 4 ≤ n)
    (S' : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f)))
    (hSU' : ∀ s ∈ S',
      s ∈ (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
        (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).range)
    (hS' : ∀ s ∈ S', ∀ s' ∈ S', Commute s s')
    (K' : Subgroup (ggU .POmegaMinus n f).K)
    (hK'comp : IsComponentOf K' ((Subgroup.centralizer S').comap
      (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
        (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)))) :
    ∃ ε eK : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (GaloisField 2 f),
      IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
        (LinearMap.toMatrix₂' (GaloisField 2 f)
          (QuadraticMap.polarBilin (Spin.quadMinus n (GaloisField 2 f)
            (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)))
        (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) ε ∧
      IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK ∧
      eK * ε = eK ∧
      (eK = ε ∨ (eK ≠ ε ∧
        formAdj (RingHom.id (GaloisField 2 f))
          (LinearMap.toMatrix₂' (GaloisField 2 f)
            (QuadraticMap.polarBilin (Spin.quadMinus n (GaloisField 2 f)
              (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) eK ≠ eK ∧
        ε = eK + formAdj (RingHom.id (GaloisField 2 f))
          (LinearMap.toMatrix₂' (GaloisField 2 f)
            (QuadraticMap.polarBilin (Spin.quadMinus n (GaloisField 2 f)
              (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) eK)) ∧
      IsComponentOf K' ⁅(glBlockCentralizer
          (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
            (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S' ε :
          Subgroup (ggU .POmegaMinus n f).K),
        (glBlockCentralizer
          (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
            (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S' ε :
          Subgroup (ggU .POmegaMinus n f).K)⁆ := by
  obtain ⟨ε, hε, hK'ε⟩ :=
    exists_isComponentOf_glBlockCentralizer_POmegaMinus n (minusCoeffs_irr 2 f) hn S' hS' hK'comp
  obtain ⟨eK, heK, heKε, hsplit⟩ :=
    exists_isPrimIdemIn_of_isPrimAdjIdemIn_POmegaMinus n f S' hSU' hS' hε
  exact ⟨ε, eK, hε, heK, heKε, hsplit, hK'ε⟩

lemma nbrpom_mem_glBlockCentralizer
    (n f : ℕ)
    (S' : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f)))
    (K' R' : Subgroup (ggU .POmegaMinus n f).K)
    (ε : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (GaloisField 2 f))
    (hK'ε : IsComponentOf K' ⁅(glBlockCentralizer
        (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S' ε :
        Subgroup (ggU .POmegaMinus n f).K),
      (glBlockCentralizer
        (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S' ε :
        Subgroup (ggU .POmegaMinus n f).K)⁆)
    (hR'K' : R' ≤ K') {g : (ggU .POmegaMinus n f).K} (hgR : g ∈ R') :
    g ∈ (glBlockCentralizer
        (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S' ε :
        Subgroup (ggU .POmegaMinus n f).K) := by
  obtain ⟨Gε, hGε⟩ : ∃ Gε : Subgroup (ggU .POmegaMinus n f).K,
      Gε = (glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
        (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S' ε :
        Subgroup (ggU .POmegaMinus n f).K) := ⟨_, rfl⟩
  rw [← hGε] at hK'ε
  have hgGε : g ∈ Gε := by
    have hle : ⁅Gε, Gε⁆ ≤ Gε := by
      refine Subgroup.commutator_le.mpr (fun a ha b hb => ?_)
      rw [commutatorElement_def]
      exact Subgroup.mul_mem Gε (Subgroup.mul_mem Gε (Subgroup.mul_mem Gε ha hb)
        (Subgroup.inv_mem Gε ha)) (Subgroup.inv_mem Gε hb)
    exact hle (hK'ε.1 (hR'K' hgR))
  exact hGε ▸ hgGε

theorem nbrpom_blockDegree_selfDual
    (n f : ℕ) (S' : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f)))
    (hSU' : ∀ s ∈ S',
      s ∈ (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
        (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).range)
    (hS' : ∀ s ∈ S', ∀ s' ∈ S', Commute s s')
    (hodd' : ∀ s ∈ S', Odd (orderOf s))
    (K' R' : Subgroup (ggU .POmegaMinus n f).K)
    (ε eK : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (GaloisField 2 f))
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) ε)
    (heK : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK)
    (heKε : eK * ε = eK)
    (hK'ε : IsComponentOf K' ⁅(glBlockCentralizer
        (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S' ε :
        Subgroup (ggU .POmegaMinus n f).K),
      (glBlockCentralizer
        (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S' ε :
        Subgroup (ggU .POmegaMinus n f).K)⁆)
    (hR'K' : R' ≤ K')
    (hshort : nbrpom_HasShortElm (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) R') (hself : eK = ε) :
    blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK < 4 := by
  obtain ⟨g, hgR, hg1, hgrank⟩ := hshort
  have hgmem := nbrpom_mem_glBlockCentralizer n f S' K' R' ε hK'ε hR'K' hgR
  have hgS : (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) g) ∈
      Subgroup.centralizer S' := (Subgroup.mem_comap.mp hgmem).1
  have hge : (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) g) ∈
      glFixing (1 - ε) := (Subgroup.mem_comap.mp hgmem).2
  have hgeK : (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) g) ∈
      glFixing (1 - eK) := by rw [hself]; exact hge
  have hdvd : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK ∣
      Matrix.rank (((Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
        (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) g) :
        Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
          (GaloisField 2 f)) - 1) :=
    blockDegree_dvd_rank_sub_one_of_glFixing (S := S') hS' hodd' heK hgS hgeK
  have hgne : (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) g) ≠ 1 := by
    intro h
    exact hg1 (nbrpom_spinMatrix_injective n f (by rw [h, map_one]))
  have hrank_pos : 1 ≤ Matrix.rank
      (((Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
        (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) g) :
        Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
          (GaloisField 2 f)) - 1) :=
    nbrpom_rank_pos (fun h => hgne (Units.ext h))
  have hle : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK ≤ 2 :=
    le_trans (Nat.le_of_dvd hrank_pos hdvd) hgrank
  omega

theorem nbrpom_blockDegree_dualPair
    (n f : ℕ) (S' : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f)))
    (hSU' : ∀ s ∈ S',
      s ∈ (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
        (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).range)
    (hS' : ∀ s ∈ S', ∀ s' ∈ S', Commute s s')
    (hodd' : ∀ s ∈ S', Odd (orderOf s))
    (K' R' : Subgroup (ggU .POmegaMinus n f).K)
    (ε eK : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (GaloisField 2 f))
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) ε)
    (heK : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK)
    (heKε : eK * ε = eK)
    (hK'ε : IsComponentOf K' ⁅(glBlockCentralizer
        (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S' ε :
        Subgroup (ggU .POmegaMinus n f).K),
      (glBlockCentralizer
        (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S' ε :
        Subgroup (ggU .POmegaMinus n f).K)⁆)
    (hR'K' : R' ≤ K')
    (hshort : nbrpom_HasShortElm (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) R')
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) eK ≠ eK)
    (heq : ε = eK + formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) eK) :
    blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK < 2 := by
  let Q := Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2
  let G := LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin Q)
  obtain ⟨g, hgR, hg1, hgrank⟩ := hshort
  have hgmem := nbrpom_mem_glBlockCentralizer n f S' K' R' ε hK'ε hR'K' hgR
  have hgS : (Spin.spinMatrix Q g) ∈ Subgroup.centralizer S' :=
    (Subgroup.mem_comap.mp hgmem).1
  have hge : (Spin.spinMatrix Q g) ∈ glFixing (1 - ε) := (Subgroup.mem_comap.mp hgmem).2
  have hGdet : IsUnit G.det :=
    nbrpom_isUnit_det Q (Spin.nondegenerate_polarBilin_quadMinus_of_finite n
      (GaloisField 2 f) (minusCoeffs_irr 2 f))
  have hGh : Matrix.transpose (G.map (RingHom.id (GaloisField 2 f))) = G := by
    simpa using nbrpom_polar_matrix_transpose_eq Q
  have hSU : ∀ s ∈ S', Matrix.transpose ((s : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
        (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f)).map
          (RingHom.id (GaloisField 2 f))) * G *
      (s : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
        (GaloisField 2 f)) = G := by
    intro s hs
    obtain ⟨gs, rfl⟩ := hSU' s hs
    simpa using nbrpom_spinMatrix_gram Q gs
  have hgiso : Matrix.transpose (((Spin.spinMatrix Q g) :
      Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
        (GaloisField 2 f)).map (RingHom.id (GaloisField 2 f))) * G *
      (Spin.spinMatrix Q g) = G := by
    simpa using nbrpom_spinMatrix_gram Q g
  have hge' : (Spin.spinMatrix Q g) ∈
      glFixing (1 - (eK + formAdj (RingHom.id (GaloisField 2 f)) G eK)) := by
    rw [← heq]
    exact hge
  have hdvd : 2 * blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK ∣
      Matrix.rank (((Spin.spinMatrix Q g) :
        Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
          (GaloisField 2 f)) - 1) :=
    two_mul_blockDegree_dvd_rank_sub_one_of_formAdj_ne (RingHom.id (GaloisField 2 f))
      (fun x => rfl) hGdet hGh hSU hS' hodd' heK hadj hgS hgiso hge'
  have hgne : (Spin.spinMatrix Q g) ≠ 1 := by
    intro h
    exact hg1 (nbrpom_spinMatrix_injective n f (by rw [h, map_one]))
  have hrank_pos : 1 ≤ Matrix.rank (((Spin.spinMatrix Q g) :
      Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
        (GaloisField 2 f)) - 1) := nbrpom_rank_pos (fun h => hgne (Units.ext h))
  have hle : 2 * blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK ≤ 2 :=
    le_trans (Nat.le_of_dvd hrank_pos hdvd) hgrank
  omega

theorem nbrpom_L4
    (n f : ℕ) (S' : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f)))
    (hSU' : ∀ s ∈ S',
      s ∈ (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
        (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).range)
    (hS' : ∀ s ∈ S', ∀ s' ∈ S', Commute s s')
    (hodd' : ∀ s ∈ S', Odd (orderOf s))
    (K' R' : Subgroup (ggU .POmegaMinus n f).K)
    (ε eK : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (GaloisField 2 f))
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) ε)
    (heK : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK)
    (heKε : eK * ε = eK)
    (hsplit : eK = ε ∨ (eK ≠ ε ∧
      formAdj (RingHom.id (GaloisField 2 f))
        (LinearMap.toMatrix₂' (GaloisField 2 f)
          (QuadraticMap.polarBilin (Spin.quadMinus n (GaloisField 2 f)
            (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) eK ≠ eK ∧
      ε = eK + formAdj (RingHom.id (GaloisField 2 f))
        (LinearMap.toMatrix₂' (GaloisField 2 f)
          (QuadraticMap.polarBilin (Spin.quadMinus n (GaloisField 2 f)
            (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) eK))
    (hK'ε : IsComponentOf K' ⁅(glBlockCentralizer
        (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S' ε :
        Subgroup (ggU .POmegaMinus n f).K),
      (glBlockCentralizer
        (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S' ε :
        Subgroup (ggU .POmegaMinus n f).K)⁆)
    (hR'K' : R' ≤ K')
    (hgeo : ∃ a₁ a₂ : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) → GaloisField 2 f,
      a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
      LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ = 0 ∧
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₂ = 0 ∧
      QuadraticMap.polar (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
        (minusCoeffs 2 f).2) a₁ a₂ = 0 ∧
      R'.map (Spin.spinAction (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
        (minusCoeffs 2 f).2)) = siegelGroup (Spin.quadMinus n (GaloisField 2 f)
        (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ a₂) :
    (eK = ε ∧ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK < 2) ∨
      (eK = ε ∧ 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK ∧
        blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK < 4) ∨
      (eK ≠ ε ∧ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK < 2) := by
  have hshort : nbrpom_HasShortElm (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) R' := by
    obtain ⟨a₁, a₂, ha₁, ha₂, hli, hQ₁, hQ₂, horth, hm⟩ := hgeo
    exact nbrpom_siegel_shortElm (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
      (Spin.nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField 2 f)
        (minusCoeffs_irr 2 f)) R' a₁ a₂ ha₁ ha₂ hli hQ₁ hQ₂ horth hm.ge
  rcases hsplit with hself | ⟨hne, hadj, heq⟩
  · by_cases hd : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK < 2
    · exact Or.inl ⟨hself, hd⟩
    · exact Or.inr (Or.inl ⟨hself, by omega,
        nbrpom_blockDegree_selfDual n f S' hSU' hS' hodd' K' R' ε eK hε heK heKε hK'ε
          hR'K' hshort hself⟩)
  · exact Or.inr (Or.inr ⟨hne,
      nbrpom_blockDegree_dualPair n f S' hSU' hS' hodd' K' R' ε eK hε heK heKε hK'ε
        hR'K' hshort hadj heq⟩)

theorem nbrpom_hnm_minusFour
    (n f : ℕ) (S' : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f)))
    (K' R' : Subgroup (ggU .POmegaMinus n f).K)
    (eK : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (GaloisField 2 f))
    (heK : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK)
    (hK'e : IsComponentOf K' ⁅(glBlockCentralizer
        (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S' eK :
        Subgroup (ggU .POmegaMinus n f).K),
      (glBlockCentralizer
        (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S' eK :
        Subgroup (ggU .POmegaMinus n f).K)⁆)
    (hR'K' : R' ≤ K')
    (hadjE : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) eK = eK)
    (a₁ a₂ : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) → GaloisField 2 f)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (hli : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    (hQ₁ : (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ = 0)
    (hQ₂ : (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₂ = 0)
    (horth : QuadraticMap.polar (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ a₂ = 0)
    (hm : R'.map (Spin.spinAction (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) =
      siegelGroup (Spin.quadMinus n (GaloisField 2 f)
        (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ a₂) :
    ¬ (eK.rank = 4 ∧ ∀ x y : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) → (GaloisField 2 f),
      Matrix.mulVec eK x = x → Matrix.mulVec eK y = y →
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) x = 0 →
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) y = 0 →
      QuadraticMap.polar (Spin.quadMinus n (GaloisField 2 f)
        (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) x y = 0 →
      ¬ LinearIndependent (GaloisField 2 f) ![x, y]) := by
  classical
  rintro ⟨hrank4, hno⟩
  let Q := Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2
  let G := LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin Q)
  have hGdet : IsUnit G.det :=
    nbrpom_isUnit_det Q (Spin.nondegenerate_polarBilin_quadMinus_of_finite n
      (GaloisField 2 f) (minusCoeffs_irr 2 f))
  have hker : LinearMap.ker (QuadraticMap.polarBilin Q) = ⊥ :=
    LinearMap.BilinForm.Nondegenerate.ker_eq_bot
      (Spin.nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField 2 f)
        (minusCoeffs_irr 2 f))
  let g₀ := CFSG.ClassicalGroups.Orthogonal.eichler Q a₁ a₂
  have hg₀mem : g₀ ∈ siegelGroup Q a₁ a₂ := by
    refine Subgroup.subset_closure ⟨1, ?_⟩
    rw [one_smul]
  have hg₀R : g₀ ∈ R'.map (Spin.spinAction Q) := by
    rw [hm]
    exact hg₀mem
  obtain ⟨g, hgR, hgval⟩ := Subgroup.mem_map.mp hg₀R
  have hGε_le : ⁅(glBlockCentralizer (Spin.spinMatrix Q) S' eK :
        Subgroup (ggU .POmegaMinus n f).K),
      (glBlockCentralizer (Spin.spinMatrix Q) S' eK :
        Subgroup (ggU .POmegaMinus n f).K)⁆ ≤
      (glBlockCentralizer (Spin.spinMatrix Q) S' eK :
        Subgroup (ggU .POmegaMinus n f).K) := by
    refine Subgroup.commutator_le.mpr (fun a ha b hb => ?_)
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  have hgGε : g ∈ (glBlockCentralizer (Spin.spinMatrix Q) S' eK :
      Subgroup (ggU .POmegaMinus n f).K) :=
    hGε_le (hK'e.1 (hR'K' hgR))
  have hgfix : (Spin.spinMatrix Q g) * (1 - eK) = 1 - eK :=
    (Subgroup.mem_comap.mp hgGε).2
  have hfix : ∀ v, g₀ ((1 - eK).mulVec v) = (1 - eK).mulVec v := by
    intro v
    have h := congrArg (fun M : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
        (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f) => M.mulVec v) hgfix
    have h2 : (Spin.spinAction Q g) ((1 - eK).mulVec v) = (1 - eK).mulVec v := by
      rw [← Spin.spinMatrix_mulVec]
      rw [Matrix.mulVec_mulVec v ((Spin.spinMatrix Q g) :
        Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
          (GaloisField 2 f)) (1 - eK)]
      exact h
    rw [← hgval]
    exact h2
  have hself : formAdj (RingHom.id (GaloisField 2 f)) G (1 - eK) = 1 - eK := by
    have h1 : formAdj (RingHom.id (GaloisField 2 f)) G 1 = 1 := by
      rw [nbrpom_formAdj_id, Matrix.transpose_one, Matrix.mul_one,
        Matrix.nonsing_inv_mul G hGdet]
    have h2 : formAdj (RingHom.id (GaloisField 2 f)) G (1 - eK) =
        formAdj (RingHom.id (GaloisField 2 f)) G 1 -
          formAdj (RingHom.id (GaloisField 2 f)) G eK := by
      rw [sub_eq_add_neg, Geo.formAdj_add, nbrpom_formAdj_neg, sub_eq_add_neg]
    rw [h2, h1, hadjE]
  have hsa : ∀ x y, QuadraticMap.polar Q ((1 - eK).mulVec x) y =
      QuadraticMap.polar Q x ((1 - eK).mulVec y) := fun x y =>
    nbrpom_polar_selfAdjoint Q hGdet hself x y
  have hpolar : ∀ v, QuadraticMap.polar Q ((1 - eK).mulVec v) a₁ = 0 ∧
      QuadraticMap.polar Q ((1 - eK).mulVec v) a₂ = 0 := by
    intro v
    set x : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) → GaloisField 2 f :=
      (1 - eK).mulVec v with hx
    have hxf : CFSG.ClassicalGroups.Orthogonal.eichler Q a₁ a₂ x = x := hfix v
    have hf := CFSG.ClassicalGroups.Orthogonal.eichler_apply (Q := Q) hQ₁ horth x
    rw [hxf] at hf
    have hQ₂' : Q a₂ = 0 := hQ₂
    rw [hQ₂', zero_mul, add_zero] at hf
    have hAB : QuadraticMap.polar Q x a₁ • a₂ = QuadraticMap.polar Q x a₂ • a₁ := by
      have h2 : x + (QuadraticMap.polar Q x a₁ • a₂ -
          QuadraticMap.polar Q x a₂ • a₁) = x + 0 := by
        rw [add_zero]
        conv_rhs => rw [hf]
        abel
      exact sub_eq_zero.mp (add_left_cancel h2)
    have hcon := (LinearIndependent.pair_iff.mp hli) (QuadraticMap.polar Q x a₂)
      (QuadraticMap.polar Q x a₁) (by rw [hAB]; exact CharTwo.add_self_eq_zero _)
    exact ⟨hcon.2, hcon.1⟩
  have hw₁ : (1 - eK).mulVec a₁ = 0 := by
    have hmem : (1 - eK).mulVec a₁ ∈ LinearMap.ker (QuadraticMap.polarBilin Q) := by
      rw [LinearMap.mem_ker]
      apply LinearMap.ext; intro v
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm, ← hsa v a₁]
      exact (hpolar v).1
    have hbot : (1 - eK).mulVec a₁ ∈ (⊥ : Submodule (GaloisField 2 f)
        ((Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) → GaloisField 2 f)) := hker ▸ hmem
    simpa using hbot
  have hw₂ : (1 - eK).mulVec a₂ = 0 := by
    have hmem : (1 - eK).mulVec a₂ ∈ LinearMap.ker (QuadraticMap.polarBilin Q) := by
      rw [LinearMap.mem_ker]
      apply LinearMap.ext; intro v
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm, ← hsa v a₂]
      exact (hpolar v).2
    have hbot : (1 - eK).mulVec a₂ ∈ (⊥ : Submodule (GaloisField 2 f)
        ((Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) → GaloisField 2 f)) := hker ▸ hmem
    simpa using hbot
  have heKa₁ : eK.mulVec a₁ = a₁ := by
    have h := hw₁
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
    exact h.symm
  have heKa₂ : eK.mulVec a₂ = a₂ := by
    have h := hw₂
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
    exact h.symm
  exact hno a₁ a₂ heKa₁ heKa₂ hQ₁ hQ₂ horth hli

lemma nbrpom_L6
    {X : Type} [Group X] [Finite X]
    (n f : ℕ) (ψ : (ggU .POmegaMinus n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hH : GGSixPosHyp .POmegaMinus n f ψ p G₀ B₁ D J L x) : 4 ≤ n := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  exact (h3.admissible).2.2

lemma mem_sup_central {U : Type} [Group U] {K Z : Subgroup U}
    (hZ : Z ≤ Subgroup.center U) {x : U} : x ∈ K ⊔ Z ↔ ∃ k ∈ K, ∃ z ∈ Z, k * z = x := by
  haveI : Z.Normal := Subgroup.normal_of_le_center hZ
  exact Subgroup.mem_sup_of_normal_right

lemma commutatorElement_mul_central_left {U : Type} [Group U]
    {c : U} (hc : c ∈ Subgroup.center U) (g h : U) : ⁅g * c, h⁆ = ⁅g, h⁆ := by
  have e : c * h * c⁻¹ = h := by
    rw [← Subgroup.mem_center_iff.mp hc h, mul_inv_cancel_right]
  simp only [commutatorElement_def, mul_inv_rev]
  calc g * c * h * (c⁻¹ * g⁻¹) * h⁻¹ = g * (c * h * c⁻¹) * g⁻¹ * h⁻¹ := by group
    _ = g * h * g⁻¹ * h⁻¹ := by rw [e]

lemma commutatorElement_mul_central_right {U : Type} [Group U]
    {c : U} (hc : c ∈ Subgroup.center U) (g h : U) : ⁅g, h * c⁆ = ⁅g, h⁆ := by
  have e : g * c * g⁻¹ = c := by
    rw [Subgroup.mem_center_iff.mp hc g, mul_inv_cancel_right]
  simp only [commutatorElement_def, mul_inv_rev]
  calc g * (h * c) * g⁻¹ * (c⁻¹ * h⁻¹)
      = (g * h * g⁻¹) * (g * c * g⁻¹) * (c⁻¹ * h⁻¹) := by group
    _ = (g * h * g⁻¹) * c * c⁻¹ * h⁻¹ := by rw [e]; group
    _ = g * h * g⁻¹ * h⁻¹ := by group

lemma commutator_sup_central_le {U : Type} [Group U] {K Z : Subgroup U}
    (hZ : Z ≤ Subgroup.center U) : ⁅K ⊔ Z, K ⊔ Z⁆ ≤ ⁅K, K⁆ := by
  refine Subgroup.commutator_le.2 fun x hx y hy => ?_
  obtain ⟨k, hk, z, hz, rfl⟩ := (mem_sup_central hZ).1 hx
  obtain ⟨k', hk', z', hz', rfl⟩ := (mem_sup_central hZ).1 hy
  rw [commutatorElement_mul_central_left (hZ hz),
    commutatorElement_mul_central_right (hZ hz')]
  exact Subgroup.commutator_mem_commutator hk hk'

lemma perfect_le_of_le_sup_center {U : Type} [Group U] {J K Z : Subgroup U}
    (hZ : Z ≤ Subgroup.center U) (hle : J ≤ K ⊔ Z) (hperf : commutator ↥J = ⊤) : J ≤ K := by
  haveI : Z.Normal := Subgroup.normal_of_le_center hZ
  have hmap2 : Subgroup.map (Subgroup.subtype J) (commutator ↥J) = ⁅J, J⁆ := by
    have hc : commutator ↥J = ⁅(⊤ : Subgroup ↥J), ⊤⁆ := rfl
    rw [hc, Subgroup.map_commutator]
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hJle : J ≤ ⁅J, J⁆ := by
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥J) ∈ commutator ↥J := by rw [hperf]; trivial
    have hxm : x ∈ Subgroup.map (Subgroup.subtype J) (commutator ↥J) :=
      ⟨⟨x, hx⟩, hx', rfl⟩
    rwa [hmap2] at hxm
  have hcommK : ⁅K ⊔ Z, K ⊔ Z⁆ ≤ K := by
    refine (commutator_sup_central_le hZ).trans ?_
    simpa using Subgroup.commutator_le_sup K K
  exact hJle.trans ((Subgroup.commutator_mono hle hle).trans hcommK)

lemma commute_adjoin {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} {T : GL ι F} (hT : T ∈ Subgroup.centralizer S)
    {ε : Matrix ι ι F} (hε : ε ∈ Algebra.adjoin F (Units.val '' S)) :
    (T : Matrix ι ι F) * ε = ε * (T : Matrix ι ι F) := by
  have hgen : (Units.val '' S : Set (Matrix ι ι F)) ⊆
      (Subalgebra.centralizer F ({(T : Matrix ι ι F)} : Set (Matrix ι ι F)) :
        Set (Matrix ι ι F)) := by
    rintro x ⟨s, hs, rfl⟩
    refine (Subalgebra.mem_centralizer_iff F).mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact congrArg (fun u : GL ι F => (u : Matrix ι ι F))
      ((Subgroup.mem_centralizer_iff.mp hT) s hs).symm
  have hA : Algebra.adjoin F (Units.val '' S) ≤
      Subalgebra.centralizer F ({(T : Matrix ι ι F)} : Set (Matrix ι ι F)) :=
    Algebra.adjoin_le hgen
  exact (Subalgebra.mem_centralizer_iff F).mp (hA hε) (T : Matrix ι ι F)
    (Set.mem_singleton (T : Matrix ι ι F))

lemma rank_lt_of_mul_eq {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {a b : Matrix ι ι F} (ha : IsIdempotentElem a) (hab : a * b = a) (hba : b * a = a)
    (hne : a ≠ b) :
    Module.finrank F (LinearMap.range (Matrix.toLin' a)) <
      Module.finrank F (LinearMap.range (Matrix.toLin' b)) := by
  have hle : LinearMap.range (Matrix.toLin' a) ≤ LinearMap.range (Matrix.toLin' b) := by
    rintro _ ⟨y, rfl⟩
    exact ⟨Matrix.toLin' a y, by rw [← Matrix.toLin'_mul_apply, hba]⟩
  have hlt : LinearMap.range (Matrix.toLin' a) < LinearMap.range (Matrix.toLin' b) := by
    refine lt_of_le_of_ne hle fun heq => hne ?_
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    have hx : Matrix.toLin' b x ∈ LinearMap.range (Matrix.toLin' a) := by
      rw [heq]
      exact ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := hx
    have h1 : Matrix.toLin' a (Matrix.toLin' b x) = Matrix.toLin' a x := by
      rw [← Matrix.toLin'_mul_apply, hab]
    have h2 : Matrix.toLin' a (Matrix.toLin' a z) = Matrix.toLin' a z := by
      rw [← Matrix.toLin'_mul_apply, ha.eq]
    rw [← h1, ← hz, h2]
  exact Submodule.finrank_lt_finrank_of_lt hlt

lemma selfDual_not_below_dualPair {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] (G : Matrix ι ι F) (hG : IsUnit G.det) {A : Subalgebra F (Matrix ι ι F)}
    (hcomm : ∀ a b : Matrix ι ι F, a ∈ A → b ∈ A → a * b = b * a)
    {e_J e' : Matrix ι ι F}
    (heJ : IsPrimIdemIn A e_J) (hadjJ : formAdj (RingHom.id F) G e_J = e_J)
    (he' : e' ∈ A) (he'star : formAdj (RingHom.id F) G e' ∈ A)
    (he'idem : IsIdempotentElem e')
    (hle : e_J * (e' + formAdj (RingHom.id F) G e') = e_J) : False := by
  obtain ⟨heJA, heJidem, heJ0, heJprim⟩ := heJ
  have hmem : e_J * e' ∈ A := A.mul_mem heJA he'
  have hidem : IsIdempotentElem (e_J * e') := by
    rw [IsIdempotentElem]
    calc (e_J * e') * (e_J * e') = e_J * (e' * e_J) * e' := by noncomm_ring
      _ = e_J * (e_J * e') * e' := by rw [hcomm e' e_J he' heJA]
      _ = (e_J * e_J) * (e' * e') := by noncomm_ring
      _ = e_J * e' := by rw [heJidem.eq, he'idem.eq]
  have hmul : (e_J * e') * e_J = e_J * e' := by
    rw [mul_assoc, hcomm e' e_J he' heJA, ← mul_assoc, heJidem.eq]
  rcases heJprim (e_J * e') hmem hidem hmul with h0 | h1
  · have hstar : e_J * formAdj (RingHom.id F) G e' = e_J := by
      have h := hle
      rw [mul_add, h0, zero_add] at h
      exact h
    have hf : formAdj (RingHom.id F) G e' * e_J = 0 := by
      have h := congrArg (formAdj (RingHom.id F) G) h0
      rw [Geo.formAdj_mul (RingHom.id F) hG, hadjJ] at h
      simpa [formAdj] using h
    have hz : e_J * formAdj (RingHom.id F) G e' = 0 :=
      (hcomm e_J (formAdj (RingHom.id F) G e') heJA he'star).trans hf
    rw [hz] at hstar
    exact heJ0 hstar.symm
  · have hstar : e_J * formAdj (RingHom.id F) G e' = e_J := by
      have h := congrArg (formAdj (RingHom.id F) G) h1
      rw [Geo.formAdj_mul (RingHom.id F) hG, hadjJ] at h
      exact (hcomm e_J (formAdj (RingHom.id F) G e') heJA he'star).trans h
    have hsum : e_J + e_J = e_J := by
      have h := hle
      rw [mul_add, h1, hstar] at h
      exact h
    exact heJ0 (add_left_cancel (by rw [add_zero, hsum]))

lemma blockDegree_le_of_mul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {A A' : Subalgebra F (Matrix ι ι F)} (hAA' : A' ≤ A)
    (hcomm : ∀ a b : Matrix ι ι F, a ∈ A → b ∈ A → a * b = b * a)
    {e_J e' : Matrix ι ι F}
    (heJ : IsPrimIdemIn A e_J) (hle : e_J * e' = e_J)
    (hfield : ∀ x ∈ A', x * e' ≠ 0 → ∃ y ∈ A', y * x * e' = e') :
    blockDegree A' e' ≤ blockDegree A e_J := by
  have hker : LinearMap.ker ((LinearMap.mulRight F e_J).comp (Subalgebra.val A').toLinearMap) ≤
      LinearMap.ker ((LinearMap.mulRight F e').comp (Subalgebra.val A').toLinearMap) := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    by_contra hne
    have hne' : (a : Matrix ι ι F) * e' ≠ 0 := by
      simpa [LinearMap.mulRight_apply] using hne
    obtain ⟨b, hb, hb'⟩ := hfield (a : Matrix ι ι F) a.2 hne'
    have haJ : (a : Matrix ι ι F) * e_J = 0 := by
      simpa [LinearMap.mulRight_apply] using ha
    have haA : (a : Matrix ι ι F) ∈ A := hAA' a.2
    have hbA : b ∈ A := hAA' hb
    have hmove : e_J * b * (a : Matrix ι ι F) = b * (a : Matrix ι ι F) * e_J := by
      rw [hcomm e_J b heJ.1 hbA, mul_assoc, hcomm e_J (a : Matrix ι ι F) heJ.1 haA,
        ← mul_assoc]
    have heq0 : e_J = 0 := by
      calc e_J = e_J * e' := hle.symm
        _ = e_J * (b * (a : Matrix ι ι F) * e') := by rw [hb']
        _ = (e_J * b * (a : Matrix ι ι F)) * e' := by noncomm_ring
        _ = (b * (a : Matrix ι ι F) * e_J) * e' := by rw [hmove]
        _ = b * ((a : Matrix ι ι F) * e_J) * e' := by noncomm_ring
        _ = 0 := by rw [haJ, mul_zero, zero_mul]
    exact heJ.2.2.1 heq0
  have hnull' := LinearMap.finrank_range_add_finrank_ker
    ((LinearMap.mulRight F e').comp (Subalgebra.val A').toLinearMap)
  have hnull := LinearMap.finrank_range_add_finrank_ker
    ((LinearMap.mulRight F e_J).comp (Subalgebra.val A').toLinearMap)
  have hkerle := Submodule.finrank_mono hker
  have hrange_le' : Module.finrank F (LinearMap.range
      ((LinearMap.mulRight F e').comp (Subalgebra.val A').toLinearMap)) ≤
      Module.finrank F (LinearMap.range ((LinearMap.mulRight F e_J).comp
        (Subalgebra.val A').toLinearMap)) := by
    omega
  have hrange_le : LinearMap.range ((LinearMap.mulRight F e_J).comp
      (Subalgebra.val A').toLinearMap) ≤
      (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e_J) := by
    rintro x ⟨a, rfl⟩
    exact ⟨(a : Matrix ι ι F), hAA' a.2, rfl⟩
  have hfin : Module.finrank F (LinearMap.range ((LinearMap.mulRight F e_J).comp
      (Subalgebra.val A').toLinearMap)) ≤ blockDegree A e_J := by
    rw [blockDegree]
    exact Submodule.finrank_mono hrange_le
  have hval : LinearMap.range (Subalgebra.val A').toLinearMap = Subalgebra.toSubmodule A' := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact a.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hrange' : (Subalgebra.toSubmodule A').map (LinearMap.mulRight F e') =
      LinearMap.range ((LinearMap.mulRight F e').comp (Subalgebra.val A').toLinearMap) := by
    rw [LinearMap.range_comp, hval]
  rw [blockDegree, hrange']
  exact hrange_le'.trans hfin

lemma mul_formAdj_eq_zero {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (G : Matrix ι ι F) (hG : IsUnit G.det)
    (hGh : Matrix.transpose (G.map (RingHom.id F)) = G)
    {A : Subalgebra F (Matrix ι ι F)}
    (hcomm : ∀ a b : Matrix ι ι F, a ∈ A → b ∈ A → a * b = b * a)
    {e : Matrix ι ι F} (he : IsPrimIdemIn A e)
    (hestarA : formAdj (RingHom.id F) G e ∈ A)
    (hfix : formAdj (RingHom.id F) G e ≠ e) :
    e * formAdj (RingHom.id F) G e = 0 := by
  by_contra hne0
  have hstar_idem : IsIdempotentElem (formAdj (RingHom.id F) G e) := by
    rw [IsIdempotentElem, ← Geo.formAdj_mul (RingHom.id F) hG e e, he.2.1.eq]
  have hidem : IsIdempotentElem (e * formAdj (RingHom.id F) G e) :=
    IsIdempotentElem.mul_of_commute (hcomm e (formAdj (RingHom.id F) G e) he.1 hestarA)
      he.2.1 hstar_idem
  have hee : (e * formAdj (RingHom.id F) G e) * e = e * formAdj (RingHom.id F) G e := by
    rw [Matrix.mul_assoc, ← hcomm e (formAdj (RingHom.id F) G e) he.1 hestarA, ← Matrix.mul_assoc,
      he.2.1.eq]
  rcases he.2.2.2 (e * formAdj (RingHom.id F) G e) (Subalgebra.mul_mem _ he.1 hestarA) hidem hee
    with h0 | heq
  · exact hne0 h0
  · apply hfix
    calc formAdj (RingHom.id F) G e =
          formAdj (RingHom.id F) G (e * formAdj (RingHom.id F) G e) := by
          rw [heq]
      _ = formAdj (RingHom.id F) G (formAdj (RingHom.id F) G e) * formAdj (RingHom.id F) G e :=
          Geo.formAdj_mul (RingHom.id F) hG e (formAdj (RingHom.id F) G e)
      _ = e * formAdj (RingHom.id F) G e := by
          rw [Geo.formAdj_formAdj (RingHom.id F) (fun x => rfl) hG hGh e]
      _ = e := heq

lemma mul_e_eq_smul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {A : Subalgebra F (Matrix ι ι F)} {e : Matrix ι ι F} (he : IsPrimIdemIn A e)
    (hdeg : blockDegree A e < 2) : ∀ a ∈ A, ∃ c : F, a * e = c • e := by
  let M : Submodule F (Matrix ι ι F) := (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e)
  have heM : e ∈ M := ⟨1, by simpa using A.one_mem, by rw [LinearMap.mulRight_apply, one_mul]⟩
  have hne : (⟨e, heM⟩ : M) ≠ 0 := by
    intro h
    exact he.2.2.1 (by simpa using congrArg Subtype.val h)
  haveI : Nontrivial M := ⟨⟨⟨e, heM⟩, 0, hne⟩⟩
  have hpos : 0 < Module.finrank F M := Module.finrank_pos_iff.mpr inferInstance
  have hlt : Module.finrank F M < 2 := hdeg
  have hfin : Module.finrank F M = 1 := by omega
  have hspan : M = Submodule.span F {e} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hfin heM he.2.2.1
  intro a ha
  have hae : a * e ∈ M := ⟨a, ha, by rw [LinearMap.mulRight_apply]⟩
  rw [hspan] at hae
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hae
  exact ⟨c, hc.symm⟩

lemma blockField_inv {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {A : Subalgebra F (Matrix ι ι F)} {e : Matrix ι ι F}
    {K : Type} [Field K] [Algebra F K] (π : A →ₐ[F] K)
    (hπs : Function.Surjective π) (hπk : ∀ a, π a = 0 ↔ (a : Matrix ι ι F) * e = 0) :
    ∀ x ∈ A, x * e ≠ 0 → ∃ y ∈ A, y * x * e = e := by
  intro x hx hxne
  have hπx : π ⟨x, hx⟩ ≠ 0 := fun h0 => hxne ((hπk ⟨x, hx⟩).mp h0)
  obtain ⟨z, hz⟩ := hπs ((π ⟨x, hx⟩)⁻¹)
  refine ⟨(z : Matrix ι ι F), z.2, ?_⟩
  have hzx : π (z * ⟨x, hx⟩) = 1 := by rw [map_mul, hz, inv_mul_cancel₀ hπx]
  have h1 : π (z * ⟨x, hx⟩ - 1) = 0 := by rw [map_sub, hzx, map_one, sub_self]
  have h2 := (hπk (z * ⟨x, hx⟩ - 1)).mp h1
  have h3 : ((z : Matrix ι ι F) * x - 1) * e = 0 := by simpa using h2
  rw [sub_mul, Matrix.one_mul] at h3
  exact sub_eq_zero.mp h3

lemma finrank_range_add_of_orth {ι F : Type*} [Fintype ι] [DecidableEq ι]
    [Field F] {a b : Matrix ι ι F} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (hab : a * b = 0) (hba : b * a = 0) :
    Module.finrank F (LinearMap.range (Matrix.toLin' (a + b))) =
      Module.finrank F (LinearMap.range (Matrix.toLin' a)) +
        Module.finrank F (LinearMap.range (Matrix.toLin' b)) := by
  have hp : LinearMap.range (Matrix.toLin' a) ≤ LinearMap.range (Matrix.toLin' (a + b)) := by
    rintro _ ⟨y, rfl⟩
    refine ⟨Matrix.toLin' a y, ?_⟩
    simp only [Matrix.toLin'_apply, Matrix.add_mul, Matrix.add_mulVec, Matrix.mulVec_mulVec,
      ha.eq, hba, Matrix.zero_mulVec, add_zero]
  have hq : LinearMap.range (Matrix.toLin' b) ≤ LinearMap.range (Matrix.toLin' (a + b)) := by
    rintro _ ⟨y, rfl⟩
    refine ⟨Matrix.toLin' b y, ?_⟩
    simp only [Matrix.toLin'_apply, Matrix.add_mul, Matrix.add_mulVec, Matrix.mulVec_mulVec,
      hb.eq, hab, Matrix.zero_mulVec, zero_add]
  have hsup : LinearMap.range (Matrix.toLin' (a + b)) =
      LinearMap.range (Matrix.toLin' a) ⊔ LinearMap.range (Matrix.toLin' b) := by
    refine le_antisymm ?_ (sup_le hp hq)
    rintro _ ⟨y, rfl⟩
    change Matrix.mulVec (a + b) y ∈
      LinearMap.range (Matrix.toLin' a) ⊔ LinearMap.range (Matrix.toLin' b)
    rw [Matrix.add_mulVec]
    exact Submodule.add_mem_sup ⟨y, by rw [Matrix.toLin'_apply]⟩
      ⟨y, by rw [Matrix.toLin'_apply]⟩
  have hdisj : LinearMap.range (Matrix.toLin' a) ⊓ LinearMap.range (Matrix.toLin' b) = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨⟨z, rfl⟩, w, hw⟩
    have h1 : Matrix.mulVec a (Matrix.mulVec a z) = 0 := by
      rw [← Matrix.toLin'_apply a z, ← hw, Matrix.toLin'_apply b w, Matrix.mulVec_mulVec,
        hab, Matrix.zero_mulVec]
    have h2 : Matrix.mulVec a (Matrix.mulVec a z) = Matrix.mulVec a z := by
      rw [Matrix.mulVec_mulVec, ha.eq]
    rw [h2] at h1
    exact h1
  have hfin := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (Matrix.toLin' a))
    (LinearMap.range (Matrix.toLin' b))
  rw [hdisj, ← hsup] at hfin
  simp only [finrank_bot, add_zero] at hfin
  omega

lemma rank_formAdj {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {G M : Matrix ι ι F} (hG : IsUnit G.det) :
    Matrix.rank (formAdj (RingHom.id F) G M) = Matrix.rank M := by
  have hM : M.map (RingHom.id F) = M := by ext i j; rfl
  have hX : (G⁻¹ * Matrix.transpose M).rank = M.rank := by
    rw [Matrix.rank_mul_eq_right_of_isUnit_det G⁻¹ (Matrix.transpose M)
      (Matrix.isUnit_nonsing_inv_det G hG), Matrix.rank_transpose]
  unfold formAdj
  rw [hM, Matrix.rank_mul_eq_left_of_isUnit_det G (G⁻¹ * Matrix.transpose M) hG, hX]

lemma adjoin_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    ∀ a ∈ Algebra.adjoin F (Units.val '' S), ∀ b ∈ Algebra.adjoin F (Units.val '' S),
      Commute a b := by
  intro a ha b hb
  have hgen : (Units.val '' S : Set (Matrix ι ι F)) ⊆
      (Subalgebra.centralizer F (Units.val '' S) : Set (Matrix ι ι F)) := by
    rintro x ⟨s, hs, rfl⟩
    refine (Subalgebra.mem_centralizer_iff F).mpr ?_
    intro y hy
    rcases hy with ⟨s', hs', rfl⟩
    have h := congrArg (fun u : GL ι F => (u : Matrix ι ι F)) (hS s' hs' s hs).eq
    simpa [Units.val_mul] using h
  have hA : Algebra.adjoin F (Units.val '' S) ≤ Subalgebra.centralizer F (Units.val '' S) :=
    Algebra.adjoin_le hgen
  have ha' : a ∈ Subalgebra.centralizer F (Units.val '' S) := hA ha
  have hgen2 : (Units.val '' S : Set (Matrix ι ι F)) ⊆
      (Subalgebra.centralizer F ({a} : Set (Matrix ι ι F)) : Set (Matrix ι ι F)) := by
    rintro x ⟨s, hs, rfl⟩
    refine (Subalgebra.mem_centralizer_iff F).mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have h := (Subalgebra.mem_centralizer_iff F).mp ha' (s : Matrix ι ι F) ⟨s, hs, rfl⟩
    exact h.symm
  have hA2 : Algebra.adjoin F (Units.val '' S) ≤
      Subalgebra.centralizer F ({a} : Set (Matrix ι ι F)) := Algebra.adjoin_le hgen2
  have hb' : b ∈ Subalgebra.centralizer F ({a} : Set (Matrix ι ι F)) := hA2 hb
  exact (Subalgebra.mem_centralizer_iff F).mp hb' a (Set.mem_singleton a)

lemma longRoot_mem_roots_univ {U : Type} [Group U] (D : UniversalRootDatum U)
    (γ : Fin D.rank → ℤ) (h : GGLongRoot D γ) : γ ∈ D.roots := by
  obtain ⟨w, γ₀, hγ₀, -, rfl⟩ := h
  exact CFSG.LieType.CurtisTits.weylAction_mem_roots hγ₀ w

end CFSG.StandardType.ClassicalPosition.NbrLeaf
