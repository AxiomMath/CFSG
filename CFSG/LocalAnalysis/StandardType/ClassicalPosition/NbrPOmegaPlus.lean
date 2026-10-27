module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Position
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualTwoPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelDualPairPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoRootConversePOmegaPlus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockRankDvd
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepACore
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompPOmegaPlus
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEOmegaFourMinusPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2POmegaPosDefs

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

open scoped commutatorElement

private lemma nbrpom_spinMatrix_injective (F : Type) [Field F] [CharP F 2] (n : ℕ) :
    Function.Injective (Spin.spinMatrix (Spin.quadPlus n F)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  exact Spin.ker_spinMatrix_quadPlus_eq_bot (CharP.cast_eq_zero F 2)

private lemma nbrpom_spinAction_injective (F : Type) [Field F] [CharP F 2] (n : ℕ) :
    Function.Injective (Spin.spinAction (Spin.quadPlus n F)) := by
  have hinj := nbrpom_spinMatrix_injective F n
  have hcomp : (Spin.spinMatrix (Spin.quadPlus n F) : ↥(spinGroup (Spin.quadPlus n F)) →*
      GL (Fin n ⊕ Fin n) F) =
      ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n ⊕ Fin n) F).symm.toMonoidHom.comp
        (Spin.spinAction (Spin.quadPlus n F))) := Spin.spinMatrix_eq_comp _
  intro x y hxy
  apply hinj
  rw [hcomp, MonoidHom.comp_apply, MonoidHom.comp_apply, hxy]

private lemma nbrpom_map_spinAction_injective {n f : ℕ}
    {A B : Subgroup (spinGroup (Spin.quadPlus n (GaloisField 2 f)))}
    (h : A.map (Spin.spinAction (Spin.quadPlus n (GaloisField 2 f))) =
      B.map (Spin.spinAction (Spin.quadPlus n (GaloisField 2 f)))) : A = B :=
  Subgroup.map_injective (nbrpom_spinAction_injective (GaloisField 2 f) n) h

private lemma nbrpom_center_bot (n f : ℕ) (hn : 3 ≤ n) :
    Subgroup.center ↥(spinGroup (Spin.quadPlus n (GaloisField 2 f))) = ⊥ :=
  CFSG.StandardType.RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn

private lemma nbrpom_lift_to_mem {X : Type} [Group X] (n : ℕ) (F : Type) [Field F] [CharP F 2]
    (ψ : spinGroup (Spin.quadPlus n F) →* X) {b : X} {s : GL (Fin n ⊕ Fin n) F}
    (hsj : s ∈ (Spin.spinMatrix (Spin.quadPlus n F)).range)
    (hs : IsGLLift (Spin.spinMatrix (Spin.quadPlus n F)) ψ s b) :
    ∃ s₀ : spinGroup (Spin.quadPlus n F),
      (Spin.spinMatrix (Spin.quadPlus n F)) s₀ = s ∧
        ∀ u, b⁻¹ * ψ u * b = ψ (s₀ * u * s₀⁻¹) := by
  obtain ⟨s₀, hs₀⟩ := hsj
  refine ⟨s₀, hs₀, fun u => ?_⟩
  obtain ⟨u', hu'j, hu'ψ⟩ := hs u
  have heq : u' = s₀ * u * s₀⁻¹ := by
    apply nbrpom_spinMatrix_injective F n
    rw [hu'j, ← hs₀]
    simp only [map_mul, map_inv]
  rw [hu'ψ, heq]

private lemma nbrpom_lift_inv {X : Type} [Group X] (n : ℕ) (F : Type) [Field F] [CharP F 2]
    (ψ : spinGroup (Spin.quadPlus n F) →* X) {b : X} {s : GL (Fin n ⊕ Fin n) F}
    (hsj : s ∈ (Spin.spinMatrix (Spin.quadPlus n F)).range)
    (hs : IsGLLift (Spin.spinMatrix (Spin.quadPlus n F)) ψ s b) :
    IsGLLift (Spin.spinMatrix (Spin.quadPlus n F)) ψ s⁻¹ b⁻¹ := by
  obtain ⟨s₀, hs₀, hsl₀⟩ := nbrpom_lift_to_mem n F ψ hsj hs
  intro u
  refine ⟨s₀⁻¹ * u * s₀, ?_, ?_⟩
  · change (Spin.spinMatrix (Spin.quadPlus n F)) (s₀⁻¹ * u * s₀) =
      s⁻¹ * (Spin.spinMatrix (Spin.quadPlus n F)) u * s
    rw [map_mul, map_mul, map_inv, hs₀]
  · have h := hsl₀ (s₀⁻¹ * u * s₀)
    have h1 : s₀ * (s₀⁻¹ * u * s₀) * s₀⁻¹ = u := by group
    rw [h1] at h
    rw [inv_inv]
    calc b * ψ u * b⁻¹ = b * (b⁻¹ * ψ (s₀⁻¹ * u * s₀) * b) * b⁻¹ := by rw [h]
      _ = ψ (s₀⁻¹ * u * s₀) := by group

private lemma nbrpom_lift_zpow {X : Type} [Group X] (n : ℕ) (F : Type) [Field F] [CharP F 2]
    (ψ : spinGroup (Spin.quadPlus n F) →* X) {b : X} {s : GL (Fin n ⊕ Fin n) F}
    (hsj : s ∈ (Spin.spinMatrix (Spin.quadPlus n F)).range)
    (hs : IsGLLift (Spin.spinMatrix (Spin.quadPlus n F)) ψ s b) (k : ℤ) :
    IsGLLift (Spin.spinMatrix (Spin.quadPlus n F)) ψ (s ^ k) (b ^ k) := by
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg k
  · rw [hm]; simpa using hs.pow m
  · rw [hm]
    rw [show s ^ (-(m : ℤ)) = (s ^ m)⁻¹ by rw [zpow_neg, zpow_natCast],
        show b ^ (-(m : ℤ)) = (b ^ m)⁻¹ by rw [zpow_neg, zpow_natCast]]
    exact nbrpom_lift_inv n F ψ (Subgroup.pow_mem _ hsj m) (hs.pow m)

private lemma nbrpom_lift_unique {X : Type} [Group X] (n : ℕ) (F : Type) [Field F] [CharP F 2]
    (hn : 3 ≤ n) (ψ : spinGroup (Spin.quadPlus n F) →* X)
    (hψ : ψ.ker ≤ Subgroup.center ↥(spinGroup (Spin.quadPlus n F))) {b : X}
    {s s' : GL (Fin n ⊕ Fin n) F}
    (hsj : s ∈ (Spin.spinMatrix (Spin.quadPlus n F)).range)
    (hs'j : s' ∈ (Spin.spinMatrix (Spin.quadPlus n F)).range)
    (hs : IsGLLift (Spin.spinMatrix (Spin.quadPlus n F)) ψ s b)
    (hs' : IsGLLift (Spin.spinMatrix (Spin.quadPlus n F)) ψ s' b) : s = s' := by
  obtain ⟨s₀, hs₀, hsl₀⟩ := nbrpom_lift_to_mem n F ψ hsj hs
  obtain ⟨s₁, hs₁, hsl₁⟩ := nbrpom_lift_to_mem n F ψ hs'j hs'
  have hconj : ∀ u, ψ (s₀ * u * s₀⁻¹) = ψ (s₁ * u * s₁⁻¹) := by
    intro u
    rw [← hsl₀ u, ← hsl₁ u]
  have hEq : s₀ = s₁ := conj_eq_unique_POmegaPlus n F hn ψ hψ hconj
  calc s = (Spin.spinMatrix (Spin.quadPlus n F)) s₀ := hs₀.symm
    _ = (Spin.spinMatrix (Spin.quadPlus n F)) s₁ := by rw [hEq]
    _ = s' := hs₁

private lemma nbrpom_injective {X : Type} [Group X] (n f : ℕ) (hn : 3 ≤ n)
    (ψ : spinGroup (Spin.quadPlus n (GaloisField 2 f)) →* X)
    (hψ : ψ.ker ≤ Subgroup.center ↥(spinGroup (Spin.quadPlus n (GaloisField 2 f)))) :
    Function.Injective ψ := by
  have hker : ψ.ker = ⊥ := le_bot_iff.mp (hψ.trans (le_of_eq (nbrpom_center_bot n f hn)))
  exact (MonoidHom.ker_eq_bot_iff ψ).mp hker

private theorem nbrpom_L1
    {X : Type} [Group X] (k f p : ℕ)
    (ψ : (ggU .POmegaPlus (k + 3) f).K →* X) (R Rm : Subgroup X)
    (hR0 : GGRootPosG0 .POmegaPlus (k + 3) f p ψ R Rm) :
    ∃ R' : Subgroup (ggU .POmegaPlus (k + 3) f).K,
      R'.map ψ = R ∧
      (∃ a₁ a₂ : (Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
        LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
        (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ = 0 ∧
        (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₂ = 0 ∧
        QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂ = 0 ∧
        R'.map (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f))) =
          siegelGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂) := by
  obtain ⟨β, hβ, -, u, hRu, -⟩ := hR0
  let R' : Subgroup (ggU .POmegaPlus (k + 3) f).K :=
    ((ggU .POmegaPlus (k + 3) f).D.rootGroup β).map (MulAut.conj u).toMonoidHom
  refine ⟨R', ?_, ?_⟩
  · rw [hRu]; rfl
  · obtain ⟨a₁, a₂, ha₁, ha₂, hli, hQ₁, hQ₂, horth, heq⟩ :=
      exists_siegelGroup_eq_rootGroup_POmegaPlus k f hβ u
    exact ⟨a₁, a₂, ha₁, ha₂, hli, hQ₁, hQ₂, horth, heq⟩

private theorem nbrpom_L3
    (k f : ℕ)
    (S' : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (hSU' : ∀ s ∈ S',
      s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS' : ∀ s ∈ S', ∀ s' ∈ S', Commute s s')
    (K' : Subgroup (ggU .POmegaPlus (k + 3) f).K)
    (hK'comp : IsComponentOf K' ((Subgroup.centralizer S').comap
      (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))))) :
    ∃ ε eK : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f),
      IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
        (LinearMap.toMatrix₂' (GaloisField 2 f)
          (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f))))
        (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) ε ∧
      IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK ∧
      eK * ε = eK ∧
      (eK = ε ∨ (eK ≠ ε ∧
        formAdj (RingHom.id (GaloisField 2 f))
          (LinearMap.toMatrix₂' (GaloisField 2 f)
            (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) eK ≠ eK ∧
        ε = eK + formAdj (RingHom.id (GaloisField 2 f))
          (LinearMap.toMatrix₂' (GaloisField 2 f)
            (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) eK)) ∧
      IsComponentOf K' ⁅(glBlockCentralizer
          (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S' ε :
          Subgroup (ggU .POmegaPlus (k + 3) f).K),
        (glBlockCentralizer
          (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S' ε :
          Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆ := by
  obtain ⟨ε, hε, hK'ε⟩ :=
    exists_isComponentOf_glBlockCentralizer_POmegaPlus (k + 3) (GaloisField 2 f) (by omega) S'
      hS' hK'comp
  obtain ⟨eK, heK, heKε, hsplit⟩ :=
    exists_isPrimIdemIn_of_isPrimAdjIdemIn_POmegaPlus k f S' hSU' hS' hε
  exact ⟨ε, eK, hε, heK, heKε, hsplit, hK'ε⟩

private lemma nbrpom_isUnit_det {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) :
    IsUnit (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).det := by
  have h1 : (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) =
      LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q) := rfl
  rw [h1]
  exact isUnit_iff_ne_zero.mpr (Matrix.nondegenerate_iff_det_ne_zero.mp
    ((LinearMap.BilinForm.nondegenerate_toMatrix'_iff).mpr hnd))

private lemma nbrpom_polar_matrix_transpose_eq {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] (Q : QuadraticForm F (ι → F)) :
    Matrix.transpose (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) =
      LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q) := by
  ext i j
  simp only [Matrix.transpose_apply, LinearMap.toMatrix₂'_apply,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]

private lemma nbrpom_spinMatrix_gram {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
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

private lemma nbrpom_rank_le_two_of_mulVec_mem {n : ℕ} {F : Type} [Field F] [DecidableEq F]
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (a₁ a₂ : Fin n ⊕ Fin n → F)
    (h : ∀ x, Matrix.mulVec A x ∈
      Submodule.span F ({a₁, a₂} : Set (Fin n ⊕ Fin n → F))) :
    Matrix.rank A ≤ 2 := by
  have hrange : A.mulVecLin.range ≤ Submodule.span F ({a₁, a₂} : Set (Fin n ⊕ Fin n → F)) := by
    rintro y ⟨x, rfl⟩
    simpa [Matrix.mulVecLin_apply] using h x
  have h1 : Module.finrank F ↥(A.mulVecLin.range) ≤
      Module.finrank F ↥(Submodule.span F ({a₁, a₂} : Set (Fin n ⊕ Fin n → F))) :=
    Submodule.finrank_mono hrange
  have h2 : Module.finrank F ↥(Submodule.span F ({a₁, a₂} : Set (Fin n ⊕ Fin n → F))) ≤ 2 := by
    have hc := finrank_span_le_card (R := F) ({a₁, a₂} : Set (Fin n ⊕ Fin n → F))
    refine le_trans hc ?_
    rw [show ({a₁, a₂} : Set (Fin n ⊕ Fin n → F)).toFinset =
        ({a₁, a₂} : Finset (Fin n ⊕ Fin n → F)) by simp]
    exact le_trans (Finset.card_insert_le a₁ {a₂}) (by simp)
  rw [Matrix.rank]
  exact le_trans h1 h2

private lemma nbrpom_rank_pos {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
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

private def nbrpom_HasShortElm (k f : ℕ)
    (R' : Subgroup (spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)))) : Prop :=
  ∃ g ∈ R', g ≠ 1 ∧
    Matrix.rank (((Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) g) :
      Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
        (GaloisField 2 f)) - 1) ≤ 2

private lemma nbrpom_eichler_ne_one (k f : ℕ)
    (a₁ a₂ : (Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f)
    (ha₁ : a₁ ≠ 0) (hli : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    (hQ₁ : (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ = 0)
    (hQ₂ : (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₂ = 0)
    (horth : QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂ = 0) :
    CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus (k + 3) (GaloisField 2 f))
      a₁ a₂ ≠ 1 := by
  intro h1
  let Q := Spin.quadPlus (k + 3) (GaloisField 2 f)
  have hnd : (QuadraticMap.polarBilin Q).Nondegenerate :=
    Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 f)
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
      have hbot : a₁ ∈ (⊥ : Submodule (GaloisField 2 f)
          ((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f)) := hker ▸ hmem
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
    exact CharTwo.add_self_eq_zero _
  have hcon := (LinearIndependent.pair_iff.mp hli) (QuadraticMap.polar Q x a₂)
    (QuadraticMap.polar Q x a₁) hzero
  exact hx hcon.2

private theorem nbrpom_siegel_shortElm (k f : ℕ)
    (R' : Subgroup (spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f))))
    (a₁ a₂ : (Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (hli : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    (hQ₁ : (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ = 0)
    (hQ₂ : (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₂ = 0)
    (horth : QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂ = 0)
    (hm : siegelGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂ ≤
      R'.map (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f)))) :
    nbrpom_HasShortElm k f R' := by
  classical
  let Q := Spin.quadPlus (k + 3) (GaloisField 2 f)
  let g₀ := CFSG.ClassicalGroups.Orthogonal.eichler Q a₁ a₂
  have hg₀mem : g₀ ∈ siegelGroup Q a₁ a₂ := by
    refine Subgroup.subset_closure ⟨1, ?_⟩
    rw [one_smul]
  have hg₀R : g₀ ∈ R'.map (Spin.spinAction Q) := hm hg₀mem
  obtain ⟨g, hgR, hgval⟩ := Subgroup.mem_map.mp hg₀R
  have hgne : g ≠ 1 := by
    intro hg1
    apply nbrpom_eichler_ne_one k f a₁ a₂ ha₁ hli hQ₁ hQ₂ horth
    have h := hgval
    rw [hg1, map_one] at h
    exact h.symm
  refine ⟨g, hgR, hgne, ?_⟩
  apply nbrpom_rank_le_two_of_mulVec_mem _ a₁ a₂
  intro x
  have hx : (((Spin.spinMatrix Q g) : Matrix (Fin (k + 3) ⊕ Fin (k + 3))
      (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))).mulVec x = g₀ x := by
    rw [Spin.spinMatrix_mulVec, hgval]
  have hsub : ((((Spin.spinMatrix Q g) : Matrix (Fin (k + 3) ⊕ Fin (k + 3))
      (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) - 1)).mulVec x = g₀ x - x := by
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

private lemma nbrpom_mem_glBlockCentralizer
    (k f : ℕ)
    (S' : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (K' R' : Subgroup (ggU .POmegaPlus (k + 3) f).K)
    (ε : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))
    (hK'ε : IsComponentOf K' ⁅(glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S' ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K),
      (glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S' ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆)
    (hR'K' : R' ≤ K') {g : (ggU .POmegaPlus (k + 3) f).K} (hgR : g ∈ R') :
    g ∈ (glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S' ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K) := by
  obtain ⟨Gε, hGε⟩ : ∃ Gε : Subgroup (ggU .POmegaPlus (k + 3) f).K,
      Gε = (glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)))
        S' ε : Subgroup (ggU .POmegaPlus (k + 3) f).K) := ⟨_, rfl⟩
  rw [← hGε] at hK'ε
  have hgGε : g ∈ Gε := by
    have hle : ⁅Gε, Gε⁆ ≤ Gε := by
      refine Subgroup.commutator_le.mpr (fun a ha b hb => ?_)
      rw [commutatorElement_def]
      exact Subgroup.mul_mem Gε (Subgroup.mul_mem Gε (Subgroup.mul_mem Gε ha hb)
        (Subgroup.inv_mem Gε ha)) (Subgroup.inv_mem Gε hb)
    exact hle (hK'ε.1 (hR'K' hgR))
  exact hGε ▸ hgGε

private theorem nbrpom_blockDegree_selfDual
    (k f : ℕ) (S' : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (hSU' : ∀ s ∈ S',
      s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS' : ∀ s ∈ S', ∀ s' ∈ S', Commute s s')
    (hodd' : ∀ s ∈ S', Odd (orderOf s))
    (K' R' : Subgroup (ggU .POmegaPlus (k + 3) f).K)
    (ε eK : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f))))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) ε)
    (heK : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK)
    (heKε : eK * ε = eK)
    (hK'ε : IsComponentOf K' ⁅(glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S' ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K),
      (glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S' ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆)
    (hR'K' : R' ≤ K')
    (hshort : nbrpom_HasShortElm k f R') (hself : eK = ε) :
    blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK < 4 := by
  obtain ⟨g, hgR, hg1, hgrank⟩ := hshort
  have hgmem := nbrpom_mem_glBlockCentralizer k f S' K' R' ε hK'ε hR'K' hgR
  have hgS : (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) g) ∈
      Subgroup.centralizer S' := (Subgroup.mem_comap.mp hgmem).1
  have hge : (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) g) ∈
      glFixing (1 - ε) := (Subgroup.mem_comap.mp hgmem).2
  have hgeK : (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) g) ∈
      glFixing (1 - eK) := by rw [hself]; exact hge
  have hdvd : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK ∣
      Matrix.rank (((Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) g) :
        Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
          (GaloisField 2 f)) - 1) :=
    blockDegree_dvd_rank_sub_one_of_glFixing (S := S') hS' hodd' heK hgS hgeK
  have hgne : (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) g) ≠ 1 := by
    intro h
    exact hg1 (nbrpom_spinMatrix_injective (GaloisField 2 f) (k + 3) (by rw [h, map_one]))
  have hrank_pos : 1 ≤ Matrix.rank
      (((Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) g) :
        Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
          (GaloisField 2 f)) - 1) :=
    nbrpom_rank_pos (fun h => hgne (Units.ext h))
  have hle : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK ≤ 2 :=
    le_trans (Nat.le_of_dvd hrank_pos hdvd) hgrank
  omega

private theorem nbrpom_blockDegree_dualPair
    (k f : ℕ) (S' : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (hSU' : ∀ s ∈ S',
      s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS' : ∀ s ∈ S', ∀ s' ∈ S', Commute s s')
    (hodd' : ∀ s ∈ S', Odd (orderOf s))
    (K' R' : Subgroup (ggU .POmegaPlus (k + 3) f).K)
    (ε eK : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f))))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) ε)
    (heK : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK)
    (heKε : eK * ε = eK)
    (hK'ε : IsComponentOf K' ⁅(glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S' ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K),
      (glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S' ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆)
    (hR'K' : R' ≤ K')
    (hshort : nbrpom_HasShortElm k f R')
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) eK ≠ eK)
    (heq : ε = eK + formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) eK) :
    blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK < 2 := by
  let Q := Spin.quadPlus (k + 3) (GaloisField 2 f)
  let G := LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin Q)
  obtain ⟨g, hgR, hg1, hgrank⟩ := hshort
  have hgmem := nbrpom_mem_glBlockCentralizer k f S' K' R' ε hK'ε hR'K' hgR
  have hgS : (Spin.spinMatrix Q g) ∈ Subgroup.centralizer S' :=
    (Subgroup.mem_comap.mp hgmem).1
  have hge : (Spin.spinMatrix Q g) ∈ glFixing (1 - ε) := (Subgroup.mem_comap.mp hgmem).2
  have hGdet : IsUnit G.det :=
    nbrpom_isUnit_det Q (Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 f))
  have hGh : Matrix.transpose (G.map (RingHom.id (GaloisField 2 f))) = G := by
    simpa using nbrpom_polar_matrix_transpose_eq Q
  have hSU : ∀ s ∈ S', Matrix.transpose ((s : Matrix (Fin (k + 3) ⊕ Fin (k + 3))
        (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)).map
          (RingHom.id (GaloisField 2 f))) * G *
      (s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
        (GaloisField 2 f)) = G := by
    intro s hs
    obtain ⟨gs, rfl⟩ := hSU' s hs
    simpa using nbrpom_spinMatrix_gram Q gs
  have hgiso : Matrix.transpose (((Spin.spinMatrix Q g) :
      Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
        (GaloisField 2 f)).map (RingHom.id (GaloisField 2 f))) * G *
      (Spin.spinMatrix Q g) = G := by
    simpa using nbrpom_spinMatrix_gram Q g
  have hge' : (Spin.spinMatrix Q g) ∈
      glFixing (1 - (eK + formAdj (RingHom.id (GaloisField 2 f)) G eK)) := by
    rw [← heq]
    exact hge
  have hdvd : 2 * blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK ∣
      Matrix.rank (((Spin.spinMatrix Q g) :
        Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
          (GaloisField 2 f)) - 1) :=
    two_mul_blockDegree_dvd_rank_sub_one_of_formAdj_ne (RingHom.id (GaloisField 2 f))
      (fun x => rfl) hGdet hGh hSU hS' hodd' heK hadj hgS hgiso hge'
  have hgne : (Spin.spinMatrix Q g) ≠ 1 := by
    intro h
    exact hg1 (nbrpom_spinMatrix_injective (GaloisField 2 f) (k + 3) (by rw [h, map_one]))
  have hrank_pos : 1 ≤ Matrix.rank (((Spin.spinMatrix Q g) :
      Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
        (GaloisField 2 f)) - 1) := nbrpom_rank_pos (fun h => hgne (Units.ext h))
  have hle : 2 * blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK ≤ 2 :=
    le_trans (Nat.le_of_dvd hrank_pos hdvd) hgrank
  omega

private theorem nbrpom_L4
    (k f : ℕ) (S' : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (hSU' : ∀ s ∈ S',
      s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS' : ∀ s ∈ S', ∀ s' ∈ S', Commute s s')
    (hodd' : ∀ s ∈ S', Odd (orderOf s))
    (K' R' : Subgroup (ggU .POmegaPlus (k + 3) f).K)
    (ε eK : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f))))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) ε)
    (heK : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK)
    (heKε : eK * ε = eK)
    (hsplit : eK = ε ∨ (eK ≠ ε ∧
      formAdj (RingHom.id (GaloisField 2 f))
        (LinearMap.toMatrix₂' (GaloisField 2 f)
          (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) eK ≠ eK ∧
      ε = eK + formAdj (RingHom.id (GaloisField 2 f))
        (LinearMap.toMatrix₂' (GaloisField 2 f)
          (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) eK))
    (hK'ε : IsComponentOf K' ⁅(glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S' ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K),
      (glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S' ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆)
    (hR'K' : R' ≤ K')
    (hgeo : ∃ a₁ a₂ : (Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
      LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
      (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ = 0 ∧
      (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₂ = 0 ∧
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂ = 0 ∧
      R'.map (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f))) =
        siegelGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂) :
    (eK = ε ∧ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK < 2) ∨
      (eK = ε ∧ 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK ∧
        blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK < 4) ∨
      (eK ≠ ε ∧ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK < 2) := by
  have hshort : nbrpom_HasShortElm k f R' := by
    obtain ⟨a₁, a₂, ha₁, ha₂, hli, hQ₁, hQ₂, horth, hm⟩ := hgeo
    exact nbrpom_siegel_shortElm k f R' a₁ a₂ ha₁ ha₂ hli hQ₁ hQ₂ horth hm.ge
  rcases hsplit with hself | ⟨hne, hadj, heq⟩
  · by_cases hd : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK < 2
    · exact Or.inl ⟨hself, hd⟩
    · exact Or.inr (Or.inl ⟨hself, by omega,
        nbrpom_blockDegree_selfDual k f S' hSU' hS' hodd' K' R' ε eK hε heK heKε hK'ε
          hR'K' hshort hself⟩)
  · exact Or.inr (Or.inr ⟨hne,
      nbrpom_blockDegree_dualPair k f S' hSU' hS' hodd' K' R' ε eK hε heK heKε hK'ε
        hR'K' hshort hadj heq⟩)

private lemma nbrpom_formAdj_id {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (G a : Matrix ι ι F) : formAdj (RingHom.id F) G a = G⁻¹ * a.transpose * G := by
  unfold formAdj
  rw [show a.map (⇑(RingHom.id F)) = a from by ext i j; rfl]

private lemma nbrpom_formAdj_neg {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (σ : F →+* F) (G a : Matrix ι ι F) : formAdj σ G (-a) = -formAdj σ G a := by
  have h : formAdj σ G (-a) + formAdj σ G a = 0 := by
    rw [← Geo.formAdj_add, neg_add_cancel]
    unfold formAdj
    rw [Matrix.map_zero σ (map_zero σ), Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul]
  exact eq_neg_of_add_eq_zero_left h

private lemma nbrpom_polar_eq_dot {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (x y : ι → F) :
    QuadraticMap.polar Q x y =
      dotProduct x ((LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).mulVec y) := by
  have h1 : (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) =
      LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q) := rfl
  rw [h1]
  rw [← Matrix.toBilin'_apply' (LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q)) x y,
    Matrix.toBilin'_toMatrix', QuadraticMap.polarBilin_apply_apply]

private lemma nbrpom_dotProduct_mulVec_transpose {ι F : Type} [Fintype ι] [CommSemiring F]
    (M : Matrix ι ι F) (x y : ι → F) :
    dotProduct (M.mulVec x) y = dotProduct x (M.transpose.mulVec y) := by
  exact ((Matrix.dotProduct_mulVec x M.transpose y).trans
    (by rw [Matrix.vecMul_transpose])).symm

private lemma nbrpom_formAdj_mulVec {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {G a : Matrix ι ι F} (hG : IsUnit G.det) (y : ι → F) :
    G.mulVec ((formAdj (RingHom.id F) G a).mulVec y) = a.transpose.mulVec (G.mulVec y) := by
  have hmat : G * (G⁻¹ * a.transpose * G) = a.transpose * G := by
    rw [← Matrix.mul_assoc G (G⁻¹ * a.transpose) G,
      ← Matrix.mul_assoc G G⁻¹ a.transpose, Matrix.mul_nonsing_inv G hG, Matrix.one_mul]
  rw [nbrpom_formAdj_id, Matrix.mulVec_mulVec, hmat, Matrix.mulVec_mulVec]

private lemma nbrpom_formAdj_apply {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
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

private lemma nbrpom_polar_selfAdjoint {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F))
    (hG : IsUnit (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).det)
    {E : Matrix ι ι F}
    (hE : formAdj (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) E = E) (x y : ι → F) :
    QuadraticMap.polar Q (E.mulVec x) y = QuadraticMap.polar Q x (E.mulVec y) := by
  rw [nbrpom_formAdj_apply Q hG E x y, hE]

private theorem nbrpom_hnm_minusFour
    (k f : ℕ) (S' : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (K' R' : Subgroup (ggU .POmegaPlus (k + 3) f).K)
    (eK : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))
    (heK : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK)
    (hK'e : IsComponentOf K' ⁅(glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S' eK :
        Subgroup (ggU .POmegaPlus (k + 3) f).K),
      (glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S' eK :
        Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆)
    (hR'K' : R' ≤ K')
    (hadjE : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) eK = eK)
    (a₁ a₂ : (Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (hli : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    (hQ₁ : (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ = 0)
    (hQ₂ : (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₂ = 0)
    (horth : QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂ = 0)
    (hm : R'.map (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f))) =
      siegelGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂) :
    ¬ (eK.rank = 4 ∧ ∀ x y : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f),
      Matrix.mulVec eK x = x → Matrix.mulVec eK y = y →
      (Spin.quadPlus (k + 3) (GaloisField 2 f)) x = 0 →
      (Spin.quadPlus (k + 3) (GaloisField 2 f)) y = 0 →
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x y = 0 →
      ¬ LinearIndependent (GaloisField 2 f) ![x, y]) := by
  classical
  rintro ⟨hrank4, hno⟩
  let Q := Spin.quadPlus (k + 3) (GaloisField 2 f)
  let G := LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin Q)
  have hGdet : IsUnit G.det :=
    nbrpom_isUnit_det Q (Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 f))
  have hker : LinearMap.ker (QuadraticMap.polarBilin Q) = ⊥ :=
    LinearMap.BilinForm.Nondegenerate.ker_eq_bot
      (Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 f))
  let g₀ := CFSG.ClassicalGroups.Orthogonal.eichler Q a₁ a₂
  have hg₀mem : g₀ ∈ siegelGroup Q a₁ a₂ := by
    refine Subgroup.subset_closure ⟨1, ?_⟩
    rw [one_smul]
  have hg₀R : g₀ ∈ R'.map (Spin.spinAction Q) := by
    rw [hm]
    exact hg₀mem
  obtain ⟨g, hgR, hgval⟩ := Subgroup.mem_map.mp hg₀R
  have hGε_le : ⁅(glBlockCentralizer (Spin.spinMatrix Q) S' eK :
        Subgroup (ggU .POmegaPlus (k + 3) f).K),
      (glBlockCentralizer (Spin.spinMatrix Q) S' eK :
        Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆ ≤
      (glBlockCentralizer (Spin.spinMatrix Q) S' eK :
        Subgroup (ggU .POmegaPlus (k + 3) f).K) := by
    refine Subgroup.commutator_le.mpr (fun a ha b hb => ?_)
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  have hgGε : g ∈ (glBlockCentralizer (Spin.spinMatrix Q) S' eK :
      Subgroup (ggU .POmegaPlus (k + 3) f).K) :=
    hGε_le (hK'e.1 (hR'K' hgR))
  have hgfix : (Spin.spinMatrix Q g) * (1 - eK) = 1 - eK :=
    (Subgroup.mem_comap.mp hgGε).2
  have hfix : ∀ v, g₀ ((1 - eK).mulVec v) = (1 - eK).mulVec v := by
    intro v
    have h := congrArg (fun M : Matrix (Fin (k + 3) ⊕ Fin (k + 3))
        (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f) => M.mulVec v) hgfix
    have h2 : (Spin.spinAction Q g) ((1 - eK).mulVec v) = (1 - eK).mulVec v := by
      rw [← Spin.spinMatrix_mulVec]
      rw [Matrix.mulVec_mulVec v ((Spin.spinMatrix Q g) : Matrix (Fin (k + 3) ⊕ Fin (k + 3))
        (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) (1 - eK)]
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
    set x : (Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f := (1 - eK).mulVec v with hx
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
        ((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f)) := hker ▸ hmem
    simpa using hbot
  have hw₂ : (1 - eK).mulVec a₂ = 0 := by
    have hmem : (1 - eK).mulVec a₂ ∈ LinearMap.ker (QuadraticMap.polarBilin Q) := by
      rw [LinearMap.mem_ker]
      apply LinearMap.ext; intro v
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm, ← hsa v a₂]
      exact (hpolar v).2
    have hbot : (1 - eK).mulVec a₂ ∈ (⊥ : Submodule (GaloisField 2 f)
        ((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f)) := hker ▸ hmem
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

private lemma nbrpom_L6 {X : Type} [Group X] [Finite X]
    (n f : ℕ) (ψ : (ggU .POmegaPlus n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hH : GGSixPosHyp .POmegaPlus n f ψ p G₀ B₁ D J L x) : 4 ≤ n := by
  have hAdm : CFSG.Open.StatedLieAdmissible .POmegaPlus n 2 f :=
    CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hH.2.2.1
  exact hAdm.2.2

private lemma nbrpomx_rank_lt_of_mul_eq {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
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

private lemma nbrpomx_selfDual_not_below_dualPair {ι F : Type} [Fintype ι] [DecidableEq ι]
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

private lemma nbrpomx_blockDegree_le_of_mul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
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

private lemma nbrpomx_mul_formAdj_eq_zero {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
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

private lemma nbrpomx_finrank_range_add_of_orth {ι F : Type*} [Fintype ι] [DecidableEq ι]
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

private lemma nbrpomx_rank_formAdj {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {G M : Matrix ι ι F} (hG : IsUnit G.det) :
    Matrix.rank (formAdj (RingHom.id F) G M) = Matrix.rank M := by
  have hM : M.map (RingHom.id F) = M := by ext i j; rfl
  have hX : (G⁻¹ * Matrix.transpose M).rank = M.rank := by
    rw [Matrix.rank_mul_eq_right_of_isUnit_det G⁻¹ (Matrix.transpose M)
      (Matrix.isUnit_nonsing_inv_det G hG), Matrix.rank_transpose]
  unfold formAdj
  rw [hM, Matrix.rank_mul_eq_left_of_isUnit_det G (G⁻¹ * Matrix.transpose M) hG, hX]

private lemma nbrpomx_adjoin_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
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

private lemma nbrpomx_longRoot_mem_roots_univ {U : Type} [Group U] (D : UniversalRootDatum U)
    (γ : Fin D.rank → ℤ) (h : GGLongRoot D γ) : γ ∈ D.roots := by
  obtain ⟨w, γ₀, hγ₀, -, rfl⟩ := h
  exact CFSG.LieType.CurtisTits.weylAction_mem_roots hγ₀ w

private lemma nbrpomx_mem_sup_central {U : Type} [Group U] {K Z : Subgroup U}
    (hZ : Z ≤ Subgroup.center U) {x : U} : x ∈ K ⊔ Z ↔ ∃ k ∈ K, ∃ z ∈ Z, k * z = x := by
  haveI : Z.Normal := Subgroup.normal_of_le_center hZ
  exact Subgroup.mem_sup_of_normal_right

private lemma nbrpomx_commutatorElement_mul_central_left {U : Type} [Group U]
    {c : U} (hc : c ∈ Subgroup.center U) (g h : U) : ⁅g * c, h⁆ = ⁅g, h⁆ := by
  have e : c * h * c⁻¹ = h := by
    rw [← Subgroup.mem_center_iff.mp hc h, mul_inv_cancel_right]
  simp only [commutatorElement_def, mul_inv_rev]
  calc g * c * h * (c⁻¹ * g⁻¹) * h⁻¹ = g * (c * h * c⁻¹) * g⁻¹ * h⁻¹ := by group
    _ = g * h * g⁻¹ * h⁻¹ := by rw [e]

private lemma nbrpomx_commutatorElement_mul_central_right {U : Type} [Group U]
    {c : U} (hc : c ∈ Subgroup.center U) (g h : U) : ⁅g, h * c⁆ = ⁅g, h⁆ := by
  have e : g * c * g⁻¹ = c := by
    rw [Subgroup.mem_center_iff.mp hc g, mul_inv_cancel_right]
  simp only [commutatorElement_def, mul_inv_rev]
  calc g * (h * c) * g⁻¹ * (c⁻¹ * h⁻¹)
      = (g * h * g⁻¹) * (g * c * g⁻¹) * (c⁻¹ * h⁻¹) := by group
    _ = (g * h * g⁻¹) * c * c⁻¹ * h⁻¹ := by rw [e]; group
    _ = g * h * g⁻¹ * h⁻¹ := by group

private lemma nbrpomx_commutator_sup_central_le {U : Type} [Group U] {K Z : Subgroup U}
    (hZ : Z ≤ Subgroup.center U) : ⁅K ⊔ Z, K ⊔ Z⁆ ≤ ⁅K, K⁆ := by
  refine Subgroup.commutator_le.2 fun x hx y hy => ?_
  obtain ⟨k, hk, z, hz, rfl⟩ := (nbrpomx_mem_sup_central hZ).1 hx
  obtain ⟨k', hk', z', hz', rfl⟩ := (nbrpomx_mem_sup_central hZ).1 hy
  rw [nbrpomx_commutatorElement_mul_central_left (hZ hz),
    nbrpomx_commutatorElement_mul_central_right (hZ hz')]
  exact Subgroup.commutator_mem_commutator hk hk'

private lemma nbrpomx_perfect_le_of_le_sup_center {U : Type} [Group U] {J K Z : Subgroup U}
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
    refine (nbrpomx_commutator_sup_central_le hZ).trans ?_
    simpa using Subgroup.commutator_le_sup K K
  exact hJle.trans ((Subgroup.commutator_mono hle hle).trans hcommK)

private lemma nbrpomx_commute_adjoin {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
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

private lemma nbrpomx_mul_e_eq_smul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
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

private lemma nbrpomx_glBlockCentralizer_le (k f : ℕ)
    {S S_e : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    (heSe : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S_e)) :
    glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S_e e ≤
      glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S e := by
  intro u hu
  obtain ⟨huc, hufix⟩ : (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) u ∈
      Subgroup.centralizer S_e ⊓ glFixing (1 - e) := Subgroup.mem_comap.mp hu
  have hfix : (((Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) u :
      GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) :
      Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) *
      (1 - e) = 1 - e := hufix
  have hcomm_e : (((Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) u :
      GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) :
      Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) * e =
      e * (((Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) u :
      GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) :
      Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) :=
    nbrpomx_commute_adjoin (S := S_e) huc heSe
  refine Subgroup.mem_comap.mpr ⟨Subgroup.mem_centralizer_iff.mpr ?_, hufix⟩
  intro s hs
  have hsA : (s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
      (GaloisField 2 f)) ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S) :=
    Algebra.subset_adjoin ⟨s, hs, rfl⟩
  obtain ⟨c, hc⟩ := nbrpomx_mul_e_eq_smul he hdeg _ hsA
  have hse : (s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
      (GaloisField 2 f)) * e =
      e * (s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
        (GaloisField 2 f)) :=
    (nbrpomx_adjoin_comm hS (s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
      (GaloisField 2 f)) hsA e he.1).eq
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  set G := (((Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) u :
      GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) :
      Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))
    with hGdef
  set Sm := (s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
    (GaloisField 2 f)) with hSmdef
  have hG : G = G * e + (1 - e) := by
    have h := hfix
    rw [Matrix.mul_sub, Matrix.mul_one] at h
    calc G = (G - G * e) + G * e := by abel
      _ = (1 - e) + G * e := by rw [h]
      _ = G * e + (1 - e) := by abel
  have hSG : Sm * G = c • (G * e) + (Sm - c • e) := by
    calc Sm * G = Sm * (G * e + (1 - e)) := by rw [← hG]
      _ = Sm * (G * e) + (Sm - Sm * e) := by
        rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one]
      _ = c • (G * e) + (Sm - c • e) := by
        rw [hc, hcomm_e, ← Matrix.mul_assoc, hc, Matrix.smul_mul]
  have hGS : G * Sm = c • (G * e) + (Sm - c • e) := by
    calc G * Sm = (G * e + (1 - e)) * Sm := by rw [← hG]
      _ = G * (e * Sm) + (Sm - e * Sm) := by
        rw [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      _ = c • (G * e) + (Sm - c • e) := by rw [← hse, hc, Matrix.mul_smul]
  rw [hSG, hGS]

private lemma nbrpomx_blockField_inv {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
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

private lemma nbrpomx_dualPair_orth (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈
      (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e_J : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (heJ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (hpair : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e_J ≠ e_J) :
    e_J * formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e_J = 0 := by
  let F := GaloisField 2 f
  let Q := Spin.quadPlus (k + 3) F
  let G := LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)
  have hG : IsUnit G.det :=
    nbrpom_isUnit_det Q (Spin.nondegenerate_polarBilin_quadPlus (k + 3) F)
  have hGh : Matrix.transpose (G.map (RingHom.id F)) = G := by
    have hmap : G.map (RingHom.id F) = G := by ext i j; rfl
    rw [hmap]
    exact nbrpom_polar_matrix_transpose_eq Q
  have hSU_iso : ∀ s ∈ S, Matrix.transpose (((s : GL (Fin (k + 3) ⊕ Fin (k + 3)) F) :
      Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) F).map
        (RingHom.id F)) * G *
      ((s : GL (Fin (k + 3) ⊕ Fin (k + 3)) F) :
        Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) F) = G := by
    intro s hs
    obtain ⟨s₀, hs₀⟩ := hSU s hs
    rw [← hs₀]
    have hmap : (((Spin.spinMatrix Q s₀ : GL (Fin (k + 3) ⊕ Fin (k + 3)) F) :
        Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) F).map
          (RingHom.id F)) = ((Spin.spinMatrix Q s₀ : GL (Fin (k + 3) ⊕ Fin (k + 3)) F) :
        Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) F) := by
      ext i j; rfl
    rw [hmap]
    exact nbrpom_spinMatrix_gram Q s₀
  refine nbrpomx_mul_formAdj_eq_zero G hG hGh ?_ heJ ?_ hpair
  · intro a b ha hb
    exact (nbrpomx_adjoin_comm hS a ha b hb).eq
  · exact Geo.formAdj_mem_adjoin (RingHom.id F) hG hSU_iso heJ.1

private theorem nbrpomx_base
    {X : Type} [Group X] [Finite X] (k f : ℕ)
    (ψ : (ggU .POmegaPlus (k + 3) f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hH : GGSixPosHyp .POmegaPlus (k + 3) f ψ p G₀ B₁ D J L x) :
    ∃ (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
      (J' : Subgroup (ggU .POmegaPlus (k + 3) f).K),
      (∀ s ∈ S, s ∈
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range) ∧
      (∀ s ∈ S, ∀ s' ∈ S, Commute s s') ∧
      (∀ s ∈ S, Odd (orderOf s)) ∧
      (∀ s : GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f),
        s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range →
        (∃ d ∈ D,
          IsGLLift (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) ψ s d) →
        s ∈ S) ∧
      IsComponentOf J' ((Subgroup.centralizer S).comap
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)))) ∧
      J'.map ψ = J := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  let F := GaloisField 2 f
  let j : spinGroup (Spin.quadPlus (k + 3) F) →* GL (Fin (k + 3) ⊕ Fin (k + 3)) F :=
    Spin.spinMatrix (Spin.quadPlus (k + 3) F)
  have hinj : Function.Injective j := nbrpom_spinMatrix_injective F (k + 3)
  let P : GL (Fin (k + 3) ⊕ Fin (k + 3)) F → Prop := fun s => s ∈ j.range
  let S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) F) := {s | P s ∧ ∃ d ∈ D, IsGLLift j ψ s d}
  have hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (D : Set X)) := by
    rw [h1]; exact h15
  have hlift : ∀ d ∈ D, ∃ s : GL (Fin (k + 3) ⊕ Fin (k + 3)) F, P s ∧ IsGLLift j ψ s d := by
    intro d hd
    have hdB : d ∈ B₁ := h11 hd
    have hb : GGPsiInnerDiag (Spin.plusDatum (k + 3) F (by omega)) ψ d := h8 d hdB
    obtain ⟨s₀, hs₀⟩ := exists_conj_eq_POmegaPlus (k + 3) F (by omega) ψ h2 hb
    exact ⟨j s₀, ⟨s₀, rfl⟩, fun u => ⟨s₀ * u * s₀⁻¹, by
      show (Spin.spinMatrix (Spin.quadPlus (k + 3) F)) (s₀ * u * s₀⁻¹) =
        (Spin.spinMatrix (Spin.quadPlus (k + 3) F)) s₀ *
          (Spin.spinMatrix (Spin.quadPlus (k + 3) F)) u *
            ((Spin.spinMatrix (Spin.quadPlus (k + 3) F)) s₀)⁻¹
      rw [map_mul, map_mul, map_inv], hs₀ u⟩⟩
  obtain ⟨J', hJ'comp, hJ'map⟩ :=
    StepA.exists_isComponentOf_comap_lift_of_isGLLift j hinj ψ h2 P hJ hlift
  refine ⟨S, J', ?_, ?_, ?_, ?_, hJ'comp, hJ'map⟩
  · intro s hs
    exact hs.1
  · intro s hs s' hs'
    obtain ⟨d, hdD, hsl⟩ := hs.2
    obtain ⟨d', hd'D, hs'l⟩ := hs'.2
    have hdB : d ∈ B₁ := h11 hdD
    have hd'B : d' ∈ B₁ := h11 hd'D
    have hbb' : Commute d d' :=
      congrArg Subtype.val (h9.1.is_comm.comm ⟨d, hdB⟩ ⟨d', hd'B⟩)
    obtain ⟨s₀, hs₀, hsl₀⟩ := nbrpom_lift_to_mem (k + 3) F ψ hs.1 hsl
    obtain ⟨s₁, hs₁, hsl₁⟩ := nbrpom_lift_to_mem (k + 3) F ψ hs'.1 hs'l
    have hc := conj_eq_commute_POmegaPlus (k + 3) F (by omega) ψ h2 hbb' hsl₀ hsl₁
    have hc' : s * s' = s' * s := by
      rw [← hs₀, ← hs₁, ← map_mul, ← map_mul, hc.eq]
    exact hc'
  · intro s hs
    obtain ⟨d, hdD, hsl⟩ := hs.2
    have hdB : d ∈ B₁ := h11 hdD
    have hdpow : d ^ p = 1 := h9.2 d hdB
    have hspowj : s ^ p ∈ j.range := Subgroup.pow_mem _ hs.1 p
    have hslpow : IsGLLift j ψ (s ^ p) 1 := by
      have h := hsl.pow p
      rwa [hdpow] at h
    have huniq : s ^ p = 1 :=
      nbrpom_lift_unique (k + 3) F (by omega) ψ h2 hspowj (Subgroup.one_mem _) hslpow
        isGLLift_one
    have hdvd : orderOf s ∣ p := orderOf_dvd_iff_pow_eq_one.mpr huniq
    have hpodd : Odd p := h5.odd_of_ne_two h6
    rcases h5.eq_one_or_self_of_dvd (orderOf s) hdvd with h | h
    · rw [h]; exact odd_one
    · rw [h]; exact hpodd
  · intro s hsP hsl
    exact ⟨hsP, hsl⟩

private theorem nbrpomx_J_degree
    {X : Type} [Group X] [Finite X] (k f : ℕ)
    (ψ : (ggU .POmegaPlus (k + 3) f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hH : GGSixPosHyp .POmegaPlus (k + 3) f ψ p G₀ B₁ D J L x)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (J' : Subgroup (ggU .POmegaPlus (k + 3) f).K)
    (ε e_J : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))
    (hSU : ∀ s ∈ S, s ∈
      (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    (hJ'map : J'.map ψ = J)
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f))))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    (heJ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (heJε : e_J * ε = e_J)
    (hsplit : e_J = ε ∨ (e_J ≠ ε ∧
      formAdj (RingHom.id (GaloisField 2 f))
        (LinearMap.toMatrix₂' (GaloisField 2 f)
          (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e_J ≠ e_J ∧
      ε = e_J + formAdj (RingHom.id (GaloisField 2 f))
        (LinearMap.toMatrix₂' (GaloisField 2 f)
          (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e_J))
    (hJ'ε : IsComponentOf J' ⁅(glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K),
      (glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆) :
    (e_J = ε ∧ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2) ∨
      (e_J = ε ∧ 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J ∧
        blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 4) ∨
      (e_J ≠ ε ∧ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  have hadm : StatedLieAdmissible .POmegaPlus (k + 3) 2 f :=
    CFSG.Blueprint.LieModel.admissible h3
  have hf : 1 ≤ f := hadm.2.1
  have hc : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  rcases hsplit with heq | ⟨hne, -, -⟩
  · by_cases hd : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2
    · exact Or.inl ⟨heq, hd⟩
    · by_cases h4 : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 4
      · exact Or.inr (Or.inl ⟨heq, by omega, h4⟩)
      · refine absurd ?_ h29
        rw [← hJ'map]
        exact ggSixLSevenFieldExtCase_POmegaPlus (k + 3) (GaloisField 2 f) (by omega) f hc ψ h2
          S hSU hS hodd hε hJ'ε heJ heJε (Or.inl ⟨heq, by omega⟩)
  · by_cases hd : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2
    · exact Or.inr (Or.inr ⟨hne, hd⟩)
    · refine absurd ?_ h29
      rw [← hJ'map]
      exact ggSixLSevenFieldExtCase_POmegaPlus (k + 3) (GaloisField 2 f) (by omega) f hc ψ h2
        S hSU hS hodd hε hJ'ε heJ heJε (Or.inr ⟨hne, by omega⟩)

private theorem nbrpomx_J_split
    {X : Type} [Group X] [Finite X] (k f : ℕ)
    (ψ : (ggU .POmegaPlus (k + 3) f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hH : GGSixPosHyp .POmegaPlus (k + 3) f ψ p G₀ B₁ D J L x) :
    ∃ (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
      (J' : Subgroup (ggU .POmegaPlus (k + 3) f).K)
      (ε e_J : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
        (GaloisField 2 f)),
      (∀ s ∈ S, s ∈
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range) ∧
      (∀ s ∈ S, ∀ s' ∈ S, Commute s s') ∧
      (∀ s ∈ S, Odd (orderOf s)) ∧
      (∀ s : GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f),
        s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range →
        (∃ d ∈ D,
          IsGLLift (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) ψ s d) →
        s ∈ S) ∧
      IsComponentOf J' ((Subgroup.centralizer S).comap
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)))) ∧
      J'.map ψ = J ∧
      IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
        (LinearMap.toMatrix₂' (GaloisField 2 f)
          (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f))))
        (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε ∧
      IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J ∧
      e_J * ε = e_J ∧
      (e_J = ε ∨ (e_J ≠ ε ∧
        formAdj (RingHom.id (GaloisField 2 f))
          (LinearMap.toMatrix₂' (GaloisField 2 f)
            (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e_J ≠ e_J ∧
        ε = e_J + formAdj (RingHom.id (GaloisField 2 f))
          (LinearMap.toMatrix₂' (GaloisField 2 f)
            (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e_J)) ∧
      IsComponentOf J' ⁅(glBlockCentralizer
          (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε :
          Subgroup (ggU .POmegaPlus (k + 3) f).K),
        (glBlockCentralizer
          (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε :
          Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆ ∧
      ((e_J = ε ∧ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2) ∨
       (e_J = ε ∧ 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J ∧
          blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 4) ∨
       (e_J ≠ ε ∧
          blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2)) := by
  obtain ⟨S, J', hSU, hS, hodd, hfull, hJ'comp, hJ'map⟩ :=
    nbrpomx_base k f ψ p G₀ B₁ D J L x hH
  obtain ⟨ε, e_J, hε, heJ, heJε, hsplit, hJ'ε⟩ :=
    nbrpom_L3 k f S hSU hS J' hJ'comp
  exact ⟨S, J', ε, e_J, hSU, hS, hodd, hfull, hJ'comp, hJ'map, hε, heJ, heJε, hsplit, hJ'ε,
    nbrpomx_J_degree k f ψ p G₀ B₁ D J L x hH S J' ε e_J hSU hS hodd hJ'map hε
      heJ heJε hsplit hJ'ε⟩

private theorem nbrpomx_J_omega
    {X : Type} [Group X] [Finite X] (k f : ℕ)
    (ψ : (ggU .POmegaPlus (k + 3) f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hH : GGSixPosHyp .POmegaPlus (k + 3) f ψ p G₀ B₁ D J L x)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (J' : Subgroup (ggU .POmegaPlus (k + 3) f).K)
    (ε e_J : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))
    (hSU : ∀ s ∈ S, s ∈
      (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    (hfull : ∀ s : GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f),
      s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range →
      (∃ d ∈ D,
        IsGLLift (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) ψ s d) →
      s ∈ S)
    (hJ'comp : IsComponentOf J' ((Subgroup.centralizer S).comap
      (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)))))
    (hJ'map : J'.map ψ = J)
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f))))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    (heJ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (hJ'ε : IsComponentOf J' ⁅(glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K),
      (glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆)
    (hcase : e_J = ε ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2) :
    ∃ (R Rm : Subgroup X), R ≤ J ∧ Rm ≤ J ∧
      GGRootPosG0 .POmegaPlus (k + 3) f p ψ R Rm ∧
      ((∃ (t' : StatedLieTag) (mJ : ℕ) (βJ : Fin (ggU t' mJ f).D.rank → ℤ),
          (t' = .POmegaPlus ∨ t' = .POmegaMinus) ∧ 3 ≤ mJ ∧
          βJ ∈ (ggU t' mJ f).D.roots ∧ GGLongRoot (ggU t' mJ f).D βJ ∧
          GGRootVia (ggU t' mJ f) J R βJ ∧
          Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e_J)) = 2 * mJ) ∨
        (∃ (kJ : ℕ) (βJ : Fin (ggU .PSL (kJ + 1) f).D.rank → ℤ),
          kJ + 1 = 2 ∧ βJ ∈ (ggU .PSL (kJ + 1) f).D.roots ∧
          GGRootVia (ggU .PSL (kJ + 1) f) J R βJ ∧
          Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e_J)) =
            2 * (kJ + 1))) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  let F := GaloisField 2 f
  let Q := Spin.quadPlus (k + 3) F
  let G := LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)
  have hf : 1 ≤ f := (CFSG.Blueprint.LieModel.admissible h3).2.1
  have hadj : formAdj (RingHom.id F) G e_J = e_J := by
    rw [hcase.1]; exact hε.2.2.2.1
  have hJe : IsComponentOf J' ⁅(glBlockCentralizer (Spin.spinMatrix Q) S e_J :
        Subgroup (ggU .POmegaPlus (k + 3) f).K),
      (glBlockCentralizer (Spin.spinMatrix Q) S e_J :
        Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆ := by
    rw [hcase.1]; exact hJ'ε
  have hnm : ¬ (e_J.rank = 4 ∧ ∀ x y : (Fin (k + 3) ⊕ Fin (k + 3)) → F,
      Matrix.mulVec e_J x = x → Matrix.mulVec e_J y = y → Q x = 0 → Q y = 0 →
      QuadraticMap.polar Q x y = 0 → ¬ LinearIndependent F ![x, y]) := by
    rintro ⟨hrank4, hminus⟩
    have hmain := ggSixLSevenFieldExtCase_omegaFourMinus_POmegaPlus (k + 3) F (by omega) f
      (GaloisField.card 2 f (by omega)) ψ h2 S hSU hS hodd hε hJ'ε
      (hcase.1 ▸ hcase.2) (hcase.1 ▸ hrank4) (hcase.1 ▸ hminus)
    exact h29 (hJ'map ▸ hmain)
  obtain ⟨t', m, ι, β₀, hdisj, hlong, hιcent, hιrange, a₁, a₂, b₁, b₂,
    hQ, h₁, h₂, h₀, hAl, hAl'⟩ :=
    exists_blockModel_selfDual_POmegaPlus_explicit k f hf S hSU hS hodd heJ hadj hcase.2 hnm hJe
  obtain ⟨β, hβroot, hβlong, u, huA, huA'⟩ :=
    exists_conj_rootGroup_eq_siegelGroup_POmegaPlus (k + 3) F (by omega) a₁ a₂ b₁ b₂
      hQ h₁ h₂ h₀
  have heqRoot : (((ggU .POmegaPlus (k + 3) f).D.rootGroup β).map
      (MulAut.conj u).toMonoidHom) = (((ggU t' m f).D.rootGroup β₀).map ι) :=
    nbrpom_map_spinAction_injective (huA.trans hAl.symm)
  have heqRootNeg : (((ggU .POmegaPlus (k + 3) f).D.rootGroup (-β)).map
      (MulAut.conj u).toMonoidHom) = (((ggU t' m f).D.rootGroup (-β₀)).map ι) :=
    nbrpom_map_spinAction_injective (huA'.trans hAl'.symm)
  refine ⟨ggRootSub (ggU .POmegaPlus (k + 3) f).D ψ β u,
    ggRootSub (ggU .POmegaPlus (k + 3) f).D ψ (-β) u, ?_, ?_, ?_, ?_⟩
  · have hBle : (((ggU t' m f).D.rootGroup β₀).map ι) ≤ ι.range := Subgroup.map_le_range ι _
    calc ggRootSub (ggU .POmegaPlus (k + 3) f).D ψ β u
        = (((ggU .POmegaPlus (k + 3) f).D.rootGroup β).map
            (MulAut.conj u).toMonoidHom).map ψ := rfl
      _ = (((ggU t' m f).D.rootGroup β₀).map ι).map ψ := by rw [heqRoot]
      _ ≤ ι.range.map ψ := Subgroup.map_mono hBle
      _ = J := by rw [hιrange, hJ'map]
  · have hBle : (((ggU t' m f).D.rootGroup (-β₀)).map ι) ≤ ι.range := Subgroup.map_le_range ι _
    calc ggRootSub (ggU .POmegaPlus (k + 3) f).D ψ (-β) u
        = (((ggU .POmegaPlus (k + 3) f).D.rootGroup (-β)).map
            (MulAut.conj u).toMonoidHom).map ψ := rfl
      _ = (((ggU t' m f).D.rootGroup (-β₀)).map ι).map ψ := by rw [heqRootNeg]
      _ ≤ ι.range.map ψ := Subgroup.map_mono hBle
      _ = J := by rw [hιrange, hJ'map]
  · exact ⟨β, hβroot, Or.inl hβlong, u, rfl, rfl⟩
  · rcases hdisj with ⟨htag, hm3, hrank⟩ | ⟨htag, hm2, hrank⟩
    · left
      refine ⟨t', m, β₀, htag, hm3, nbrpomx_longRoot_mem_roots_univ (ggU t' m f).D β₀ hlong,
        hlong, ?_, hrank.symm⟩
      refine ⟨ψ.comp ι, ?_, ?_, 1, ?_⟩
      · calc (ψ.comp ι).range = Subgroup.map ψ ι.range := MonoidHom.range_comp ψ ι
          _ = Subgroup.map ψ J' := by rw [hιrange]
          _ = J := hJ'map
      · intro y hy
        apply hιcent
        apply h2
        exact MonoidHom.mem_ker.mpr (show ψ (ι y) = 1 from MonoidHom.mem_ker.mp hy)
      · have hconj : Subgroup.map (MulAut.conj (1 : (ggU t' m f).K)).toMonoidHom
            ((ggU t' m f).D.rootGroup β₀) = (ggU t' m f).D.rootGroup β₀ := by
          ext y; simp
        unfold ggRootSub
        erw [hconj, heqRoot]
        exact Subgroup.map_map ((ggU t' m f).D.rootGroup β₀) ψ ι
    · right
      subst htag
      subst hm2
      refine ⟨1, β₀, rfl, nbrpomx_longRoot_mem_roots_univ (ggU .PSL 2 f).D β₀ hlong, ?_, hrank⟩
      refine ⟨ψ.comp ι, ?_, ?_, 1, ?_⟩
      · calc (ψ.comp ι).range = Subgroup.map ψ ι.range := MonoidHom.range_comp ψ ι
          _ = Subgroup.map ψ J' := by rw [hιrange]
          _ = J := hJ'map
      · intro y hy
        apply hιcent
        apply h2
        exact MonoidHom.mem_ker.mpr (show ψ (ι y) = 1 from MonoidHom.mem_ker.mp hy)
      · have hconj : Subgroup.map (MulAut.conj (1 : (ggU .PSL 2 f).K)).toMonoidHom
            ((ggU .PSL 2 f).D.rootGroup β₀) = (ggU .PSL 2 f).D.rootGroup β₀ := by
          ext y; simp
        unfold ggRootSub
        erw [hconj, heqRoot]
        exact Subgroup.map_map ((ggU .PSL 2 f).D.rootGroup β₀) ψ ι

private theorem nbrpomx_J_su
    {X : Type} [Group X] [Finite X] (k f : ℕ)
    (ψ : (ggU .POmegaPlus (k + 3) f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hH : GGSixPosHyp .POmegaPlus (k + 3) f ψ p G₀ B₁ D J L x)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (J' : Subgroup (ggU .POmegaPlus (k + 3) f).K)
    (ε e_J : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))
    (hSU : ∀ s ∈ S, s ∈
      (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    (hfull : ∀ s : GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f),
      s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range →
      (∃ d ∈ D,
        IsGLLift (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) ψ s d) →
      s ∈ S)
    (hJ'comp : IsComponentOf J' ((Subgroup.centralizer S).comap
      (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)))))
    (hJ'map : J'.map ψ = J)
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f))))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    (heJ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (hJ'ε : IsComponentOf J' ⁅(glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K),
      (glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆)
    (hcase : e_J = ε ∧
      2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 4) :
    ∃ (R Rm : Subgroup X), R ≤ J ∧ Rm ≤ J ∧
      GGRootPosG0 .POmegaPlus (k + 3) f p ψ R Rm ∧
      ∃ (m'J : ℕ) (βJ : Fin (ggU .PSU m'J f).D.rank → ℤ),
        βJ ∈ (ggU .PSU m'J f).D.roots ∧
        GGRootVia (ggU .PSU m'J f) J R βJ ∧
        Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e_J)) = 2 * m'J := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  let F := GaloisField 2 f
  let Q := Spin.quadPlus (k + 3) F
  let G := LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)
  have hf : 1 ≤ f := (CFSG.Blueprint.LieModel.admissible h3).2.1
  have hadj : formAdj (RingHom.id F) G e_J = e_J := by
    rw [hcase.1]; exact hε.2.2.2.1
  have hJe : IsComponentOf J' ⁅(glBlockCentralizer (Spin.spinMatrix Q) S e_J :
        Subgroup (ggU .POmegaPlus (k + 3) f).K),
      (glBlockCentralizer (Spin.spinMatrix Q) S e_J :
        Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆ := by
    rw [hcase.1]; exact hJ'ε
  have hmodel :=
    exists_blockModel_selfDualTwo_POmegaPlus_explicit k f S hSU hS hodd heJ hadj
      hcase.2.1 hcase.2.2 hJe
  rw [max_eq_left hf] at hmodel
  obtain ⟨r, ι, β₀, hrank, hlong, hιcent, hιrange, a₁, a₂, b₁, b₂, hQv, h1v, h2v, h0v,
    hAl, hAl'⟩ := hmodel
  obtain ⟨β, hβroot, hβlong, u, huA, huA'⟩ :=
    exists_conj_rootGroup_eq_siegelGroup_POmegaPlus (k + 3) F (by omega) a₁ a₂ b₁ b₂
      hQv h1v h2v h0v
  have heqRoot : (((ggU .POmegaPlus (k + 3) f).D.rootGroup β).map
      (MulAut.conj u).toMonoidHom) = (((ggU .PSU r f).D.rootGroup β₀).map ι) :=
    nbrpom_map_spinAction_injective (huA.trans hAl.symm)
  have heqRootNeg : (((ggU .POmegaPlus (k + 3) f).D.rootGroup (-β)).map
      (MulAut.conj u).toMonoidHom) = (((ggU .PSU r f).D.rootGroup (-β₀)).map ι) :=
    nbrpom_map_spinAction_injective (huA'.trans hAl'.symm)
  have hrk : Module.finrank (GaloisField 2 f)
      (LinearMap.range (Matrix.toLin' e_J)) = 2 * r := by
    rw [Matrix.toLin'_apply']
    exact hrank.symm
  refine ⟨ggRootSub (ggU .POmegaPlus (k + 3) f).D ψ β u,
    ggRootSub (ggU .POmegaPlus (k + 3) f).D ψ (-β) u, ?_, ?_, ?_, r, β₀,
    nbrpomx_longRoot_mem_roots_univ (ggU .PSU r f).D β₀ hlong, ?_, hrk⟩
  · have hBle : (((ggU .PSU r f).D.rootGroup β₀).map ι) ≤ ι.range := Subgroup.map_le_range ι _
    calc ggRootSub (ggU .POmegaPlus (k + 3) f).D ψ β u
        = (((ggU .POmegaPlus (k + 3) f).D.rootGroup β).map
            (MulAut.conj u).toMonoidHom).map ψ := rfl
      _ = (((ggU .PSU r f).D.rootGroup β₀).map ι).map ψ := by rw [heqRoot]
      _ ≤ ι.range.map ψ := Subgroup.map_mono hBle
      _ = J := by rw [hιrange, hJ'map]
  · have hBle : (((ggU .PSU r f).D.rootGroup (-β₀)).map ι) ≤ ι.range :=
      Subgroup.map_le_range ι _
    calc ggRootSub (ggU .POmegaPlus (k + 3) f).D ψ (-β) u
        = (((ggU .POmegaPlus (k + 3) f).D.rootGroup (-β)).map
            (MulAut.conj u).toMonoidHom).map ψ := rfl
      _ = (((ggU .PSU r f).D.rootGroup (-β₀)).map ι).map ψ := by rw [heqRootNeg]
      _ ≤ ι.range.map ψ := Subgroup.map_mono hBle
      _ = J := by rw [hιrange, hJ'map]
  · exact ⟨β, hβroot, Or.inl hβlong, u, rfl, rfl⟩
  · refine ⟨ψ.comp ι, ?_, ?_, 1, ?_⟩
    · calc (ψ.comp ι).range = Subgroup.map ψ ι.range := MonoidHom.range_comp ψ ι
        _ = Subgroup.map ψ J' := by rw [hιrange]
        _ = J := hJ'map
    · intro y hy
      apply hιcent
      apply h2
      exact MonoidHom.mem_ker.mpr (show ψ (ι y) = 1 from MonoidHom.mem_ker.mp hy)
    · have hconj : Subgroup.map (MulAut.conj (1 : (ggU .PSU r f).K)).toMonoidHom
            ((ggU .PSU r f).D.rootGroup β₀) = (ggU .PSU r f).D.rootGroup β₀ := by
        ext y; simp
      calc ggRootSub (ggU .POmegaPlus (k + 3) f).D ψ β u
          = (((ggU .POmegaPlus (k + 3) f).D.rootGroup β).map
              (MulAut.conj u).toMonoidHom).map ψ := rfl
        _ = (((ggU .PSU r f).D.rootGroup β₀).map ι).map ψ := by rw [heqRoot]
        _ = ggRootSub (ggU .PSU r f).D (ψ.comp ι) β₀ 1 := by
            unfold ggRootSub
            rw [hconj]
            exact Subgroup.map_map ((ggU .PSU r f).D.rootGroup β₀) ψ ι

private theorem nbrpomx_J_sl
    {X : Type} [Group X] [Finite X] (k f : ℕ)
    (ψ : (ggU .POmegaPlus (k + 3) f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hH : GGSixPosHyp .POmegaPlus (k + 3) f ψ p G₀ B₁ D J L x)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (J' : Subgroup (ggU .POmegaPlus (k + 3) f).K)
    (ε e_J : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))
    (hSU : ∀ s ∈ S, s ∈
      (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    (hfull : ∀ s : GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f),
      s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range →
      (∃ d ∈ D,
        IsGLLift (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) ψ s d) →
      s ∈ S)
    (hJ'comp : IsComponentOf J' ((Subgroup.centralizer S).comap
      (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)))))
    (hJ'map : J'.map ψ = J)
    (heJ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (hJ'ε : IsComponentOf J' ⁅(glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K),
      (glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆)
    (hcase : e_J ≠ ε ∧
      formAdj (RingHom.id (GaloisField 2 f))
        (LinearMap.toMatrix₂' (GaloisField 2 f)
          (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e_J ≠ e_J ∧
      ε = e_J + formAdj (RingHom.id (GaloisField 2 f))
        (LinearMap.toMatrix₂' (GaloisField 2 f)
          (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e_J ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2) :
    ∃ (R Rm : Subgroup X), R ≤ J ∧ Rm ≤ J ∧
      GGRootPosG0 .POmegaPlus (k + 3) f p ψ R Rm ∧
      ∃ (kJ : ℕ) (βJ : Fin (ggU .PSL (kJ + 1) f).D.rank → ℤ),
        βJ ∈ (ggU .PSL (kJ + 1) f).D.roots ∧
        GGRootVia (ggU .PSL (kJ + 1) f) J R βJ ∧
        Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e_J)) = kJ + 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  let F := GaloisField 2 f
  let Q := Spin.quadPlus (k + 3) F
  let G := LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)
  have hf : 1 ≤ f := (CFSG.Blueprint.LieModel.admissible h3).2.1
  obtain ⟨k', ι, β₀, hrank, hlong, hιcent, hιrange, a₁, a₂, b₁, b₂, hQ, h₁, h₂, h₀, hAl,
    hAl'⟩ :=
    exists_blockModel_dualPair_POmegaPlus_explicit k f hf S hSU hS hodd heJ hcase.2.1
      hcase.2.2.2 (by rw [← hcase.2.2.1]; exact hJ'ε)
  obtain ⟨β, hβroot, hβlong, u, huA, huA'⟩ :=
    exists_conj_rootGroup_eq_siegelGroup_POmegaPlus (k + 3) F (by omega) a₁ a₂ b₁ b₂
      hQ h₁ h₂ h₀
  have heqRoot : (((ggU .POmegaPlus (k + 3) f).D.rootGroup β).map
      (MulAut.conj u).toMonoidHom) = (((ggU .PSL (k' + 1) f).D.rootGroup β₀).map ι) :=
    nbrpom_map_spinAction_injective (huA.trans hAl.symm)
  have heqRootNeg : (((ggU .POmegaPlus (k + 3) f).D.rootGroup (-β)).map
      (MulAut.conj u).toMonoidHom) = (((ggU .PSL (k' + 1) f).D.rootGroup (-β₀)).map ι) :=
    nbrpom_map_spinAction_injective (huA'.trans hAl'.symm)
  refine ⟨ggRootSub (ggU .POmegaPlus (k + 3) f).D ψ β u,
    ggRootSub (ggU .POmegaPlus (k + 3) f).D ψ (-β) u, ?_, ?_, ?_, k', β₀,
    nbrpomx_longRoot_mem_roots_univ (ggU .PSL (k' + 1) f).D β₀ hlong, ?_, hrank.symm⟩
  · have hBle : (((ggU .PSL (k' + 1) f).D.rootGroup β₀).map ι) ≤ ι.range :=
      Subgroup.map_le_range ι _
    calc ggRootSub (ggU .POmegaPlus (k + 3) f).D ψ β u
        = (((ggU .POmegaPlus (k + 3) f).D.rootGroup β).map
            (MulAut.conj u).toMonoidHom).map ψ := rfl
      _ = (((ggU .PSL (k' + 1) f).D.rootGroup β₀).map ι).map ψ := by rw [heqRoot]
      _ ≤ ι.range.map ψ := Subgroup.map_mono hBle
      _ = J := by rw [hιrange, hJ'map]
  · have hBle : (((ggU .PSL (k' + 1) f).D.rootGroup (-β₀)).map ι) ≤ ι.range :=
      Subgroup.map_le_range ι _
    calc ggRootSub (ggU .POmegaPlus (k + 3) f).D ψ (-β) u
        = (((ggU .POmegaPlus (k + 3) f).D.rootGroup (-β)).map
            (MulAut.conj u).toMonoidHom).map ψ := rfl
      _ = (((ggU .PSL (k' + 1) f).D.rootGroup (-β₀)).map ι).map ψ := by rw [heqRootNeg]
      _ ≤ ι.range.map ψ := Subgroup.map_mono hBle
      _ = J := by rw [hιrange, hJ'map]
  · exact ⟨β, hβroot, Or.inl hβlong, u, rfl, rfl⟩
  · refine ⟨ψ.comp ι, ?_, ?_, 1, ?_⟩
    · calc (ψ.comp ι).range = Subgroup.map ψ ι.range := MonoidHom.range_comp ψ ι
        _ = Subgroup.map ψ J' := by rw [hιrange]
        _ = J := hJ'map
    · intro y hy
      apply hιcent
      apply h2
      exact MonoidHom.mem_ker.mpr (show ψ (ι y) = 1 from MonoidHom.mem_ker.mp hy)
    · have hconj : Subgroup.map (MulAut.conj (1 : (ggU .PSL (k' + 1) f).K)).toMonoidHom
            ((ggU .PSL (k' + 1) f).D.rootGroup β₀) = (ggU .PSL (k' + 1) f).D.rootGroup β₀ := by
        ext y; simp
      unfold ggRootSub
      rw [hconj]
      exact (congrArg (Subgroup.map ψ) heqRoot).trans
        (Subgroup.map_map ((ggU .PSL (k' + 1) f).D.rootGroup β₀) ψ ι)

private theorem nbrpomx_liftComponents
    {X : Type} [Group X] [Finite X] (k f : ℕ)
    (ψ : (ggU .POmegaPlus (k + 3) f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hH : GGSixPosHyp .POmegaPlus (k + 3) f ψ p G₀ B₁ D J L x)
    (e : X) (heD : e ∈ D) (K : Subgroup X) (hKG₀ : K ≤ G₀)
    (hKcomp : IsComponentOf K (Subgroup.centralizer {e}))
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (hfull : ∀ s : GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f),
      s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range →
      (∃ d ∈ D,
        IsGLLift (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) ψ s d) →
      s ∈ S) :
    ∃ S' : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)),
      S' ⊆ S ∧
      (∀ s ∈ S', s ∈
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range) ∧
      (∀ s ∈ S', ∀ s' ∈ S', Commute s s') ∧
      (∀ s ∈ S', Odd (orderOf s)) ∧
      ∃ K' : Subgroup (ggU .POmegaPlus (k + 3) f).K,
        IsComponentOf K' ((Subgroup.centralizer S').comap
          (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)))) ∧
        K'.map ψ = K := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  let F := GaloisField 2 f
  let j : spinGroup (Spin.quadPlus (k + 3) F) →* GL (Fin (k + 3) ⊕ Fin (k + 3)) F :=
    Spin.spinMatrix (Spin.quadPlus (k + 3) F)
  have hj : Function.Injective j := nbrpom_spinMatrix_injective F (k + 3)
  let P : GL (Fin (k + 3) ⊕ Fin (k + 3)) F → Prop := fun s => s ∈ j.range
  have heB : e ∈ B₁ := h11 heD
  have heID : GGPsiInnerDiag (Spin.plusDatum (k + 3) F (by omega)) ψ e := h8 e heB
  obtain ⟨se₀, hse₀⟩ := exists_conj_eq_POmegaPlus (k + 3) F (by omega) ψ h2 heID
  let se : GL (Fin (k + 3) ⊕ Fin (k + 3)) F := j se₀
  have hseP : se ∈ j.range := ⟨se₀, rfl⟩
  have hseLift : IsGLLift j ψ se e := fun u => ⟨se₀ * u * se₀⁻¹, by
    show j (se₀ * u * se₀⁻¹) = j se₀ * j u * (j se₀)⁻¹
    rw [map_mul, map_mul, map_inv], hse₀ u⟩
  have hlift : ∀ d ∈ Subgroup.zpowers e, ∃ s : GL (Fin (k + 3) ⊕ Fin (k + 3)) F,
      P s ∧ IsGLLift j ψ s d := by
    intro d hd
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hd
    refine ⟨se ^ m, Subgroup.zpow_mem _ hseP m, ?_⟩
    rw [← hm]
    exact nbrpom_lift_zpow (k + 3) F ψ hseP hseLift m
  have hcent : Subgroup.centralizer (Subgroup.zpowers e : Set X) =
      Subgroup.centralizer ({e} : Set X) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hKcomp' : IsComponentOf K (Subgroup.centralizer (Subgroup.zpowers e : Set X)) := by
    rw [hcent]; exact hKcomp
  have hJ : IsComponentOf K (ψ.range ⊓ Subgroup.centralizer
      (Subgroup.zpowers e : Set X)) := by
    rw [h1]
    exact CFSG.Assembly.IsComponentOf.of_le_of_le hKcomp'
      (le_inf hKG₀ hKcomp'.1) inf_le_right
  obtain ⟨K', hK'comp, hK'map⟩ :=
    StepA.exists_isComponentOf_comap_lift_of_isGLLift j hj ψ h2 P hJ hlift
  let S' : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) F) :=
    {s | P s ∧ ∃ d ∈ Subgroup.zpowers e, IsGLLift j ψ s d}
  have hSU' : ∀ s ∈ S', s ∈ j.range := fun s hs => hs.1
  have hSe : S' ⊆ S := by
    intro s hs
    obtain ⟨d, hd, hsl⟩ := hs.2
    exact hfull s hs.1 ⟨d, Subgroup.zpowers_le.mpr heD hd, hsl⟩
  have hS' : ∀ s ∈ S', ∀ s' ∈ S', Commute s s' := by
    intro s hs s' hs'
    obtain ⟨d, hd, hsl⟩ := hs.2
    obtain ⟨d', hd', hs'l⟩ := hs'.2
    have hdd' : Commute d d' := by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hd
      obtain ⟨m', hm'⟩ := Subgroup.mem_zpowers_iff.mp hd'
      rw [← hm, ← hm']
      exact (Commute.refl e).zpow_zpow m m'
    obtain ⟨s₀, hs₀, hsl₀⟩ := nbrpom_lift_to_mem (k + 3) F ψ hs.1 hsl
    obtain ⟨s₁, hs₁, hsl₁⟩ := nbrpom_lift_to_mem (k + 3) F ψ hs'.1 hs'l
    have hc := conj_eq_commute_POmegaPlus (k + 3) F (by omega) ψ h2 hdd' hsl₀ hsl₁
    have hc' : s * s' = s' * s := by
      rw [← hs₀, ← hs₁, ← map_mul, ← map_mul, hc.eq]
    exact hc'
  have hodd' : ∀ s ∈ S', Odd (orderOf s) := by
    intro s hs
    obtain ⟨d, hd, hsl⟩ := hs.2
    have hdB : d ∈ B₁ := Subgroup.zpowers_le.mpr heB hd
    have hdpow : d ^ p = 1 := h9.2 d hdB
    have hspowj : s ^ p ∈ j.range := Subgroup.pow_mem _ hs.1 p
    have hslpow : IsGLLift j ψ (s ^ p) 1 := by
      have h := hsl.pow p
      rwa [hdpow] at h
    have huniq : s ^ p = 1 :=
      nbrpom_lift_unique (k + 3) F (by omega) ψ h2 hspowj (Subgroup.one_mem _) hslpow
        isGLLift_one
    have hdvd : orderOf s ∣ p := orderOf_dvd_iff_pow_eq_one.mpr huniq
    have hpodd : Odd p := h5.odd_of_ne_two h6
    rcases h5.eq_one_or_self_of_dvd (orderOf s) hdvd with h | h
    · rw [h]; exact odd_one
    · rw [h]; exact hpodd
  exact ⟨S', hSe, hSU', hS', hodd', K', hK'comp, hK'map⟩

private theorem nbrpomx_neighbourBlockData
    {X : Type} [Group X] [Finite X] (k f : ℕ)
    (ψ : (ggU .POmegaPlus (k + 3) f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hH : GGSixPosHyp .POmegaPlus (k + 3) f ψ p G₀ B₁ D J L x)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (J' : Subgroup (ggU .POmegaPlus (k + 3) f).K)
    (ε : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hfull : ∀ s : GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f),
      s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range →
      (∃ d ∈ D,
        IsGLLift (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) ψ s d) →
      s ∈ S)
    (hJ'comp : IsComponentOf J' ((Subgroup.centralizer S).comap
      (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)))))
    (hJ'map : J'.map ψ = J)
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f))))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    (hJ'ε : IsComponentOf J' ⁅(glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K),
      (glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆)
    (e : X) (heD : e ∈ D) (K : Subgroup X) (hKG₀ : K ≤ G₀)
    (hKcomp : IsComponentOf K (Subgroup.centralizer {e})) (hJK : J ≤ K) :
    ∃ (S' : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
      (K' : Subgroup (ggU .POmegaPlus (k + 3) f).K)
      (ε' e' : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
        (GaloisField 2 f)),
      S' ⊆ S ∧
      (∀ s ∈ S', s ∈
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range) ∧
      (∀ s ∈ S', ∀ s'' ∈ S', Commute s s'') ∧
      (∀ s ∈ S', Odd (orderOf s)) ∧
      IsComponentOf K' ((Subgroup.centralizer S').comap
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)))) ∧
      K'.map ψ = K ∧
      IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
        (LinearMap.toMatrix₂' (GaloisField 2 f)
          (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f))))
        (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) ε' ∧
      IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' ∧
      e' * ε' = e' ∧
      (e' = ε' ∨ (e' ≠ ε' ∧
        formAdj (RingHom.id (GaloisField 2 f))
          (LinearMap.toMatrix₂' (GaloisField 2 f)
            (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e' ≠ e' ∧
        ε' = e' + formAdj (RingHom.id (GaloisField 2 f))
          (LinearMap.toMatrix₂' (GaloisField 2 f)
            (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e')) ∧
      IsComponentOf K' ⁅(glBlockCentralizer
          (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S' ε' :
          Subgroup (ggU .POmegaPlus (k + 3) f).K),
        (glBlockCentralizer
          (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S' ε' :
          Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆ ∧
      J' ≤ K' ∧ ε * ε' = ε := by
  have hkerc : ψ.ker ≤ Subgroup.center (ggU .POmegaPlus (k + 3) f).K := hH.2.1
  obtain ⟨S', hSe, hSU', hS', hodd', K', hK'comp, hK'map⟩ :=
    nbrpomx_liftComponents k f ψ p G₀ B₁ D J L x hH e heD K hKG₀ hKcomp S hfull
  obtain ⟨ε', e', hε', he', he'ε', hsplit', hK'ε'⟩ :=
    nbrpom_L3 k f S' hSU' hS' K' hK'comp
  have hJK' : J' ≤ K' := by
    have hmapJK : J'.map ψ ≤ K'.map ψ := by
      calc J'.map ψ = J := hJ'map
        _ ≤ K := hJK
        _ = K'.map ψ := hK'map.symm
    have hleJK : J' ≤ K' ⊔ ψ.ker := Subgroup.map_le_map_iff.mp hmapJK
    have hperf : commutator ↥J' = ⊤ := hJ'comp.2.2.1
    exact nbrpomx_perfect_le_of_le_sup_center hkerc hleJK hperf
  let F := GaloisField 2 f
  let Q := Spin.quadPlus (k + 3) F
  let G := LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)
  have hG : IsUnit G.det :=
    nbrpom_isUnit_det Q (Spin.nondegenerate_polarBilin_quadPlus (k + 3) F)
  have htie : ε * ε' = ε := by
    have hAe_le : Algebra.adjoin F (Units.val '' S') ≤ Algebra.adjoin F (Units.val '' S) :=
      Algebra.adjoin_mono (Set.image_mono hSe)
    have hε'A : ε' ∈ Algebra.adjoin F (Units.val '' S) := hAe_le hε'.1
    have hcommA : ∀ a ∈ Algebra.adjoin F (Units.val '' S),
        ∀ b ∈ Algebra.adjoin F (Units.val '' S), a * b = b * a :=
      fun a ha b hb => (nbrpomx_adjoin_comm hS a ha b hb).eq
    have hmem : ε * ε' ∈ Algebra.adjoin F (Units.val '' S) :=
      Subalgebra.mul_mem _ hε.1 hε'A
    have hidem : IsIdempotentElem (ε * ε') := by
      rw [IsIdempotentElem]
      calc (ε * ε') * (ε * ε') = ε * (ε' * (ε * ε')) := by rw [mul_assoc]
        _ = ε * ((ε' * ε) * ε') := by rw [mul_assoc]
        _ = ε * ((ε * ε') * ε') := by rw [hcommA ε' hε'A ε hε.1]
        _ = ε * (ε * (ε' * ε')) := by rw [mul_assoc]
        _ = ε * (ε * ε') := by rw [hε'.2.1.eq]
        _ = (ε * ε) * ε' := by rw [← mul_assoc]
        _ = ε * ε' := by rw [hε.2.1.eq]
    have hadj : formAdj (RingHom.id F) G (ε * ε') = ε * ε' := by
      rw [Geo.formAdj_mul (RingHom.id F) hG, hε.2.2.2.1, hε'.2.2.2.1]
      exact hcommA ε' hε'A ε hε.1
    have hbelow : (ε * ε') * ε = ε * ε' := by
      rw [mul_assoc, hcommA ε' hε'A ε hε.1, ← mul_assoc, hε.2.1.eq]
    rcases hε.2.2.2.2 (ε * ε') hmem hidem hadj hbelow with h0 | heq
    · exfalso
      have hJ'bot : J' = ⊥ := by
        rw [eq_bot_iff]
        intro u hu
        have huG : u ∈ glBlockCentralizer (Spin.spinMatrix Q) S ε := by
          have h := (Subgroup.commutator_le_sup _ _) (hJ'ε.1 hu)
          rwa [sup_idem] at h
        have huGe : u ∈ glBlockCentralizer (Spin.spinMatrix Q) S' ε' := by
          have h := (Subgroup.commutator_le_sup _ _) (hK'ε'.1 (hJK' hu))
          rwa [sup_idem] at h
        have huG' : (Spin.spinMatrix Q) u ∈ Subgroup.centralizer S ⊓ glFixing (1 - ε) :=
          Subgroup.mem_comap.mp huG
        have huGe' : (Spin.spinMatrix Q) u ∈ Subgroup.centralizer S' ⊓ glFixing (1 - ε') :=
          Subgroup.mem_comap.mp huGe
        have huc : (Spin.spinMatrix Q) u ∈ Subgroup.centralizer S := huG'.1
        let U : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) F :=
          ((Spin.spinMatrix Q u : GL (Fin (k + 3) ⊕ Fin (k + 3)) F) :
            Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) F)
        have hfixJ : U * (1 - ε) = 1 - ε := huG'.2
        have hfixe : U * (1 - ε') = 1 - ε' := huGe'.2
        have hcomm_u : U * ε = ε * U := nbrpomx_commute_adjoin huc hε.1
        have h1 : ε * (1 - ε') = ε := by rw [Matrix.mul_sub, Matrix.mul_one, h0, sub_zero]
        have hmat_eU : U * ε = ε := by
          calc U * ε = U * (ε * (1 - ε')) := by rw [h1]
            _ = (U * ε) * (1 - ε') := by rw [mul_assoc]
            _ = (ε * U) * (1 - ε') := by rw [hcomm_u]
            _ = ε * (U * (1 - ε')) := by rw [mul_assoc]
            _ = ε * (1 - ε') := by rw [hfixe]
            _ = ε := h1
        have hmat_one : U = 1 := by
          calc U = U * 1 := by rw [mul_one]
            _ = U * (ε + (1 - ε)) := by rw [add_sub_cancel]
            _ = U * ε + U * (1 - ε) := by rw [mul_add]
            _ = ε + (1 - ε) := by rw [hmat_eU, hfixJ]
            _ = 1 := by rw [add_sub_cancel]
        have hu1 : u = 1 := nbrpom_spinMatrix_injective F (k + 3) (by
          calc (Spin.spinMatrix (Spin.quadPlus (k + 3) F)) u = 1 := Units.ext hmat_one
            _ = (Spin.spinMatrix (Spin.quadPlus (k + 3) F)) 1 := (map_one _).symm)
        exact Subgroup.mem_bot.mpr hu1
      have hnt : Nontrivial ↥J' := by
        haveI : IsSimpleGroup (↥J' ⧸ Subgroup.center ↥J') := hJ'comp.2.2.2
        exact (QuotientGroup.mk'_surjective (Subgroup.center ↥J')).nontrivial
      exact (Subgroup.nontrivial_iff_ne_bot J').mp hnt hJ'bot
    · exact heq
  exact ⟨S', K', ε', e', hSe, hSU', hS', hodd', hK'comp, hK'map, hε', he', he'ε', hsplit',
    hK'ε', hJK', htie⟩

private lemma nbrpomx_gram_det (k f : ℕ) :
    IsUnit (LinearMap.toMatrix₂' (GaloisField 2 f)
      (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))).det :=
  nbrpom_isUnit_det (Spin.quadPlus (k + 3) (GaloisField 2 f))
    (Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 f))

private lemma nbrpomx_gram_transpose (k f : ℕ) :
    Matrix.transpose ((LinearMap.toMatrix₂' (GaloisField 2 f)
      (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))).map
        (RingHom.id (GaloisField 2 f))) =
      LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f))) := by
  simpa using nbrpom_polar_matrix_transpose_eq (Spin.quadPlus (k + 3) (GaloisField 2 f))

private lemma nbrpomx_gram_iso (k f : ℕ)
    {s : GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (hs : s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range) :
    Matrix.transpose ((s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
        (GaloisField 2 f)).map (RingHom.id (GaloisField 2 f))) *
      LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f))) *
      (s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) =
      LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f))) := by
  obtain ⟨gs, rfl⟩ := hs
  simpa using nbrpom_spinMatrix_gram (Spin.quadPlus (k + 3) (GaloisField 2 f)) gs

private lemma nbrpomx_rank_le_of_mul_eq {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {a b : Matrix ι ι F} (ha : IsIdempotentElem a) (hab : a * b = a) (hba : b * a = a) :
    Module.finrank F (LinearMap.range (Matrix.toLin' a)) ≤
      Module.finrank F (LinearMap.range (Matrix.toLin' b)) := by
  by_cases h : a = b
  · rw [h]
  · exact (nbrpomx_rank_lt_of_mul_eq ha hab hba h).le

private lemma nbrpomx_notSU {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    [CharP F 2]
    {S S' : Set (GL ι F)} (hSe : S' ⊆ S) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hS' : ∀ s ∈ S', ∀ s'' ∈ S', Commute s s'') (hodd' : ∀ s ∈ S', Odd (orderOf s))
    {e_J e' : Matrix ι ι F} (heJ : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e_J)
    (he' : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S')) e')
    (htie : e_J * e' = e_J)
    (hdegJ : blockDegree (Algebra.adjoin F (Units.val '' S)) e_J < 2)
    (hdeg' : 2 ≤ blockDegree (Algebra.adjoin F (Units.val '' S')) e') : False := by
  obtain ⟨Kf, hKf, hKa, hKfin, π, hπs, hπk, -⟩ := exists_blockField (S := S') hS' hodd' he'
  letI : Field Kf := hKf
  letI : Algebra F Kf := hKa
  have hfield := nbrpomx_blockField_inv π hπs hπk
  have hAA' : Algebra.adjoin F (Units.val '' S') ≤ Algebra.adjoin F (Units.val '' S) :=
    Algebra.adjoin_mono (Set.image_mono hSe)
  have hle := nbrpomx_blockDegree_le_of_mul (A := Algebra.adjoin F (Units.val '' S))
    (A' := Algebra.adjoin F (Units.val '' S')) hAA'
    (fun a b ha hb => (nbrpomx_adjoin_comm hS a ha b hb).eq) heJ htie hfield
  omega

private lemma nbrpomx_notSL {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    (G : Matrix ι ι F)
    (hG : IsUnit G.det) {S S' : Set (GL ι F)} (hSe : S' ⊆ S)
    (hSiso : ∀ s ∈ S, Matrix.transpose ((s : Matrix ι ι F).map (RingHom.id F)) * G *
      (s : Matrix ι ι F) = G)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e_J e' ε' : Matrix ι ι F} (heJ : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e_J)
    (hadjJ : formAdj (RingHom.id F) G e_J = e_J)
    (he' : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S')) e')
    (hsplit' : e' ≠ ε' ∧ formAdj (RingHom.id F) G e' ≠ e' ∧
      ε' = e' + formAdj (RingHom.id F) G e')
    (htie : e_J * ε' = e_J) : False := by
  have he'A : e' ∈ Algebra.adjoin F (Units.val '' S) :=
    Algebra.adjoin_mono (Set.image_mono hSe) he'.1
  have hstarA : formAdj (RingHom.id F) G e' ∈ Algebra.adjoin F (Units.val '' S) :=
    Geo.formAdj_mem_adjoin (RingHom.id F) hG hSiso he'A
  have hle : e_J * (e' + formAdj (RingHom.id F) G e') = e_J := by
    rw [← hsplit'.2.2]; exact htie
  exact nbrpomx_selfDual_not_below_dualPair G hG
    (fun a b ha hb => (nbrpomx_adjoin_comm hS a ha b hb).eq) heJ hadjJ he'A hstarA he'.2.1 hle

private lemma nbrpomx_rank_eps (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈
      (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e_J : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (heJ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (hpairJ : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e_J ≠ e_J)
    (heqJ : ε = e_J + formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e_J)
    (kJ : ℕ)
    (hrankJ : Module.finrank (GaloisField 2 f)
      (LinearMap.range (Matrix.toLin' e_J)) = kJ + 1) :
    Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' ε)) = 2 * (kJ + 1) := by
  let F := GaloisField 2 f
  let Q := Spin.quadPlus (k + 3) F
  let G := LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)
  have hG : IsUnit G.det := nbrpomx_gram_det k f
  have hAcomm : ∀ a b : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) F,
      a ∈ Algebra.adjoin F (Units.val '' S) → b ∈ Algebra.adjoin F (Units.val '' S) →
      a * b = b * a :=
    fun a b ha hb => (nbrpomx_adjoin_comm hS a ha b hb).eq
  have hstarA : formAdj (RingHom.id F) G e_J ∈ Algebra.adjoin F (Units.val '' S) :=
    Geo.formAdj_mem_adjoin (RingHom.id F) hG (fun s hs => nbrpomx_gram_iso k f (hSU s hs)) heJ.1
  have horth : e_J * formAdj (RingHom.id F) G e_J = 0 :=
    nbrpomx_dualPair_orth k f S hSU hS heJ hpairJ
  have hba : formAdj (RingHom.id F) G e_J * e_J = 0 := by
    rw [hAcomm _ _ hstarA heJ.1, horth]
  have hstaridem : IsIdempotentElem (formAdj (RingHom.id F) G e_J) := by
    rw [IsIdempotentElem, ← Geo.formAdj_mul (RingHom.id F) hG e_J e_J, heJ.2.1.eq]
  rw [heqJ, nbrpomx_finrank_range_add_of_orth heJ.2.1 hstaridem horth hba]
  have hr : Module.finrank F (LinearMap.range (Matrix.toLin' (formAdj (RingHom.id F) G e_J))) =
      kJ + 1 := by
    rw [show Module.finrank F (LinearMap.range (Matrix.toLin' (formAdj (RingHom.id F) G e_J))) =
        Matrix.rank (formAdj (RingHom.id F) G e_J) from rfl, nbrpomx_rank_formAdj hG]
    exact hrankJ
  rw [hrankJ, hr]
  ring

private lemma nbrpomx_isPrimIdemIn_formAdj (k f : ℕ)
    (S' : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (hSU' : ∀ s ∈ S', s ∈
      (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS' : ∀ s ∈ S', ∀ s'' ∈ S', Commute s s'')
    {e' : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (he' : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e') :
    IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S'))
      (formAdj (RingHom.id (GaloisField 2 f))
        (LinearMap.toMatrix₂' (GaloisField 2 f)
          (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e') := by
  let F := GaloisField 2 f
  let Q := Spin.quadPlus (k + 3) F
  let G := LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)
  have hG : IsUnit G.det := nbrpomx_gram_det k f
  have hSU'_iso : ∀ s ∈ S', Matrix.transpose ((s : Matrix (Fin (k + 3) ⊕ Fin (k + 3))
      (Fin (k + 3) ⊕ Fin (k + 3)) F).map (RingHom.id F)) * G *
      (s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) F) = G :=
    fun s hs => nbrpomx_gram_iso k f (hSU' s hs)
  have hGh : Matrix.transpose (G.map (RingHom.id F)) = G := nbrpomx_gram_transpose k f
  have hA'comm : ∀ {a b : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) F},
      a ∈ Algebra.adjoin F (Units.val '' S') → b ∈ Algebra.adjoin F (Units.val '' S') →
      a * b = b * a :=
    fun ha hb => (nbrpomx_adjoin_comm hS' _ ha _ hb).eq
  refine ⟨Geo.formAdj_mem_adjoin (RingHom.id F) hG hSU'_iso he'.1, ?_, ?_, ?_⟩
  · rw [IsIdempotentElem, ← Geo.formAdj_mul (RingHom.id F) hG e' e', he'.2.1.eq]
  · intro h0
    have h := congrArg (formAdj (RingHom.id F) G) h0
    rw [Geo.formAdj_formAdj (RingHom.id F) (fun x => rfl) hG hGh e',
      show formAdj (RingHom.id F) G 0 = 0 by simp [formAdj]] at h
    exact he'.2.2.1 h
  · intro x hx hxidem hxe
    have hx' : formAdj (RingHom.id F) G x ∈ Algebra.adjoin F (Units.val '' S') :=
      Geo.formAdj_mem_adjoin (RingHom.id F) hG hSU'_iso hx
    have hx'idem : IsIdempotentElem (formAdj (RingHom.id F) G x) := by
      rw [IsIdempotentElem, ← Geo.formAdj_mul (RingHom.id F) hG x x, hxidem.eq]
    have hx'e : formAdj (RingHom.id F) G x * e' = formAdj (RingHom.id F) G x := by
      have h := congrArg (formAdj (RingHom.id F) G) hxe
      rw [Geo.formAdj_mul (RingHom.id F) hG x (formAdj (RingHom.id F) G e'),
        Geo.formAdj_formAdj (RingHom.id F) (fun x => rfl) hG hGh e'] at h
      rw [hA'comm hx' he'.1]
      exact h
    rcases he'.2.2.2 (formAdj (RingHom.id F) G x) hx' hx'idem hx'e with h | h
    · left
      have h2 := congrArg (formAdj (RingHom.id F) G) h
      rw [Geo.formAdj_formAdj (RingHom.id F) (fun x => rfl) hG hGh x,
        show formAdj (RingHom.id F) G 0 = 0 by simp [formAdj]] at h2
      exact h2
    · right
      have h2 := congrArg (formAdj (RingHom.id F) G) h
      rw [Geo.formAdj_formAdj (RingHom.id F) (fun x => rfl) hG hGh x] at h2
      exact h2

private theorem nbrpomx_rootVia
    {X : Type} [Group X] (k f : ℕ)
    (ψ : (ggU .POmegaPlus (k + 3) f).K →* X)
    (hψ : ψ.ker ≤ Subgroup.center (ggU .POmegaPlus (k + 3) f).K) {t : StatedLieTag} {m : ℕ}
    (ι : (ggU t m f).K →* (ggU .POmegaPlus (k + 3) f).K)
    (hιcent : ∀ y, ι y ∈ Subgroup.center (ggU .POmegaPlus (k + 3) f).K →
      y ∈ Subgroup.center (ggU t m f).K)
    (K' R' : Subgroup (ggU .POmegaPlus (k + 3) f).K) (K R : Subgroup X)
    (hK'map : K'.map ψ = K) (hR'map : R'.map ψ = R) (hιrange : ι.range = K')
    (β : Fin (ggU t m f).D.rank → ℤ) (u : (ggU t m f).K)
    (hroot : (((ggU t m f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι = R') :
    GGRootVia (ggU t m f) K R β := by
  refine ⟨ψ.comp ι, ?_, ?_, u, ?_⟩
  · rw [MonoidHom.range_comp, hιrange]
    exact hK'map
  · intro y hy
    exact hιcent y (hψ (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hy)))
  · rw [ggRootSub]
    have h := congrArg (Subgroup.map ψ) hroot
    rw [hR'map] at h
    rw [← h]
    exact Subgroup.map_map _ ψ ι

section KLeaves

local notation "Ix" k:max => (Fin (k + 3) ⊕ Fin (k + 3))
local notation "Mx" k:max f:max => Matrix (Ix k) (Ix k) (GaloisField 2 f)
set_option quotPrecheck false in
local notation "UK" k:max f:max => (ggU .POmegaPlus (k + 3) f).K
set_option quotPrecheck false in
local notation "ρm" k:max f:max => Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))
set_option quotPrecheck false in
local notation "Gm" k:max f:max => LinearMap.toMatrix₂' (GaloisField 2 f)
  (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))
local notation "AdS" f:max S:max => Algebra.adjoin (GaloisField 2 f) (Units.val '' S)
local notation "Fadj" k:max f:max e:max => formAdj (RingHom.id (GaloisField 2 f)) (Gm k f) e
local notation "BlkC" k:max f:max S:max ε:max =>
  (glBlockCentralizer (ρm k f) S ε : Subgroup (UK k f))
local notation "rk" f:max e:max =>
  Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e))

private theorem nbrpomx_ne_one
    {X : Type} [Group X] (k f : ℕ) (ψ : UK k f →* X)
    (S : Set (GL (Ix k) (GaloisField 2 f))) (J' : Subgroup (UK k f)) (ε e_J : Mx k f)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (heJ : IsPrimIdemIn (AdS f S) e_J)
    (hcase : e_J = ε ∧ blockDegree (AdS f S) e_J < 2)
    (J K : Subgroup X) (hKne : K ≠ J) (hJ'map : J'.map ψ = J)
    (S' : Set (GL (Ix k) (GaloisField 2 f))) (K' : Subgroup (UK k f)) (ε' e' : Mx k f)
    (hK'map : K'.map ψ = K) (hSe : S' ⊆ S)
    (hε' : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f)) (Gm k f) (AdS f S') ε')
    (hK'ε' : IsComponentOf K' ⁅BlkC k f S' ε', BlkC k f S' ε'⁆)
    (hJ'ε : IsComponentOf J' ⁅BlkC k f S ε, BlkC k f S ε⁆) (hJK' : J' ≤ K')
    (hcaseSp : e' = ε' ∧ blockDegree (AdS f S') e' < 2) :
    e_J ≠ e' := by
  intro heq
  have heqε : ε = ε' := by rw [← hcase.1, heq, ← hcaseSp.1]
  have hK'block : IsComponentOf K' ⁅BlkC k f S' ε, BlkC k f S' ε⁆ := by
    rw [heqε]; exact hK'ε'
  have heSe : ε ∈ AdS f S' := by rw [heqε]; exact hε'.1
  have hle : BlkC k f S' ε ≤ BlkC k f S ε := by
    have hprim : IsPrimIdemIn (AdS f S) ε := by rw [← hcase.1]; exact heJ
    have hdeg : blockDegree (AdS f S) ε < 2 := by rw [← hcase.1]; exact hcase.2
    exact nbrpomx_glBlockCentralizer_le k f (S := S) (S_e := S') hS hprim hdeg heSe
  have hge : BlkC k f S ε ≤ BlkC k f S' ε := by
    intro u hu
    obtain ⟨huc, hufix⟩ : (ρm k f) u ∈ Subgroup.centralizer S ⊓ glFixing (1 - ε) :=
      Subgroup.mem_comap.mp hu
    exact Subgroup.mem_comap.mpr ⟨Subgroup.centralizer_le hSe huc, hufix⟩
  have hG_eq : BlkC k f S ε = BlkC k f S' ε := le_antisymm hge hle
  have hK'blockS : IsComponentOf K' ⁅BlkC k f S ε, BlkC k f S ε⁆ :=
    hG_eq.symm ▸ hK'block
  haveI : Finite (UK k f) :=
    Finite.of_injective (ρm k f) (nbrpom_spinMatrix_injective (GaloisField 2 f) (k + 3))
  have hJK'' : J' = K' :=
    CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_le hJ'ε hK'blockS hJK'
  have hKJ : K = J :=
    ((hJ'map.symm.trans (congrArg (Subgroup.map ψ) hJK'')).trans hK'map).symm
  exact hKne hKJ

private lemma nbrpomx_glBlockCentralizer_le_two {k f : ℕ}
    {S S_e : Set (GL (Ix k) (GaloisField 2 f))}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Mx k f}
    (he : IsPrimIdemIn (AdS f S) e)
    (heSe : e ∈ AdS f S_e)
    (hAe : ∀ s ∈ S, (s : Mx k f) * e ∈ AdS f S_e) :
    glBlockCentralizer (ρm k f) S_e e ≤ glBlockCentralizer (ρm k f) S e := by
  intro u hu
  obtain ⟨huc, hufix⟩ : (ρm k f) u ∈ Subgroup.centralizer S_e ⊓ glFixing (1 - e) :=
    Subgroup.mem_comap.mp hu
  have hfix : (((ρm k f) u : GL (Ix k) (GaloisField 2 f)) : Mx k f) * (1 - e) = 1 - e := hufix
  have hcomm_e : (((ρm k f) u : GL (Ix k) (GaloisField 2 f)) : Mx k f) * e =
      e * (((ρm k f) u : GL (Ix k) (GaloisField 2 f)) : Mx k f) :=
    nbrpomx_commute_adjoin (S := S_e) huc heSe
  refine Subgroup.mem_comap.mpr ⟨Subgroup.mem_centralizer_iff.mpr ?_, hufix⟩
  intro s hs
  have hsA : (s : Mx k f) ∈ AdS f S := Algebra.subset_adjoin ⟨s, hs, rfl⟩
  have hse : (s : Mx k f) * e = e * (s : Mx k f) :=
    (nbrpomx_adjoin_comm hS (s : Mx k f) hsA e he.1).eq
  have hSme : (s : Mx k f) * e ∈ AdS f S_e := hAe s hs
  have hGSm : (((ρm k f) u : GL (Ix k) (GaloisField 2 f)) : Mx k f) * ((s : Mx k f) * e) =
      ((s : Mx k f) * e) * (((ρm k f) u : GL (Ix k) (GaloisField 2 f)) : Mx k f) :=
    nbrpomx_commute_adjoin (S := S_e) huc hSme
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  set G := (((ρm k f) u : GL (Ix k) (GaloisField 2 f)) : Mx k f) with hGdef
  set Sm := (s : Mx k f) with hSmdef
  have hG : G = G * e + (1 - e) := by
    have h := hfix
    rw [Matrix.mul_sub, Matrix.mul_one] at h
    calc G = (G - G * e) + G * e := by abel
      _ = (1 - e) + G * e := by rw [h]
      _ = G * e + (1 - e) := by abel
  have hSG : Sm * G = Sm * (G * e) + (Sm - Sm * e) := by
    calc Sm * G = Sm * (G * e + (1 - e)) := by rw [← hG]
      _ = Sm * (G * e) + Sm * (1 - e) := by rw [Matrix.mul_add]
      _ = Sm * (G * e) + (Sm - Sm * e) := by rw [Matrix.mul_sub, Matrix.mul_one]
  have hGS : G * Sm = (G * e) * Sm + (Sm - Sm * e) := by
    calc G * Sm = (G * e + (1 - e)) * Sm := by rw [← hG]
      _ = (G * e) * Sm + (1 - e) * Sm := by rw [Matrix.add_mul]
      _ = (G * e) * Sm + (Sm - e * Sm) := by rw [Matrix.sub_mul, Matrix.one_mul]
      _ = (G * e) * Sm + (Sm - Sm * e) := by rw [hse]
  have hkey : Sm * (G * e) = (G * e) * Sm := by
    calc Sm * (G * e) = Sm * (e * G) := by rw [hcomm_e]
      _ = (Sm * e) * G := by noncomm_ring
      _ = G * (Sm * e) := hGSm.symm
      _ = G * (e * Sm) := by rw [hse]
      _ = (G * e) * Sm := by noncomm_ring
  change Sm * G = G * Sm
  rw [hSG, hGS, hkey]

private lemma nbrpomx_blockDegree_eq_two_of_selfDual {k f : ℕ}
    {S : Set (GL (Ix k) (GaloisField 2 f))}
    (hSU : ∀ s ∈ S, s ∈ (ρm k f).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Mx k f}
    (he : IsPrimIdemIn (AdS f S) e)
    (hadj : Fadj k f e = e)
    (h2 : 2 ≤ blockDegree (AdS f S) e)
    (h4 : blockDegree (AdS f S) e < 4) :
    blockDegree (AdS f S) e = 2 := by
  have hGdet : IsUnit (Gm k f).det := nbrpomx_gram_det k f
  have hSG : ∀ s ∈ S, Matrix.transpose (((s : GL (Ix k) (GaloisField 2 f)) : Mx k f).map
      (RingHom.id (GaloisField 2 f))) * Gm k f *
      ((s : GL (Ix k) (GaloisField 2 f)) : Mx k f) = Gm k f := by
    intro s hs
    exact nbrpomx_gram_iso k f (hSU s hs)
  have hpar := blockDegree_eq_one_or_even_of_formAdj_eq hGdet hS hodd hSG he hadj
  rcases hpar with h1 | heven
  · omega
  · obtain ⟨m, hm⟩ := heven
    omega

private theorem nbrpomx_ne_two
    {X : Type} [Group X] (k f : ℕ) (ψ : UK k f →* X)
    (S : Set (GL (Ix k) (GaloisField 2 f))) (J' : Subgroup (UK k f)) (ε e_J : Mx k f)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hSU : ∀ s ∈ S, s ∈ (ρm k f).range)
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f)) (Gm k f) (AdS f S) ε)
    (heJ : IsPrimIdemIn (AdS f S) e_J) (hcase : e_J = ε)
    (hdegJ : blockDegree (AdS f S) e_J < 4)
    (J K : Subgroup X) (hKne : K ≠ J) (hJ'map : J'.map ψ = J)
    (S' : Set (GL (Ix k) (GaloisField 2 f))) (K' : Subgroup (UK k f)) (ε' e' : Mx k f)
    (hK'map : K'.map ψ = K) (hSe : S' ⊆ S)
    (hS' : ∀ s ∈ S', ∀ s'' ∈ S', Commute s s'') (hSU' : ∀ s ∈ S', s ∈ (ρm k f).range)
    (hodd' : ∀ s ∈ S', Odd (orderOf s))
    (hε' : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f)) (Gm k f) (AdS f S') ε')
    (he' : IsPrimIdemIn (AdS f S') e')
    (hK'ε' : IsComponentOf K' ⁅BlkC k f S' ε', BlkC k f S' ε'⁆)
    (hJ'ε : IsComponentOf J' ⁅BlkC k f S ε, BlkC k f S ε⁆) (hJK' : J' ≤ K')
    (hcaseSU : e' = ε' ∧ 2 ≤ blockDegree (AdS f S') e' ∧ blockDegree (AdS f S') e' < 4) :
    e_J ≠ e' := by
  intro heq
  have heqε : ε = ε' := by rw [← hcase, heq, ← hcaseSU.1]
  have hsub : AdS f S' ≤ AdS f S := Algebra.adjoin_mono (Set.image_mono hSe)
  have hadj' : Fadj k f e' = e' := by
    rw [hcaseSU.1]
    exact hε'.2.2.2.1
  have hdegA' : blockDegree (AdS f S') e' = 2 :=
    nbrpomx_blockDegree_eq_two_of_selfDual hSU' hS' hodd' he' hadj' hcaseSU.2.1 hcaseSU.2.2
  have hadjJ : Fadj k f e_J = e_J := by
    rw [hcase]
    exact hε.2.2.2.1
  have hmono : blockDegree (AdS f S') e' ≤ blockDegree (AdS f S) e' :=
    Submodule.finrank_mono (Submodule.map_mono hsub)
  have h2 : 2 ≤ blockDegree (AdS f S) e_J := by
    rw [heq]
    exact le_trans hcaseSU.2.1 hmono
  have hdegJ2 : blockDegree (AdS f S) e_J = 2 :=
    nbrpomx_blockDegree_eq_two_of_selfDual hSU hS hodd heJ hadjJ h2 hdegJ
  have hdegA'J : blockDegree (AdS f S') e_J = 2 := by
    rw [heq]
    exact hdegA'
  have heJA : e_J ∈ AdS f S' := by
    rw [heq]
    exact he'.1
  have hAe : ∀ s ∈ S, (s : Mx k f) * e_J ∈ AdS f S' := by
    intro s hs
    have hleM : (Subalgebra.toSubmodule (AdS f S')).map
        (LinearMap.mulRight (GaloisField 2 f) e_J) ≤
        (Subalgebra.toSubmodule (AdS f S)).map (LinearMap.mulRight (GaloisField 2 f) e_J) :=
      Submodule.map_mono hsub
    have heqm : (Subalgebra.toSubmodule (AdS f S')).map
        (LinearMap.mulRight (GaloisField 2 f) e_J) =
        (Subalgebra.toSubmodule (AdS f S)).map (LinearMap.mulRight (GaloisField 2 f) e_J) :=
      Submodule.eq_of_le_of_finrank_eq hleM (by
        show blockDegree (AdS f S') e_J = blockDegree (AdS f S) e_J
        rw [hdegA'J, hdegJ2])
    have hsM : (s : Mx k f) * e_J ∈
        (Subalgebra.toSubmodule (AdS f S)).map (LinearMap.mulRight (GaloisField 2 f) e_J) :=
      ⟨s, Algebra.subset_adjoin ⟨s, hs, rfl⟩, by rw [LinearMap.mulRight_apply]⟩
    rw [← heqm] at hsM
    obtain ⟨a, ha, hae⟩ := hsM
    rw [LinearMap.mulRight_apply] at hae
    rw [← hae]
    exact Subalgebra.mul_mem _ ha heJA
  have hK'block : IsComponentOf K' ⁅BlkC k f S' ε, BlkC k f S' ε⁆ := by
    rw [heqε]
    exact hK'ε'
  have heSe : ε ∈ AdS f S' := by
    rw [heqε]
    exact hε'.1
  have hle : BlkC k f S' ε ≤ BlkC k f S ε := by
    have hprim : IsPrimIdemIn (AdS f S) ε := by
      rw [← hcase]
      exact heJ
    have hdeg : blockDegree (AdS f S) ε < 4 := by
      rw [← hcase]
      exact hdegJ
    exact nbrpomx_glBlockCentralizer_le_two (S := S) (S_e := S') hS hprim heSe
      (fun s hs => by rw [← hcase]; exact hAe s hs)
  have hge : BlkC k f S ε ≤ BlkC k f S' ε := by
    intro u hu
    obtain ⟨huc, hufix⟩ := Subgroup.mem_comap.mp hu
    exact Subgroup.mem_comap.mpr ⟨Subgroup.centralizer_le hSe huc, hufix⟩
  have hG_eq : BlkC k f S ε = BlkC k f S' ε := le_antisymm hge hle
  have hK'blockS : IsComponentOf K' ⁅BlkC k f S ε, BlkC k f S ε⁆ :=
    hG_eq.symm ▸ hK'block
  haveI : Finite (UK k f) :=
    Finite.of_injective (ρm k f) (nbrpom_spinMatrix_injective (GaloisField 2 f) (k + 3))
  have hJK'' : J' = K' :=
    CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_le hJ'ε hK'blockS hJK'
  have hKJ : K = J :=
    ((hJ'map.symm.trans (congrArg (Subgroup.map ψ) hJK'')).trans hK'map).symm
  exact hKne hKJ

private theorem nbrpomx_ne_dual
    {X : Type} [Group X] (k f : ℕ) (ψ : UK k f →* X)
    (S S' : Set (GL (Ix k) (GaloisField 2 f))) (hSe : S' ⊆ S)
    (hSU : ∀ s ∈ S, s ∈ (ρm k f).range) (hSU' : ∀ s ∈ S', s ∈ (ρm k f).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {K' : Subgroup (UK k f)} {K : Subgroup X} (hK'map : K'.map ψ = K)
    (J : Subgroup X) {J' : Subgroup (UK k f)} (hJ'map : J'.map ψ = J)
    (hJ'comp : IsComponentOf J' ((Subgroup.centralizer S).comap (ρm k f)))
    (hK'comp : IsComponentOf K' ((Subgroup.centralizer S').comap (ρm k f)))
    (hJ'K' : J' ≤ K') (hKne : K ≠ J) {ε e_J e' : Mx k f}
    (hK'ε : IsComponentOf K' ⁅BlkC k f S' ε, BlkC k f S' ε⁆)
    (heJ : IsPrimIdemIn (AdS f S) e_J) (hdegJ : blockDegree (AdS f S) e_J < 2)
    (hdual' : e' ≠ ε ∧ Fadj k f e' ≠ e' ∧ ε = e' + Fadj k f e')
    (he' : IsPrimIdemIn (AdS f S') e') :
    e_J ≠ e' := by
  have hG : IsUnit (Gm k f).det := nbrpomx_gram_det k f
  have hSU_iso : ∀ s ∈ S, Matrix.transpose (((s : GL (Ix k) (GaloisField 2 f)) :
      Mx k f).map (RingHom.id (GaloisField 2 f))) * Gm k f *
      ((s : GL (Ix k) (GaloisField 2 f)) : Mx k f) = Gm k f := by
    intro s hs
    exact nbrpomx_gram_iso k f (hSU s hs)
  have hSU'_iso : ∀ s ∈ S', Matrix.transpose (((s : GL (Ix k) (GaloisField 2 f)) :
      Mx k f).map (RingHom.id (GaloisField 2 f))) * Gm k f *
      ((s : GL (Ix k) (GaloisField 2 f)) : Mx k f) = Gm k f := by
    intro s hs
    exact nbrpomx_gram_iso k f (hSU' s hs)
  intro heq
  have heJ' : IsPrimIdemIn (AdS f S) e' := by rw [← heq]; exact heJ
  have hdegJ' : blockDegree (AdS f S) e' < 2 := by rw [← heq]; exact hdegJ
  have hK'H : K' ≤ (Subgroup.centralizer S).comap (ρm k f) := by
    intro u hu
    have huG : (ρm k f) u ∈ Subgroup.centralizer S' ⊓ glFixing (1 - ε) :=
      Subgroup.mem_comap.mp (le_trans hK'ε.1 (Subgroup.commutator_le_self _) hu)
    obtain ⟨hcent_e, hfix⟩ := huG
    refine Subgroup.mem_comap.mpr (Subgroup.mem_centralizer_iff.mpr ?_)
    intro s hs
    have hse : (s : Mx k f) ∈ AdS f S := Algebra.subset_adjoin ⟨s, hs, rfl⟩
    obtain ⟨c_s, hc_s⟩ := nbrpomx_mul_e_eq_smul heJ' hdegJ' _ hse
    have hsE : (s : Mx k f) * e' = e' * (s : Mx k f) :=
      (nbrpomx_adjoin_comm (S := S) hS _ hse _ heJ'.1).eq
    have hformAdj_mem_S : Fadj k f e' ∈ AdS f S :=
      Geo.formAdj_mem_adjoin (RingHom.id (GaloisField 2 f)) hG hSU_iso heJ'.1
    have hsF : (s : Mx k f) * Fadj k f e' = Fadj k f e' * (s : Mx k f) :=
      (nbrpomx_adjoin_comm (S := S) hS _ hse _ hformAdj_mem_S).eq
    have hε_mem_S : ε ∈ AdS f S := by
      rw [hdual'.2.2]; exact add_mem heJ'.1 hformAdj_mem_S
    have hs_eps : (s : Mx k f) * ε = ε * (s : Mx k f) :=
      (nbrpomx_adjoin_comm (S := S) hS _ hse _ hε_mem_S).eq
    have hs1e : (s : Mx k f) * (1 - ε) = (1 - ε) * (s : Mx k f) := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hs_eps]
    have huE : ((ρm k f) u : Mx k f) * e' = e' * ((ρm k f) u : Mx k f) :=
      nbrpomx_commute_adjoin (S := S') hcent_e he'.1
    have hformAdj_mem_se : Fadj k f e' ∈ AdS f S' :=
      Geo.formAdj_mem_adjoin (RingHom.id (GaloisField 2 f)) hG hSU'_iso he'.1
    have huF : ((ρm k f) u : Mx k f) * Fadj k f e' =
        Fadj k f e' * ((ρm k f) u : Mx k f) :=
      nbrpomx_commute_adjoin (S := S') hcent_e hformAdj_mem_se
    have hisom : Matrix.transpose (((s : GL (Ix k) (GaloisField 2 f)) :
        Mx k f).map (RingHom.id (GaloisField 2 f))) * Gm k f *
        (s : Mx k f) = Gm k f := hSU_iso s hs
    have hss : (((s⁻¹ : GL (Ix k) (GaloisField 2 f)) : Mx k f) * (s : Mx k f)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hc_ne : c_s ≠ 0 := by
      intro h0
      have h1 : (s : Mx k f) * e' = 0 := by rw [hc_s, h0, zero_smul]
      have h2 := congrArg (fun M : Mx k f =>
        (((s⁻¹ : GL (Ix k) (GaloisField 2 f)) : Mx k f)) * M) h1
      rw [Matrix.mul_zero, ← Matrix.mul_assoc, hss, Matrix.one_mul] at h2
      exact heJ'.2.2.1 h2
    have h2 : Fadj k f e' = c_s • ((s : Mx k f) * Fadj k f e') := by
      have h := congrArg (fun M : Mx k f => M * (s : Mx k f))
        (show Fadj k f ((s : Mx k f) * e') = Fadj k f (c_s • e') from by rw [hc_s])
      rw [Geo.formAdj_mul (RingHom.id (GaloisField 2 f)) hG,
        Geo.formAdj_eq_inv_of_isometry (RingHom.id (GaloisField 2 f)) hG s hisom,
        Geo.formAdj_smul, Matrix.mul_assoc, hss, Matrix.mul_one, Matrix.smul_mul, ← hsF] at h
      exact h
    have hd_s : (s : Mx k f) * Fadj k f e' = c_s⁻¹ • Fadj k f e' := by
      have h3 := congrArg (fun M : Mx k f => c_s⁻¹ • M) h2
      rw [smul_smul, inv_mul_cancel₀ hc_ne, one_smul] at h3
      exact h3.symm
    have hkill1 : ((((ρm k f) u : Mx k f) * (s : Mx k f) -
        (s : Mx k f) * ((ρm k f) u : Mx k f))) * e' = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, hc_s, Matrix.mul_smul, huE,
        ← Matrix.mul_assoc, hc_s, Matrix.smul_mul, sub_self]
    have hkill2 : ((((ρm k f) u : Mx k f) * (s : Mx k f) -
        (s : Mx k f) * ((ρm k f) u : Mx k f))) * Fadj k f e' = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, hd_s, Matrix.mul_smul, huF,
        ← Matrix.mul_assoc, hd_s, Matrix.smul_mul, sub_self]
    have hkill3 : ((((ρm k f) u : Mx k f) * (s : Mx k f) -
        (s : Mx k f) * ((ρm k f) u : Mx k f))) * (1 - ε) = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, hs1e, ← Matrix.mul_assoc, hfix,
        hs1e, sub_self]
    have hsum : e' + Fadj k f e' + (1 - ε) = 1 := by
      rw [hdual'.2.2]; abel
    have hzero : (((ρm k f) u : Mx k f) * (s : Mx k f) -
        (s : Mx k f) * ((ρm k f) u : Mx k f)) = 0 := by
      calc (((ρm k f) u : Mx k f) * (s : Mx k f) -
          (s : Mx k f) * ((ρm k f) u : Mx k f))
          = _ * 1 := by rw [Matrix.mul_one]
        _ = _ * (e' + Fadj k f e' + (1 - ε)) := by rw [hsum]
        _ = _ * e' + _ * Fadj k f e' + _ * (1 - ε) := by rw [Matrix.mul_add, Matrix.mul_add]
        _ = 0 := by rw [hkill1, hkill2, hkill3]; abel
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact (sub_eq_zero.mp hzero).symm
  have hSe' : (Subgroup.centralizer S).comap (ρm k f) ≤
      (Subgroup.centralizer S').comap (ρm k f) :=
    Subgroup.comap_mono (Subgroup.centralizer_le hSe)
  haveI : Finite (UK k f) :=
    Finite.of_injective (ρm k f) (nbrpom_spinMatrix_injective (GaloisField 2 f) (k + 3))
  have hK'compS : IsComponentOf K' ((Subgroup.centralizer S).comap (ρm k f)) :=
    IsComponentOf.of_le_of_le hK'comp hK'H hSe'
  have hJK' : J' = K' :=
    CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_le hJ'comp hK'compS hJ'K'
  exact hKne (by rw [← hK'map, ← hJ'map, hJK'])

private theorem nbrpomx_stdSylow_eq_upperUnipotent {F : Type*} [Field F] :
    CFSG.Quasithin.SL2Sylow.stdSylow F = CFSG.Timmesfeld.upperUnipotent F := by
  ext g
  rw [CFSG.Quasithin.SL2Sylow.mem_stdSylow,
    CFSG.Timmesfeld.RankOne.mem_upperUnipotent_iff]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, by
      apply CFSG.Quasithin.SL2Sylow.ext_entries <;>
        simp [CFSG.Quasithin.SL2Sylow.upperElt_00, CFSG.Quasithin.SL2Sylow.upperElt_01,
          CFSG.Quasithin.SL2Sylow.upperElt_10, CFSG.Quasithin.SL2Sylow.upperElt_11,
          CFSG.Timmesfeld.RankOne.upperElt]⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, by
      apply CFSG.Quasithin.SL2Sylow.ext_entries <;>
        simp [CFSG.Quasithin.SL2Sylow.upperElt_00, CFSG.Quasithin.SL2Sylow.upperElt_01,
          CFSG.Quasithin.SL2Sylow.upperElt_10, CFSG.Quasithin.SL2Sylow.upperElt_11,
          CFSG.Timmesfeld.RankOne.upperElt]⟩

private theorem nbrpomx_eq_top_of_stdSylow_le {F : Type*} [Field F]
    {A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)} (hperf : commutator ↥A = ⊤)
    (hU : CFSG.Quasithin.SL2Sylow.stdSylow F ≤ A) : A = ⊤ := by
  haveI : Group.IsPerfect ↥A := ⟨hperf⟩
  by_cases hle : A ≤ CFSG.Quasithin.SL2Sylow.borel F
  · exfalso
    have hne1 : CFSG.Quasithin.SL2Sylow.upperElt (1 : F) ≠ 1 := by
      intro h
      have h0 : (1 : F) = 0 := by
        apply CFSG.Quasithin.SL2Sylow.upperElt_injective
        rw [h, CFSG.Quasithin.SL2Sylow.upperElt_zero]
      exact one_ne_zero h0
    haveI : Nontrivial ↥A :=
      (Subgroup.nontrivial_iff_exists_ne_one A).mpr
        ⟨CFSG.Quasithin.SL2Sylow.upperElt (1 : F),
          hU (CFSG.Quasithin.SL2Sylow.upperElt_mem_stdSylow 1), hne1⟩
    haveI : Group.IsSolvable ↥A :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
    exact Group.IsPerfect.not_isSolvable ↥A inferInstance
  · obtain ⟨g, hgA, hgB⟩ := Set.not_subset.mp hle
    have hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
      simpa [CFSG.Quasithin.SL2Sylow.mem_borel] using hgB
    have hlow : ∀ s : F, CFSG.Quasithin.SL2Sylow.lowerElt s ∈ A := by
      intro s
      have hconj := CFSG.Quasithin.SL2Sylow.conj_upperElt_conj_eq_lowerElt g hc
        (-(s / (g : Matrix (Fin 2) (Fin 2) F) 1 0 ^ 2))
      have ht : -((-(s / (g : Matrix (Fin 2) (Fin 2) F) 1 0 ^ 2)) *
          (g : Matrix (Fin 2) (Fin 2) F) 1 0 ^ 2) = s := by
        field_simp
      rw [ht] at hconj
      rw [← hconj]
      exact mul_mem (mul_mem (hU (CFSG.Quasithin.SL2Sylow.upperElt_mem_stdSylow _))
        (mul_mem (mul_mem hgA (hU (CFSG.Quasithin.SL2Sylow.upperElt_mem_stdSylow _)))
          (inv_mem hgA)))
        (hU (CFSG.Quasithin.SL2Sylow.upperElt_mem_stdSylow _))
    exact CFSG.Quasithin.SL2Sylow.eq_top_of_unitriangular_mem
      (fun t => hU (CFSG.Quasithin.SL2Sylow.upperElt_mem_stdSylow t)) hlow

private theorem nbrpomx_eq_top_of_conj_stdSylow_le {F : Type*} [Field F]
    {A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)} (hperf : commutator ↥A = ⊤)
    (v : Matrix.SpecialLinearGroup (Fin 2) F)
    (hU : ∀ x ∈ CFSG.Quasithin.SL2Sylow.stdSylow F, v * x * v⁻¹ ∈ A) : A = ⊤ := by
  haveI : Group.IsPerfect ↥A := ⟨hperf⟩
  let e : Matrix.SpecialLinearGroup (Fin 2) F ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    MulAut.conj v⁻¹
  have hU1 : CFSG.Quasithin.SL2Sylow.stdSylow F ≤ A.map e.toMonoidHom := by
    intro x hx
    refine Subgroup.mem_map.mpr ⟨v * x * v⁻¹, hU x hx, ?_⟩
    show (MulAut.conj v⁻¹) (v * x * v⁻¹) = x
    rw [MulAut.conj_apply]
    group
  haveI : Group.IsPerfect ↥(A.map e.toMonoidHom) :=
    Group.IsPerfect.map (H := A) (f := e.toMonoidHom)
  have hmap : A.map e.toMonoidHom = ⊤ :=
    nbrpomx_eq_top_of_stdSylow_le (A := A.map e.toMonoidHom)
      (Group.IsPerfect.commutator_eq_top (G := ↥(A.map e.toMonoidHom))) hU1
  have htop : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).map e.symm.toMonoidHom = A :=
    (Subgroup.map_symm_eq_iff_map_eq (H := ⊤) A (e := e)).mpr hmap
  rw [Subgroup.map_top_of_surjective e.symm.toMonoidHom
    (EquivLike.surjective e.symm)] at htop
  exact htop.symm

private theorem nbrpomx_plus_four
    (k f : ℕ) (hf : 1 ≤ f) (ι : (ggU .PSL 2 f).K →* UK k f)
    (hιcent : ∀ y, ι y ∈ Subgroup.center (UK k f) → y ∈ Subgroup.center (ggU .PSL 2 f).K)
    (β : Fin (ggU .PSL 2 f).D.rank → ℤ) (hβ : β ∈ (ggU .PSL 2 f).D.roots)
    (u : (ggU .PSL 2 f).K) (J' : Subgroup (UK k f)) (hperf : commutator ↥J' = ⊤)
    (hJι : J' ≤ ι.range)
    (hR : (((ggU .PSL 2 f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι ≤ J') :
    ι.range ≤ J' := by
  classical
  let H : Subgroup (ggU .PSL 2 f).K := J'.comap ι
  have hHdef : H = J'.comap ι := rfl
  have hmap : H.map ι = J' := by
    rw [hHdef, Subgroup.map_comap_eq, inf_eq_right.mpr hJι]
  have hcenter : Subgroup.center ((ggU .PSL 2 f).K) = ⊥ := by
    change Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) = ⊥
    exact CFSG.Timmesfeld.RankOne.center_SL2_eq_bot (GaloisField 2 f)
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hyc : y ∈ Subgroup.center ((ggU .PSL 2 f).K) :=
      hιcent y (by rw [hy]; exact Subgroup.one_mem _)
    rw [hcenter] at hyc
    exact Subgroup.mem_bot.mp hyc
  have hHperf : commutator ↥H = ⊤ := by
    have e : ↥H ≃* ↥(H.map ι) := Subgroup.equivMapOfInjective H ι hιinj
    haveI : Group.IsPerfect ↥(H.map ι) := by
      rw [hmap]
      exact ⟨hperf⟩
    haveI : Group.IsPerfect ↥H :=
      Group.IsPerfect.ofSurjective (f := (e.symm : ↥(H.map ι) →* ↥H))
        (EquivLike.surjective e.symm)
    exact Group.IsPerfect.commutator_eq_top (G := ↥H)
  have key : H = ⊤ := by
    let u' : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) := u
    have hβ' :=
      CFSG.Timmesfeld.ARS.CaseOA.eq_or_eq_neg_of_mem_roots_SL2 (F := GaloisField 2 f) hβ
    rcases hβ' with hβpos | hβneg
    · have hU : ∀ x ∈ CFSG.Quasithin.SL2Sylow.stdSylow (GaloisField 2 f),
          u' * x * u'⁻¹ ∈ H := by
        intro x hx
        have hxU : x ∈ CFSG.Timmesfeld.upperUnipotent (GaloisField 2 f) := by
          rwa [← nbrpomx_stdSylow_eq_upperUnipotent]
        have hroot : x ∈ (ggU .PSL 2 f).D.rootGroup β := by
          have hsingle : (ggU .PSL 2 f).D.rootGroup β =
              CFSG.Timmesfeld.upperUnipotent (GaloisField 2 f) := by
            rw [hβpos]
            exact CFSG.Timmesfeld.ARS.CaseOA.rootGroup_SL2_single (GaloisField 2 f)
          rw [hsingle]
          exact hxU
        have hx' : u' * x * u'⁻¹ ∈ ((ggU .PSL 2 f).D.rootGroup β).map
            (MulAut.conj u).toMonoidHom := Subgroup.mem_map.mpr ⟨x, hroot, rfl⟩
        exact Subgroup.mem_comap.mpr (hR (Subgroup.mem_map.mpr ⟨_, hx', rfl⟩))
      exact nbrpomx_eq_top_of_conj_stdSylow_le (A := H) hHperf u' hU
    · let w : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) :=
        CFSG.Timmesfeld.ARS.NaturalModule.weylElt (GaloisField 2 f)
      have hw : w⁻¹ = w :=
        inv_eq_of_mul_eq_one_right CFSG.Timmesfeld.ARS.NaturalModule.weylElt_mul_self
      have hU : ∀ x ∈ CFSG.Quasithin.SL2Sylow.stdSylow (GaloisField 2 f),
          (u' * w) * x * (u' * w)⁻¹ ∈ H := by
        intro x hx
        have hxU : x ∈ CFSG.Timmesfeld.upperUnipotent (GaloisField 2 f) := by
          rwa [← nbrpomx_stdSylow_eq_upperUnipotent]
        obtain ⟨t, rfl⟩ :=
          (CFSG.Timmesfeld.RankOne.mem_upperUnipotent_iff (GaloisField 2 f)).mp hxU
        have hlow : CFSG.Timmesfeld.RankOne.lowerElt (GaloisField 2 f) t ∈
            CFSG.Timmesfeld.lowerUnipotent (GaloisField 2 f) :=
          (CFSG.Timmesfeld.RankOne.mem_lowerUnipotent_iff (GaloisField 2 f)).mpr ⟨t, rfl⟩
        have hroot : CFSG.Timmesfeld.RankOne.lowerElt (GaloisField 2 f) t ∈
            (ggU .PSL 2 f).D.rootGroup β := by
          have hsingle : (ggU .PSL 2 f).D.rootGroup β =
              CFSG.Timmesfeld.lowerUnipotent (GaloisField 2 f) := by
            rw [hβneg]
            exact CFSG.Timmesfeld.ARS.CaseOA.rootGroup_SL2_neg_single (GaloisField 2 f)
          rw [hsingle]
          exact hlow
        have hx' : u' * CFSG.Timmesfeld.RankOne.lowerElt (GaloisField 2 f) t * u'⁻¹ ∈
            ((ggU .PSL 2 f).D.rootGroup β).map (MulAut.conj u).toMonoidHom :=
          Subgroup.mem_map.mpr ⟨_, hroot, rfl⟩
        have hmem : u' * CFSG.Timmesfeld.RankOne.lowerElt (GaloisField 2 f) t * u'⁻¹ ∈ H :=
          Subgroup.mem_comap.mpr (hR (Subgroup.mem_map.mpr ⟨_, hx', rfl⟩))
        have heq : (u' * w) * CFSG.Timmesfeld.RankOne.upperElt (GaloisField 2 f) t *
              (u' * w)⁻¹
            = u' * CFSG.Timmesfeld.RankOne.lowerElt (GaloisField 2 f) t * u'⁻¹ := by
          calc (u' * w) * CFSG.Timmesfeld.RankOne.upperElt (GaloisField 2 f) t * (u' * w)⁻¹
              = u' * (w * CFSG.Timmesfeld.RankOne.upperElt (GaloisField 2 f) t * w) *
                  u'⁻¹ := by
                rw [mul_inv_rev, hw]; group
            _ = u' * CFSG.Timmesfeld.RankOne.lowerElt (GaloisField 2 f) t * u'⁻¹ := by
                rw [CFSG.Timmesfeld.ARS.NaturalModule.weylElt_mul_upperElt_mul_weylElt t]
        rw [heq]
        exact hmem
      exact nbrpomx_eq_top_of_conj_stdSylow_le (A := H) hHperf (u' * w) hU
  have hJ : J' = ι.range := by
    rw [← hmap, key, MonoidHom.range_eq_map]
  exact ge_of_eq hJ

private theorem nbrpomx_K_model
    {X : Type} [Group X] (k f : ℕ) (hf : 1 ≤ f)
    (S' : Set (GL (Ix k) (GaloisField 2 f))) (hSU' : ∀ s ∈ S', s ∈ (ρm k f).range)
    (hS' : ∀ s ∈ S', ∀ s'' ∈ S', Commute s s'') (hodd' : ∀ s ∈ S', Odd (orderOf s))
    (K' R' : Subgroup (UK k f)) (ε' e' : Mx k f)
    (hε' : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f)) (Gm k f) (AdS f S') ε')
    (he' : IsPrimIdemIn (AdS f S') e') (he'ε' : e' * ε' = e')
    (hsplit' : e' = ε' ∨ (e' ≠ ε' ∧ Fadj k f e' ≠ e' ∧ ε' = e' + Fadj k f e'))
    (hK'ε' : IsComponentOf K' ⁅BlkC k f S' ε', BlkC k f S' ε'⁆) (hR'K' : R' ≤ K')
    (hgeo : ∃ a₁ a₂ : Ix k → GaloisField 2 f, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
      LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
      (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ = 0 ∧
      (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₂ = 0 ∧
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂ = 0 ∧
      R'.map (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f))) =
        siegelGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂)
    (hdeg : (e' = ε' ∧ blockDegree (AdS f S') e' < 2) ∨
      (e' = ε' ∧ 2 ≤ blockDegree (AdS f S') e' ∧ blockDegree (AdS f S') e' < 4) ∨
      (e' ≠ ε' ∧ blockDegree (AdS f S') e' < 2)) :
    ∃ (t' : StatedLieTag) (m : ℕ) (ι : (ggU t' m f).K →* UK k f)
      (β : Fin (ggU t' m f).D.rank → ℤ) (u : (ggU t' m f).K),
      β ∈ (ggU t' m f).D.roots ∧ GGLongRoot (ggU t' m f).D β ∧ ι.range = K' ∧
      (∀ y, ι y ∈ Subgroup.center (UK k f) → y ∈ Subgroup.center (ggU t' m f).K) ∧
      (((ggU t' m f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι = R' ∧
      ((e' = ε' ∧ blockDegree (AdS f S') e' < 2 →
          (((t' = .POmegaPlus ∨ t' = .POmegaMinus) ∧ 3 ≤ m ∧ 2 * m = rk f e') ∨
            (t' = .PSL ∧ m = 2 ∧ rk f e' = 4))) ∧
        (e' = ε' ∧ 2 ≤ blockDegree (AdS f S') e' ∧ blockDegree (AdS f S') e' < 4 →
          t' = .PSU ∧ 2 * m = rk f e') ∧
        (e' ≠ ε' ∧ blockDegree (AdS f S') e' < 2 → t' = .PSL ∧ m = rk f e')) := by
  classical
  let Q := Spin.quadPlus (k + 3) (GaloisField 2 f)
  let G := LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin Q)
  obtain ⟨a₁, a₂, ha₁, ha₂, hli, hQ₁, hQ₂, horth, hm⟩ := hgeo
  have hle : siegelGroup Q a₁ a₂ ≤ K'.map (Spin.spinAction Q) := by
    rw [← hm]
    exact Subgroup.map_mono hR'K'
  rcases hsplit' with hself | ⟨hne, hadj, heq⟩
  · have hadjE : formAdj (RingHom.id (GaloisField 2 f)) G e' = e' := by
      rw [hself]; exact hε'.2.2.2.1
    have hK'E : IsComponentOf K' ⁅(glBlockCentralizer (Spin.spinMatrix Q) S' e' :
        Subgroup (UK k f)), (glBlockCentralizer (Spin.spinMatrix Q) S' e' :
        Subgroup (UK k f))⁆ := by
      rw [hself]; exact hK'ε'
    rcases hdeg with ⟨-, hd⟩ | ⟨-, hd1, hd2⟩ | ⟨hne', -⟩
    · obtain ⟨t', m, ι, hshape, hcenter, hrange, hclos⟩ :=
        exists_blockModelClosure_selfDual_POmegaPlus_explicit k f hf S' hSU' hS' hodd' he'
          hadjE hd (nbrpom_hnm_minusFour k f S' K' R' e' he' hK'E hR'K' hadjE a₁ a₂ ha₁
            ha₂ hli hQ₁ hQ₂ horth hm) hK'E
      obtain ⟨β, u, hβ, hβlong, hβeq⟩ := hclos a₁ a₂ ha₁ ha₂ hli hQ₁ hQ₂ horth hle
      refine ⟨t', m, ι, β, u, hβ, hβlong, hrange, hcenter,
        nbrpom_map_spinAction_injective (hβeq.trans hm.symm), ?_, ?_, ?_⟩
      · intro _
        exact hshape
      · intro h
        exact absurd h.2.1 (not_le.mpr hd)
      · intro h
        exact absurd hself h.1
    · have h :=
        exists_blockModelClosure_selfDualTwo_POmegaPlus_explicit k f S' hSU' hS' hodd' he'
          hadjE hd1 hd2 hK'E
      rw [max_eq_left hf] at h
      obtain ⟨r, ι, hrank, hcenter, hrange, hclos⟩ := h
      rw [← Matrix.toLin'_apply'] at hrank
      obtain ⟨β, u, hβ, hβlong, hβeq⟩ := hclos a₁ a₂ ha₁ ha₂ hli hQ₁ hQ₂ horth hle
      refine ⟨.PSU, r, ι, β, u, hβ, hβlong, hrange, hcenter,
        nbrpom_map_spinAction_injective (hβeq.trans hm.symm), ?_, ?_, ?_⟩
      · intro h
        exact absurd h.2 (not_lt.mpr hd1)
      · intro _
        exact ⟨rfl, hrank⟩
      · intro h
        exact absurd hself h.1
    · exact absurd hself hne'
  · rw [heq] at hK'ε'
    rcases hdeg with ⟨hself', -⟩ | ⟨hself', -⟩ | ⟨-, hd⟩
    · exact absurd hself' hne
    · exact absurd hself' hne
    · obtain ⟨r, ι, hrank, hcenter, hrange, hclos⟩ :=
        exists_blockModelClosure_dualPair_POmegaPlus_explicit k f hf S' hSU' hS' hodd' he'
          hadj hd hK'ε'
      obtain ⟨β, u, hβ, hβlong, hβeq⟩ := hclos a₁ a₂ ha₁ ha₂ hli hQ₁ hQ₂ horth hle
      refine ⟨.PSL, r + 1, ι, β, u, hβ, hβlong, hrange, hcenter,
        nbrpom_map_spinAction_injective (hβeq.trans hm.symm), ?_, ?_, ?_⟩
      · intro h
        exact absurd h.1 hne
      · intro h
        exact absurd h.1 hne
      · intro _
        exact ⟨rfl, hrank⟩

private theorem nbrpomx_K_setup
    {X : Type} [Group X] [Finite X] (k f : ℕ) (ψ : UK k f →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hH : GGSixPosHyp .POmegaPlus (k + 3) f ψ p G₀ B₁ D J L x)
    (S : Set (GL (Ix k) (GaloisField 2 f))) (J' : Subgroup (UK k f)) (ε : Mx k f)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hfull : ∀ s : GL (Ix k) (GaloisField 2 f), s ∈ (ρm k f).range →
      (∃ d ∈ D, IsGLLift (ρm k f) ψ s d) → s ∈ S)
    (hJ'comp : IsComponentOf J' ((Subgroup.centralizer S).comap (ρm k f)))
    (hJ'map : J'.map ψ = J)
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f)) (Gm k f) (AdS f S) ε)
    (hJ'ε : IsComponentOf J' ⁅BlkC k f S ε, BlkC k f S ε⁆)
    (e : X) (heD : e ∈ D) (K : Subgroup X) (hKG₀ : K ≤ G₀)
    (hKcomp : IsComponentOf K (Subgroup.centralizer {e})) (hJK : J ≤ K)
    (R Rm : Subgroup X) (hR : R ≤ J) (hR0 : GGRootPosG0 .POmegaPlus (k + 3) f p ψ R Rm) :
    ∃ (S' : Set (GL (Ix k) (GaloisField 2 f))) (K' R' : Subgroup (UK k f)) (ε' e' : Mx k f),
      S' ⊆ S ∧
      ((∀ s ∈ S', s ∈ (ρm k f).range) ∧ (∀ s ∈ S', ∀ s'' ∈ S', Commute s s'') ∧
        (∀ s ∈ S', Odd (orderOf s)) ∧
        IsComponentOf K' ((Subgroup.centralizer S').comap (ρm k f)) ∧ K'.map ψ = K) ∧
      (IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f)) (Gm k f) (AdS f S') ε' ∧
        IsComponentOf K' ⁅BlkC k f S' ε', BlkC k f S' ε'⁆) ∧
      IsPrimIdemIn (AdS f S') e' ∧ e' * ε' = e' ∧
      (e' = ε' ∨ (e' ≠ ε' ∧ Fadj k f e' ≠ e' ∧ ε' = e' + Fadj k f e')) ∧
      J' ≤ K' ∧ ε * ε' = ε ∧ R'.map ψ = R ∧ R' ≤ J' ∧
      (∃ a₁ a₂ : Ix k → GaloisField 2 f, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
        LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
        (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ = 0 ∧
        (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₂ = 0 ∧
        QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂ = 0 ∧
        R'.map (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f))) =
          siegelGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂) ∧
      ((e' = ε' ∧ blockDegree (AdS f S') e' < 2) ∨
        (e' = ε' ∧ 2 ≤ blockDegree (AdS f S') e' ∧ blockDegree (AdS f S') e' < 4) ∨
        (e' ≠ ε' ∧ blockDegree (AdS f S') e' < 2)) := by
  obtain ⟨S', K', ε', e', hSe, hSU', hS', hodd', hK'comp, hK'map, hε', he', he'ε', hsplit',
    hK'ε', hJK', htie⟩ := nbrpomx_neighbourBlockData k f ψ p G₀ B₁ D J L x hH S J' ε hS hfull
      hJ'comp hJ'map hε hJ'ε e heD K hKG₀ hKcomp hJK
  obtain ⟨R', hR'map, hgeo⟩ := nbrpom_L1 k f p ψ R Rm hR0
  have hinj : Function.Injective ψ := nbrpom_injective (k + 3) f (by omega) ψ hH.2.1
  have hR'J' : R' ≤ J' := by
    intro y hy
    have hyR : ψ y ∈ R := by rw [← hR'map]; exact Subgroup.mem_map_of_mem ψ hy
    have hyJ : ψ y ∈ J'.map ψ := by rw [hJ'map]; exact hR hyR
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hyJ
    rwa [hinj hzy] at hz
  have hR'K' : R' ≤ K' := hR'J'.trans hJK'
  have hdeg := nbrpom_L4 k f S' hSU' hS' hodd' K' R' ε' e' hε' he' he'ε' hsplit' hK'ε' hR'K'
    hgeo
  exact ⟨S', K', R', ε', e', hSe, ⟨hSU', hS', hodd', hK'comp, hK'map⟩, ⟨hε', hK'ε'⟩, he', he'ε',
    hsplit', hJK', htie, hR'map, hR'J', hgeo, hdeg⟩

private theorem nbrpomx_K_omega
    {X : Type} [Group X] [Finite X] (k f : ℕ)
    (ψ : (ggU .POmegaPlus (k + 3) f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hH : GGSixPosHyp .POmegaPlus (k + 3) f ψ p G₀ B₁ D J L x)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (J' : Subgroup (ggU .POmegaPlus (k + 3) f).K)
    (ε e_J : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))
    (hSU : ∀ s ∈ S, s ∈
      (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    (hfull : ∀ s : GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f),
      s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range →
      (∃ d ∈ D,
        IsGLLift (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) ψ s d) →
      s ∈ S)
    (hJ'comp : IsComponentOf J' ((Subgroup.centralizer S).comap
      (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)))))
    (hJ'map : J'.map ψ = J)
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f))))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    (heJ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (hJ'ε : IsComponentOf J' ⁅(glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K),
      (glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆)
    (hcase : e_J = ε ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2)
    (t' : StatedLieTag) (mJ : ℕ) (βJ : Fin (ggU t' mJ f).D.rank → ℤ)
    (ht' : t' = .POmegaPlus ∨ t' = .POmegaMinus) (hmJ : 3 ≤ mJ)
    (hrankJ : Module.finrank (GaloisField 2 f)
      (LinearMap.range (Matrix.toLin' e_J)) = 2 * mJ)
    (R Rm : Subgroup X) (hR : R ≤ J)
    (hR0 : GGRootPosG0 .POmegaPlus (k + 3) f p ψ R Rm)
    (e : X) (heD : e ∈ D) (K : Subgroup X) (hKG₀ : K ≤ G₀)
    (hKcomp : IsComponentOf K (Subgroup.centralizer {e})) (hJK : J ≤ K) (hKne : K ≠ J) :
    ∃ (t'' : StatedLieTag) (mK : ℕ) (βK : Fin (ggU t'' mK f).D.rank → ℤ),
      (t'' = .POmegaPlus ∨ t'' = .POmegaMinus) ∧ mJ < mK ∧
      βK ∈ (ggU t'' mK f).D.roots ∧ GGLongRoot (ggU t'' mK f).D βK ∧
      GGRootVia (ggU t'' mK f) K R βK := by
  have hψ : ψ.ker ≤ Subgroup.center (UK k f) := hH.2.1
  have hf : 1 ≤ f := (hH.2.2.1).admissible.2.1
  obtain ⟨S', K', R', ε', e', hSe, hKd, hEd, he', he'ε', hsplit', hJK', htie, hR'map, hR'J',
    hgeo, hdeg⟩ := nbrpomx_K_setup k f ψ p G₀ B₁ D J L x hH S J' ε hS hfull
      hJ'comp hJ'map hε hJ'ε e heD K hKG₀ hKcomp hJK R Rm hR hR0
  obtain ⟨hSU', hS', hodd', hK'comp, hK'map⟩ := hKd
  obtain ⟨hε', hK'ε'⟩ := hEd
  have hsplit'' : e' = ε' ∨ (e' ≠ ε' ∧ Fadj k f e' ≠ e' ∧ ε' = e' + Fadj k f e') := hsplit'
  have hR'K' : R' ≤ K' := hR'J'.trans hJK'
  have he'A : e' ∈ AdS f S := Algebra.adjoin_mono (Set.image_mono hSe) he'.1
  have hcomm : ∀ a b : Mx k f, a ∈ AdS f S → b ∈ AdS f S → a * b = b * a :=
    fun a b ha hb => (nbrpomx_adjoin_comm hS a ha b hb).eq
  have hperf : commutator ↥J' = ⊤ := hJ'comp.2.2.1
  have hadjJ : Fadj k f e_J = e_J := by rw [hcase.1]; exact hε.2.2.2.1
  have htieJ' : e_J * ε' = e_J := by rw [hcase.1]; exact htie

  have hedge : ∀ (ι : (ggU .PSL 2 f).K →* UK k f) (β : Fin (ggU .PSL 2 f).D.rank → ℤ)
      (u : (ggU .PSL 2 f).K), β ∈ (ggU .PSL 2 f).D.roots → ι.range = K' →
      (((ggU .PSL 2 f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι = R' →
      (∀ y, ι y ∈ Subgroup.center (UK k f) → y ∈ Subgroup.center (ggU .PSL 2 f).K) → False := by
    intro ι β u hβ hrange hroot hcent
    have hle : ι.range ≤ J' :=
      nbrpomx_plus_four k f hf ι hcent β hβ u J' hperf (hrange ▸ hJK') (hroot.le.trans hR'J')
    have hK'J' : K' ≤ J' := hrange ▸ hle
    apply hKne
    apply le_antisymm _ hJK
    rw [← hK'map, ← hJ'map]
    exact Subgroup.map_mono hK'J'
  rcases hdeg with ⟨heq, hd⟩ | ⟨heq, hd1, hd2⟩ | ⟨hne, hd⟩
  · obtain ⟨t'', m, ι, β, u, hβ, hlong, hrange, hcent, hroot, htype⟩ :=
      nbrpomx_K_model (X := X) k f hf S' hSU' hS' hodd' K' R' ε' e' hε' he' he'ε' hsplit''
        hK'ε' hR'K' hgeo (Or.inl ⟨heq, hd⟩)
    have hvia := nbrpomx_rootVia k f ψ hψ ι hcent K' R' K R hK'map hR'map hrange β u hroot
    have htieJ : e_J * e' = e_J := by rw [heq]; exact htieJ'
    have hba : e' * e_J = e_J := (hcomm e' e_J he'A heJ.1).trans htieJ
    have hne' : e_J ≠ e' :=
      nbrpomx_ne_one k f ψ S J' ε e_J hS heJ hcase J K hKne hJ'map S' K' ε' e' hK'map hSe hε'
        hK'ε' hJ'ε hJK' ⟨heq, hd⟩
    have hlt := nbrpomx_rank_lt_of_mul_eq heJ.2.1 htieJ hba hne'
    rcases (htype.1 ⟨heq, hd⟩) with ⟨ht'', h3, hrk⟩ | ⟨rfl, rfl, hrk4⟩
    · exact ⟨t'', m, β, ht'', by omega, hβ, hlong, hvia⟩
    · exact (hedge ι β u hβ hrange hroot hcent).elim
  · have htieJ : e_J * e' = e_J := by rw [heq]; exact htieJ'
    exact (nbrpomx_notSU hSe hS hS' hodd' heJ he' htieJ hcase.2 (by omega)).elim
  · have hs3 := hsplit''.resolve_left hne
    exact (nbrpomx_notSL (Gm k f) (nbrpomx_gram_det k f) hSe
      (fun s hs => nbrpomx_gram_iso k f (hSU s hs)) hS heJ hadjJ
      he' hs3 htieJ').elim

private theorem nbrpomx_K_su
    {X : Type} [Group X] [Finite X] (k f : ℕ)
    (ψ : (ggU .POmegaPlus (k + 3) f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hH : GGSixPosHyp .POmegaPlus (k + 3) f ψ p G₀ B₁ D J L x)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (J' : Subgroup (ggU .POmegaPlus (k + 3) f).K)
    (ε e_J : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))
    (hSU : ∀ s ∈ S, s ∈
      (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    (hfull : ∀ s : GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f),
      s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range →
      (∃ d ∈ D,
        IsGLLift (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) ψ s d) →
      s ∈ S)
    (hJ'comp : IsComponentOf J' ((Subgroup.centralizer S).comap
      (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)))))
    (hJ'map : J'.map ψ = J)
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f))))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    (heJ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (hJ'ε : IsComponentOf J' ⁅(glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K),
      (glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆)
    (hcase : e_J = ε ∧
      2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 4)
    (m'J : ℕ) (βJ : Fin (ggU .PSU m'J f).D.rank → ℤ)
    (hrankJ : Module.finrank (GaloisField 2 f)
      (LinearMap.range (Matrix.toLin' e_J)) = 2 * m'J)
    (R Rm : Subgroup X) (hR : R ≤ J)
    (hR0 : GGRootPosG0 .POmegaPlus (k + 3) f p ψ R Rm)
    (e : X) (heD : e ∈ D) (K : Subgroup X) (hKG₀ : K ≤ G₀)
    (hKcomp : IsComponentOf K (Subgroup.centralizer {e})) (hJK : J ≤ K) (hKne : K ≠ J) :
    (∃ (m'K : ℕ) (βK : Fin (ggU .PSU m'K f).D.rank → ℤ), m'J < m'K ∧
      βK ∈ (ggU .PSU m'K f).D.roots ∧ GGLongRoot (ggU .PSU m'K f).D βK ∧
      GGRootVia (ggU .PSU m'K f) K R βK) ∨
      (∃ (t'' : StatedLieTag) (mK : ℕ) (βK : Fin (ggU t'' mK f).D.rank → ℤ),
        (t'' = .POmegaPlus ∨ t'' = .POmegaMinus) ∧ 3 ≤ mK ∧ m'J ≤ mK ∧
        βK ∈ (ggU t'' mK f).D.roots ∧ GGLongRoot (ggU t'' mK f).D βK ∧
        GGRootVia (ggU t'' mK f) K R βK) := by
  have hψ : ψ.ker ≤ Subgroup.center (UK k f) := hH.2.1
  have hf : 1 ≤ f := (hH.2.2.1).admissible.2.1
  obtain ⟨S', K', R', ε', e', hSe, hKd, hEd, he', he'ε', hsplit', hJK', htie, hR'map, hR'J',
    hgeo, hdeg⟩ := nbrpomx_K_setup k f ψ p G₀ B₁ D J L x hH S J' ε hS hfull
      hJ'comp hJ'map hε hJ'ε e heD K hKG₀ hKcomp hJK R Rm hR hR0
  obtain ⟨hSU', hS', hodd', hK'comp, hK'map⟩ := hKd
  obtain ⟨hε', hK'ε'⟩ := hEd
  have hsplit'' : e' = ε' ∨ (e' ≠ ε' ∧ Fadj k f e' ≠ e' ∧ ε' = e' + Fadj k f e') := hsplit'
  have hR'K' : R' ≤ K' := hR'J'.trans hJK'
  have he'A : e' ∈ AdS f S := Algebra.adjoin_mono (Set.image_mono hSe) he'.1
  have hcomm : ∀ a b : Mx k f, a ∈ AdS f S → b ∈ AdS f S → a * b = b * a :=
    fun a b ha hb => (nbrpomx_adjoin_comm hS a ha b hb).eq
  have hperf : commutator ↥J' = ⊤ := hJ'comp.2.2.1
  have hadjJ : Fadj k f e_J = e_J := by rw [hcase.1]; exact hε.2.2.2.1
  have htieJ' : e_J * ε' = e_J := by rw [hcase.1]; exact htie

  have hedge : ∀ (ι : (ggU .PSL 2 f).K →* UK k f) (β : Fin (ggU .PSL 2 f).D.rank → ℤ)
      (u : (ggU .PSL 2 f).K), β ∈ (ggU .PSL 2 f).D.roots → ι.range = K' →
      (((ggU .PSL 2 f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι = R' →
      (∀ y, ι y ∈ Subgroup.center (UK k f) → y ∈ Subgroup.center (ggU .PSL 2 f).K) → False := by
    intro ι β u hβ hrange hroot hcent
    have hle : ι.range ≤ J' :=
      nbrpomx_plus_four k f hf ι hcent β hβ u J' hperf (hrange ▸ hJK') (hroot.le.trans hR'J')
    have hK'J' : K' ≤ J' := hrange ▸ hle
    apply hKne
    apply le_antisymm _ hJK
    rw [← hK'map, ← hJ'map]
    exact Subgroup.map_mono hK'J'
  rcases hdeg with ⟨heq, hd⟩ | ⟨heq, hd1, hd2⟩ | ⟨hne, hd⟩
  · obtain ⟨t'', m, ι, β, u, hβ, hlong, hrange, hcent, hroot, htype⟩ :=
      nbrpomx_K_model (X := X) k f hf S' hSU' hS' hodd' K' R' ε' e' hε' he' he'ε' hsplit''
        hK'ε' hR'K' hgeo (Or.inl ⟨heq, hd⟩)
    have hvia := nbrpomx_rootVia k f ψ hψ ι hcent K' R' K R hK'map hR'map hrange β u hroot
    have htieJ : e_J * e' = e_J := by rw [heq]; exact htieJ'
    have hba : e' * e_J = e_J := (hcomm e' e_J he'A heJ.1).trans htieJ
    have hle := nbrpomx_rank_le_of_mul_eq heJ.2.1 htieJ hba
    rcases (htype.1 ⟨heq, hd⟩) with ⟨ht'', h3, hrk⟩ | ⟨rfl, rfl, hrk4⟩
    · exact Or.inr ⟨t'', m, β, ht'', h3, by omega, hβ, hlong, hvia⟩
    · exact (hedge ι β u hβ hrange hroot hcent).elim
  · obtain ⟨t'', m, ι, β, u, hβ, hlong, hrange, hcent, hroot, htype⟩ :=
      nbrpomx_K_model (X := X) k f hf S' hSU' hS' hodd' K' R' ε' e' hε' he' he'ε' hsplit''
        hK'ε' hR'K' hgeo (Or.inr (Or.inl ⟨heq, hd1, hd2⟩))
    have hvia := nbrpomx_rootVia k f ψ hψ ι hcent K' R' K R hK'map hR'map hrange β u hroot
    have htieJ : e_J * e' = e_J := by rw [heq]; exact htieJ'
    have hba : e' * e_J = e_J := (hcomm e' e_J he'A heJ.1).trans htieJ
    have hne' : e_J ≠ e' :=
      nbrpomx_ne_two k f ψ S J' ε e_J hS hSU hodd hε heJ hcase.1 hcase.2.2 J K hKne hJ'map S' K'
        ε' e' hK'map hSe hS' hSU' hodd' hε' he' hK'ε' hJ'ε hJK' ⟨heq, hd1, hd2⟩
    have hlt := nbrpomx_rank_lt_of_mul_eq heJ.2.1 htieJ hba hne'
    obtain ⟨rfl, hrk⟩ := htype.2.1 ⟨heq, hd1, hd2⟩
    exact Or.inl ⟨m, β, by omega, hβ, hlong, hvia⟩
  · have hs3 := hsplit''.resolve_left hne
    exact (nbrpomx_notSL (Gm k f) (nbrpomx_gram_det k f) hSe
      (fun s hs => nbrpomx_gram_iso k f (hSU s hs)) hS heJ hadjJ
      he' hs3 htieJ').elim

private theorem nbrpomx_K_omega_sl
    {X : Type} [Group X] [Finite X] (k f : ℕ)
    (ψ : (ggU .POmegaPlus (k + 3) f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hH : GGSixPosHyp .POmegaPlus (k + 3) f ψ p G₀ B₁ D J L x)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (J' : Subgroup (ggU .POmegaPlus (k + 3) f).K)
    (ε e_J : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))
    (hSU : ∀ s ∈ S, s ∈
      (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    (hfull : ∀ s : GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f),
      s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range →
      (∃ d ∈ D,
        IsGLLift (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) ψ s d) →
      s ∈ S)
    (hJ'comp : IsComponentOf J' ((Subgroup.centralizer S).comap
      (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)))))
    (hJ'map : J'.map ψ = J)
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f))))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    (heJ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (hJ'ε : IsComponentOf J' ⁅(glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K),
      (glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆)
    (hcase : e_J = ε ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2)
    (kJ : ℕ) (βJ : Fin (ggU .PSL (kJ + 1) f).D.rank → ℤ)
    (hrankJ : Module.finrank (GaloisField 2 f)
      (LinearMap.range (Matrix.toLin' e_J)) = 2 * (kJ + 1))
    (R Rm : Subgroup X) (hR : R ≤ J)
    (hR0 : GGRootPosG0 .POmegaPlus (k + 3) f p ψ R Rm)
    (e : X) (heD : e ∈ D) (K : Subgroup X) (hKG₀ : K ≤ G₀)
    (hKcomp : IsComponentOf K (Subgroup.centralizer {e})) (hJK : J ≤ K) (hKne : K ≠ J) :
    (∃ (kK : ℕ) (βK : Fin (ggU .PSL (kK + 1) f).D.rank → ℤ), kJ < kK ∧
      βK ∈ (ggU .PSL (kK + 1) f).D.roots ∧
      GGRootVia (ggU .PSL (kK + 1) f) K R βK) ∨
      (∃ (t'' : StatedLieTag) (mK : ℕ) (βK : Fin (ggU t'' mK f).D.rank → ℤ),
        (t'' = .POmegaPlus ∨ t'' = .POmegaMinus) ∧ 3 ≤ mK ∧ kJ + 1 ≤ mK ∧
        βK ∈ (ggU t'' mK f).D.roots ∧ GGLongRoot (ggU t'' mK f).D βK ∧
        GGRootVia (ggU t'' mK f) K R βK) := by
  have hψ : ψ.ker ≤ Subgroup.center (UK k f) := hH.2.1
  have hf : 1 ≤ f := (hH.2.2.1).admissible.2.1
  obtain ⟨S', K', R', ε', e', hSe, hKd, hEd, he', he'ε', hsplit', hJK', htie, hR'map, hR'J',
    hgeo, hdeg⟩ := nbrpomx_K_setup k f ψ p G₀ B₁ D J L x hH S J' ε hS hfull
      hJ'comp hJ'map hε hJ'ε e heD K hKG₀ hKcomp hJK R Rm hR hR0
  obtain ⟨hSU', hS', hodd', hK'comp, hK'map⟩ := hKd
  obtain ⟨hε', hK'ε'⟩ := hEd
  have hsplit'' : e' = ε' ∨ (e' ≠ ε' ∧ Fadj k f e' ≠ e' ∧ ε' = e' + Fadj k f e') := hsplit'
  have hR'K' : R' ≤ K' := hR'J'.trans hJK'
  have he'A : e' ∈ AdS f S := Algebra.adjoin_mono (Set.image_mono hSe) he'.1
  have hcomm : ∀ a b : Mx k f, a ∈ AdS f S → b ∈ AdS f S → a * b = b * a :=
    fun a b ha hb => (nbrpomx_adjoin_comm hS a ha b hb).eq
  have hperf : commutator ↥J' = ⊤ := hJ'comp.2.2.1
  have hadjJ : Fadj k f e_J = e_J := by rw [hcase.1]; exact hε.2.2.2.1
  have htieJ' : e_J * ε' = e_J := by rw [hcase.1]; exact htie

  have hedge : ∀ (ι : (ggU .PSL 2 f).K →* UK k f) (β : Fin (ggU .PSL 2 f).D.rank → ℤ)
      (u : (ggU .PSL 2 f).K), β ∈ (ggU .PSL 2 f).D.roots → ι.range = K' →
      (((ggU .PSL 2 f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι = R' →
      (∀ y, ι y ∈ Subgroup.center (UK k f) → y ∈ Subgroup.center (ggU .PSL 2 f).K) → False := by
    intro ι β u hβ hrange hroot hcent
    have hle : ι.range ≤ J' :=
      nbrpomx_plus_four k f hf ι hcent β hβ u J' hperf (hrange ▸ hJK') (hroot.le.trans hR'J')
    have hK'J' : K' ≤ J' := hrange ▸ hle
    apply hKne
    apply le_antisymm _ hJK
    rw [← hK'map, ← hJ'map]
    exact Subgroup.map_mono hK'J'
  rcases hdeg with ⟨heq, hd⟩ | ⟨heq, hd1, hd2⟩ | ⟨hne, hd⟩
  · obtain ⟨t'', m, ι, β, u, hβ, hlong, hrange, hcent, hroot, htype⟩ :=
      nbrpomx_K_model (X := X) k f hf S' hSU' hS' hodd' K' R' ε' e' hε' he' he'ε' hsplit''
        hK'ε' hR'K' hgeo (Or.inl ⟨heq, hd⟩)
    have hvia := nbrpomx_rootVia k f ψ hψ ι hcent K' R' K R hK'map hR'map hrange β u hroot
    have htieJ : e_J * e' = e_J := by rw [heq]; exact htieJ'
    have hba : e' * e_J = e_J := (hcomm e' e_J he'A heJ.1).trans htieJ
    have hle := nbrpomx_rank_le_of_mul_eq heJ.2.1 htieJ hba
    rcases (htype.1 ⟨heq, hd⟩) with ⟨ht'', h3, hrk⟩ | ⟨rfl, rfl, hrk4⟩
    · exact Or.inr ⟨t'', m, β, ht'', h3, by omega, hβ, hlong, hvia⟩
    · exact (hedge ι β u hβ hrange hroot hcent).elim
  · have htieJ : e_J * e' = e_J := by rw [heq]; exact htieJ'
    exact (nbrpomx_notSU hSe hS hS' hodd' heJ he' htieJ hcase.2 (by omega)).elim
  · have hs3 := hsplit''.resolve_left hne
    exact (nbrpomx_notSL (Gm k f) (nbrpomx_gram_det k f) hSe
      (fun s hs => nbrpomx_gram_iso k f (hSU s hs)) hS heJ hadjJ
      he' hs3 htieJ').elim

private theorem nbrpomx_K_sl
    {X : Type} [Group X] [Finite X] (k f : ℕ)
    (ψ : (ggU .POmegaPlus (k + 3) f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hH : GGSixPosHyp .POmegaPlus (k + 3) f ψ p G₀ B₁ D J L x)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (J' : Subgroup (ggU .POmegaPlus (k + 3) f).K)
    (ε e_J : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))
    (hSU : ∀ s ∈ S, s ∈
      (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    (hfull : ∀ s : GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f),
      s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range →
      (∃ d ∈ D,
        IsGLLift (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) ψ s d) →
      s ∈ S)
    (hJ'comp : IsComponentOf J' ((Subgroup.centralizer S).comap
      (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)))))
    (hJ'map : J'.map ψ = J)
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f))))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    (heJ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (hJ'ε : IsComponentOf J' ⁅(glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K),
      (glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε :
        Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆)
    (hcase : e_J ≠ ε ∧
        formAdj (RingHom.id (GaloisField 2 f))
          (LinearMap.toMatrix₂' (GaloisField 2 f)
            (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e_J ≠ e_J ∧
        ε = e_J + formAdj (RingHom.id (GaloisField 2 f))
          (LinearMap.toMatrix₂' (GaloisField 2 f)
            (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e_J ∧
        blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2)
    (kJ : ℕ) (βJ : Fin (ggU .PSL (kJ + 1) f).D.rank → ℤ)
    (hrankJ : Module.finrank (GaloisField 2 f)
      (LinearMap.range (Matrix.toLin' e_J)) = kJ + 1)
    (R Rm : Subgroup X) (hR : R ≤ J)
    (hR0 : GGRootPosG0 .POmegaPlus (k + 3) f p ψ R Rm)
    (e : X) (heD : e ∈ D) (K : Subgroup X) (hKG₀ : K ≤ G₀)
    (hKcomp : IsComponentOf K (Subgroup.centralizer {e})) (hJK : J ≤ K) (hKne : K ≠ J) :
    (∃ (kK : ℕ) (βK : Fin (ggU .PSL (kK + 1) f).D.rank → ℤ), kJ < kK ∧
      βK ∈ (ggU .PSL (kK + 1) f).D.roots ∧
      GGRootVia (ggU .PSL (kK + 1) f) K R βK) ∨
      (∃ (t'' : StatedLieTag) (mK : ℕ) (βK : Fin (ggU t'' mK f).D.rank → ℤ),
        (t'' = .POmegaPlus ∨ t'' = .POmegaMinus) ∧ 3 ≤ mK ∧ kJ + 1 ≤ mK ∧
        βK ∈ (ggU t'' mK f).D.roots ∧ GGLongRoot (ggU t'' mK f).D βK ∧
        GGRootVia (ggU t'' mK f) K R βK) := by
  have hψ : ψ.ker ≤ Subgroup.center (UK k f) := hH.2.1
  have hf : 1 ≤ f := (hH.2.2.1).admissible.2.1
  obtain ⟨S', K', R', ε', e', hSe, hKd, hEd, he', he'ε', hsplit', hJK', htie, hR'map, hR'J',
    hgeo, hdeg⟩ := nbrpomx_K_setup k f ψ p G₀ B₁ D J L x hH S J' ε hS hfull
      hJ'comp hJ'map hε hJ'ε e heD K hKG₀ hKcomp hJK R Rm hR hR0
  obtain ⟨hSU', hS', hodd', hK'comp, hK'map⟩ := hKd
  obtain ⟨hε', hK'ε'⟩ := hEd
  have hsplit'' : e' = ε' ∨ (e' ≠ ε' ∧ Fadj k f e' ≠ e' ∧ ε' = e' + Fadj k f e') := hsplit'
  have hR'K' : R' ≤ K' := hR'J'.trans hJK'
  have he'A : e' ∈ AdS f S := Algebra.adjoin_mono (Set.image_mono hSe) he'.1
  have hcomm : ∀ a b : Mx k f, a ∈ AdS f S → b ∈ AdS f S → a * b = b * a :=
    fun a b ha hb => (nbrpomx_adjoin_comm hS a ha b hb).eq
  have hperf : commutator ↥J' = ⊤ := hJ'comp.2.2.1
  have hrank_eps : rk f ε = 2 * (kJ + 1) :=
    nbrpomx_rank_eps k f S hSU hS heJ hcase.2.1 hcase.2.2.1 kJ hrankJ
  have horth : e_J * Fadj k f e_J = 0 := nbrpomx_dualPair_orth k f S hSU hS heJ hcase.2.1
  have heJε : e_J * ε = e_J := by
    rw [hcase.2.2.1, mul_add, heJ.2.1.eq, horth, add_zero]
  have heJε' : e_J * ε' = e_J := by
    calc e_J * ε' = (e_J * ε) * ε' := by rw [heJε]
      _ = e_J * (ε * ε') := by rw [Matrix.mul_assoc]
      _ = e_J * ε := by rw [htie]
      _ = e_J := heJε
  have hε'A : ε' ∈ AdS f S := Algebra.adjoin_mono (Set.image_mono hSe) hε'.1
  have hba' : ε' * ε = ε := (hcomm ε' ε hε'A hε.1).trans htie

  have hedge : ∀ (ι : (ggU .PSL 2 f).K →* UK k f) (β : Fin (ggU .PSL 2 f).D.rank → ℤ)
      (u : (ggU .PSL 2 f).K), β ∈ (ggU .PSL 2 f).D.roots → ι.range = K' →
      (((ggU .PSL 2 f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι = R' →
      (∀ y, ι y ∈ Subgroup.center (UK k f) → y ∈ Subgroup.center (ggU .PSL 2 f).K) → False := by
    intro ι β u hβ hrange hroot hcent
    have hle : ι.range ≤ J' :=
      nbrpomx_plus_four k f hf ι hcent β hβ u J' hperf (hrange ▸ hJK') (hroot.le.trans hR'J')
    have hK'J' : K' ≤ J' := hrange ▸ hle
    apply hKne
    apply le_antisymm _ hJK
    rw [← hK'map, ← hJ'map]
    exact Subgroup.map_mono hK'J'
  rcases hdeg with ⟨heq, hd⟩ | ⟨heq, hd1, hd2⟩ | ⟨hne, hd⟩
  · obtain ⟨t'', m, ι, β, u, hβ, hlong, hrange, hcent, hroot, htype⟩ :=
      nbrpomx_K_model (X := X) k f hf S' hSU' hS' hodd' K' R' ε' e' hε' he' he'ε' hsplit''
        hK'ε' hR'K' hgeo (Or.inl ⟨heq, hd⟩)
    have hvia := nbrpomx_rootVia k f ψ hψ ι hcent K' R' K R hK'map hR'map hrange β u hroot
    have hle := nbrpomx_rank_le_of_mul_eq hε.2.1 htie hba'
    have hrk' : rk f e' = rk f ε' := by rw [heq]
    rcases (htype.1 ⟨heq, hd⟩) with ⟨ht'', h3, hrk⟩ | ⟨rfl, rfl, hrk4⟩
    · exact Or.inr ⟨t'', m, β, ht'', h3, by omega, hβ, hlong, hvia⟩
    · exact (hedge ι β u hβ hrange hroot hcent).elim
  · have htieJ : e_J * e' = e_J := by rw [heq]; exact heJε'
    exact (nbrpomx_notSU hSe hS hS' hodd' heJ he' htieJ hcase.2.2.2 (by omega)).elim
  · obtain ⟨hne1, hpair', hεeq'⟩ := hsplit''.resolve_left hne
    obtain ⟨t'', m, ι, β, u, hβ, hlong, hrange, hcent, hroot, htype⟩ :=
      nbrpomx_K_model (X := X) k f hf S' hSU' hS' hodd' K' R' ε' e' hε' he' he'ε' hsplit''
        hK'ε' hR'K' hgeo (Or.inr (Or.inr ⟨hne, hd⟩))
    obtain ⟨rfl, hm⟩ := htype.2.2 ⟨hne, hd⟩
    have hvia := nbrpomx_rootVia k f ψ hψ ι hcent K' R' K R hK'map hR'map hrange β u hroot
    have hG := nbrpomx_gram_det k f
    have hGh := nbrpomx_gram_transpose k f
    have hinv : Fadj k f (Fadj k f e') = e' :=
      Geo.formAdj_formAdj (RingHom.id (GaloisField 2 f)) (fun x => rfl) hG hGh e'
    have hrk'' : rk f (Fadj k f e') = rk f e' := nbrpomx_rank_formAdj hG
    have hsumJ : e_J * e' + e_J * Fadj k f e' = e_J := by
      rw [← mul_add, ← hεeq', heJε']
    have hJe' : e_J * e' = 0 ∨ e_J * e' = e_J := by
      apply heJ.2.2.2
      · exact Subalgebra.mul_mem _ heJ.1 he'A
      · rw [IsIdempotentElem]
        calc (e_J * e') * (e_J * e') = e_J * (e' * (e_J * e')) := by rw [mul_assoc]
          _ = e_J * ((e' * e_J) * e') := by rw [mul_assoc]
          _ = e_J * ((e_J * e') * e') := by rw [hcomm e' e_J he'A heJ.1]
          _ = e_J * (e_J * (e' * e')) := by rw [mul_assoc]
          _ = e_J * (e_J * e') := by rw [he'.2.1.eq]
          _ = (e_J * e_J) * e' := by rw [mul_assoc]
          _ = e_J * e' := by rw [heJ.2.1.eq]
      · rw [mul_assoc, hcomm e' e_J he'A heJ.1, ← mul_assoc, heJ.2.1.eq]
    have hlt' : rk f e_J < rk f e' := by
      rcases hJe' with h0 | hA
      · have hB' : e_J * Fadj k f e' = e_J := by
          have h := hsumJ
          rw [h0, zero_add] at h
          exact h
        have hPrim'' := nbrpomx_isPrimIdemIn_formAdj k f S' hSU' hS' he'
        have hstar_ne : Fadj k f e' ≠ ε' := by
          intro h
          apply hne1
          have hh := congrArg (formAdj (RingHom.id (GaloisField 2 f)) (Gm k f)) h
          rw [hinv, hε'.2.2.2.1] at hh
          exact hh
        have hstar_pair : Fadj k f (Fadj k f e') ≠ Fadj k f e' := by
          rw [hinv]; exact fun h => hpair' h.symm
        have hstar_sum : ε' = Fadj k f e' + Fadj k f (Fadj k f e') := by
          rw [hinv]; exact hεeq'.trans (add_comm _ _)
        have hne2 : e_J ≠ Fadj k f e' :=
          nbrpomx_ne_dual k f ψ S S' hSe hSU hSU' hS hK'map J hJ'map hJ'comp hK'comp hJK' hKne
            hK'ε' heJ hcase.2.2.2 ⟨hstar_ne, hstar_pair, hstar_sum⟩ hPrim''
        have hstarA : Fadj k f e' ∈ AdS f S := Algebra.adjoin_mono (Set.image_mono hSe) hPrim''.1
        have hba2 : Fadj k f e' * e_J = e_J := (hcomm _ e_J hstarA heJ.1).trans hB'
        have hlt := nbrpomx_rank_lt_of_mul_eq heJ.2.1 hB' hba2 hne2
        omega
      · have hne2 : e_J ≠ e' :=
          nbrpomx_ne_dual k f ψ S S' hSe hSU hSU' hS hK'map J hJ'map hJ'comp hK'comp hJK' hKne
            hK'ε' heJ hcase.2.2.2 ⟨hne1, hpair', hεeq'⟩ he'
        have hba1 : e' * e_J = e_J := (hcomm e' e_J he'A heJ.1).trans hA
        exact nbrpomx_rank_lt_of_mul_eq heJ.2.1 hA hba1 hne2
    obtain ⟨kK, rfl⟩ : ∃ kK, m = kK + 1 := ⟨m - 1, by omega⟩
    exact Or.inl ⟨kK, β, by omega, hβ, hvia⟩

end KLeaves

private theorem nbrpomx_assembly
    {X : Type} [Group X] [Finite X] (k f : ℕ)
    (ψ : (ggU .POmegaPlus (k + 3) f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hH : GGSixPosHyp .POmegaPlus (k + 3) f ψ p G₀ B₁ D J L x) :
    ∃ (R Rm : Subgroup X), R ≤ J ∧ Rm ≤ J ∧
      GGRootPosG0 .POmegaPlus (k + 3) f p ψ R Rm ∧
      ((∃ (t' : StatedLieTag) (mJ : ℕ) (βJ : Fin (ggU t' mJ f).D.rank → ℤ),
          (t' = .POmegaPlus ∨ t' = .POmegaMinus) ∧ 3 ≤ mJ ∧
          βJ ∈ (ggU t' mJ f).D.roots ∧ GGLongRoot (ggU t' mJ f).D βJ ∧
          GGRootVia (ggU t' mJ f) J R βJ ∧
          ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
            IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
            Odd (Nat.card (Subgroup.center ↥K)) →
            ∃ (t'' : StatedLieTag) (mK : ℕ) (βK : Fin (ggU t'' mK f).D.rank → ℤ),
              (t'' = .POmegaPlus ∨ t'' = .POmegaMinus) ∧ mJ < mK ∧
              βK ∈ (ggU t'' mK f).D.roots ∧ GGLongRoot (ggU t'' mK f).D βK ∧
              GGRootVia (ggU t'' mK f) K R βK) ∨
        (∃ (kJ : ℕ) (βJ : Fin (ggU .PSL (kJ + 1) f).D.rank → ℤ),
          βJ ∈ (ggU .PSL (kJ + 1) f).D.roots ∧
          GGRootVia (ggU .PSL (kJ + 1) f) J R βJ ∧
          ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
            IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
            Odd (Nat.card (Subgroup.center ↥K)) →
            (∃ (kK : ℕ) (βK : Fin (ggU .PSL (kK + 1) f).D.rank → ℤ), kJ < kK ∧
              βK ∈ (ggU .PSL (kK + 1) f).D.roots ∧
              GGRootVia (ggU .PSL (kK + 1) f) K R βK) ∨
            (∃ (t'' : StatedLieTag) (mK : ℕ) (βK : Fin (ggU t'' mK f).D.rank → ℤ),
              (t'' = .POmegaPlus ∨ t'' = .POmegaMinus) ∧ 3 ≤ mK ∧ kJ + 1 ≤ mK ∧
              βK ∈ (ggU t'' mK f).D.roots ∧ GGLongRoot (ggU t'' mK f).D βK ∧
              GGRootVia (ggU t'' mK f) K R βK)) ∨
        (∃ (m'J : ℕ) (βJ : Fin (ggU .PSU m'J f).D.rank → ℤ),
          βJ ∈ (ggU .PSU m'J f).D.roots ∧
          GGRootVia (ggU .PSU m'J f) J R βJ ∧
          ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
            IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
            Odd (Nat.card (Subgroup.center ↥K)) →
            (∃ (m'K : ℕ) (βK : Fin (ggU .PSU m'K f).D.rank → ℤ), m'J < m'K ∧
              βK ∈ (ggU .PSU m'K f).D.roots ∧ GGLongRoot (ggU .PSU m'K f).D βK ∧
              GGRootVia (ggU .PSU m'K f) K R βK) ∨
              (∃ (t'' : StatedLieTag) (mK : ℕ) (βK : Fin (ggU t'' mK f).D.rank → ℤ),
                (t'' = .POmegaPlus ∨ t'' = .POmegaMinus) ∧ 3 ≤ mK ∧ m'J ≤ mK ∧
                βK ∈ (ggU t'' mK f).D.roots ∧ GGLongRoot (ggU t'' mK f).D βK ∧
                GGRootVia (ggU t'' mK f) K R βK))) := by
  obtain ⟨S, J', ε, e_J, hSU, hS, hodd, hfull, hJ'comp, hJ'map, hε, heJ, heJε, hsplit,
    hJ'ε, hcase⟩ := nbrpomx_J_split k f ψ p G₀ B₁ D J L x hH
  rcases hcase with homega | hsu | hsl
  · obtain ⟨R, Rm, hRJ, hRmJ, hR0, hJcase⟩ :=
      nbrpomx_J_omega k f ψ p G₀ B₁ D J L x hH S J' ε e_J hSU hS hodd hfull hJ'comp
        hJ'map hε heJ hJ'ε homega
    rcases hJcase with hO | hSL2
    · obtain ⟨t', mJ, βJ, ht', hmJ, hβJ, hlongJ, hviaJ, hrankJ⟩ := hO
      refine ⟨R, Rm, hRJ, hRmJ, hR0, Or.inl ⟨t', mJ, βJ, ht', hmJ, hβJ, hlongJ, hviaJ, ?_⟩⟩
      intro e heD he1 K hKG₀ hKcomp hJK hKne hZodd
      exact nbrpomx_K_omega k f ψ p G₀ B₁ D J L x hH S J' ε e_J hSU hS hodd hfull hJ'comp
        hJ'map hε heJ hJ'ε homega t' mJ βJ ht' hmJ hrankJ R Rm hRJ hR0 e heD K hKG₀ hKcomp
        hJK hKne
    · obtain ⟨kJ, βJ, hkJ, hβJ, hviaJ, hrankJ⟩ := hSL2
      refine ⟨R, Rm, hRJ, hRmJ, hR0, Or.inr (Or.inl ⟨kJ, βJ, hβJ, hviaJ, ?_⟩)⟩
      intro e heD he1 K hKG₀ hKcomp hJK hKne hZodd
      exact nbrpomx_K_omega_sl k f ψ p G₀ B₁ D J L x hH S J' ε e_J hSU hS hodd hfull hJ'comp
        hJ'map hε heJ hJ'ε homega kJ βJ hrankJ R Rm hRJ hR0 e heD K hKG₀ hKcomp
        hJK hKne
  · obtain ⟨R, Rm, hRJ, hRmJ, hR0, m'J, βJ, hβJ, hviaJ, hrankJ⟩ :=
      nbrpomx_J_su k f ψ p G₀ B₁ D J L x hH S J' ε e_J hSU hS hodd hfull hJ'comp
        hJ'map hε heJ hJ'ε hsu
    refine ⟨R, Rm, hRJ, hRmJ, hR0, Or.inr (Or.inr ⟨m'J, βJ, hβJ, hviaJ, ?_⟩)⟩
    intro e heD he1 K hKG₀ hKcomp hJK hKne hZodd
    exact nbrpomx_K_su k f ψ p G₀ B₁ D J L x hH S J' ε e_J hSU hS hodd hfull hJ'comp
      hJ'map hε heJ hJ'ε hsu m'J βJ hrankJ R Rm hRJ hR0 e heD K hKG₀ hKcomp hJK hKne
  · have hsl' : e_J ≠ ε ∧
        formAdj (RingHom.id (GaloisField 2 f))
          (LinearMap.toMatrix₂' (GaloisField 2 f)
            (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e_J ≠ e_J ∧
        ε = e_J + formAdj (RingHom.id (GaloisField 2 f))
          (LinearMap.toMatrix₂' (GaloisField 2 f)
            (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e_J ∧
        blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2 := by
      rcases hsplit with hself | ⟨hne, hpair, heq⟩
      · exact absurd hself hsl.1
      · exact ⟨hne, hpair, heq, hsl.2⟩
    obtain ⟨R, Rm, hRJ, hRmJ, hR0, kJ, βJ, hβJ, hviaJ, hrankJ⟩ :=
      nbrpomx_J_sl k f ψ p G₀ B₁ D J L x hH S J' ε e_J hSU hS hodd hfull hJ'comp
        hJ'map heJ hJ'ε hsl'
    refine ⟨R, Rm, hRJ, hRmJ, hR0, Or.inr (Or.inl ⟨kJ, βJ, hβJ, hviaJ, ?_⟩)⟩
    intro e heD he1 K hKG₀ hKcomp hJK hKne hZodd
    exact nbrpomx_K_sl k f ψ p G₀ B₁ D J L x hH S J' ε e_J hSU hS hodd hfull hJ'comp
      hJ'map hε heJ hJ'ε hsl' kJ βJ hrankJ R Rm hRJ hR0 e heD K hKG₀ hKcomp
      hJK hKne

theorem ggSixPOmegaPlusPosExplicit_holds :
    CFSG.StandardType.LieKnownR2.POmega.GGSixPOmegaPosExplicit .POmegaPlus := by
  unfold CFSG.StandardType.LieKnownR2.POmega.GGSixPOmegaPosExplicit
  intro X hX hXfin n f ψ p G₀ B₁ D J L x hH
  have h4 : 4 ≤ n := nbrpom_L6 n f ψ p G₀ B₁ D J L x hH
  obtain ⟨k, hk⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  subst n
  exact nbrpomx_assembly k f ψ p G₀ B₁ D J L x hH

end CFSG.StandardType.ClassicalPosition
