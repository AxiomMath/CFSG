module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3Def
public import CFSG.LinearAlgebra.FixedPointFreeOrderThreeField
public import CFSG.CharacterTheory.Semidihedral.ElementaryActionTransport
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartOne.KC.OrthogonalSelfDualBlock
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryField
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LinearAlgebra
open CFSG.Semidihedral.ElementaryActionTransport
open Module

private def s16k_even (i : Fin 3) : Fin 6 := ⟨2 * i.val, by omega⟩

private def s16k_odd (i : Fin 3) : Fin 6 := ⟨2 * i.val + 1, by omega⟩

private def s16k_diagR : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun r c =>
    if r.val / 2 = c.val / 2 then
      (if r.val % 2 = 0 then (if c.val % 2 = 1 then 1 else 0) else 1)
    else 0

private lemma s16k_blockMat_prod :
    s16kBlockMat 0 * s16kBlockMat 1 * s16kBlockMat 2 = s16k_diagR := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp only [s16k_diagR, Matrix.mul_apply, s16kBlockMat, Matrix.of_apply] <;>
    decide

private lemma s16k_finProdFinEquiv_zero (i : Fin 3) :
    finProdFinEquiv (i, (0 : Fin 2)) = s16k_even i := by
  apply Fin.ext
  simp [finProdFinEquiv, s16k_even]

private lemma s16k_finProdFinEquiv_one (i : Fin 3) :
    finProdFinEquiv (i, (1 : Fin 2)) = s16k_odd i := by
  apply Fin.ext
  simp [finProdFinEquiv, s16k_odd]
  omega

private lemma s16k_diagR_col_even (i : Fin 3) :
    s16k_diagR.col (s16k_even i) = Pi.single (s16k_odd i) 1 := by
  funext r
  fin_cases r <;> fin_cases i <;>
    simp only [s16k_diagR, s16k_even, s16k_odd, Matrix.col_apply, Pi.single_apply] <;>
    decide

private lemma s16k_diagR_col_odd (i : Fin 3) :
    s16k_diagR.col (s16k_odd i) = Pi.single (s16k_odd i) 1 + Pi.single (s16k_even i) 1 := by
  funext r
  fin_cases r <;> fin_cases i <;>
    simp only [s16k_diagR, s16k_even, s16k_odd, Matrix.col_apply, Pi.single_apply,
      Pi.add_apply] <;>
    decide

private lemma s16k_fin6_cases (n : Fin 6) :
    (∃ i : Fin 3, n = s16k_even i) ∨ (∃ i : Fin 3, n = s16k_odd i) := by
  fin_cases n
  · exact Or.inl ⟨⟨0, by omega⟩, by decide⟩
  · exact Or.inr ⟨⟨0, by omega⟩, by decide⟩
  · exact Or.inl ⟨⟨1, by omega⟩, by decide⟩
  · exact Or.inr ⟨⟨1, by omega⟩, by decide⟩
  · exact Or.inl ⟨⟨2, by omega⟩, by decide⟩
  · exact Or.inr ⟨⟨2, by omega⟩, by decide⟩

section Coord

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module OmegaField V]
  [IsScalarTower (ZMod 2) OmegaField V]

private theorem s16k_omegaPB_dim : (AdjoinRoot.powerBasis' omegaPoly_monic).dim = 2 := by
  rw [AdjoinRoot.powerBasis'_dim, omegaPoly_natDegree]

private noncomputable def s16k_omegaBasis : Basis (Fin 2) (ZMod 2) OmegaField :=
  (AdjoinRoot.powerBasis' omegaPoly_monic).basis.reindex (finCongr s16k_omegaPB_dim)

private lemma s16k_omegaBasis_zero : s16k_omegaBasis (0 : Fin 2) = 1 := by
  rw [s16k_omegaBasis, Basis.reindex_apply]
  simp only [PowerBasis.coe_basis]
  have hx : (((finCongr s16k_omegaPB_dim).symm (0 : Fin 2) :
      Fin (AdjoinRoot.powerBasis' omegaPoly_monic).dim) : ℕ) = 0 := rfl
  rw [hx, pow_zero]

private lemma s16k_omegaBasis_one : s16k_omegaBasis (1 : Fin 2) = CFSG.LinearAlgebra.omega := by
  rw [s16k_omegaBasis, Basis.reindex_apply]
  simp only [PowerBasis.coe_basis]
  have hx : (((finCongr s16k_omegaPB_dim).symm (1 : Fin 2) :
      Fin (AdjoinRoot.powerBasis' omegaPoly_monic).dim) : ℕ) = 1 := rfl
  rw [hx, pow_one]
  rfl

private noncomputable def s16k_omegaEquiv : OmegaField ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
  s16k_omegaBasis.equivFun

private lemma s16k_omegaEquiv_one : s16k_omegaEquiv (1 : OmegaField) = Pi.single (0 : Fin 2) 1 := by
  conv_lhs => rw [← s16k_omegaBasis_zero]
  funext j
  rw [s16k_omegaEquiv, Basis.equivFun_self]
  simp [Pi.single_apply, eq_comm]

private lemma s16k_omegaEquiv_omega :
    s16k_omegaEquiv CFSG.LinearAlgebra.omega = Pi.single (1 : Fin 2) 1 := by
  conv_lhs => rw [← s16k_omegaBasis_one]
  funext j
  rw [s16k_omegaEquiv, Basis.equivFun_self]
  simp [Pi.single_apply, eq_comm]

private noncomputable def s16k_piCurryFin :
    (Fin 3 → Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2) where
  toFun f := fun n =>
    let p := (finProdFinEquiv (m := 3) (n := 2)).symm n
    f p.1 p.2
  invFun g := fun i j => g (finProdFinEquiv (m := 3) (n := 2) (i, j))
  left_inv f := by
    funext i j
    dsimp only
    simp
  right_inv g := by
    funext n
    dsimp only
    simp
  map_add' f g := by
    funext n
    rfl
  map_smul' c f := by
    funext n
    rfl

private noncomputable def s16k_restrict (b3 : Basis (Fin 3) OmegaField V) :
    V ≃ₗ[ZMod 2] (Fin 3 → OmegaField) where
  toFun := b3.equivFun
  invFun := b3.equivFun.symm
  left_inv := b3.equivFun.left_inv
  right_inv := b3.equivFun.right_inv
  map_add' := fun x y => map_add b3.equivFun x y
  map_smul' := fun c x => by
    show b3.equivFun (c • x) = c • b3.equivFun x
    rw [← IsScalarTower.algebraMap_smul (A := OmegaField) c x,
      map_smul b3.equivFun (algebraMap (ZMod 2) OmegaField c) x,
      IsScalarTower.algebraMap_smul (A := OmegaField) c]

private noncomputable def s16k_coordEquiv (b3 : Basis (Fin 3) OmegaField V) :
    V ≃ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
  (s16k_restrict b3).trans
    ((LinearEquiv.piCongrRight (fun _ : Fin 3 => s16k_omegaEquiv)).trans s16k_piCurryFin)

private lemma s16k_coordEquiv_apply_restrict (b3 : Basis (Fin 3) OmegaField V) (v : V) :
    (s16k_restrict b3) v = b3.equivFun v := rfl

private lemma s16k_piCurryFin_single_one (i : Fin 3) (j : Fin 2) :
    s16k_piCurryFin (Pi.single i (Pi.single j (1 : ZMod 2))) =
      Pi.single (finProdFinEquiv (m := 3) (n := 2) (i, j)) 1 := by
  funext n
  fin_cases n <;> fin_cases i <;> fin_cases j <;>
    simp [s16k_piCurryFin, Pi.single_apply, finProdFinEquiv] <;> decide

private lemma s16k_piCurryFin_single (i : Fin 3) (j : Fin 2) (c : ZMod 2) :
    s16k_piCurryFin (Pi.single i (Pi.single j c)) =
      Pi.single (finProdFinEquiv (m := 3) (n := 2) (i, j)) c := by
  have h : (Pi.single i (Pi.single j c) : Fin 3 → Fin 2 → ZMod 2) =
      c • Pi.single i (Pi.single j (1 : ZMod 2)) := by
    funext k l
    by_cases hk : k = i <;> by_cases hl : l = j <;>
      simp [Pi.single_apply, hk, hl, Pi.smul_apply, smul_eq_mul]
  rw [h, map_smul, s16k_piCurryFin_single_one]
  funext n
  simp [Pi.single_apply]

private lemma s16k_congrLinearEquiv_apply
    (e : V ≃ₗ[ZMod 2] (Fin 6 → ZMod 2))
    (g : LinearMap.GeneralLinearGroup (ZMod 2) V) (x : Fin 6 → ZMod 2) :
    (LinearMap.GeneralLinearGroup.congrLinearEquiv e g :
        Module.End (ZMod 2) (Fin 6 → ZMod 2)) x =
      e ((g : Module.End (ZMod 2) V) (e.symm x)) := by
  rfl

private lemma s16k_coordEquiv_basis (b3 : Basis (Fin 3) OmegaField V) (i : Fin 3) :
    s16k_coordEquiv b3 (b3 i) = Pi.single (s16k_even i) 1 := by
  have h1 : b3.equivFun (b3 i) = Pi.single i (1 : OmegaField) := by
    funext j
    rw [Basis.equivFun_self]
    simp [Pi.single_apply, eq_comm]
  have h2 : (fun j : Fin 3 =>
        s16k_omegaEquiv (((Pi.single i (1 : OmegaField) : Fin 3 → OmegaField)) j)) =
      (Pi.single i (s16k_omegaEquiv 1) : Fin 3 → Fin 2 → ZMod 2) := by
    funext j
    by_cases hj : j = i
    · simp [Pi.single_apply, hj]
    · simp [Pi.single_apply, hj]
  rw [s16k_coordEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  change s16k_piCurryFin (fun j : Fin 3 => s16k_omegaEquiv ((s16k_restrict b3) (b3 i) j)) = _
  rw [s16k_coordEquiv_apply_restrict b3 (b3 i), h1, h2, s16k_omegaEquiv_one,
    s16k_piCurryFin_single, s16k_finProdFinEquiv_zero]

private lemma s16k_coordEquiv_omega_basis (b3 : Basis (Fin 3) OmegaField V) (i : Fin 3) :
    s16k_coordEquiv b3 (CFSG.LinearAlgebra.omega • b3 i) = Pi.single (s16k_odd i) 1 := by
  have h1 : b3.equivFun (b3 i) = Pi.single i (1 : OmegaField) := by
    funext j
    rw [Basis.equivFun_self]
    simp [Pi.single_apply, eq_comm]
  have hsm : b3.equivFun (CFSG.LinearAlgebra.omega • b3 i) =
      CFSG.LinearAlgebra.omega • Pi.single i (1 : OmegaField) := by
    rw [map_smul, h1]
  have h2 : (fun j : Fin 3 =>
        s16k_omegaEquiv (((CFSG.LinearAlgebra.omega • Pi.single i (1 : OmegaField) :
          Fin 3 → OmegaField)) j)) =
      (Pi.single i (s16k_omegaEquiv CFSG.LinearAlgebra.omega) : Fin 3 → Fin 2 → ZMod 2) := by
    funext j
    by_cases hj : j = i
    · simp [Pi.single_apply, hj, Pi.smul_apply]
    · simp [Pi.single_apply, hj, Pi.smul_apply]
  rw [s16k_coordEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  change s16k_piCurryFin
      (fun j : Fin 3 =>
        s16k_omegaEquiv ((s16k_restrict b3) (CFSG.LinearAlgebra.omega • b3 i) j)) = _
  rw [s16k_coordEquiv_apply_restrict b3 (CFSG.LinearAlgebra.omega • b3 i), hsm, h2,
    s16k_omegaEquiv_omega, s16k_piCurryFin_single, s16k_finProdFinEquiv_one]

end Coord

theorem s16k_z3_model {W : Type} [CommGroup W] [Finite W] (hW : ∀ x : W, x ^ 2 = 1)
    (hcard : Nat.card W = 2 ^ 6) {Lb : Subgroup (MulAut W)} (hLb : IsCyclicOrd ↥Lb 3)
    (hfpf : ∀ l ∈ Lb, ∀ x : W, l x = x → l = 1 ∨ x = 1) :
    ∃ (e : W ≃* Multiplicative (Fin 6 → ZMod 2)) (φ : MulAut W ≃* S16kGL6),
      (∀ (g : MulAut W) (w : W), Multiplicative.toAdd (e (g w)) =
        ((φ g : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec (Multiplicative.toAdd (e w))) ∧
      Lb.map φ.toMonoidHom = s16kScal := by
  classical
  haveI hEA : IsElementaryAbelian 2 W :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hW }
  let V := Additive W
  haveI : Finite V := inferInstance
  have hfin6 : Module.finrank (ZMod 2) V = 6 := by
    have h := card_eq_prime_pow_finrank (p := 2) (R := W)
    rw [hcard] at h
    exact (Nat.pow_right_injective (by norm_num : 1 < 2) h).symm
  obtain ⟨ω₀, hω₀gen⟩ := hLb.1.exists_generator
  let ω : MulAut W := (ω₀ : MulAut W)
  have hωmem : ω ∈ Lb := ω₀.property
  have hLb_eq : Lb = Subgroup.zpowers ω := by
    apply le_antisymm
    · intro x hx
      have hx' : (⟨x, hx⟩ : ↥Lb) ∈ Subgroup.zpowers ω₀ := hω₀gen ⟨x, hx⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx'
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      have := congrArg Subtype.val hk
      simpa using this
    · rw [Subgroup.zpowers_le]
      exact hωmem
  have hωorder : orderOf ω = 3 := by
    have h1 : orderOf (ω₀ : MulAut W) = orderOf ω₀ := Subgroup.orderOf_coe ω₀
    have h2 : orderOf ω₀ = 3 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hω₀gen, hLb.2]
    exact h1.trans h2
  have hωne : ω ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hωorder
    omega
  let z : LinearMap.GeneralLinearGroup (ZMod 2) V := autEquivGL (p := 2) (R := W) ω
  have hzorder : orderOf z = 3 := by
    have h1 : orderOf (autEquivGL (p := 2) (R := W) ω) = orderOf ω :=
      orderOf_injective (autEquivGL (p := 2) (R := W)).toMonoidHom
        (autEquivGL (p := 2) (R := W)).injective ω
    exact h1.trans hωorder
  have hzfix : ∀ v : V, (z : V →ₗ[ZMod 2] V) v = v → v = 0 := by
    intro v hv
    have hv' : (autEquivGL (p := 2) (R := W) ω : Module.End (ZMod 2) V)
        (Additive.ofMul (Additive.toMul v)) = Additive.ofMul (Additive.toMul v) := hv
    change (autToGL (p := 2) (R := W) ω : Module.End (ZMod 2) V)
        (Additive.ofMul (Additive.toMul v)) = Additive.ofMul (Additive.toMul v) at hv'
    rw [autToGL_apply] at hv'
    have hww : ω (Additive.toMul v) = Additive.toMul v := Additive.ofMul.injective hv'
    rcases hfpf ω hωmem (Additive.toMul v) hww with h1 | h1
    · exact absurd h1 hωne
    · have hv0 : v = 0 := by
        change (Additive.ofMul (Additive.toMul v) : Additive W) = 0
        rw [h1]
        rfl
      exact hv0
  letI : Module OmegaField V := omegaModule z hzorder hzfix
  haveI : IsScalarTower (ZMod 2) OmegaField V := omegaModule_isScalarTower z hzorder hzfix
  have homega : ∀ v : V, CFSG.LinearAlgebra.omega • v = (z : V →ₗ[ZMod 2] V) v :=
    omegaModule_omega_smul z hzorder hzfix
  have hfin3 : Module.finrank OmegaField V = 3 := by
    have hmul := Module.finrank_mul_finrank (ZMod 2) OmegaField V
    rw [finrank_omegaField, hfin6] at hmul
    omega
  let b3 : Basis (Fin 3) OmegaField V := finBasisOfFinrankEq OmegaField V hfin3
  let eLin : V ≃ₗ[ZMod 2] (Fin 6 → ZMod 2) := s16k_coordEquiv b3
  let bF2 : Fin 6 → V := fun n => eLin.symm (Pi.single n 1)
  have hb3_even : ∀ i : Fin 3, bF2 (s16k_even i) = b3 i := by
    intro i
    change eLin.symm (Pi.single (s16k_even i) 1) = b3 i
    rw [← s16k_coordEquiv_basis b3 i, LinearEquiv.symm_apply_apply]
  have hb3_odd : ∀ i : Fin 3, bF2 (s16k_odd i) = CFSG.LinearAlgebra.omega • b3 i := by
    intro i
    change eLin.symm (Pi.single (s16k_odd i) 1) = CFSG.LinearAlgebra.omega • b3 i
    rw [← s16k_coordEquiv_omega_basis b3 i, LinearEquiv.symm_apply_apply]
  have hconj : (LinearMap.GeneralLinearGroup.congrLinearEquiv eLin
        (autEquivGL (p := 2) (R := W) ω) :
      (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) =
      Matrix.mulVecLin (s16kBlockMat 0 * s16kBlockMat 1 * s16kBlockMat 2) := by
    apply (Pi.basisFun (ZMod 2) (Fin 6)).ext
    intro n
    rw [Pi.basisFun_apply]
    change eLin ((autEquivGL (p := 2) (R := W) ω : Module.End (ZMod 2) V) (bF2 n)) =
      Matrix.mulVecLin (s16kBlockMat 0 * s16kBlockMat 1 * s16kBlockMat 2) (Pi.single n 1)
    rw [← homega (bF2 n)]
    rcases s16k_fin6_cases n with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [hb3_even i, s16k_coordEquiv_omega_basis, Matrix.mulVecLin_apply,
        Matrix.mulVec_single_one, s16k_blockMat_prod, s16k_diagR_col_even]
    · rw [hb3_odd i, smul_smul, ← pow_two, omega_sq, add_smul, one_smul, map_add,
        s16k_coordEquiv_omega_basis, s16k_coordEquiv_basis, Matrix.mulVecLin_apply,
        Matrix.mulVec_single_one, s16k_blockMat_prod, s16k_diagR_col_odd]
  let e : W ≃* Multiplicative (Fin 6 → ZMod 2) :=
    { toFun := fun w => Multiplicative.ofAdd (eLin (Additive.ofMul w))
      invFun := fun x => Additive.toMul (eLin.symm (Multiplicative.toAdd x))
      left_inv := fun w => by simp
      right_inv := fun x => by simp
      map_mul' := fun a b => by simp }
  let φ : MulAut W ≃* S16kGL6 :=
    (autEquivGL (p := 2) (R := W)).trans
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv eLin).trans
        (Matrix.GeneralLinearGroup.toLin (n := Fin 6) (R := ZMod 2)).symm)
  have htofun : ∀ g : MulAut W,
      Matrix.GeneralLinearGroup.toLin (n := Fin 6) (R := ZMod 2) (φ g) =
      LinearMap.GeneralLinearGroup.congrLinearEquiv eLin (autEquivGL (p := 2) (R := W) g) := by
    intro g
    simp only [φ, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  refine ⟨e, φ, ?_, ?_⟩
  · intro g w
    have happ : (autEquivGL (p := 2) (R := W) g : Module.End (ZMod 2) V)
        (Additive.ofMul w) = Additive.ofMul (g w) := by
      change (autToGL (p := 2) (R := W) g : Module.End (ZMod 2) V) (Additive.ofMul w) =
        Additive.ofMul (g w)
      rw [autToGL_apply]
    have hc := s16k_congrLinearEquiv_apply eLin (autEquivGL (p := 2) (R := W) g)
      (eLin (Additive.ofMul w))
    rw [LinearEquiv.symm_apply_apply] at hc
    rw [happ] at hc
    change eLin (Additive.ofMul (g w)) =
      Matrix.mulVec ((φ g : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2))
        (eLin (Additive.ofMul w))
    conv_rhs => rw [← Matrix.mulVecLin_apply, ← Matrix.GeneralLinearGroup.coe_toLin, htofun g]
    exact hc.symm
  · have hφω : ((φ ω : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        s16kBlockMat 0 * s16kBlockMat 1 * s16kBlockMat 2 := by
      apply Matrix.ext_of_mulVec_single
      intro n
      conv_lhs => rw [← Matrix.mulVecLin_apply, ← Matrix.GeneralLinearGroup.coe_toLin, htofun ω,
        hconj]
      rw [Matrix.mulVecLin_apply]
    have hscal : s16kScal = Subgroup.zpowers (φ ω) := by
      rw [s16kScal, Subgroup.zpowers_eq_closure]
      congr 1
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro hg
        exact Units.ext (hg.trans hφω.symm)
      · intro hg
        rw [hg]
        exact hφω
    calc Lb.map φ.toMonoidHom = (Subgroup.zpowers ω).map φ.toMonoidHom := by rw [hLb_eq]
      _ = Subgroup.zpowers (φ ω) := MonoidHom.map_zpowers φ.toMonoidHom ω
      _ = s16kScal := hscal.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
