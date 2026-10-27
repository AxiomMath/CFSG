module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalMultiplicity
public import CFSG.Quasithin.Background.F918Z5ATensor
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.TensorAssemble
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp
open scoped TensorProduct Matrix

theorem s168e3_tensorNatL32_of_threeNat_kBar_168
    {W : Type} [CommGroup W] [Finite W]
    {A B T : Subgroup (MulAut W)}
    (h : ThreeNat A B T)
    (h7 : Nat.card ↥(irrSet B) = 7)
    (hL3 : IsL3 ↥B 1)
    (hFix : fixV B = ⊥)
    (hK168 : Nat.card ↥(s1t3KBar A B) = 168) :
    TensorNatL32 A := by
  classical
  letI : Module (ZMod 2) (Additive W) := MulAutTwo.zmod2Module h.elem
  obtain ⟨m⟩ := h.exists_naturalThreeMultiplicityData h7 hL3
  letI : AddCommGroup m.Q := m.qAdd
  letI : Module (ZMod 2) m.Q := m.qModule
  letI : Finite m.Q := m.qFinite
  letI : AddCommGroup m.X := m.xAdd
  letI : Module (ZMod 2) m.X := m.xModule
  letI : Finite m.X := m.xFinite
  haveI : Module.Finite (ZMod 2) m.X := Module.Finite.of_finite
  let K : Subgroup (MulAut W) := s1t3KBar A B
  have hKcard : Nat.card ↥K = 168 := hK168
  have hker : LinearMap.ker m.qW = ⊥ := by
    rw [m.ker_qW, hFix]
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [mem_s16smSubmod] at hx
    have hx1 : Additive.toMul x = 1 := by simpa using hx
    rw [← ofMul_toMul x, hx1]
    rfl
  have hqW_inj : Function.Injective m.qW := LinearMap.ker_eq_bot.mp hker
  let qWe : Additive W ≃ₗ[ZMod 2] m.Q ⊗[ZMod 2] m.X :=
    LinearEquiv.ofBijective m.qW ⟨hqW_inj, m.qW_surjective⟩
  let bQ : Module.Basis (Fin 3) (ZMod 2) m.Q := Module.Basis.ofEquivFun m.coordQ
  let bX : Module.Basis (Fin 3) (ZMod 2) m.X :=
    Module.finBasisOfFinrankEq (ZMod 2) m.X m.finrank_X
  let kAct : ↥K →* (m.X ≃ₗ[ZMod 2] m.X) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) m.X).toMonoidHom.comp
      m.kappaX.asGroupHom
  have hkAct_apply : ∀ k : ↥K,
      ((kAct k : m.X ≃ₗ[ZMod 2] m.X) : m.X →ₗ[ZMod 2] m.X) =
        ((m.kappaX.asGroupHom k : (m.X →ₗ[ZMod 2] m.X)ˣ) :
          m.X →ₗ[ZMod 2] m.X) := fun k =>
    LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap (m.kappaX.asGroupHom k)
  have hkAct_inj : Function.Injective kAct := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k hk
    rw [Subgroup.mem_bot]
    have hk1 : kAct k = 1 := MonoidHom.mem_ker.mp hk
    have hkappa1 : (m.kappaX k : m.X →ₗ[ZMod 2] m.X) = LinearMap.id := by
      have h1 := congrArg (fun e : m.X ≃ₗ[ZMod 2] m.X =>
        (e : m.X →ₗ[ZMod 2] m.X)) hk1
      rw [hkAct_apply k, Representation.asGroupHom_apply] at h1
      simpa using h1
    have hfixk : ∀ v : W, (k : MulAut W) v = v := by
      intro v
      have hqK : m.qW (Additive.ofMul ((k : MulAut W) v)) =
          TensorProduct.map LinearMap.id (m.kappaX k) (m.qW (Additive.ofMul v)) := by
        have hstep := m.qW_K k (Additive.ofMul v)
        rw [s16smRepW_apply] at hstep
        simpa using hstep
      rw [hkappa1, TensorProduct.map_id] at hqK
      exact congrArg Additive.toMul (hqW_inj hqK)
    exact Subtype.ext (MulEquiv.ext hfixk)
  let sigmaK : ↥K →* ↥(StatedSL 3 (ZMod 2)) :=
    ((basisGL bX).comp kAct).codRestrict (StatedSL 3 (ZMod 2))
      (fun _ => CFSG.Open.StatedAPI.mem_statedSL_zmod_two _)
  have hsigmaK_inj : Function.Injective sigmaK := by
    intro a b hab
    apply hkAct_inj
    apply basisGL_injective bX
    have h1 := congrArg (fun s : ↥(StatedSL 3 (ZMod 2)) =>
      (s : GL (Fin 3) (ZMod 2))) hab
    simpa [sigmaK] using h1
  have hcardK : Nat.card ↥K = Nat.card ↥(StatedSL 3 (ZMod 2)) := by
    rw [hKcard, CFSG.Open.StatedAPI.card_statedSL_three_zmod_two]
  let kappa : ↥K ≃* ↥(StatedSL 3 (ZMod 2)) :=
    MulEquiv.ofBijective sigmaK (hsigmaK_inj.bijective_of_nat_card_le hcardK.symm.le)
  let iB : ↥B →* ↥A := Subgroup.inclusion h.le
  let iK : ↥K →* ↥A := Subgroup.inclusion (show K ≤ A from inf_le_left)
  have hcomm : ∀ b : ↥B, ∀ k : ↥K, Commute (iB b) (iK k) := by
    intro b k
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp k.2).2 (b : MulAut W) b.2
  let productMap : (↥B × ↥K) →* ↥A :=
    iB.noncommCoprod iK (fun b k => hcomm b k)
  let pi : (↥(StatedSL 3 (ZMod 2)) × ↥(StatedSL 3 (ZMod 2))) →* ↥A :=
    productMap.comp (MulEquiv.prodCongr m.theta kappa).symm.toMonoidHom
  have hpi_val : ∀ γ : ↥(StatedSL 3 (ZMod 2)) × ↥(StatedSL 3 (ZMod 2)),
      ((pi γ : ↥A) : MulAut W) =
        (m.theta.symm γ.1 : MulAut W) * (kappa.symm γ.2 : MulAut W) := by
    rintro ⟨s₁, s₂⟩
    simp [pi, productMap, iB, iK, MulEquiv.prodCongr, MonoidHom.noncommCoprod_apply]
  have hpi : Function.Surjective pi := by
    intro a
    obtain ⟨l, hl, k, hk, hlk⟩ := h.exists_mul_kBar_of_card_eq_168 h7
      (CFSG.LocalAnalysis.WeakClosure81.card_eq_of_isL3 hL3) a.2
    refine ⟨(m.theta ⟨l, hl⟩, kappa ⟨k, hk⟩), ?_⟩
    apply Subtype.ext
    rw [hpi_val, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    simpa using hlk.symm
  let beta : W ≃* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    AddEquiv.toMultiplicativeRight
      (qWe.toAddEquiv.trans (tensorMatrixEquiv bQ bX).toAddEquiv)
  have hbeta_val : ∀ v : W,
      beta v = Multiplicative.ofAdd
        ((tensorMatrixEquiv bQ bX) (qWe (Additive.ofMul v))) := by
    intro v
    exact AddEquiv.toMultiplicativeRight_apply_apply _ v
  have hmatB : ∀ b : ↥B,
      LinearMap.toMatrix bQ bQ (m.rhoQ b) =
        (((m.theta b : ↥(StatedSL 3 (ZMod 2))) : GL (Fin 3) (ZMod 2)) :
          Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    intro b
    rw [Matrix.ext_iff_mulVec]
    intro x
    obtain ⟨q, rfl⟩ := m.coordQ.surjective x
    have h1 : (LinearMap.toMatrix bQ bQ (m.rhoQ b)).mulVec (bQ.equivFun q) =
        bQ.equivFun (m.rhoQ b q) :=
      LinearMap.toMatrix_mulVec_repr bQ bQ (m.rhoQ b) q
    rw [Module.Basis.equivFun_ofEquivFun] at h1
    rw [h1, m.coordQ_apply]
  have hmatK : ∀ k : ↥K,
      LinearMap.toMatrix bX bX (m.kappaX k) =
        (((kappa k : ↥(StatedSL 3 (ZMod 2))) : GL (Fin 3) (ZMod 2)) :
          Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    intro k
    have h1 : ((kappa k : ↥(StatedSL 3 (ZMod 2))) : GL (Fin 3) (ZMod 2)) =
        basisGL bX (kAct k) := rfl
    rw [h1, coe_basisGL]
    rw [hkAct_apply k, Representation.asGroupHom_apply]
  have hβ : ∀ (γ : ↥(StatedSL 3 (ZMod 2)) × ↥(StatedSL 3 (ZMod 2))) (v : W),
      beta ((pi γ : MulAut W) v) = tensorAct 3 (ZMod 2) γ (beta v) := by
    rintro ⟨s₁, s₂⟩ v
    have hqK : ∀ y : W, m.qW (Additive.ofMul ((kappa.symm s₂ : MulAut W) y)) =
        TensorProduct.map LinearMap.id (m.kappaX (kappa.symm s₂))
          (m.qW (Additive.ofMul y)) := by
      intro y
      have hstep := m.qW_K (kappa.symm s₂) (Additive.ofMul y)
      rw [s16smRepW_apply] at hstep
      simpa using hstep
    have hqB : ∀ y : W, m.qW (Additive.ofMul ((m.theta.symm s₁ : MulAut W) y)) =
        TensorProduct.map (m.rhoQ (m.theta.symm s₁)) LinearMap.id
          (m.qW (Additive.ofMul y)) := by
      intro y
      have hstep := m.qW_L (m.theta.symm s₁) (Additive.ofMul y)
      rw [s16smRepW_apply] at hstep
      simpa using hstep
    have hq1 : m.qW (Additive.ofMul ((pi (s₁, s₂) : MulAut W) v)) =
        TensorProduct.map (m.rhoQ (m.theta.symm s₁)) LinearMap.id
          (TensorProduct.map LinearMap.id (m.kappaX (kappa.symm s₂))
            (m.qW (Additive.ofMul v))) := by
      rw [hpi_val]
      rw [show ((m.theta.symm s₁ : MulAut W) * (kappa.symm s₂ : MulAut W)) v =
          (m.theta.symm s₁ : MulAut W) ((kappa.symm s₂ : MulAut W) v) from rfl]
      rw [hqB, hqK]
    have hΦ : (tensorMatrixEquiv bQ bX)
          (m.qW (Additive.ofMul ((pi (s₁, s₂) : MulAut W) v))) =
        (((s₁ : GL (Fin 3) (ZMod 2))) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
          (tensorMatrixEquiv bQ bX) (m.qW (Additive.ofMul v)) *
          ((((s₂ : GL (Fin 3) (ZMod 2))) : Matrix (Fin 3) (Fin 3) (ZMod 2)))ᵀ := by
      rw [hq1, tensorMatrixEquiv_map_left, tensorMatrixEquiv_map_right,
        hmatB (m.theta.symm s₁), hmatK (kappa.symm s₂),
        MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, Matrix.mul_assoc]
    have hqWe_apply : ∀ x : Additive W, qWe x = m.qW x := fun x => rfl
    calc
      beta ((pi (s₁, s₂) : MulAut W) v)
          = Multiplicative.ofAdd ((tensorMatrixEquiv bQ bX)
              (qWe (Additive.ofMul ((pi (s₁, s₂) : MulAut W) v)))) := hbeta_val _
      _ = Multiplicative.ofAdd ((tensorMatrixEquiv bQ bX)
              (m.qW (Additive.ofMul ((pi (s₁, s₂) : MulAut W) v)))) := by
            rw [hqWe_apply]
      _ = Multiplicative.ofAdd
              (((s₁ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
                (tensorMatrixEquiv bQ bX) (m.qW (Additive.ofMul v)) *
                (((s₂ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))ᵀ) := by
            rw [hΦ]
      _ = tensorAct 3 (ZMod 2) (s₁, s₂) (beta v) := rfl
  exact tensorNatL32_of_tensorData pi hpi beta hβ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
