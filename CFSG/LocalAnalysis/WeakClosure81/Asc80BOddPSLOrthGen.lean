module

import CFSG.LieType.SeitzGeneration.LinearOuterLocal
import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSL
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.OppositeRadicals
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.LieType.Seitz.Defs
public import CFSG.LieType.SeitzGeneration.OutdiagParabolic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch11SecOE5B

public section

namespace CFSG.LocalAnalysis.WeakClosure81.PSLOuter

open Subgroup Matrix CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private lemma matrix_scalar_eq_smul_one {K : Type*} [Semiring K] {m : Type*}
    [Fintype m] [DecidableEq m] (a : K) :
    Matrix.scalar m a = a • (1 : Matrix m m K) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.scalar_apply, h]

private lemma conjActionGL_eq_neg_of_mem_thetaSpace {F : Type} [Field F] {n : ℕ}
    {D : GL (Fin n) F} (hD2 : D * D = 1)
    {W W' : Submodule F (Fin n → F)} (hsup : W ⊔ W' = ⊤)
    (hDW : ∀ w ∈ W, (D : Matrix (Fin n) (Fin n) F) *ᵥ w = w)
    (hDW' : ∀ w ∈ W', (D : Matrix (Fin n) (Fin n) F) *ᵥ w = -w)
    {φ : Matrix (Fin n) (Fin n) F} (hφ : φ ∈ thetaSpace W ∨ φ ∈ thetaSpace W') :
    conjActionGL D φ = -φ := by
  have hDm2 : (D : Matrix (Fin n) (Fin n) F) * (D : Matrix (Fin n) (Fin n) F) = 1 := by
    have h := congrArg (fun x : GL (Fin n) F => (x : Matrix (Fin n) (Fin n) F)) hD2
    simpa only [GeneralLinearGroup.coe_mul, Units.val_one] using h
  have hinv : ((D⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (D : Matrix (Fin n) (Fin n) F) := by
    rw [GeneralLinearGroup.coe_inv, Matrix.inv_eq_right_inv hDm2]
  rw [conjActionGL_apply, hinv]
  apply Matrix.ext_iff_mulVec.2
  intro v
  have hv : v ∈ W ⊔ W' := hsup ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule F (Fin n → F)))
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hv
  subst hab
  have hDa : (D : Matrix (Fin n) (Fin n) F) *ᵥ a = a := hDW a ha
  have hDb : (D : Matrix (Fin n) (Fin n) F) *ᵥ b = -b := hDW' b hb
  have h1 : (D : Matrix (Fin n) (Fin n) F) *ᵥ (a + b) = a - b := by
    rw [Matrix.mulVec_add, hDa, hDb, sub_eq_add_neg]
  have hstep : ((D : Matrix (Fin n) (Fin n) F) * φ * (D : Matrix (Fin n) (Fin n) F)) *ᵥ
        (a + b) =
      (D : Matrix (Fin n) (Fin n) F) *ᵥ
        (φ *ᵥ ((D : Matrix (Fin n) (Fin n) F) *ᵥ (a + b))) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hstep, h1]
  rcases hφ with hφ | hφ
  · have hφa : φ *ᵥ a = 0 := (mem_thetaSpace.1 hφ).2 a ha
    have hφb : φ *ᵥ b ∈ W := (mem_thetaSpace.1 hφ).1 b
    have h2 : φ *ᵥ (a - b) = -(φ *ᵥ b) := by
      rw [Matrix.mulVec_sub, hφa, zero_sub]
    have h3 : (D : Matrix (Fin n) (Fin n) F) *ᵥ (-(φ *ᵥ b)) = -(φ *ᵥ b) := by
      rw [Matrix.mulVec_neg, hDW (φ *ᵥ b) hφb]
    rw [h2, h3, Matrix.neg_mulVec, Matrix.mulVec_add, hφa, zero_add]
  · have hφa : φ *ᵥ a ∈ W' := (mem_thetaSpace.1 hφ).1 a
    have hφb : φ *ᵥ b = 0 := (mem_thetaSpace.1 hφ).2 b hb
    have h2 : φ *ᵥ (a - b) = φ *ᵥ a := by
      rw [Matrix.mulVec_sub, hφb, sub_zero]
    have h3 : (D : Matrix (Fin n) (Fin n) F) *ᵥ (φ *ᵥ a) = -(φ *ᵥ a) :=
      hDW' (φ *ᵥ a) hφa
    rw [h2, h3, Matrix.neg_mulVec, Matrix.mulVec_add, hφb, add_zero]

private lemma mem_comap_closure_of_theta {F : Type} [Field F] [Finite F] {n : ℕ}
    (h2 : (2 : F) ≠ 0) {A A' D : GL (Fin n) F} {u : Fˣ}
    (hAA : A * A = GeneralLinearGroup.scalar (Fin n) u)
    (hA'D : A' = A * D)
    {U : Submodule F (Fin n → F)}
    (hAU : ∀ w ∈ U, (A : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ U)
    (hAUi : ∀ w ∈ U, ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ U)
    (hDneg : ∀ ψ ∈ thetaSpace U, conjActionGL D ψ = -ψ)
    (g : SpecialLinearGroup (Fin n) F)
    (hg : (g : Matrix (Fin n) (Fin n) F) - 1 ∈ thetaSpace U) :
    g ∈ (Subgroup.closure {x : projectiveSL n F |
      conjAut n F A x = x ∨ conjAut n F A' x = x}).comap (proj n F) := by
  classical
  let φ : Matrix (Fin n) (Fin n) F := (g : Matrix (Fin n) (Fin n) F) - 1
  have hφU : φ ∈ thetaSpace U := hg
  have hAconj : conjActionGL A φ ∈ thetaSpace U :=
    conjActionGL_mem_thetaSpace hAU hAUi hφU
  let N₁ : Matrix (Fin n) (Fin n) F := (2 : F)⁻¹ • (φ + conjActionGL A φ)
  let N₂ : Matrix (Fin n) (Fin n) F := (2 : F)⁻¹ • (φ - conjActionGL A φ)
  have hN₁U : N₁ ∈ thetaSpace U :=
    (thetaSpace U).smul_mem _ ((thetaSpace U).add_mem hφU hAconj)
  have hN₂U : N₂ ∈ thetaSpace U :=
    (thetaSpace U).smul_mem _ ((thetaSpace U).sub_mem hφU hAconj)
  have hN₁N₂ : N₁ * N₂ = 0 := thetaSpace_mul hN₁U hN₂U
  have hsum : N₁ + N₂ = φ := by
    show (2 : F)⁻¹ • (φ + conjActionGL A φ) + (2 : F)⁻¹ • (φ - conjActionGL A φ) = φ
    have h : (2 : F)⁻¹ • (φ + conjActionGL A φ) + (2 : F)⁻¹ • (φ - conjActionGL A φ) =
        (2 : F)⁻¹ • ((φ + conjActionGL A φ) + (φ - conjActionGL A φ)) :=
      (smul_add _ _ _).symm
    rw [h]
    have h3 : (φ + conjActionGL A φ) + (φ - conjActionGL A φ) = (2 : F) • φ := by
      rw [two_smul]
      abel
    rw [h3, smul_smul, inv_mul_cancel₀ h2, one_smul]
  have hAconjA : conjActionGL A (conjActionGL A φ) = φ := by
    have h1 : conjActionGL A (conjActionGL A φ) = conjActionGL (A * A) φ := by
      rw [map_mul]
      rfl
    rw [h1, hAA, conjActionGL_scalar]
    rfl
  have hN₁fixA : conjActionGL A N₁ = N₁ := by
    show conjActionGL A ((2 : F)⁻¹ • (φ + conjActionGL A φ)) =
      (2 : F)⁻¹ • (φ + conjActionGL A φ)
    rw [map_smul, map_add, hAconjA, add_comm]
  have hN₂fixA : conjActionGL A N₂ = -N₂ := by
    show conjActionGL A ((2 : F)⁻¹ • (φ - conjActionGL A φ)) =
      -((2 : F)⁻¹ • (φ - conjActionGL A φ))
    rw [map_smul, map_sub, hAconjA, ← smul_neg, neg_sub]
  have hN₂fixD : conjActionGL D N₂ = -N₂ := hDneg N₂ hN₂U
  have hN₂fixA' : conjActionGL A' N₂ = N₂ := by
    rw [hA'D, map_mul]
    change conjActionGL A (conjActionGL D N₂) = N₂
    rw [hN₂fixD, map_neg, hN₂fixA, neg_neg]
  have hmul_inv : (A : Matrix (Fin n) (Fin n) F) *
      ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    have h : ((A * A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by simp
    rwa [GeneralLinearGroup.coe_mul] at h
  have hN₁fixmat : (A : Matrix (Fin n) (Fin n) F) * N₁ *
      ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = N₁ := by
    rw [← conjActionGL_apply]
    exact hN₁fixA
  have hN₂fixmat : (A' : Matrix (Fin n) (Fin n) F) * N₂ *
      ((A'⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = N₂ := by
    rw [← conjActionGL_apply]
    exact hN₂fixA'
  have hg_eq : g = unipSL hN₁U * unipSL hN₂U := by
    have hg_eq_mat : (g : Matrix (Fin n) (Fin n) F) =
        ((unipSL hN₁U * unipSL hN₂U : SpecialLinearGroup (Fin n) F) :
          Matrix (Fin n) (Fin n) F) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_unipSL, coe_unipSL]
      have hg1 : (g : Matrix (Fin n) (Fin n) F) = 1 + φ := by
        show (g : Matrix (Fin n) (Fin n) F) = 1 + ((g : Matrix (Fin n) (Fin n) F) - 1)
        abel
      rw [hg1, ← hsum]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul, hN₁N₂,
        add_zero]
      abel
    exact Subtype.ext hg_eq_mat
  have hfix₁ : conjAut n F A (proj n F (unipSL hN₁U)) = proj n F (unipSL hN₁U) := by
    rw [conjAut_proj]
    congr 1
    apply Subtype.ext
    show ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F A
      (unipSL hN₁U) : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((unipSL hN₁U : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)
    rw [coe_slConjugation, coe_unipSL]
    have e1 : (A : Matrix (Fin n) (Fin n) F) * (1 + N₁) =
        (A : Matrix (Fin n) (Fin n) F) + (A : Matrix (Fin n) (Fin n) F) * N₁ := by
      rw [Matrix.mul_add, Matrix.mul_one]
    have e2 : ((A : Matrix (Fin n) (Fin n) F) + (A : Matrix (Fin n) (Fin n) F) * N₁) *
        ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        (A : Matrix (Fin n) (Fin n) F) * ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) +
          ((A : Matrix (Fin n) (Fin n) F) * N₁) *
            ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      rw [Matrix.add_mul]
    rw [e1, e2, hmul_inv, hN₁fixmat]
  have hfix₂ : conjAut n F A' (proj n F (unipSL hN₂U)) = proj n F (unipSL hN₂U) := by
    rw [conjAut_proj]
    congr 1
    apply Subtype.ext
    show ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F A'
      (unipSL hN₂U) : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((unipSL hN₂U : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)
    rw [coe_slConjugation, coe_unipSL]
    have hmul_inv' : (A' : Matrix (Fin n) (Fin n) F) *
        ((A'⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
      have h : ((A' * A'⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by simp
      rwa [GeneralLinearGroup.coe_mul] at h
    have e1 : (A' : Matrix (Fin n) (Fin n) F) * (1 + N₂) =
        (A' : Matrix (Fin n) (Fin n) F) + (A' : Matrix (Fin n) (Fin n) F) * N₂ := by
      rw [Matrix.mul_add, Matrix.mul_one]
    have e2 : ((A' : Matrix (Fin n) (Fin n) F) + (A' : Matrix (Fin n) (Fin n) F) * N₂) *
        ((A'⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        (A' : Matrix (Fin n) (Fin n) F) * ((A'⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) +
          ((A' : Matrix (Fin n) (Fin n) F) * N₂) *
            ((A'⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      rw [Matrix.add_mul]
    rw [e1, e2, hmul_inv', hN₂fixmat]
  rw [Subgroup.mem_comap, hg_eq, map_mul]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl hfix₁))
    (Subgroup.subset_closure (Or.inr hfix₂))

theorem planeGen_of_normalized_unipotent {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : ringChar F ≠ 2) {E : Subgroup (MulAut (projectiveSL n F))} (hE : IsElemAbelian 2 E)
    (h4 : Nat.card E = 4) (X : SpecialLinearGroup (Fin n) F)
    (hX1 : (X : Matrix (Fin n) (Fin n) F) ≠ 1)
    (hX3 : ((X : Matrix (Fin n) (Fin n) F) - 1) ^ 3 = 0)
    (hnorm : ∀ e ∈ E, e (proj n F X) ∈ Subgroup.zpowers (proj n F X)) : PlaneGen E := by
  classical
  let ℓ := ringChar F
  have hℓ : ℓ.Prime := CharP.char_is_prime F ℓ
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ2 : ℓ ≠ 2 := hF
  have hℓ3 : 3 ≤ ℓ := by
    have h2 := hℓ.two_le
    omega
  have hn1 : 1 ≤ n := by
    rcases n with _ | n
    · exfalso
      apply hX1
      ext i
      exact i.elim0
    · omega
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have : CharP F ℓ := ringChar.charP F
  have : CharP (Matrix (Fin n) (Fin n) F) ℓ :=
    charP_of_injective_algebraMap (algebraMap F (Matrix (Fin n) (Fin n) F)).injective ℓ
  let N : Matrix (Fin n) (Fin n) F := (X : Matrix (Fin n) (Fin n) F) - 1
  have hN3 : N ^ 3 = 0 := by simpa [N] using hX3
  have hXeq : (X : Matrix (Fin n) (Fin n) F) = 1 + N := by
    simp [N]
  have hNℓ : N ^ ℓ = 0 := by
    obtain ⟨k, hk⟩ : ∃ k, ℓ = 3 + k := ⟨ℓ - 3, by omega⟩
    rw [hk, pow_add, hN3, Matrix.zero_mul]
  have hXmat : (X : Matrix (Fin n) (Fin n) F) ^ ℓ = 1 := by
    rw [hXeq, add_pow_char_of_commute ℓ (Commute.one_left N), hNℓ, add_zero, one_pow]
  have hXg : X ^ ℓ = 1 := by
    apply Subtype.ext
    change (X : Matrix (Fin n) (Fin n) F) ^ ℓ = 1
    exact hXmat
  have hπXpow : (proj n F X) ^ ℓ = 1 := by rw [← map_pow, hXg, map_one]
  have hπX1 : proj n F X ≠ 1 := by
    intro h
    have hker : X ∈ (proj n F).ker := MonoidHom.mem_ker.mpr h
    rw [ker_proj] at hker
    obtain ⟨c, hc, hXc⟩ := mem_scalars.mp hker
    have hNscalar : N = Matrix.scalar (Fin n) ((c : F) - 1) := by
      simp only [N, hXc]
      rw [← map_one (Matrix.scalar (Fin n)), ← map_sub]
    have h3 : (Matrix.scalar (Fin n) ((c : F) - 1)) ^ 3 = 0 := by
      rw [← hNscalar]
      exact hN3
    have h3' : Matrix.scalar (Fin n) (((c : F) - 1) ^ 3) = 0 := by
      rw [map_pow]
      exact h3
    have hentry := congrFun (congrFun h3' ⟨0, hn1⟩) ⟨0, hn1⟩
    simp [Matrix.scalar_apply] at hentry
    have hc1 : (c : F) = 1 := sub_eq_zero.mp hentry
    exact hX1 (by rw [hXc, hc1, map_one])
  have hord : orderOf (proj n F X) = ℓ := orderOf_eq_prime hπXpow hπX1
  let R : Subgroup (projectiveSL n F) := Subgroup.zpowers (proj n F X)
  have hRr : IsPGroup ℓ R := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord, pow_one]
  have hRne : R ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hπX1
  have hER : ∀ e ∈ E, R.map e.toMonoidHom = R := by
    intro e he
    have hmem : e (proj n F X) ∈ R := hnorm e he
    have hle : R.map e.toMonoidHom ≤ R := by
      rw [show R = Subgroup.zpowers (proj n F X) from rfl, MonoidHom.map_zpowers]
      exact Subgroup.zpowers_le.2 hmem
    have hcard : Nat.card (R.map e.toMonoidHom) = Nat.card R :=
      Subgroup.card_map_of_injective e.injective
    exact Subgroup.eq_of_le_of_card_ge hle hcard.ge
  have hgood : ∀ Q : Subgroup (projectiveSL n F), Q ≠ ⊥ →
      CFSG.GroupTheory.IsRadicalPGroup ℓ ⊤ Q →
      CFSG.GroupTheory.HasGoodOppositePRadicals ℓ ⊤ Q := by
    intro Q hQne hQ
    have hrad {Y : Subgroup (projectiveSL n F)} :
        CFSG.GroupTheory.IsRadicalPGroup ℓ ⊤ Y ↔
          pCoreOf ℓ (Subgroup.normalizer (Y : Set _)) = Y := by
      rw [CFSG.GroupTheory.IsRadicalPGroup, top_inf_eq]
    have hker : (proj n F).ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) F) := by
      rw [ker_proj]
      exact (scalars_eq_center n F).le
    obtain ⟨V, hVrad, hVc, hVb, hQV, hall⟩ :=
      CFSG.StandardType.GGOppRad.intrinsic_opposition_of_sl_central_quotient
        (proj n F) (proj_surjective n F) hker Q hQne (hrad.mp hQ)
    refine ⟨V, ⟨hrad.mpr hVrad, hVc, ?_⟩, hQV, fun W hW => ?_⟩
    · simpa [top_inf_eq] using hVb
    · exact hall W (hrad.mp hW.1) hW.2.1 (by simpa [top_inf_eq] using hW.2.2)
  exact CFSG.LieType.SeitzGeneration.planeGen_of_normalized_rSubgroup_of_hasGoodOppositePRadicals
    hℓ2 hgood E hE h4 R hRne hRr hER

theorem closure_fixed_conjAut_eq_top {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : ringChar F ≠ 2) (A A' : GL (Fin n) F) {μ : F}
    (hA2 : (A : Matrix (Fin n) (Fin n) F) * A = μ • 1)
    (hA'2 : (A' : Matrix (Fin n) (Fin n) F) * A' = μ • 1)
    (hcomm : (A : Matrix (Fin n) (Fin n) F) * A' = A' * A)
    (hne : ∀ c : F, (A' : Matrix (Fin n) (Fin n) F) ≠ c • (A : Matrix (Fin n) (Fin n) F)) :
    Subgroup.closure {x : projectiveSL n F | conjAut n F A x = x ∨ conjAut n F A' x = x} =
      ⊤ := by
  classical
  by_cases hn0 : n = 0
  ·
    subst hn0
    have : Subsingleton (SpecialLinearGroup (Fin 0) F) :=
      ⟨fun a b => Subtype.ext (Matrix.ext fun i _ => i.elim0)⟩
    rw [eq_top_iff]
    intro x _
    obtain ⟨g, rfl⟩ := proj_surjective 0 F x
    rw [Subsingleton.elim g 1, map_one]
    exact Subgroup.one_mem _
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn0⟩⟩
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hμ : μ ≠ 0 := by
    intro h0
    have hmul : ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        (A : Matrix (Fin n) (Fin n) F) = 1 := by simp
    have hA0 : (A : Matrix (Fin n) (Fin n) F) = 0 := by
      calc (A : Matrix (Fin n) (Fin n) F)
          = 1 * (A : Matrix (Fin n) (Fin n) F) := (Matrix.one_mul _).symm
        _ = (((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
              (A : Matrix (Fin n) (Fin n) F)) * (A : Matrix (Fin n) (Fin n) F) := by rw [hmul]
        _ = ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
              ((A : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F)) :=
            Matrix.mul_assoc _ _ _
        _ = ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (μ • 1) := by rw [hA2]
        _ = 0 := by rw [h0, zero_smul, Matrix.mul_zero]
    exact (Units.isUnit A).ne_zero hA0
  let u : Fˣ := Units.mk0 μ hμ
  have hAA : A * A = GeneralLinearGroup.scalar (Fin n) u := by
    apply Units.ext
    rw [GeneralLinearGroup.coe_mul, hA2, GeneralLinearGroup.coe_scalar,
      matrix_scalar_eq_smul_one, Units.val_mk0]
  have hA'A' : A' * A' = GeneralLinearGroup.scalar (Fin n) u := by
    apply Units.ext
    rw [GeneralLinearGroup.coe_mul, hA'2, GeneralLinearGroup.coe_scalar,
      matrix_scalar_eq_smul_one, Units.val_mk0]
  have hcommGL : A * A' = A' * A := by
    apply Units.ext
    rw [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_mul, hcomm]
  let D : GL (Fin n) F := A⁻¹ * A'
  have hAinvmat : ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      μ⁻¹ • (A : Matrix (Fin n) (Fin n) F) := by
    rw [GeneralLinearGroup.coe_inv]
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.mul_smul, hA2, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  have hDcoe : (D : Matrix (Fin n) (Fin n) F) = μ⁻¹ •
      ((A : Matrix (Fin n) (Fin n) F) * (A' : Matrix (Fin n) (Fin n) F)) := by
    rw [show D = A⁻¹ * A' from rfl, GeneralLinearGroup.coe_mul, hAinvmat, Matrix.smul_mul]
  have hcommAinv : A' * A⁻¹ = A⁻¹ * A' := by
    calc A' * A⁻¹ = A⁻¹ * (A * A') * A⁻¹ := by group
      _ = A⁻¹ * (A' * A) * A⁻¹ := by rw [hcommGL]
      _ = A⁻¹ * A' := by group
  have hD2 : D * D = 1 := by
    rw [show D = A⁻¹ * A' from rfl]
    calc (A⁻¹ * A') * (A⁻¹ * A') = A⁻¹ * (A' * A⁻¹) * A' := by group
      _ = A⁻¹ * (A⁻¹ * A') * A' := by rw [hcommAinv]
      _ = (A⁻¹ * A⁻¹) * (A' * A') := by group
      _ = (A * A)⁻¹ * (A' * A') := by rw [← _root_.mul_inv_rev]
      _ = (A * A)⁻¹ * (A * A) := by rw [hA'A', ← hAA]
      _ = 1 := inv_mul_cancel _
  have hDA : D * A = A * D := by
    rw [show D = A⁻¹ * A' from rfl]
    calc A⁻¹ * A' * A = A⁻¹ * (A' * A) := by group
      _ = A⁻¹ * (A * A') := by rw [← hcommGL]
      _ = A' := by group
      _ = A * A⁻¹ * A' := by group
      _ = A * (A⁻¹ * A') := by group
  have hA'D : A' = A * D := by
    rw [show D = A⁻¹ * A' from rfl]
    group
  have hDm2 : (D : Matrix (Fin n) (Fin n) F) * (D : Matrix (Fin n) (Fin n) F) = 1 := by
    have h := congrArg (fun x : GL (Fin n) F => (x : Matrix (Fin n) (Fin n) F)) hD2
    simpa only [GeneralLinearGroup.coe_mul, Units.val_one] using h
  have hDmA : (D : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F) =
      (A : Matrix (Fin n) (Fin n) F) * (D : Matrix (Fin n) (Fin n) F) := by
    have h := congrArg (fun x : GL (Fin n) F => (x : Matrix (Fin n) (Fin n) F)) hDA
    simpa only [GeneralLinearGroup.coe_mul] using h
  have hDAi : (A⁻¹ : GL (Fin n) F) * D = D * A⁻¹ := by
    rw [show D = A⁻¹ * A' from rfl, mul_assoc, hcommAinv]
  have hDAim : ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (D : Matrix (Fin n) (Fin n) F) =
      (D : Matrix (Fin n) (Fin n) F) * ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    have h := congrArg (fun x : GL (Fin n) F => (x : Matrix (Fin n) (Fin n) F)) hDAi
    simpa only [GeneralLinearGroup.coe_mul] using h
  let W : Submodule F (Fin n → F) :=
    LinearMap.ker (Matrix.mulVecLin ((D : Matrix (Fin n) (Fin n) F) - 1))
  let W' : Submodule F (Fin n → F) :=
    LinearMap.ker (Matrix.mulVecLin ((D : Matrix (Fin n) (Fin n) F) + 1))
  have hDW : ∀ w ∈ W, (D : Matrix (Fin n) (Fin n) F) *ᵥ w = w := by
    intro w hw
    have h : Matrix.mulVecLin ((D : Matrix (Fin n) (Fin n) F) - 1) w = 0 :=
      LinearMap.mem_ker.1 hw
    rw [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
    exact h
  have hDW' : ∀ w ∈ W', (D : Matrix (Fin n) (Fin n) F) *ᵥ w = -w := by
    intro w hw
    have h : Matrix.mulVecLin ((D : Matrix (Fin n) (Fin n) F) + 1) w = 0 :=
      LinearMap.mem_ker.1 hw
    rw [Matrix.mulVecLin_apply, Matrix.add_mulVec, Matrix.one_mulVec,
      add_eq_zero_iff_eq_neg] at h
    exact h
  have hDisj : Disjoint W W' := by
    rw [disjoint_iff, eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf] at hv
    have hDv : (D : Matrix (Fin n) (Fin n) F) *ᵥ v = v := hDW v hv.1
    have hDv' : (D : Matrix (Fin n) (Fin n) F) *ᵥ v = -v := hDW' v hv.2
    rw [hDv] at hDv'
    have h4 : v + v = 0 := eq_neg_iff_add_eq_zero.mp hDv'
    have h5 : (2 : F) • v = 0 := by rw [two_smul]; exact h4
    exact (smul_eq_zero.1 h5).resolve_left h2
  have hva : ∀ v : Fin n → F, v + (D : Matrix (Fin n) (Fin n) F) *ᵥ v ∈ W := by
    intro v
    rw [show W = LinearMap.ker (Matrix.mulVecLin ((D : Matrix (Fin n) (Fin n) F) - 1))
      from rfl, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_mulVec, hDm2, Matrix.one_mulVec]
    abel
  have hvb : ∀ v : Fin n → F, v - (D : Matrix (Fin n) (Fin n) F) *ᵥ v ∈ W' := by
    intro v
    rw [show W' = LinearMap.ker (Matrix.mulVecLin ((D : Matrix (Fin n) (Fin n) F) + 1))
      from rfl, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.add_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hDm2, Matrix.one_mulVec]
    abel
  have hSup : W ⊔ W' = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : (2 : F)⁻¹ • (v + (D : Matrix (Fin n) (Fin n) F) *ᵥ v) +
        (2 : F)⁻¹ • (v - (D : Matrix (Fin n) (Fin n) F) *ᵥ v) = v := by
      have h : (2 : F)⁻¹ • (v + (D : Matrix (Fin n) (Fin n) F) *ᵥ v) +
          (2 : F)⁻¹ • (v - (D : Matrix (Fin n) (Fin n) F) *ᵥ v) =
          (2 : F)⁻¹ • ((v + (D : Matrix (Fin n) (Fin n) F) *ᵥ v) +
            (v - (D : Matrix (Fin n) (Fin n) F) *ᵥ v)) := (smul_add _ _ _).symm
      rw [h]
      have h3 : (v + (D : Matrix (Fin n) (Fin n) F) *ᵥ v) +
          (v - (D : Matrix (Fin n) (Fin n) F) *ᵥ v) = (2 : F) • v := by
        rw [two_smul]
        abel
      rw [h3, smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [← hv]
    exact Submodule.add_mem (W ⊔ W')
      (Submodule.smul_mem _ _ (Submodule.mem_sup_left (hva v)))
      (Submodule.smul_mem _ _ (Submodule.mem_sup_right (hvb v)))
  have hcompl : IsCompl W W' := ⟨hDisj, codisjoint_iff.mpr hSup⟩
  have hWne : W ≠ ⊥ := by
    intro hbot
    have hmv : ∀ v : Fin n → F, (D : Matrix (Fin n) (Fin n) F) *ᵥ v = -v := by
      intro v
      have hmem : ((D : Matrix (Fin n) (Fin n) F) + 1) *ᵥ v ∈ W := by
        rw [show W = LinearMap.ker (Matrix.mulVecLin ((D : Matrix (Fin n) (Fin n) F) - 1))
          from rfl, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
          Matrix.one_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_add,
          Matrix.mulVec_mulVec, hDm2, Matrix.one_mulVec]
        abel
      rw [hbot, Submodule.mem_bot, Matrix.add_mulVec, Matrix.one_mulVec,
        add_eq_zero_iff_eq_neg] at hmem
      exact hmem
    have hD1 : (D : Matrix (Fin n) (Fin n) F) = -1 := by
      apply Matrix.ext_iff_mulVec.2
      intro v
      rw [Matrix.neg_mulVec, Matrix.one_mulVec]
      exact hmv v
    refine hne (-1) ?_
    calc (A' : Matrix (Fin n) (Fin n) F) = (A : Matrix (Fin n) (Fin n) F) *
          (D : Matrix (Fin n) (Fin n) F) := by rw [hA'D, GeneralLinearGroup.coe_mul]
      _ = (A : Matrix (Fin n) (Fin n) F) * (-1 : Matrix (Fin n) (Fin n) F) := by rw [hD1]
      _ = -(A : Matrix (Fin n) (Fin n) F) := by rw [Matrix.mul_neg, Matrix.mul_one]
      _ = (-1 : F) • (A : Matrix (Fin n) (Fin n) F) := by rw [neg_one_smul]
  have hW'ne : W' ≠ ⊥ := by
    intro hbot
    have hmv : ∀ v : Fin n → F, (D : Matrix (Fin n) (Fin n) F) *ᵥ v = v := by
      intro v
      have hmem : ((D : Matrix (Fin n) (Fin n) F) - 1) *ᵥ v ∈ W' := by
        rw [show W' = LinearMap.ker (Matrix.mulVecLin ((D : Matrix (Fin n) (Fin n) F) + 1))
          from rfl, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.add_mulVec,
          Matrix.one_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub,
          Matrix.mulVec_mulVec, hDm2, Matrix.one_mulVec]
        abel
      rw [hbot, Submodule.mem_bot, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hmem
      exact hmem
    have hD1 : (D : Matrix (Fin n) (Fin n) F) = 1 := by
      apply Matrix.ext_iff_mulVec.2
      intro v
      rw [Matrix.one_mulVec]
      exact hmv v
    refine hne 1 ?_
    calc (A' : Matrix (Fin n) (Fin n) F) = (A : Matrix (Fin n) (Fin n) F) *
          (D : Matrix (Fin n) (Fin n) F) := by rw [hA'D, GeneralLinearGroup.coe_mul]
      _ = (A : Matrix (Fin n) (Fin n) F) * 1 := by rw [hD1]
      _ = (1 : F) • (A : Matrix (Fin n) (Fin n) F) := by rw [Matrix.mul_one, one_smul]
  have hWA : ∀ w ∈ W, (A : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W := by
    intro w hw
    rw [show W = LinearMap.ker (Matrix.mulVecLin ((D : Matrix (Fin n) (Fin n) F) - 1))
      from rfl, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
      Matrix.one_mulVec, sub_eq_zero]
    rw [Matrix.mulVec_mulVec, hDmA, ← Matrix.mulVec_mulVec, hDW w hw]
  have hWAi : ∀ w ∈ W, ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W := by
    intro w hw
    rw [show W = LinearMap.ker (Matrix.mulVecLin ((D : Matrix (Fin n) (Fin n) F) - 1))
      from rfl, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
      Matrix.one_mulVec, sub_eq_zero]
    rw [Matrix.mulVec_mulVec, ← hDAim, ← Matrix.mulVec_mulVec, hDW w hw]
  have hWA' : ∀ w ∈ W', (A : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W' := by
    intro w hw
    rw [show W' = LinearMap.ker (Matrix.mulVecLin ((D : Matrix (Fin n) (Fin n) F) + 1))
      from rfl, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.add_mulVec,
      Matrix.one_mulVec, add_eq_zero_iff_eq_neg]
    rw [Matrix.mulVec_mulVec, hDmA, ← Matrix.mulVec_mulVec, hDW' w hw, Matrix.mulVec_neg]
  have hWAi' : ∀ w ∈ W', ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W' := by
    intro w hw
    rw [show W' = LinearMap.ker (Matrix.mulVecLin ((D : Matrix (Fin n) (Fin n) F) + 1))
      from rfl, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.add_mulVec,
      Matrix.one_mulVec, add_eq_zero_iff_eq_neg]
    rw [Matrix.mulVec_mulVec, ← hDAim, ← Matrix.mulVec_mulVec, hDW' w hw, Matrix.mulVec_neg]
  have hDnegW : ∀ ψ ∈ thetaSpace W, conjActionGL D ψ = -ψ := fun ψ hψ =>
    conjActionGL_eq_neg_of_mem_thetaSpace hD2 hSup hDW hDW' (Or.inl hψ)
  have hDnegW' : ∀ ψ ∈ thetaSpace W', conjActionGL D ψ = -ψ := fun ψ hψ =>
    conjActionGL_eq_neg_of_mem_thetaSpace hD2 hSup hDW hDW' (Or.inr hψ)
  have hKtop : (Subgroup.closure {x : projectiveSL n F |
      conjAut n F A x = x ∨ conjAut n F A' x = x}).comap (proj n F) = ⊤ :=
    eq_top_of_unip_isCompl hcompl hWne hW'ne
      (fun g hg => mem_comap_closure_of_theta h2 hAA hA'D hWA hWAi hDnegW g hg)
      (fun g hg => mem_comap_closure_of_theta h2 hAA hA'D hWA' hWAi' hDnegW' g hg)
  have h := congrArg (Subgroup.map (proj n F)) hKtop
  rw [Subgroup.map_comap_eq_self_of_surjective (proj_surjective n F),
    Subgroup.map_top_of_surjective (proj n F) (proj_surjective n F)] at h
  exact h

private lemma det_one_add_eq_one_of_cube_zero {K : Type*} [Field K] [Finite K] {n : ℕ}
    [Nonempty (Fin n)] (hK : ringChar K ≠ 2) {N : Matrix (Fin n) (Fin n) K} (hN : N ^ 3 = 0) :
    (1 + N).det = 1 := by
  classical
  let ℓ := ringChar K
  have hℓ : ℓ.Prime := CharP.char_is_prime K ℓ
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := ringChar.charP K
  have : CharP (Matrix (Fin n) (Fin n) K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (Matrix (Fin n) (Fin n) K)).injective ℓ
  have hℓ2 : ℓ ≠ 2 := hK
  have hℓ3 : 3 ≤ ℓ := by
    have h2 := hℓ.two_le
    omega
  have hNℓ : N ^ ℓ = 0 := by
    obtain ⟨k, hk⟩ : ∃ k, ℓ = 3 + k := ⟨ℓ - 3, by omega⟩
    rw [hk, pow_add, hN, Matrix.zero_mul]
  have hXℓ : (1 + N) ^ ℓ = 1 := by
    rw [add_pow_char_of_commute ℓ (Commute.one_left N), hNℓ, add_zero, one_pow]
  have hdetpow : (1 + N).det ^ ℓ = 1 := by
    rw [← Matrix.det_pow, hXℓ, Matrix.det_one]
  have hzero : ((1 + N).det - 1) ^ ℓ = 0 := by
    rw [sub_pow_char_of_commute ℓ (Commute.one_right _), hdetpow, one_pow, sub_self]
  have hsub : (1 + N).det - 1 = 0 := (pow_eq_zero_iff (by omega : ℓ ≠ 0)).mp hzero
  exact sub_eq_zero.mp hsub

private lemma inv_transpose_conj_eq_of_isometry {F : Type} [Field F] {n : ℕ}
    {Φ : Matrix (Fin n) (Fin n) F} (hΦ : Φ.det ≠ 0)
    {g : Matrix (Fin n) (Fin n) F} (hg : g.det ≠ 0)
    (h : gᵀ * Φ * g = Φ) : Φ⁻¹ * (g⁻¹)ᵀ * Φ = g := by
  have hΦu : IsUnit Φ.det := isUnit_iff_ne_zero.mpr hΦ
  have hgu : IsUnit g.det := isUnit_iff_ne_zero.mpr hg
  have hΦ1 : Φ⁻¹ * Φ = 1 := Matrix.nonsing_inv_mul Φ hΦu
  have hg1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hgu
  have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) F => M⁻¹) h
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev] at h2
  have h3 : Φ⁻¹ * (gᵀ)⁻¹ = g * Φ⁻¹ := by
    calc Φ⁻¹ * (gᵀ)⁻¹ = 1 * (Φ⁻¹ * (gᵀ)⁻¹) := (Matrix.one_mul _).symm
      _ = (g * g⁻¹) * (Φ⁻¹ * (gᵀ)⁻¹) := by rw [hg1]
      _ = g * (g⁻¹ * (Φ⁻¹ * (gᵀ)⁻¹)) := Matrix.mul_assoc _ _ _
      _ = g * Φ⁻¹ := by rw [h2]
  calc Φ⁻¹ * (g⁻¹)ᵀ * Φ = Φ⁻¹ * (gᵀ)⁻¹ * Φ := by rw [Matrix.transpose_nonsing_inv]
    _ = (Φ⁻¹ * (gᵀ)⁻¹) * Φ := rfl
    _ = (g * Φ⁻¹) * Φ := by rw [h3]
    _ = g * (Φ⁻¹ * Φ) := Matrix.mul_assoc _ _ _
    _ = g := by rw [hΦ1, Matrix.mul_one]

theorem planeGen_of_graph_orth_conj {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 3 ≤ n)
    (hF : ringChar F ≠ 2) {E : Subgroup (MulAut (projectiveSL n F))} (hE : IsElemAbelian 2 E)
    (h4 : Nat.card E = 4) (A Φ : GL (Fin n) F) {μ : F}
    (hA2 : (A : Matrix (Fin n) (Fin n) F) * A = μ • 1)
    (hgen : E = Subgroup.zpowers (conjAut n F A) ⊔
      Subgroup.zpowers (conjAut n F Φ⁻¹ * dualAut n F))
    (g : Matrix (Fin n) (Fin n) F) (hgΦ : gᵀ * (Φ : Matrix (Fin n) (Fin n) F) * g = Φ)
    (hg1 : g.det = 1)
    (hgc : g * A * g⁻¹ * A = (A : Matrix (Fin n) (Fin n) F) * (g * A * g⁻¹))
    (hgne : ∀ c : F, g * A * g⁻¹ ≠ c • (A : Matrix (Fin n) (Fin n) F)) : PlaneGen E := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hu1 : conjAut n F A ≠ 1 := by
    intro h
    obtain ⟨c, hc⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff hn A).mp h
    have hAmat : (A : Matrix (Fin n) (Fin n) F) = (c : F) • 1 := by
      rw [← hc, GeneralLinearGroup.coe_scalar, matrix_scalar_eq_smul_one]
    have hgu : IsUnit g.det := by rw [hg1]; exact isUnit_one
    refine hgne 1 ?_
    rw [hAmat, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_nonsing_inv g hgu, one_smul]
  have ht1 : conjAut n F Φ⁻¹ * dualAut n F ≠ 1 := by
    intro h
    have huE : conjAut n F A ∈ E := by
      rw [hgen]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    have hu2 : conjAut n F A ^ 2 = 1 := hE.2 _ huE
    have hE2 : E = Subgroup.zpowers (conjAut n F A) := by
      rw [hgen, h, Subgroup.zpowers_one_eq_bot, sup_bot_eq]
    have hord : orderOf (conjAut n F A) ∣ 2 := orderOf_dvd_of_pow_eq_one hu2
    have hcard : Nat.card E ≤ 2 := by
      rw [hE2, Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) hord
    rw [h4] at hcard
    omega
  have hgu : IsUnit g.det := by rw [hg1]; exact isUnit_one
  have hgdet0 : g.det ≠ 0 := by rw [hg1]; exact one_ne_zero
  have hΦdet0 : (Φ : Matrix (Fin n) (Fin n) F).det ≠ 0 := by
    have h := (Matrix.GeneralLinearGroup.det Φ).ne_zero
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at h
  have hgadj : g.adjugate = g⁻¹ := by
    refine (Matrix.inv_eq_right_inv ?_).symm
    rw [Matrix.mul_adjugate, hg1, one_smul]
  let gs : SpecialLinearGroup (Fin n) F := ⟨g, hg1⟩
  have hgs : (gs : Matrix (Fin n) (Fin n) F) = g := rfl
  have ht_fix : (conjAut n F Φ⁻¹ * dualAut n F) (proj n F gs) = proj n F gs := by
    rw [MulAut.mul_apply, dualAut_proj, conjAut_proj]
    congr 1
    apply Subtype.ext
    rw [coe_slConjugation, SpecialLinearGroup.coe_transpose,
      Matrix.SpecialLinearGroup.coe_inv, hgadj]
    have hΦinv : (((Φ⁻¹ : GL (Fin n) F)⁻¹ : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) = (Φ : Matrix (Fin n) (Fin n) F) := by
      rw [inv_inv]
    rw [GeneralLinearGroup.coe_inv, hΦinv]
    exact inv_transpose_conj_eq_of_isometry hΦdet0 hgdet0 hgΦ
  have hgs_plane : proj n F gs ∈ planeClosure E := by
    refine mem_planeClosure_of_fixed (e := conjAut n F Φ⁻¹ * dualAut n F) ?_ ht1 ht_fix
    rw [hgen]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hμ : μ ≠ 0 := by
    intro h0
    have hmul : ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        (A : Matrix (Fin n) (Fin n) F) = 1 := by simp
    have hA0 : (A : Matrix (Fin n) (Fin n) F) = 0 := by
      calc (A : Matrix (Fin n) (Fin n) F)
          = 1 * (A : Matrix (Fin n) (Fin n) F) := (Matrix.one_mul _).symm
        _ = (((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
              (A : Matrix (Fin n) (Fin n) F)) * (A : Matrix (Fin n) (Fin n) F) := by rw [hmul]
        _ = ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
              ((A : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F)) :=
            Matrix.mul_assoc _ _ _
        _ = ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (μ • 1) := by rw [hA2]
        _ = 0 := by rw [h0, zero_smul, Matrix.mul_zero]
    exact (Units.isUnit A).ne_zero hA0
  let u : Fˣ := Units.mk0 μ hμ
  have hAA : A * A = GeneralLinearGroup.scalar (Fin n) u := by
    apply Units.ext
    rw [GeneralLinearGroup.coe_mul, hA2, GeneralLinearGroup.coe_scalar,
      matrix_scalar_eq_smul_one, Units.val_mk0]
  let A' : GL (Fin n) F := SpecialLinearGroup.toGL gs * A * (SpecialLinearGroup.toGL gs)⁻¹
  have hA'mat : (A' : Matrix (Fin n) (Fin n) F) = g * (A : Matrix (Fin n) (Fin n) F) * g⁻¹ := by
    simp only [A', GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_inv,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hgs]
  have hA'2gl : A' * A' = GeneralLinearGroup.scalar (Fin n) u := by
    rw [show A' = SpecialLinearGroup.toGL gs * A * (SpecialLinearGroup.toGL gs)⁻¹ from rfl]
    calc (SpecialLinearGroup.toGL gs * A * (SpecialLinearGroup.toGL gs)⁻¹) *
          (SpecialLinearGroup.toGL gs * A * (SpecialLinearGroup.toGL gs)⁻¹)
        = SpecialLinearGroup.toGL gs * (A * A) * (SpecialLinearGroup.toGL gs)⁻¹ := by group
      _ = SpecialLinearGroup.toGL gs * GeneralLinearGroup.scalar (Fin n) u *
            (SpecialLinearGroup.toGL gs)⁻¹ := by rw [hAA]
      _ = GeneralLinearGroup.scalar (Fin n) u := by
          rw [← GeneralLinearGroup.scalar_commute u (SpecialLinearGroup.toGL gs)]
          group
  have hA'2 : (A' : Matrix (Fin n) (Fin n) F) * A' = μ • 1 := by
    have h := congrArg (fun x : GL (Fin n) F => (x : Matrix (Fin n) (Fin n) F)) hA'2gl
    rw [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_scalar,
      matrix_scalar_eq_smul_one] at h
    rwa [show ((u : F)) = μ from rfl] at h
  have hcomm : (A : Matrix (Fin n) (Fin n) F) * A' = A' * (A : Matrix (Fin n) (Fin n) F) := by
    rw [hA'mat]
    exact hgc.symm
  have hne : ∀ c : F, (A' : Matrix (Fin n) (Fin n) F) ≠
      c • (A : Matrix (Fin n) (Fin n) F) := by
    intro c
    rw [hA'mat]
    exact hgne c
  have hTCG := closure_fixed_conjAut_eq_top hF A A' hA2 hA'2 hcomm hne
  have hconj : conjAut n F A' = MulAut.conj (proj n F gs) * conjAut n F A *
      (MulAut.conj (proj n F gs))⁻¹ := by
    rw [show A' = SpecialLinearGroup.toGL gs * A * (SpecialLinearGroup.toGL gs)⁻¹ from rfl]
    rw [map_mul, map_mul, map_inv, CFSG.LieType.SeitzGeneration.conjAut_toGL]
  have hfixA' : ∀ x : projectiveSL n F, conjAut n F A' x = x →
      ∃ y : projectiveSL n F, conjAut n F A y = y ∧
        x = proj n F gs * y * (proj n F gs)⁻¹ := by
    intro x hx
    have hx' : (proj n F gs) * (conjAut n F A ((proj n F gs)⁻¹ * x * proj n F gs)) *
        (proj n F gs)⁻¹ = x := by
      rw [hconj] at hx
      simpa only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply] using hx
    have hy : conjAut n F A ((proj n F gs)⁻¹ * x * proj n F gs) =
        (proj n F gs)⁻¹ * x * proj n F gs := by
      have h1 := congrArg (fun z => (proj n F gs)⁻¹ * z * proj n F gs) hx'
      simpa [mul_assoc] using h1
    rw [hy] at hx'
    exact ⟨(proj n F gs)⁻¹ * x * proj n F gs, hy, hx'.symm⟩
  have hle : Subgroup.closure {x : projectiveSL n F |
      conjAut n F A x = x ∨ conjAut n F A' x = x} ≤ planeClosure E := by
    refine (Subgroup.closure_le (planeClosure E)).2 ?_
    rintro x (hx | hx)
    · refine mem_planeClosure_of_fixed (e := conjAut n F A) ?_ hu1 hx
      rw [hgen]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · obtain ⟨y, hy, rfl⟩ := hfixA' x hx
      have huE : conjAut n F A ∈ E := by
        rw [hgen]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      have hy' : y ∈ planeClosure E := mem_planeClosure_of_fixed huE hu1 hy
      exact (planeClosure E).mul_mem ((planeClosure E).mul_mem hgs_plane hy')
        ((planeClosure E).inv_mem hgs_plane)
  unfold PlaneGen
  rw [eq_top_iff, ← hTCG]
  exact hle

theorem planeGen_of_graph_orth_inverted {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 3 ≤ n)
    (hF : ringChar F ≠ 2) {E : Subgroup (MulAut (projectiveSL n F))} (hE : IsElemAbelian 2 E)
    (h4 : Nat.card E = 4) (A Φ : GL (Fin n) F)
    (hgen : E = Subgroup.zpowers (conjAut n F A) ⊔
      Subgroup.zpowers (conjAut n F Φ⁻¹ * dualAut n F))
    (Y : Matrix (Fin n) (Fin n) F) (hY1 : Y ≠ 1) (hY3 : (Y - 1) ^ 3 = 0)
    (hYΦ : Yᵀ * (Φ : Matrix (Fin n) (Fin n) F) * Y = Φ)
    (hAY : (A : Matrix (Fin n) (Fin n) F) * Y * (A : Matrix (Fin n) (Fin n) F)⁻¹ = Y⁻¹) :
    PlaneGen E := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hYdet : Y.det = 1 := by
    have h := det_one_add_eq_one_of_cube_zero (K := F) (n := n) hF hY3
    rwa [show (1 : Matrix (Fin n) (Fin n) F) + (Y - 1) = Y from by abel] at h
  have hYdet0 : Y.det ≠ 0 := by rw [hYdet]; exact one_ne_zero
  have hΦdet0 : (Φ : Matrix (Fin n) (Fin n) F).det ≠ 0 := by
    have h := (Matrix.GeneralLinearGroup.det Φ).ne_zero
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at h
  have hYadj : Y.adjugate = Y⁻¹ := by
    refine (Matrix.inv_eq_right_inv ?_).symm
    rw [Matrix.mul_adjugate, hYdet, one_smul]
  let Ys : SpecialLinearGroup (Fin n) F := ⟨Y, hYdet⟩
  have hYs : (Ys : Matrix (Fin n) (Fin n) F) = Y := rfl
  have hinv : (conjAut n F A).toMonoidHom (proj n F Ys) = (proj n F Ys)⁻¹ := by
    change conjAut n F A (proj n F Ys) = (proj n F Ys)⁻¹
    rw [conjAut_proj, ← map_inv]
    congr 1
    apply Subtype.ext
    rw [coe_slConjugation, GeneralLinearGroup.coe_inv, hAY,
      Matrix.SpecialLinearGroup.coe_inv, hYadj]
  have hfix : (conjAut n F Φ⁻¹ * dualAut n F).toMonoidHom (proj n F Ys) = proj n F Ys := by
    change (conjAut n F Φ⁻¹ * dualAut n F) (proj n F Ys) = proj n F Ys
    rw [MulAut.mul_apply, dualAut_proj, conjAut_proj]
    congr 1
    apply Subtype.ext
    rw [coe_slConjugation, SpecialLinearGroup.coe_transpose,
      Matrix.SpecialLinearGroup.coe_inv, hYadj]
    have hΦinv : (((Φ⁻¹ : GL (Fin n) F)⁻¹ : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) = (Φ : Matrix (Fin n) (Fin n) F) := by
      rw [inv_inv]
    rw [GeneralLinearGroup.coe_inv, hΦinv]
    exact inv_transpose_conj_eq_of_isometry hΦdet0 hYdet0 hYΦ
  let R : Subgroup (projectiveSL n F) := Subgroup.zpowers (proj n F Ys)
  let H : Subgroup (MulAut (projectiveSL n F)) :=
    { carrier := {e | R.map e.toMonoidHom = R}
      one_mem' := by
        ext x
        simp [Subgroup.mem_map]
      mul_mem' := fun {e f} he hf => by
        show R.map (e * f).toMonoidHom = R
        have h : (e * f).toMonoidHom = e.toMonoidHom.comp f.toMonoidHom := rfl
        rw [h, ← Subgroup.map_map, hf, he]
      inv_mem' := fun {e} he => by
        show R.map (e⁻¹).toMonoidHom = R
        refine le_antisymm ?_ ?_
        · intro y hy
          obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hy
          have hz' : z ∈ R.map e.toMonoidHom := by rwa [← he] at hz
          obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.1 hz'
          rw [← hzy, ← hwz]
          simpa using hw
        · intro x hx
          refine Subgroup.mem_map.2 ⟨e x, ?_, ?_⟩
          · have hx' : e x ∈ R.map e.toMonoidHom := Subgroup.mem_map.2 ⟨x, hx, rfl⟩
            rwa [he] at hx'
          · simp }
  have hu : conjAut n F A ∈ H := by
    show R.map (conjAut n F A).toMonoidHom = R
    rw [show R = Subgroup.zpowers (proj n F Ys) from rfl, MonoidHom.map_zpowers, hinv,
      Subgroup.zpowers_inv]
  have ht : conjAut n F Φ⁻¹ * dualAut n F ∈ H := by
    show R.map (conjAut n F Φ⁻¹ * dualAut n F).toMonoidHom = R
    rw [show R = Subgroup.zpowers (proj n F Ys) from rfl, MonoidHom.map_zpowers, hfix]
  have hEsub : E ≤ H := by
    rw [hgen]
    exact sup_le (Subgroup.zpowers_le.2 hu) (Subgroup.zpowers_le.2 ht)
  refine planeGen_of_normalized_unipotent hF hE h4 Ys hY1 hY3 ?_
  intro e he
  have hmap : R.map e.toMonoidHom = R := hEsub he
  have hmem : e (proj n F Ys) ∈ R.map e.toMonoidHom :=
    Subgroup.mem_map.2 ⟨proj n F Ys, Subgroup.mem_zpowers _, rfl⟩
  rwa [hmap] at hmem

end CFSG.LocalAnalysis.WeakClosure81.PSLOuter
