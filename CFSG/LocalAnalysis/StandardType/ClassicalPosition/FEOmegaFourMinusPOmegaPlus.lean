module

public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.Models.PGLSimple
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
open scoped commutatorElement

private lemma feomeg_finite (F : Type) {f : ℕ} (hc : Nat.card F = 2 ^ f) :
    Finite F := by
  rw [← not_infinite_iff_finite]
  intro hinf
  have h0 : Nat.card F = 0 := Nat.card_eq_zero.mpr (Or.inr hinf)
  rw [hc] at h0
  exact (pow_ne_zero f (by norm_num : (2 : ℕ) ≠ 0)) h0

private lemma feomeg_one_le (F : Type) [Field F] {f : ℕ} (hc : Nat.card F = 2 ^ f) :
    1 ≤ f := by
  haveI : Finite F := feomeg_finite F hc
  have h2 : 2 ≤ Nat.card F := by
    have := Finite.one_lt_card (α := F)
    omega
  rw [hc] at h2
  by_contra h
  have hf : f = 0 := by omega
  subst hf
  norm_num at h2

private lemma feomeg_charP (F : Type) [Field F] [Finite F] {f : ℕ} (hc : Nat.card F = 2 ^ f) :
    CharP F 2 := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨n, hpprime, hcard⟩ := FiniteField.card F (ringChar F)
  have hcard' : (ringChar F) ^ (n : ℕ) = 2 ^ f := by
    rw [← hcard, ← Nat.card_eq_fintype_card, hc]
  have hdvd : ringChar F ∣ 2 := by
    have hpow : ringChar F ∣ (ringChar F) ^ (n : ℕ) := dvd_pow_self _ n.pos.ne'
    rw [hcard'] at hpow
    exact Nat.Prime.dvd_of_dvd_pow hpprime hpow
  have hrceq : ringChar F = 2 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd with h | h
    · exact absurd h hpprime.ne_one
    · exact h
  have hchar := ringChar.charP F
  rw [hrceq] at hchar
  exact hchar

private lemma feomeg_admissible (f : ℕ) (hf : 1 ≤ f) :
    CFSG.Open.StatedLieAdmissible .PSL 2 2 (2 * f) := by
  have hpow2 : 2 ^ (2 * f) ≠ 2 := by
    intro h
    have hle : 2 ^ 2 ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hpow3 : 2 ^ (2 * f) ≠ 3 := by
    intro h
    have hle : 2 ^ 2 ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact ⟨Nat.prime_two, by omega, by norm_num, fun h => hpow2 (congrArg Prod.snd h),
    fun h => hpow3 (congrArg Prod.snd h)⟩

private lemma feomeg_quotientCenter
    {U : Type} [Group U] {X : Type} [Group X] (ψ : U →* X)
    (hψ : ψ.ker ≤ Subgroup.center U)
    {J' : Subgroup U} (hperf : _root_.commutator ↥J' = ⊤) :
    Nonempty (↥J' ⧸ Subgroup.center ↥J' ≃* ↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ)) := by
  classical
  let fmap : ↥J' →* ↥(J'.map ψ) :=
    (ψ.comp J'.subtype).codRestrict (J'.map ψ) (fun x => Subgroup.mem_map_of_mem ψ x.2)
  have hf : Function.Surjective fmap := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hkerf : fmap.ker ≤ Subgroup.center ↥J' := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx1 : (x : U) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      have h := congrArg (fun z : ↥(J'.map ψ) => (z : X)) hx
      simpa [fmap] using h
    have hxc := hψ hx1
    apply Subtype.ext
    simpa using (Subgroup.mem_center_iff.mp hxc (y : U))
  haveI : Group.IsPerfect ↥J' := ⟨hperf⟩
  have hcen : Subgroup.center (↥J' ⧸ fmap.ker) =
      (Subgroup.center ↥J').map (QuotientGroup.mk' fmap.ker) :=
    (CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel
      (QuotientGroup.mk' fmap.ker) (QuotientGroup.mk'_surjective fmap.ker)
      (by rwa [QuotientGroup.ker_mk'])).symm
  let e1 : ↥J' ⧸ fmap.ker ≃* ↥(J'.map ψ) := QuotientGroup.quotientKerEquivOfSurjective fmap hf
  let e2 : ↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ) ≃*
      (↥J' ⧸ fmap.ker) ⧸ Subgroup.center (↥J' ⧸ fmap.ker) :=
    QuotientGroup.congr (Subgroup.center ↥(J'.map ψ)) (Subgroup.center (↥J' ⧸ fmap.ker))
      e1.symm (Subgroup.map_center_eq e1.symm)
  exact ⟨(e2.trans ((QuotientGroup.quotientMulEquivOfEq hcen).trans
    (QuotientGroup.quotientQuotientEquivQuotient _ _ hkerf))).symm⟩

private lemma feomeg_mem_block {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (A : Subalgebra F (Matrix ι ι F)) (x e : Matrix ι ι F) :
    x ∈ (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e) ↔ ∃ a ∈ A, a * e = x := by
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨a, ha, hfa⟩
    exact ⟨a, (Subalgebra.mem_toSubmodule A).mp ha, by rwa [LinearMap.mulRight_apply] at hfa⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, (Subalgebra.mem_toSubmodule A).mpr ha, by rw [LinearMap.mulRight_apply]⟩

private lemma feomeg_blockDegree_pos {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (A : Subalgebra F (Matrix ι ι F)) {e : Matrix ι ι F} (hne : e ≠ 0) :
    1 ≤ blockDegree A e := by
  have hmem : e ∈ (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e) := by
    rw [Submodule.mem_map]
    exact ⟨1, by simpa using A.one_mem, by rw [LinearMap.mulRight_apply, one_mul]⟩
  by_contra h
  have h0 : blockDegree A e = 0 := by omega
  have hbot : (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e) = ⊥ :=
    Submodule.finrank_eq_zero.mp h0
  rw [hbot] at hmem
  exact hne (by simpa using hmem)

private lemma feomeg_gram_isUnit {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F))
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) :
    IsUnit (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).det := by
  have hEqB : Matrix.toLinearMap₂' F (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q))
      = QuadraticMap.polarBilin Q := by
    rw [show LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)
      = LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q) from rfl]
    exact Matrix.toLinearMap₂'_toMatrix' _
  have hJnd : (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).Nondegenerate := by
    refine ⟨Matrix.separatingLeft_def.mpr fun v hv => ?_,
      Matrix.separatingRight_def.mpr fun w hw => ?_⟩
    · apply hnd.1 v
      intro w
      have h := hv w
      rwa [← Matrix.toLinearMap₂'_apply' (M := LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)),
        hEqB] at h
    · apply hnd.2 w
      intro v
      have h := hw v
      rwa [← Matrix.toLinearMap₂'_apply' (M := LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)),
        hEqB] at h
  exact isUnit_iff_ne_zero.mpr (Matrix.nondegenerate_iff_det_ne_zero.mp hJnd)

private lemma feomeg_gram_isometry {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) {s : GL ι F}
    (hs : s ∈ (Spin.spinMatrix Q).range) :
    Matrix.transpose ((s : Matrix ι ι F).map (RingHom.id F)) *
      LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q) * (s : Matrix ι ι F)
      = LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q) := by
  obtain ⟨x, rfl⟩ := hs
  set G := LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q) with hGdef
  have hEqB : Matrix.toBilin' G = QuadraticMap.polarBilin Q := by
    rw [hGdef, show LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)
      = LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q) from rfl]
    exact Matrix.toBilin'_toMatrix' _
  have hcomp := Matrix.toBilin'_comp G (Spin.spinMatrix Q x : Matrix ι ι F)
    (Spin.spinMatrix Q x : Matrix ι ι F)
  have hEq : Matrix.toBilin' (Matrix.transpose (Spin.spinMatrix Q x : Matrix ι ι F) * G *
      (Spin.spinMatrix Q x : Matrix ι ι F)) = Matrix.toBilin' G := by
    rw [← hcomp]
    refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
    rw [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, hEqB,
      QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
    simp only [Spin.spinMatrix_mulVec]
    exact Spin.polar_spinAction Q x v w
  have hmap : ((Spin.spinMatrix Q x : Matrix ι ι F)).map (⇑(RingHom.id F))
      = (Spin.spinMatrix Q x : Matrix ι ι F) := by
    rw [show (⇑(RingHom.id F) : F → F) = id from rfl, Matrix.map_id]
  rw [hmap]
  exact (Matrix.toBilin' (R₁ := F)).injective hEq

private lemma feomeg_block_eq_smul_of_degree_le_one
    {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {A : Subalgebra F (Matrix ι ι F)} {e x : Matrix ι ι F}
    (hx : x ∈ A) (he0 : e ≠ 0) (hdeg : blockDegree A e ≤ 1) :
    ∃ c : F, x * e = c • e := by
  have heP : e ∈ (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e) := by
    rw [feomeg_mem_block]
    exact ⟨1, A.one_mem, by rw [Matrix.one_mul]⟩
  have hxP : x * e ∈ (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e) := by
    rw [feomeg_mem_block]
    exact ⟨x, hx, rfl⟩
  have hP1 : Module.finrank F (↥((Subalgebra.toSubmodule A).map (LinearMap.mulRight F e))) ≤ 1 :=
    hdeg
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hP1
  obtain ⟨c₀, hc₀⟩ := hv ⟨e, heP⟩
  have hc₀ne : c₀ ≠ 0 := by
    intro h0
    have hzero : (⟨e, heP⟩ : ↥((Subalgebra.toSubmodule A).map
        (LinearMap.mulRight F e))) = 0 := by
      rw [← hc₀, h0, zero_smul]
    exact he0 (by simpa using congrArg Subtype.val hzero)
  have hvε : v = c₀⁻¹ • (⟨e, heP⟩ : ↥((Subalgebra.toSubmodule A).map
        (LinearMap.mulRight F e))) := by
    rw [← hc₀, smul_smul, inv_mul_cancel₀ hc₀ne, one_smul]
  obtain ⟨c, hc⟩ := hv ⟨x * e, hxP⟩
  refine ⟨c * c₀⁻¹, ?_⟩
  have h : (c * c₀⁻¹) • (⟨e, heP⟩ : ↥((Subalgebra.toSubmodule A).map
        (LinearMap.mulRight F e))) = ⟨x * e, hxP⟩ := by
    rw [← smul_smul, ← hvε, hc]
  exact (congrArg Subtype.val h).symm

private lemma feomeg_S_trivial_on_block
    (n : ℕ) (F : Type) [Field F]
    (S : Set (GL (Fin n ⊕ Fin n) F))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus n F)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F)))
      (Algebra.adjoin F (Units.val '' S)) ε)
    (hdeg : blockDegree (Algebra.adjoin F (Units.val '' S)) ε < 2) :
    ∀ s ∈ S, ∀ w : Fin n ⊕ Fin n → F, Matrix.mulVec ε w = w →
      Matrix.mulVec (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) w = w := by
  classical
  have hcommP : (Units.val '' S : Set (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)).Pairwise
      Commute := by
    rintro a ⟨s, hs, rfl⟩ b ⟨s', hs', rfl⟩ _
    have h := hS s hs s' hs'
    show (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        (s' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (s' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    rw [← Units.val_mul, ← Units.val_mul, h]
  letI : CommRing (Algebra.adjoin F (Units.val '' S)) :=
    Algebra.adjoinCommRingOfComm F hcommP
  have hG : IsUnit (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F))).det :=
    feomeg_gram_isUnit (Spin.quadPlus n F) (Spin.nondegenerate_polarBilin_quadPlus n F)
  have hSU' : ∀ s ∈ S, Matrix.transpose
      ((s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).map (RingHom.id F)) *
      LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F)) *
      (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F)) :=
    fun s hs => feomeg_gram_isometry (Spin.quadPlus n F) (hSU s hs)
  have hbd : blockDegree (Algebra.adjoin F (Units.val '' S)) ε = 1 :=
    le_antisymm (by omega)
      (feomeg_blockDegree_pos (Algebra.adjoin F (Units.val '' S)) hε.2.2.1)
  intro s hs w hw
  have hsA : (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ∈
      Algebra.adjoin F (Units.val '' S) :=
    Algebra.subset_adjoin ⟨s, hs, rfl⟩
  obtain ⟨c, hsce⟩ := feomeg_block_eq_smul_of_degree_le_one hsA hε.2.2.1 (by omega)
  have hcomm : (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε = ε *
      (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
    have h := mul_comm (⟨(s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F), hsA⟩ :
      Algebra.adjoin F (Units.val '' S)) ⟨ε, hε.1⟩
    simpa using congrArg Subtype.val h
  have h1 : formAdj (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F)))
      ((s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε) = c • ε := by
    rw [hsce, Geo.formAdj_smul, hε.2.2.2.1]
    rfl
  have h3 : formAdj (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F)))
      ((s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε) =
      ε * ((s⁻¹ : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
    rw [Geo.formAdj_mul (RingHom.id F) hG (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ε,
      Geo.formAdj_eq_inv_of_isometry (RingHom.id F) hG s (hSU' s hs), hε.2.2.2.1]
  have h4 : c • ε = ε * ((s⁻¹ : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := h1.symm.trans h3
  have h5 : (c • ε) * (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = ε := by
    rw [h4, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  have h6 : (c • ε) * (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = (c * c) • ε := by
    rw [Matrix.smul_mul, hcomm.symm, hsce, smul_smul]
  have h7 : (c * c) • ε = ε := h6.symm.trans h5
  have hc2 : c ^ 2 = 1 := by
    have h8 : (c * c - 1) • ε = 0 := by
      rw [sub_smul, h7, one_smul, sub_self]
    have h9 : c * c - 1 = 0 := by
      rcases smul_eq_zero.mp h8 with h | h
      · exact h
      · exact absurd h hε.2.2.1
    have h10 : c * c = 1 := sub_eq_zero.mp h9
    rwa [pow_two]
  have hpow : ∀ k : ℕ, (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ k * ε =
      (c ^ k) • ε := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, Matrix.mul_assoc, hsce, Matrix.mul_smul, ih, smul_smul,
          ← pow_succ']
  have hsm : (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ^ orderOf s = 1 := by
    rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  have hcm : c ^ orderOf s = 1 := by
    have h := hpow (orderOf s)
    rw [hsm, Matrix.one_mul] at h
    have h' : (c ^ orderOf s - 1) • ε = 0 := by
      rw [sub_smul, ← h, one_smul, sub_self]
    rcases smul_eq_zero.mp h' with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 hε.2.2.1
  obtain ⟨k, hk⟩ := hodd s hs
  rw [hk, pow_succ, pow_mul, hc2, one_pow, one_mul] at hcm
  have hsε : (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε = ε := by
    rw [hsce, hcm, one_smul]
  calc Matrix.mulVec (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) w
      = Matrix.mulVec (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
          (Matrix.mulVec ε w) := by rw [hw]
    _ = Matrix.mulVec ((s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε) w := by
          rw [Matrix.mulVec_mulVec]
    _ = Matrix.mulVec ε w := by rw [hsε]
    _ = w := hw

private lemma feomeg_polar_eq {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (x y : ι → F) :
    QuadraticMap.polar Q x y =
      dotProduct x ((LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).mulVec y) := by
  let G := LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)
  have h : QuadraticMap.polarBilin Q = Matrix.toBilin' G := by
    apply (LinearMap.BilinForm.toMatrix' (R₁ := F)).injective
    rw [LinearMap.BilinForm.toMatrix'_toBilin']
    rfl
  have hGG : (LinearMap.toMatrix₂' F) (Matrix.toBilin' G) = G :=
    LinearMap.BilinForm.toMatrix'_toBilin' G
  rw [← QuadraticMap.polarBilin_apply_apply, h, Matrix.toBilin'_apply', hGG]

private lemma feomeg_dotProduct_mulVec_transpose {m n R : Type} [Fintype n] [Fintype m]
    [NonUnitalCommSemiring R] (A : Matrix m n R) (x : n → R) (z : m → R) :
    dotProduct (Matrix.mulVec A x) z = dotProduct x ((Matrix.transpose A).mulVec z) := by
  rw [← Matrix.vecMul_transpose]
  exact (Matrix.dotProduct_mulVec x (Matrix.transpose A) z).symm

private lemma feomeg_polar_formAdj {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F))
    (hG : IsUnit (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).det)
    (a : Matrix ι ι F) (x y : ι → F) :
    QuadraticMap.polar Q (Matrix.mulVec a x) y =
      QuadraticMap.polar Q x
        (Matrix.mulVec (formAdj (RingHom.id F)
          (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) a) y) := by
  let G := LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)
  have hform : formAdj (RingHom.id F) G a = G⁻¹ * Matrix.transpose a * G := by
    simp [formAdj, Matrix.map_id]
  have hGinv : G * (G⁻¹ * Matrix.transpose a * G) = Matrix.transpose a * G := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv G hG,
      Matrix.one_mul]
  rw [feomeg_polar_eq Q, feomeg_polar_eq Q, hform]
  calc
    dotProduct ((Matrix.mulVec a x)) (G.mulVec y)
        = dotProduct x ((Matrix.transpose a).mulVec (G.mulVec y)) :=
          feomeg_dotProduct_mulVec_transpose a x (G.mulVec y)
    _ = dotProduct x ((Matrix.transpose a * G).mulVec y) := by
          rw [← Matrix.mulVec_mulVec]
    _ = dotProduct x (G.mulVec ((G⁻¹ * Matrix.transpose a * G).mulVec y)) := by
          rw [Matrix.mulVec_mulVec, hGinv]

private lemma feomeg_block_nondegenerate
    (n : ℕ) (F : Type) [Field F]
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} (hεid : IsIdempotentElem ε)
    (hεadj : formAdj (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F))) ε = ε) :
    ∀ x : Fin n ⊕ Fin n → F, Matrix.mulVec ε x = x →
      (∀ y : Fin n ⊕ Fin n → F, Matrix.mulVec ε y = y →
        QuadraticMap.polar (Spin.quadPlus n F) x y = 0) → x = 0 := by
  intro x hx hxperp
  have hG : IsUnit (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F))).det :=
    feomeg_gram_isUnit (Spin.quadPlus n F) (Spin.nondegenerate_polarBilin_quadPlus n F)
  have hnd : (QuadraticMap.polarBilin (Spin.quadPlus n F)).Nondegenerate :=
    Spin.nondegenerate_polarBilin_quadPlus n F
  apply hnd.1 x
  intro v
  have h1 : QuadraticMap.polar (Spin.quadPlus n F) x (Matrix.mulVec ε v) = 0 :=
    hxperp (Matrix.mulVec ε v) (by rw [Matrix.mulVec_mulVec, hεid.eq])
  have h2 : QuadraticMap.polar (Spin.quadPlus n F) x (Matrix.mulVec (1 - ε) v) = 0 := by
    rw [← hx]
    rw [feomeg_polar_formAdj (Spin.quadPlus n F) hG ε x (Matrix.mulVec (1 - ε) v), hεadj]
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, hεid.eq, sub_self,
      Matrix.zero_mulVec]
    exact QuadraticMap.polar_zero_right (Spin.quadPlus n F) x
  have hsplit : v = Matrix.mulVec ε v + Matrix.mulVec (1 - ε) v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  have hadd : QuadraticMap.polar (Spin.quadPlus n F) x
      (Matrix.mulVec ε v + Matrix.mulVec (1 - ε) v) =
      QuadraticMap.polar (Spin.quadPlus n F) x (Matrix.mulVec ε v) +
      QuadraticMap.polar (Spin.quadPlus n F) x (Matrix.mulVec (1 - ε) v) := by
    rw [← QuadraticMap.polarBilin_apply_apply, ← QuadraticMap.polarBilin_apply_apply,
      ← QuadraticMap.polarBilin_apply_apply]
    exact map_add (QuadraticMap.polarBilin (Spin.quadPlus n F) x) _ _
  rw [QuadraticMap.polarBilin_apply_apply, hsplit, hadd, h1, h2, add_zero]

private lemma feomeg_block_isMinusFour
    (n : ℕ) (F : Type) [Field F]
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} (hεid : IsIdempotentElem ε)
    (hrank : ε.rank = 4)
    (hminus : ∀ x y : Fin n ⊕ Fin n → F, Matrix.mulVec ε x = x → Matrix.mulVec ε y = y →
      (Spin.quadPlus n F) x = 0 → (Spin.quadPlus n F) y = 0 → QuadraticMap.polar (Spin.quadPlus n F)
      x y = 0 → ¬ LinearIndependent F ![x, y]) :
    Module.finrank F (LinearMap.range (Matrix.mulVecLin ε)) = 4 ∧
      (∀ U : Submodule F (LinearMap.range (Matrix.mulVecLin ε)),
        (∀ u ∈ U, (Spin.quadPlus n F) (u : Fin n ⊕ Fin n → F) = 0) →
          Module.finrank F U ≤ 1) := by
  constructor
  · exact hrank
  · intro U hU
    by_contra h
    haveI : Module.Free F ↥U := Module.Free.of_divisionRing F ↥U
    haveI : Module.Finite F ↥U := inferInstance
    have hiff : Module.finrank F ↥U ≤ 1 ↔
        ∃ v : ↥U, ∀ w : ↥U, ∃ c : F, c • v = w :=
      finrank_le_one_iff (K := F) (V := ↥U)
    rw [hiff] at h
    push Not at h
    obtain ⟨w, hw⟩ := h 0
    have hw0 : w ≠ 0 := by
      intro h0
      exact hw 0 (by rw [h0, zero_smul])
    obtain ⟨w', hw'⟩ := h w
    have hindep : LinearIndependent F
        ![(w : Fin n ⊕ Fin n → F), (w' : Fin n ⊕ Fin n → F)] := by
      rw [LinearIndependent.pair_iff' (V := Fin n ⊕ Fin n → F)
        (x := (w : Fin n ⊕ Fin n → F)) (y := (w' : Fin n ⊕ Fin n → F))
        (by intro h0; exact hw0 (Subtype.ext (Subtype.ext (by simpa using h0))))]
      intro c hc
      exact hw' c (Subtype.ext (Subtype.ext (by simpa using hc)))
    have hfixed : ∀ u : U, Matrix.mulVec ε (u : Fin n ⊕ Fin n → F) =
        (u : Fin n ⊕ Fin n → F) := by
      intro u
      have hu : (u : Fin n ⊕ Fin n → F) ∈ LinearMap.range (Matrix.mulVecLin ε) :=
        (u : LinearMap.range (Matrix.mulVecLin ε)).2
      obtain ⟨v, hv⟩ := hu
      have hv' : Matrix.mulVec ε v = (u : Fin n ⊕ Fin n → F) := by
        simpa only [Matrix.mulVecLin_apply] using hv
      calc Matrix.mulVec ε (u : Fin n ⊕ Fin n → F)
          = Matrix.mulVec ε (Matrix.mulVec ε v) := by rw [hv']
        _ = Matrix.mulVec (ε * ε) v := by rw [Matrix.mulVec_mulVec]
        _ = Matrix.mulVec ε v := by rw [hεid.eq]
        _ = (u : Fin n ⊕ Fin n → F) := hv'
    have hQw : (Spin.quadPlus n F) (w : Fin n ⊕ Fin n → F) = 0 := hU w w.2
    have hQw' : (Spin.quadPlus n F) (w' : Fin n ⊕ Fin n → F) = 0 := hU w' w'.2
    have hpolar : QuadraticMap.polar (Spin.quadPlus n F)
        (w : Fin n ⊕ Fin n → F) (w' : Fin n ⊕ Fin n → F) = 0 := by
      have h := QuadraticMap.map_add (Spin.quadPlus n F)
        (w : Fin n ⊕ Fin n → F) (w' : Fin n ⊕ Fin n → F)
      rw [hQw, hQw'] at h
      have hQsum : (Spin.quadPlus n F) ((w + w' : U) : Fin n ⊕ Fin n → F) = 0 :=
        hU (w + w') (w + w').2
      have hQsum' : (Spin.quadPlus n F) ((w : Fin n ⊕ Fin n → F) +
          (w' : Fin n ⊕ Fin n → F)) = 0 := by simpa using hQsum
      rw [hQsum'] at h
      simpa using h.symm
    exact hminus (w : Fin n ⊕ Fin n → F) (w' : Fin n ⊕ Fin n → F)
      (hfixed w) (hfixed w') hQw hQw' hpolar hindep

private lemma feomeg_blockCentralizer_commute_adjoin
    {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι] [Field F]
    (j : U →* GL ι F) (S : Set (GL ι F)) {ε : Matrix ι ι F}
    (u : glBlockCentralizer j S ε)
    {a : Matrix ι ι F} (ha : a ∈ Algebra.adjoin F (Units.val '' S)) :
    (j (u : U) : Matrix ι ι F) * a = a * (j (u : U) : Matrix ι ι F) := by
  let M : Matrix ι ι F := (j (u : U) : Matrix ι ι F)
  have hT : j (u : U) ∈ Subgroup.centralizer S :=
    (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp u.2)).1
  have hgen : (Units.val '' S : Set (Matrix ι ι F)) ⊆
      (Subalgebra.centralizer F ({M} : Set (Matrix ι ι F)) : Set (Matrix ι ι F)) := by
    rintro x ⟨s, hs, rfl⟩
    refine (Subalgebra.mem_centralizer_iff F).mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact congrArg (fun g : GL ι F => (g : Matrix ι ι F))
      ((Subgroup.mem_centralizer_iff.mp hT) s hs).symm
  have hA : Algebra.adjoin F (Units.val '' S) ≤
      Subalgebra.centralizer F ({M} : Set (Matrix ι ι F)) :=
    Algebra.adjoin_le hgen
  exact (Subalgebra.mem_centralizer_iff F).mp (hA ha) M (Set.mem_singleton M)

private lemma feomeg_blockCentralizer_commute_block
    {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι] [Field F]
    (j : U →* GL ι F) (S : Set (GL ι F)) {ε : Matrix ι ι F}
    (hεA : ε ∈ Algebra.adjoin F (Units.val '' S))
    (u : glBlockCentralizer j S ε) :
    (j (u : U) : Matrix ι ι F) * ε = ε * (j (u : U) : Matrix ι ι F) :=
  feomeg_blockCentralizer_commute_adjoin j S u hεA

private lemma feomeg_blockCentralizer_stable
    {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι] [Field F]
    (j : U →* GL ι F) (S : Set (GL ι F)) {ε : Matrix ι ι F}
    (hεA : ε ∈ Algebra.adjoin F (Units.val '' S))
    (u : glBlockCentralizer j S ε) :
    ∀ w ∈ LinearMap.range (Matrix.mulVecLin ε),
      Matrix.mulVecLin (j (u : U) : Matrix ι ι F) w ∈
        LinearMap.range (Matrix.mulVecLin ε) := by
  intro w hw
  obtain ⟨v, hv⟩ := hw
  have hv' : Matrix.mulVec ε v = w := by
    simpa only [Matrix.mulVecLin_apply] using hv
  refine ⟨Matrix.mulVec (j (u : U) : Matrix ι ι F) v, ?_⟩
  have hcomm : ε * (j (u : U) : Matrix ι ι F) =
      (j (u : U) : Matrix ι ι F) * ε :=
    (feomeg_blockCentralizer_commute_block j S hεA u).symm
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
  calc Matrix.mulVec ε (Matrix.mulVec (j (u : U) : Matrix ι ι F) v)
      = Matrix.mulVec (ε * (j (u : U) : Matrix ι ι F)) v := by
        rw [Matrix.mulVec_mulVec]
    _ = Matrix.mulVec ((j (u : U) : Matrix ι ι F) * ε) v := by rw [hcomm]
    _ = Matrix.mulVec (j (u : U) : Matrix ι ι F) (Matrix.mulVec ε v) := by
        rw [Matrix.mulVec_mulVec]
    _ = Matrix.mulVec (j (u : U) : Matrix ι ι F) w := by rw [hv']

private lemma feomeg_blockCentralizer_fixes_ker
    {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι] [Field F]
    (j : U →* GL ι F) (S : Set (GL ι F)) {ε : Matrix ι ι F}
    (u : glBlockCentralizer j S ε) :
    ∀ w : ι → F, Matrix.mulVec (1 - ε) w = w →
      Matrix.mulVec (j (u : U) : Matrix ι ι F) w = w := by
  intro w hw
  have hfix : (j (u : U) : GL ι F) ∈ glFixing (1 - ε) :=
    (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp u.2)).2
  have h : (j (u : U) : Matrix ι ι F) * (1 - ε) = (1 - ε) := hfix
  calc Matrix.mulVec (j (u : U) : Matrix ι ι F) w
      = Matrix.mulVec (j (u : U) : Matrix ι ι F) (Matrix.mulVec (1 - ε) w) := by
        rw [hw]
    _ = Matrix.mulVec ((j (u : U) : Matrix ι ι F) * (1 - ε)) w := by
        rw [Matrix.mulVec_mulVec]
    _ = Matrix.mulVec (1 - ε) w := by rw [h]
    _ = w := hw

private lemma feomeg_blockCentralizer_action
    (n : ℕ) (F : Type) [Field F]
    (S : Set (GL (Fin n ⊕ Fin n) F))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hεA : ε ∈ Algebra.adjoin F (Units.val '' S)) :
    ∃ ρ : glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε →*
        (↥(LinearMap.range (Matrix.mulVecLin ε)) ≃ₗ[F]
         ↥(LinearMap.range (Matrix.mulVecLin ε))),
      ∀ (u : glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε)
        (w : ↥(LinearMap.range (Matrix.mulVecLin ε))),
        ((ρ u) w : Fin n ⊕ Fin n → F) =
          Matrix.mulVec (Spin.spinMatrix (Spin.quadPlus n F)
            (u : ↥(spinGroup (Spin.quadPlus n F)))) (w : Fin n ⊕ Fin n → F) := by
  classical
  let Q := Spin.quadPlus n F
  let W : Submodule F (Fin n ⊕ Fin n → F) := LinearMap.range (Matrix.mulVecLin ε)
  let G := glBlockCentralizer (Spin.spinMatrix Q) S ε
  let M : G → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
    fun u => (Spin.spinMatrix Q (u : ↥(spinGroup Q)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
  let N : G → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
    fun u => (((Spin.spinMatrix Q (u : ↥(spinGroup Q)))⁻¹ : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
  have hMN : ∀ u : G, M u * N u = 1 := by
    intro u
    change (Spin.spinMatrix Q (u : ↥(spinGroup Q)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      (((Spin.spinMatrix Q (u : ↥(spinGroup Q)))⁻¹ : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = 1
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hNM : ∀ u : G, N u * M u = 1 := by
    intro u
    change (((Spin.spinMatrix Q (u : ↥(spinGroup Q)))⁻¹ : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      (Spin.spinMatrix Q (u : ↥(spinGroup Q)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = 1
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcomm : ∀ u : G, M u * ε = ε * M u := by
    intro u
    exact feomeg_blockCentralizer_commute_block (Spin.spinMatrix Q) S hεA u
  have hcommN : ∀ u : G, N u * ε = ε * N u := by
    intro u
    calc N u * ε = N u * ε * (M u * N u) := by rw [hMN u, mul_one]
      _ = N u * (ε * (M u * N u)) := by simp only [Matrix.mul_assoc]
      _ = N u * ((ε * M u) * N u) := by simp only [Matrix.mul_assoc]
      _ = N u * ((M u * ε) * N u) := by rw [← hcomm u]
      _ = N u * (M u * (ε * N u)) := by simp only [Matrix.mul_assoc]
      _ = (N u * M u) * (ε * N u) := by simp only [Matrix.mul_assoc]
      _ = 1 * (ε * N u) := by rw [hNM u]
      _ = ε * N u := by rw [one_mul]
  have hstable : ∀ u : G, ∀ w ∈ W, Matrix.mulVec (M u) w ∈ W := by
    intro u
    exact feomeg_blockCentralizer_stable (Spin.spinMatrix Q) S hεA u
  have hinv_mem : ∀ u : G, ∀ w ∈ W, Matrix.mulVec (N u) w ∈ W := by
    intro u w hw
    obtain ⟨x, hx⟩ := hw
    have hx' : Matrix.mulVec ε x = w := by simpa only [Matrix.mulVecLin_apply] using hx
    refine ⟨Matrix.mulVec (N u) x, ?_⟩
    calc Matrix.mulVec ε (Matrix.mulVec (N u) x)
        = Matrix.mulVec (ε * N u) x := by rw [Matrix.mulVec_mulVec]
      _ = Matrix.mulVec (N u * ε) x := by rw [← hcommN u]
      _ = Matrix.mulVec (N u) (Matrix.mulVec ε x) := by rw [Matrix.mulVec_mulVec]
      _ = Matrix.mulVec (N u) w := by rw [hx']
  let rho : G →* (W ≃ₗ[F] W) :=
    { toFun := fun u =>
        { toFun := fun w => ⟨Matrix.mulVec (M u) (w : Fin n ⊕ Fin n → F), hstable u w w.2⟩
          invFun := fun w => ⟨Matrix.mulVec (N u) (w : Fin n ⊕ Fin n → F), hinv_mem u w w.2⟩
          left_inv := by
            intro w
            apply Subtype.ext
            change Matrix.mulVec (N u) (Matrix.mulVec (M u) (w : Fin n ⊕ Fin n → F)) =
              (w : Fin n ⊕ Fin n → F)
            rw [Matrix.mulVec_mulVec, hNM u, Matrix.one_mulVec]
          right_inv := by
            intro w
            apply Subtype.ext
            change Matrix.mulVec (M u) (Matrix.mulVec (N u) (w : Fin n ⊕ Fin n → F)) =
              (w : Fin n ⊕ Fin n → F)
            rw [Matrix.mulVec_mulVec, hMN u, Matrix.one_mulVec]
          map_add' := by
            intro a b
            apply Subtype.ext
            change Matrix.mulVec (M u) ((a : Fin n ⊕ Fin n → F) + (b : Fin n ⊕ Fin n → F)) =
              Matrix.mulVec (M u) (a : Fin n ⊕ Fin n → F) +
                Matrix.mulVec (M u) (b : Fin n ⊕ Fin n → F)
            rw [Matrix.mulVec_add]
          map_smul' := by
            intro c a
            apply Subtype.ext
            change Matrix.mulVec (M u) (c • (a : Fin n ⊕ Fin n → F)) =
              c • Matrix.mulVec (M u) (a : Fin n ⊕ Fin n → F)
            rw [Matrix.mulVec_smul] }
      map_one' := by
        apply LinearEquiv.ext
        intro w
        apply Subtype.ext
        change Matrix.mulVec (M 1) (w : Fin n ⊕ Fin n → F) = (w : Fin n ⊕ Fin n → F)
        simp [M]
      map_mul' := by
        intro u v
        apply LinearEquiv.ext
        intro w
        apply Subtype.ext
        change Matrix.mulVec (M (u * v)) (w : Fin n ⊕ Fin n → F) =
          Matrix.mulVec (M u) (Matrix.mulVec (M v) (w : Fin n ⊕ Fin n → F))
        rw [Matrix.mulVec_mulVec]
        rw [show M (u * v) = M u * M v from by
          simp only [M, Subgroup.coe_mul, map_mul, Units.val_mul]] }
  refine ⟨rho, ?_⟩
  intro u w
  rfl

private lemma feomeg_blockCentralizer_isometry
    (n : ℕ) (F : Type) [Field F]
    (S : Set (GL (Fin n ⊕ Fin n) F))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} :
    ∀ (u : glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε)
      (w : Fin n ⊕ Fin n → F),
      (Spin.quadPlus n F) (Matrix.mulVec (Spin.spinMatrix (Spin.quadPlus n F)
        (u : ↥(spinGroup (Spin.quadPlus n F)))) w) = (Spin.quadPlus n F) w := by
  intro u w
  simp only [Spin.spinMatrix_mulVec, Spin.map_spinAction]

private noncomputable def feomeg_blockCentralizer_commutatorAction
    (n : ℕ) (F : Type) [Field F]
    (S : Set (GL (Fin n ⊕ Fin n) F))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hεA : ε ∈ Algebra.adjoin F (Units.val '' S)) :
    (↥(⁅glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε,
      glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε⁆ :
        Subgroup ↥(spinGroup (Spin.quadPlus n F)))) →*
      (↥(LinearMap.range (Matrix.mulVecLin ε)) ≃ₗ[F]
       ↥(LinearMap.range (Matrix.mulVecLin ε))) :=
  let G : Subgroup ↥(spinGroup (Spin.quadPlus n F)) :=
    glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε
  (Classical.choose (feomeg_blockCentralizer_action n F S hεA)).comp
    (Subgroup.inclusion (by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      exact G.mul_mem (G.mul_mem (G.mul_mem hx hy) (G.inv_mem hx)) (G.inv_mem hy)))

private noncomputable def feomeg_blockForm
    (n : ℕ) (F : Type) [Field F]
    (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) :
    QuadraticForm F ↥(LinearMap.range (Matrix.mulVecLin ε)) :=
  (Spin.quadPlus n F).comp (LinearMap.range (Matrix.mulVecLin ε)).subtype

private lemma feomeg_blockForm_mem_fixed
    {ι F : Type} [Fintype ι] [Field F]
    {ε : Matrix ι ι F} (hεid : IsIdempotentElem ε)
    {x : ι → F} (hx : x ∈ LinearMap.range (Matrix.mulVecLin ε)) :
    Matrix.mulVec ε x = x := by
  obtain ⟨v, hv⟩ := hx
  have hv' : Matrix.mulVec ε v = x := by simpa only [Matrix.mulVecLin_apply] using hv
  rw [← hv', Matrix.mulVec_mulVec, hεid.eq]

private lemma feomeg_blockForm_isMinusFour
    (n : ℕ) (F : Type) [Field F]
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} (hεid : IsIdempotentElem ε)
    (hεadj : formAdj (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F))) ε = ε)
    (hrank : ε.rank = 4)
    (hminus : ∀ x y : Fin n ⊕ Fin n → F, Matrix.mulVec ε x = x → Matrix.mulVec ε y = y →
      (Spin.quadPlus n F) x = 0 → (Spin.quadPlus n F) y = 0 → QuadraticMap.polar (Spin.quadPlus n F)
      x y = 0 → ¬ LinearIndependent F ![x, y]) :
    Module.finrank F ↥(LinearMap.range (Matrix.mulVecLin ε)) = 4 ∧
      (∀ x : ↥(LinearMap.range (Matrix.mulVecLin ε)),
        (∀ y, QuadraticMap.polar (feomeg_blockForm n F ε) x y = 0) → x = 0) ∧
      (∀ U : Submodule F ↥(LinearMap.range (Matrix.mulVecLin ε)),
        (∀ u ∈ U, feomeg_blockForm n F ε u = 0) → Module.finrank F U ≤ 1) := by
  refine ⟨(feomeg_block_isMinusFour n F hεid hrank hminus).1, ?_, ?_⟩
  · intro x hx
    apply Subtype.ext
    refine feomeg_block_nondegenerate n F hεid hεadj (x : Fin n ⊕ Fin n → F)
      (feomeg_blockForm_mem_fixed hεid x.2) ?_
    intro y hy
    exact hx ⟨y, LinearMap.mem_range.mpr ⟨y, by simpa only [Matrix.mulVecLin_apply] using hy⟩⟩
  · exact (feomeg_block_isMinusFour n F hεid hrank hminus).2

private lemma feomeg_blockCentralizer_commutatorAction_range_le_omega
    (n : ℕ) (F : Type) [Field F]
    (S : Set (GL (Fin n ⊕ Fin n) F))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hεA : ε ∈ Algebra.adjoin F (Units.val '' S)) :
    (feomeg_blockCentralizer_commutatorAction n F S hεA).range ≤
      ⁅TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε),
        TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε)⁆ := by
  classical
  let K : Subgroup ↥(spinGroup (Spin.quadPlus n F)) :=
    glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε
  let W := LinearMap.range (Matrix.mulVecLin ε)
  let O : Subgroup (W ≃ₗ[F] W) :=
    TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε)
  let φ : ↥K →* (W ≃ₗ[F] W) :=
    Classical.choose (feomeg_blockCentralizer_action n F S hεA)
  have hspec := Classical.choose_spec (feomeg_blockCentralizer_action n F S hεA)
  have hcomm : ⁅K,K⁆.subgroupOf K = commutator ↥K := by
    ext z
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hz
      rw [← Subgroup.map_subtype_commutator K, Subgroup.mem_map] at hz
      obtain ⟨y, hy, hyz⟩ := hz
      have hyz' : y = z := Subtype.ext hyz
      simpa [hyz'] using hy
    · intro hz
      rw [← Subgroup.map_subtype_commutator K]
      exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  have hφO : Subgroup.map φ ⊤ ≤ O := by
    rw [Subgroup.map_top]
    rintro x ⟨u, rfl⟩
    refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
    change (Spin.quadPlus n F) (((φ u) v : W) : Fin n ⊕ Fin n → F) =
      (Spin.quadPlus n F) ((v : W) : Fin n ⊕ Fin n → F)
    rw [hspec u v]
    exact feomeg_blockCentralizer_isometry n F S u (v : Fin n ⊕ Fin n → F)
  calc
    (feomeg_blockCentralizer_commutatorAction n F S hεA).range
        = Subgroup.map φ (commutator ↥K) := by
          rw [feomeg_blockCentralizer_commutatorAction, MonoidHom.range_comp,
            Subgroup.inclusion_range, hcomm]
    _ = ⁅Subgroup.map φ ⊤, Subgroup.map φ ⊤⁆ := by
          rw [commutator_def, Subgroup.map_commutator]
    _ ≤ ⁅O, O⁆ := Subgroup.commutator_mono hφO hφO

private abbrev feomeg_blockForm_minusFourHyp
    (n : ℕ) (F : Type) [Field F]
    (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) : Prop :=
  Module.finrank F ↥(LinearMap.range (Matrix.mulVecLin ε)) = 4 ∧
    (∀ x : ↥(LinearMap.range (Matrix.mulVecLin ε)),
      (∀ y, QuadraticMap.polar (feomeg_blockForm n F ε) x y = 0) → x = 0) ∧
    (∀ U : Submodule F ↥(LinearMap.range (Matrix.mulVecLin ε)),
      (∀ u ∈ U, feomeg_blockForm n F ε u = 0) → Module.finrank F U ≤ 1)

private lemma feomeg_blockCentralizer_commutatorAction_commutator_le_elementaryGroup_iff
    (n : ℕ) (F : Type) [Field F]
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} :
    ⁅TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε),
        TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε)⁆ ≤
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup (feomeg_blockForm n F ε) ↔
    ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε),
      ∀ h ∈ TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε),
        ⁅g, h⁆ ∈ CFSG.ClassicalGroups.Orthogonal.elementaryGroup (feomeg_blockForm n F ε) :=
  Subgroup.commutator_le

private lemma feomeg_blockCentralizer_commutatorAction_commutatorElement_mem_elementaryGroup
    (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hbf : feomeg_blockForm_minusFourHyp n F ε) :
    ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε),
      ∀ h ∈ TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε),
        ⁅g, h⁆ ∈ CFSG.ClassicalGroups.Orthogonal.elementaryGroup (feomeg_blockForm n F ε) := by
  obtain ⟨b, c, hirr⟩ := CFSG.LieType.Universal.exists_irreducible_quadratic F
  haveI : FiniteDimensional F ↥(LinearMap.range (Matrix.mulVecLin ε)) := inferInstance
  have hleft : (QuadraticMap.polarBilin (feomeg_blockForm n F ε)).SeparatingLeft :=
    fun x hx => hbf.2.1 x (fun y => by simpa using hx y)
  have hright : (QuadraticMap.polarBilin (feomeg_blockForm n F ε)).SeparatingRight :=
    fun y hy => hbf.2.1 y (fun x => by simpa [QuadraticMap.polar_comm] using hy x)
  have hnd : LinearMap.Nondegenerate (QuadraticMap.polarBilin (feomeg_blockForm n F ε)) :=
    ⟨hleft, hright⟩
  have hdim : Module.finrank F ↥(LinearMap.range (Matrix.mulVecLin ε)) = 2 * 2 := by
    rw [hbf.1]
  have hnotplus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (feomeg_blockForm n F ε) := by
    rintro ⟨W, hW, hWs⟩
    have hW2 : Module.finrank F W = 2 := by
      have h1 := hbf.1
      omega
    have hle := hbf.2.2 W hWs
    omega
  obtain ⟨e⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_of_not_isPlusType
    hnd (n := 2) (by norm_num) hdim hnotplus hirr
  have hmodel : ⁅TauCeti.QuadraticMap.orthogonalGroup (Spin.quadMinus 2 F b c),
      TauCeti.QuadraticMap.orthogonalGroup (Spin.quadMinus 2 F b c)⁆ =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup (Spin.quadMinus 2 F b c) :=
    CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadMinus_of_two_le
      (n := 2) (by norm_num) hirr
  have htrans :=
    CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.derived_eq_elementary_isometry
      e.symm hmodel
  exact Subgroup.commutator_le.mp (le_of_eq htrans)

private lemma feomeg_blockCentralizer_commutatorAction_commutator_le_elementaryGroup
    (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hbf : feomeg_blockForm_minusFourHyp n F ε) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε),
        TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε)⁆ ≤
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup (feomeg_blockForm n F ε) :=
  (feomeg_blockCentralizer_commutatorAction_commutator_le_elementaryGroup_iff
    n F).mpr
    (feomeg_blockCentralizer_commutatorAction_commutatorElement_mem_elementaryGroup
      n F hbf)

private lemma
    feomeg_blockCentralizer_commutatorAction_commutator_eq_elementaryGroup_of_minusFour
    (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hbf : feomeg_blockForm_minusFourHyp n F ε) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε),
        TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε)⁆ =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup (feomeg_blockForm n F ε) := by
  obtain ⟨b, c, hirr⟩ := CFSG.LieType.Universal.exists_irreducible_quadratic F
  haveI : FiniteDimensional F ↥(LinearMap.range (Matrix.mulVecLin ε)) := inferInstance
  have hleft : (QuadraticMap.polarBilin (feomeg_blockForm n F ε)).SeparatingLeft :=
    fun x hx => hbf.2.1 x (fun y => by simpa using hx y)
  have hright : (QuadraticMap.polarBilin (feomeg_blockForm n F ε)).SeparatingRight :=
    fun y hy => hbf.2.1 y (fun x => by simpa [QuadraticMap.polar_comm] using hy x)
  have hnd : LinearMap.Nondegenerate (QuadraticMap.polarBilin (feomeg_blockForm n F ε)) :=
    ⟨hleft, hright⟩
  have hdim : Module.finrank F ↥(LinearMap.range (Matrix.mulVecLin ε)) = 2 * 2 := by
    rw [hbf.1]
  have hnotplus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (feomeg_blockForm n F ε) := by
    rintro ⟨W, hW, hWs⟩
    have hW2 : Module.finrank F W = 2 := by
      have h1 := hbf.1
      omega
    have hle := hbf.2.2 W hWs
    omega
  obtain ⟨e⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_of_not_isPlusType
    hnd (n := 2) (by norm_num) hdim hnotplus hirr
  have hmodel : ⁅TauCeti.QuadraticMap.orthogonalGroup (Spin.quadMinus 2 F b c),
      TauCeti.QuadraticMap.orthogonalGroup (Spin.quadMinus 2 F b c)⁆ =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup (Spin.quadMinus 2 F b c) :=
    CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadMinus_of_two_le
      (n := 2) (by norm_num) hirr
  exact
    CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.derived_eq_elementary_isometry
      e.symm hmodel

private lemma feomeg_blockCentralizer_commutatorAction_elementaryGroup_le_commutator
    (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hbf : feomeg_blockForm_minusFourHyp n F ε) :
    CFSG.ClassicalGroups.Orthogonal.elementaryGroup (feomeg_blockForm n F ε) ≤
      ⁅TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε),
        TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε)⁆ :=
  le_of_eq
    (feomeg_blockCentralizer_commutatorAction_commutator_eq_elementaryGroup_of_minusFour
      n F hbf).symm

private lemma feomeg_blockCentralizer_commutatorAction_commutator_eq_elementaryGroup
    (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hbf : feomeg_blockForm_minusFourHyp n F ε) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε),
        TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε)⁆ =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup (feomeg_blockForm n F ε) :=
  le_antisymm
    (feomeg_blockCentralizer_commutatorAction_commutator_le_elementaryGroup n F hbf)
    (feomeg_blockCentralizer_commutatorAction_elementaryGroup_le_commutator n F hbf)

private def feomeg_blockCentralizerContext
    (n : ℕ) (F : Type) [Field F]
    (S : Set (GL (Fin n ⊕ Fin n) F))
    (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) : Prop :=
  3 ≤ n ∧
  (∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus n F)).range) ∧
    (∀ s ∈ S, ∀ s' ∈ S, Commute s s') ∧
    (∀ s ∈ S, Odd (orderOf s)) ∧
    IsPrimAdjIdemIn (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F)))
      (Algebra.adjoin F (Units.val '' S)) ε ∧
    blockDegree (Algebra.adjoin F (Units.val '' S)) ε < 2 ∧
    ε.rank = 4 ∧
    (∀ x y : Fin n ⊕ Fin n → F, Matrix.mulVec ε x = x → Matrix.mulVec ε y = y →
      (Spin.quadPlus n F) x = 0 → (Spin.quadPlus n F) y = 0 →
      QuadraticMap.polar (Spin.quadPlus n F) x y = 0 → ¬ LinearIndependent F ![x, y])

private noncomputable def feomeg_blockCentralizer_actionHom
    (n : ℕ) (F : Type) [Field F]
    (S : Set (GL (Fin n ⊕ Fin n) F))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hεA : ε ∈ Algebra.adjoin F (Units.val '' S)) :
    ↥(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε) →*
      (↥(LinearMap.range (Matrix.mulVecLin ε)) ≃ₗ[F]
       ↥(LinearMap.range (Matrix.mulVecLin ε))) :=
  Classical.choose (feomeg_blockCentralizer_action n F S hεA)

private lemma feomeg_block_range_perp_ker
    (n : ℕ) (F : Type) [Field F]
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hεadj : formAdj (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F))) ε = ε) :
    ∀ x ∈ LinearMap.range (Matrix.mulVecLin ε),
      ∀ y ∈ LinearMap.ker (Matrix.mulVecLin ε),
      QuadraticMap.polar (Spin.quadPlus n F) x y = 0 := by
  intro x hx y hy
  obtain ⟨x', rfl⟩ := hx
  have hy' : Matrix.mulVec ε y = 0 := by simpa [Matrix.mulVecLin_apply] using hy
  have hG : IsUnit (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F))).det :=
    feomeg_gram_isUnit (Spin.quadPlus n F) (Spin.nondegenerate_polarBilin_quadPlus n F)
  change QuadraticMap.polar (Spin.quadPlus n F) (Matrix.mulVec ε x') y = 0
  rw [feomeg_polar_formAdj (Spin.quadPlus n F) hG ε x' y, hεadj, hy',
    QuadraticMap.polar_zero_right]

private lemma feomeg_blockCentralizer_spinAction_of_mem_range
    (n : ℕ) (F : Type) [Field F]
    (S : Set (GL (Fin n ⊕ Fin n) F))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hεid : IsIdempotentElem ε)
    (g' : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F))
    (hSg' : ∀ s ∈ S, ∀ x, g' (Matrix.mulVec (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x) =
      Matrix.mulVec (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (g' x))
    (hker : ∀ x, Matrix.mulVec (1 - ε) x = x → g' x = x)
    (hg'range : g' ∈ (Spin.spinAction (Spin.quadPlus n F)).range) :
    ∃ u : ↥(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε),
      ∀ x, Spin.spinAction (Spin.quadPlus n F)
        (u : ↥(spinGroup (Spin.quadPlus n F))) x = g' x := by
  have h1eid : (1 - ε) * (1 - ε) = (1 - ε) := by
    calc (1 - ε) * (1 - ε) = 1 * (1 - ε) - ε * (1 - ε) := by rw [Matrix.sub_mul]
      _ = (1 - ε) - (ε * 1 - ε * ε) := by rw [Matrix.one_mul, Matrix.mul_sub]
      _ = (1 - ε) - (ε - ε) := by rw [Matrix.mul_one, hεid.eq]
      _ = 1 - ε := by abel
  obtain ⟨x, hx⟩ := hg'range
  refine ⟨⟨x, ?_⟩, fun y => congrArg (fun e => e y) hx⟩
  rw [glBlockCentralizer, Subgroup.mem_comap]
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro s hs
    apply Units.ext
    simp only [Units.val_mul]
    exact Matrix.mulVec_injective (funext fun y => by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Spin.spinMatrix_mulVec,
        Spin.spinMatrix_mulVec, hx, hSg' s hs y])
  · exact Matrix.mulVec_injective (funext fun y => by
      rw [← Matrix.mulVec_mulVec, Spin.spinMatrix_mulVec, hx]
      exact hker ((1 - ε).mulVec y) (by rw [Matrix.mulVec_mulVec, h1eid]))

private lemma feomeg_blockCentralizer_spinAction_of_extends
    (n : ℕ) (F : Type) [Field F]
    (S : Set (GL (Fin n ⊕ Fin n) F))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hctx : feomeg_blockCentralizerContext n F S ε)
    (g' : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F))
    (hg'elem : g' ∈ CFSG.ClassicalGroups.Orthogonal.elementaryGroup (Spin.quadPlus n F))
    (hSg' : ∀ s ∈ S, ∀ x, g' (Matrix.mulVec (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x) =
      Matrix.mulVec (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (g' x))
    (hker : ∀ x, Matrix.mulVec (1 - ε) x = x → g' x = x) :
    ∃ u : ↥(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε),
      ∀ x, Spin.spinAction (Spin.quadPlus n F)
        (u : ↥(spinGroup (Spin.quadPlus n F))) x = g' x :=
  feomeg_blockCentralizer_spinAction_of_mem_range n F S hctx.2.2.2.2.1.2.1 g' hSg' hker
    (by rw [CFSG.LieType.Universal.Spin.range_spinAction_quadPlus (K := F) hctx.1]
        exact hg'elem)

private lemma feomeg_blockCentralizer_commutatorAction_range_eq_commutator
    (n : ℕ) (F : Type) [Field F]
    (S : Set (GL (Fin n ⊕ Fin n) F))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hεA : ε ∈ Algebra.adjoin F (Units.val '' S)) :
    (feomeg_blockCentralizer_commutatorAction n F S hεA).range =
      ⁅Subgroup.map (feomeg_blockCentralizer_actionHom n F S hεA) ⊤,
        Subgroup.map (feomeg_blockCentralizer_actionHom n F S hεA) ⊤⁆ := by
  let K : Subgroup ↥(spinGroup (Spin.quadPlus n F)) :=
    glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε
  let φ := feomeg_blockCentralizer_actionHom n F S hεA
  have hcomm : ⁅K,K⁆.subgroupOf K = commutator ↥K := by
    ext z
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hz
      rw [← Subgroup.map_subtype_commutator K, Subgroup.mem_map] at hz
      obtain ⟨y, hy, hyz⟩ := hz
      have hyz' : y = z := Subtype.ext hyz
      simpa [hyz'] using hy
    · intro hz
      rw [← Subgroup.map_subtype_commutator K]
      exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  calc
    (feomeg_blockCentralizer_commutatorAction n F S hεA).range
        = Subgroup.map φ (commutator ↥K) := by
          rw [feomeg_blockCentralizer_commutatorAction, MonoidHom.range_comp,
            Subgroup.inclusion_range, hcomm]
          rfl
    _ = ⁅Subgroup.map φ ⊤, Subgroup.map φ ⊤⁆ := by
          rw [commutator_def, Subgroup.map_commutator]

private lemma feomeg_blockCentralizer_actionHom_range_contains_elementaryGroup
    (n : ℕ) (F : Type) [Field F]
    (S : Set (GL (Fin n ⊕ Fin n) F))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hεA : ε ∈ Algebra.adjoin F (Units.val '' S))
    (hctx : feomeg_blockCentralizerContext n F S ε) :
    CFSG.ClassicalGroups.Orthogonal.elementaryGroup (feomeg_blockForm n F ε) ≤
      Subgroup.map (feomeg_blockCentralizer_actionHom n F S hεA) ⊤ := by
  classical
  have hεid : IsIdempotentElem ε := hctx.2.2.2.2.1.2.1
  have hεadj : formAdj (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F))) ε = ε :=
    hctx.2.2.2.2.1.2.2.2.1
  have hperp := feomeg_block_range_perp_ker n F hεadj
  have hcommP : (Units.val '' S : Set (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)).Pairwise
      Commute := by
    rintro a ⟨s1, hs1, rfl⟩ b ⟨s2, hs2, rfl⟩ _
    have h := hctx.2.2.1 s1 hs1 s2 hs2
    show (s1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        (s2 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (s2 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        (s1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    rw [← Units.val_mul, ← Units.val_mul, h]
  letI : CommRing (Algebra.adjoin F (Units.val '' S)) :=
    Algebra.adjoinCommRingOfComm F hcommP
  have hSε : ∀ s ∈ S, ε * (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε := by
    intro s hs
    have hsA : (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ∈
        Algebra.adjoin F (Units.val '' S) := Algebra.subset_adjoin ⟨s, hs, rfl⟩
    have h := mul_comm (⟨ε, hεA⟩ : Algebra.adjoin F (Units.val '' S))
      ⟨(s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F), hsA⟩
    exact congrArg Subtype.val h
  have hfix := feomeg_S_trivial_on_block n F S hctx.2.1 hctx.2.2.1 hctx.2.2.2.1
    hctx.2.2.2.2.1 hctx.2.2.2.2.2.1
  have h1eid : (1 - ε) * (1 - ε) = (1 - ε) := by
    calc (1 - ε) * (1 - ε) = 1 * (1 - ε) - ε * (1 - ε) := by rw [Matrix.sub_mul]
      _ = (1 - ε) - (ε * 1 - ε * ε) := by rw [Matrix.one_mul, Matrix.mul_sub]
      _ = (1 - ε) - (ε - ε) := by rw [Matrix.mul_one, hεid.eq]
      _ = 1 - ε := by abel
  have h1es : ∀ s ∈ S, (1 - ε) * (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * (1 - ε) := by
    intro s hs
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hSε s hs]
  have hsplit : ∀ y : Fin n ⊕ Fin n → F, y = Matrix.mulVec ε y + Matrix.mulVec (1 - ε) y := by
    intro y
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  apply CFSG.ClassicalGroups.Orthogonal.elementaryGroup_le_of_eichler_mem
  intro u w hu huw
  have huV : (Spin.quadPlus n F) (u : Fin n ⊕ Fin n → F) = 0 := by
    simpa [feomeg_blockForm] using hu
  have huwV : QuadraticMap.polar (Spin.quadPlus n F) (u : Fin n ⊕ Fin n → F)
      (w : Fin n ⊕ Fin n → F) = 0 := by
    simpa [feomeg_blockForm, QuadraticMap.polar, QuadraticMap.comp_apply] using huw
  have hg'el : CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus n F)
      (u : Fin n ⊕ Fin n → F) (w : Fin n ⊕ Fin n → F) ∈
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup (Spin.quadPlus n F) :=
    CFSG.ClassicalGroups.Orthogonal.eichler_mem_elementaryGroup _ _ _
  have hEfix : ∀ y : Fin n ⊕ Fin n → F, Matrix.mulVec (1 - ε) y = y →
      CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus n F)
        (u : Fin n ⊕ Fin n → F) (w : Fin n ⊕ Fin n → F) y = y := by
    intro y hy
    have hyK : y ∈ LinearMap.ker (Matrix.mulVecLin ε) := by
      show Matrix.mulVec ε y = 0
      have h2 : y - Matrix.mulVec ε y = y := by
        simpa [Matrix.sub_mulVec, Matrix.one_mulVec] using hy
      exact sub_eq_self.mp h2
    have hyu : QuadraticMap.polar (Spin.quadPlus n F) y (u : Fin n ⊕ Fin n → F) = 0 := by
      rw [QuadraticMap.polar_comm]
      exact hperp (u : Fin n ⊕ Fin n → F) u.2 y hyK
    have hyw : QuadraticMap.polar (Spin.quadPlus n F) y (w : Fin n ⊕ Fin n → F) = 0 := by
      rw [QuadraticMap.polar_comm]
      exact hperp (w : Fin n ⊕ Fin n → F) w.2 y hyK
    rw [CFSG.ClassicalGroups.Orthogonal.eichler_apply huV huwV, hyu, hyw]
    simp
  have hEpresW : ∀ y : Fin n ⊕ Fin n → F, Matrix.mulVec ε
      (CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus n F)
        (u : Fin n ⊕ Fin n → F) (w : Fin n ⊕ Fin n → F) (Matrix.mulVec ε y)) =
      CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus n F)
        (u : Fin n ⊕ Fin n → F) (w : Fin n ⊕ Fin n → F) (Matrix.mulVec ε y) := by
    intro y
    rw [CFSG.ClassicalGroups.Orthogonal.eichler_apply huV huwV]
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, hεid.eq, feomeg_blockForm_mem_fixed hεid u.2,
      feomeg_blockForm_mem_fixed hεid w.2]
  have hSg' : ∀ s ∈ S, ∀ y : Fin n ⊕ Fin n → F,
      CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus n F)
        (u : Fin n ⊕ Fin n → F) (w : Fin n ⊕ Fin n → F)
        (Matrix.mulVec (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) y) =
      Matrix.mulVec (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        (CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus n F)
          (u : Fin n ⊕ Fin n → F) (w : Fin n ⊕ Fin n → F) y) := by
    intro s hs y
    have hsK : Matrix.mulVec (1 - ε)
        (Matrix.mulVec (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
          (Matrix.mulVec (1 - ε) y)) =
        Matrix.mulVec (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
          (Matrix.mulVec (1 - ε) y) := by
      calc
        Matrix.mulVec (1 - ε)
            (Matrix.mulVec (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
              (Matrix.mulVec (1 - ε) y))
            = Matrix.mulVec ((1 - ε) * (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F))
                (Matrix.mulVec (1 - ε) y) := Matrix.mulVec_mulVec _ (1 - ε) _
        _ = Matrix.mulVec ((s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * (1 - ε))
                (Matrix.mulVec (1 - ε) y) := by rw [h1es s hs]
        _ = Matrix.mulVec (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
                (Matrix.mulVec (1 - ε) (Matrix.mulVec (1 - ε) y)) :=
              (Matrix.mulVec_mulVec _ _ (1 - ε)).symm
        _ = Matrix.mulVec (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
                (Matrix.mulVec ((1 - ε) * (1 - ε)) y) :=
              congrArg (fun t => Matrix.mulVec
                (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) t)
                (Matrix.mulVec_mulVec y (1 - ε) (1 - ε))
        _ = Matrix.mulVec (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
                (Matrix.mulVec (1 - ε) y) := by rw [h1eid]
    have hfixε : Matrix.mulVec (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        (CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus n F)
          (u : Fin n ⊕ Fin n → F) (w : Fin n ⊕ Fin n → F) (Matrix.mulVec ε y)) =
        CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus n F)
          (u : Fin n ⊕ Fin n → F) (w : Fin n ⊕ Fin n → F) (Matrix.mulVec ε y) :=
      hfix s hs _ (hEpresW y)
    have hEfix1e : CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus n F)
        (u : Fin n ⊕ Fin n → F) (w : Fin n ⊕ Fin n → F) (Matrix.mulVec (1 - ε) y) =
        Matrix.mulVec (1 - ε) y :=
      hEfix _ (by rw [Matrix.mulVec_mulVec, h1eid])
    have hEfixs : CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus n F)
        (u : Fin n ⊕ Fin n → F) (w : Fin n ⊕ Fin n → F)
        (Matrix.mulVec (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
          (Matrix.mulVec (1 - ε) y)) =
        Matrix.mulVec (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
          (Matrix.mulVec (1 - ε) y) :=
      hEfix _ hsK
    have hfixWs : Matrix.mulVec (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        (Matrix.mulVec ε y) = Matrix.mulVec ε y :=
      hfix s hs _ (by rw [Matrix.mulVec_mulVec, hεid.eq])
    have hy : y = Matrix.mulVec ε y + Matrix.mulVec (1 - ε) y := hsplit y
    calc
      CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus n F)
          (u : Fin n ⊕ Fin n → F) (w : Fin n ⊕ Fin n → F)
          (Matrix.mulVec (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) y)
          = CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus n F)
              (u : Fin n ⊕ Fin n → F) (w : Fin n ⊕ Fin n → F)
              (Matrix.mulVec (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
                (Matrix.mulVec ε y) +
               Matrix.mulVec (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
                (Matrix.mulVec (1 - ε) y)) := by
            conv_lhs => rw [hy, Matrix.mulVec_add]
      _ = CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus n F)
              (u : Fin n ⊕ Fin n → F) (w : Fin n ⊕ Fin n → F)
              (Matrix.mulVec ε y +
               Matrix.mulVec (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
                (Matrix.mulVec (1 - ε) y)) := by
            rw [hfixWs]
      _ = CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus n F)
              (u : Fin n ⊕ Fin n → F) (w : Fin n ⊕ Fin n → F) (Matrix.mulVec ε y) +
          CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus n F)
              (u : Fin n ⊕ Fin n → F) (w : Fin n ⊕ Fin n → F)
              (Matrix.mulVec (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
                (Matrix.mulVec (1 - ε) y)) := by
            rw [map_add]
      _ = CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus n F)
              (u : Fin n ⊕ Fin n → F) (w : Fin n ⊕ Fin n → F) (Matrix.mulVec ε y) +
          Matrix.mulVec (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
              (Matrix.mulVec (1 - ε) y) := by
            rw [hEfixs]
      _ = Matrix.mulVec (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
              (CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus n F)
                (u : Fin n ⊕ Fin n → F) (w : Fin n ⊕ Fin n → F) y) := by
            conv_rhs => rw [hy, map_add, Matrix.mulVec_add, hfixε, hEfix1e]

  obtain ⟨u₀, hu₀⟩ := feomeg_blockCentralizer_spinAction_of_extends n F S hctx
    (CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus n F)
      (u : Fin n ⊕ Fin n → F) (w : Fin n ⊕ Fin n → F)) hg'el hSg' hEfix
  refine Subgroup.mem_map.mpr ⟨u₀, Subgroup.mem_top _, ?_⟩
  apply LinearEquiv.ext
  intro v
  apply Subtype.ext
  have hspec := Classical.choose_spec (feomeg_blockCentralizer_action n F S hεA) u₀ v
  rw [feomeg_blockCentralizer_actionHom, hspec, Spin.spinMatrix_mulVec, hu₀]
  rw [CFSG.ClassicalGroups.Orthogonal.eichler_apply huV huwV,
    CFSG.ClassicalGroups.Orthogonal.eichler_apply hu huw]
  simp [feomeg_blockForm, QuadraticMap.polar, QuadraticMap.comp_apply]

private lemma feomeg_blockCentralizer_elementaryGroup_perfect
    (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hbf : feomeg_blockForm_minusFourHyp n F ε) :
    ⁅CFSG.ClassicalGroups.Orthogonal.elementaryGroup (feomeg_blockForm n F ε),
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup (feomeg_blockForm n F ε)⁆ =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup (feomeg_blockForm n F ε) := by
  haveI : FiniteDimensional F ↥(LinearMap.range (Matrix.mulVecLin ε)) := inferInstance
  obtain ⟨b, c, hirr⟩ := CFSG.LieType.Universal.exists_irreducible_quadratic F
  have hleft : (QuadraticMap.polarBilin (feomeg_blockForm n F ε)).SeparatingLeft :=
    fun x hx => hbf.2.1 x (fun y => by simpa using hx y)
  have hright : (QuadraticMap.polarBilin (feomeg_blockForm n F ε)).SeparatingRight :=
    fun y hy => hbf.2.1 y (fun x => by simpa [QuadraticMap.polar_comm] using hy x)
  have hQ : LinearMap.Nondegenerate (QuadraticMap.polarBilin (feomeg_blockForm n F ε)) :=
    ⟨hleft, hright⟩
  have hts : ∀ U : Submodule F ↥(LinearMap.range (Matrix.mulVecLin ε)),
      Module.finrank F U = Module.finrank F ↥(LinearMap.range (Matrix.mulVecLin ε)) / 2 →
      ∃ u ∈ U, feomeg_blockForm n F ε u ≠ 0 := by
    intro U hU
    by_contra h
    have hzero : ∀ u ∈ U, feomeg_blockForm n F ε u = 0 := by
      intro u hu
      by_contra hq
      exact h ⟨u, hu, hq⟩
    have hle := hbf.2.2 U hzero
    rw [hU, hbf.1] at hle
    omega
  have hperfGen : Group.IsPerfect
      ↥⁅TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε),
        TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε)⁆ :=
    (CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction
      (feomeg_blockForm n F ε) hQ (Or.inl hbf.1) hts).2.1
  have hnotplus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (feomeg_blockForm n F ε) := by
    rintro ⟨W, hW, hWs⟩
    have hW2 : Module.finrank F W = 2 := by
      have h1 := hbf.1
      omega
    have hle := hbf.2.2 W hWs
    omega
  obtain ⟨e⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_of_not_isPlusType hQ (n := 2)
    (by norm_num) (by rw [hbf.1]) hnotplus hirr
  have hmodel : ⁅TauCeti.QuadraticMap.orthogonalGroup (Spin.quadMinus 2 F b c),
      TauCeti.QuadraticMap.orthogonalGroup (Spin.quadMinus 2 F b c)⁆ =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup (Spin.quadMinus 2 F b c) :=
    CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadMinus_of_two_le
      (n := 2) (by norm_num) hirr
  have hEq : ⁅TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε),
        TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε)⁆ =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup (feomeg_blockForm n F ε) :=
    CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.derived_eq_elementary_isometry
      e.symm hmodel
  rw [hEq] at hperfGen
  haveI := hperfGen
  exact Subgroup.commutator_eq_self

private lemma feomeg_blockCentralizer_commutatorAction_eichler_mem_range
    (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]
    (S : Set (GL (Fin n ⊕ Fin n) F))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hεA : ε ∈ Algebra.adjoin F (Units.val '' S))
    (hctx : feomeg_blockCentralizerContext n F S ε)
    (hbf : feomeg_blockForm_minusFourHyp n F ε)
    (u w : ↥(LinearMap.range (Matrix.mulVecLin ε))) :
    CFSG.ClassicalGroups.Orthogonal.eichler (feomeg_blockForm n F ε) u w ∈
      (feomeg_blockCentralizer_commutatorAction n F S hεA).range := by
  have hperf := feomeg_blockCentralizer_elementaryGroup_perfect n F hbf
  have hmem : CFSG.ClassicalGroups.Orthogonal.eichler (feomeg_blockForm n F ε) u w ∈
      ⁅CFSG.ClassicalGroups.Orthogonal.elementaryGroup (feomeg_blockForm n F ε),
        CFSG.ClassicalGroups.Orthogonal.elementaryGroup (feomeg_blockForm n F ε)⁆ := by
    rw [hperf]
    exact CFSG.ClassicalGroups.Orthogonal.eichler_mem_elementaryGroup
      (feomeg_blockForm n F ε) u w
  have hle : ⁅CFSG.ClassicalGroups.Orthogonal.elementaryGroup (feomeg_blockForm n F ε),
        CFSG.ClassicalGroups.Orthogonal.elementaryGroup (feomeg_blockForm n F ε)⁆ ≤
      (feomeg_blockCentralizer_commutatorAction n F S hεA).range := by
    rw [feomeg_blockCentralizer_commutatorAction_range_eq_commutator]
    exact Subgroup.commutator_mono
      (feomeg_blockCentralizer_actionHom_range_contains_elementaryGroup n F S hεA hctx)
      (feomeg_blockCentralizer_actionHom_range_contains_elementaryGroup n F S hεA hctx)
  exact hle hmem

private lemma feomeg_blockCentralizer_commutatorAction_elementaryGroup_le_range
    (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]
    (S : Set (GL (Fin n ⊕ Fin n) F))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hεA : ε ∈ Algebra.adjoin F (Units.val '' S))
    (hctx : feomeg_blockCentralizerContext n F S ε)
    (hbf : feomeg_blockForm_minusFourHyp n F ε) :
    CFSG.ClassicalGroups.Orthogonal.elementaryGroup (feomeg_blockForm n F ε) ≤
      (feomeg_blockCentralizer_commutatorAction n F S hεA).range := by
  rw [CFSG.ClassicalGroups.Orthogonal.elementaryGroup]
  refine (Subgroup.closure_le _).mpr ?_
  rintro g ⟨u, w, hu, huw, rfl⟩
  exact feomeg_blockCentralizer_commutatorAction_eichler_mem_range n F S hεA hctx hbf u w

private lemma feomeg_blockCentralizer_commutatorAction_omega_le_range
    (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]
    (S : Set (GL (Fin n ⊕ Fin n) F))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hεA : ε ∈ Algebra.adjoin F (Units.val '' S))
    (hbf : feomeg_blockForm_minusFourHyp n F ε)
    (hctx : feomeg_blockCentralizerContext n F S ε) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε),
        TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε)⁆ ≤
      (feomeg_blockCentralizer_commutatorAction n F S hεA).range := by
  rw [feomeg_blockCentralizer_commutatorAction_commutator_eq_elementaryGroup n F hbf]
  exact feomeg_blockCentralizer_commutatorAction_elementaryGroup_le_range n F S hεA hctx hbf

private lemma feomeg_blockCentralizer_commutatorAction_range_eq_omega
    (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]
    (S : Set (GL (Fin n ⊕ Fin n) F))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hεA : ε ∈ Algebra.adjoin F (Units.val '' S))
    (hbf : feomeg_blockForm_minusFourHyp n F ε)
    (hctx : feomeg_blockCentralizerContext n F S ε) :
    (feomeg_blockCentralizer_commutatorAction n F S hεA).range =
      ⁅TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε),
        TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε)⁆ :=
  le_antisymm
    (feomeg_blockCentralizer_commutatorAction_range_le_omega n F S hεA)
    (feomeg_blockCentralizer_commutatorAction_omega_le_range n F S hεA hbf hctx)

private lemma feomeg_blockCentralizer_commutatorAction_rangeIso_omega
    (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]
    (S : Set (GL (Fin n ⊕ Fin n) F))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hεA : ε ∈ Algebra.adjoin F (Units.val '' S))
    (hbf : feomeg_blockForm_minusFourHyp n F ε)
    (hctx : feomeg_blockCentralizerContext n F S ε) :
    Nonempty (↥((feomeg_blockCentralizer_commutatorAction n F S hεA).range) ≃*
      ↥⁅TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε),
        TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε)⁆) :=
  ⟨MulEquiv.subgroupCongr
    (feomeg_blockCentralizer_commutatorAction_range_eq_omega n F S hεA hbf hctx)⟩

private noncomputable def feomeg_specialLinearEquiv
    {E E' : Type} [Field E] [Field E'] (ρ : E ≃+* E') :
    Matrix.SpecialLinearGroup (Fin 2) E ≃* Matrix.SpecialLinearGroup (Fin 2) E' where
  toFun := Matrix.SpecialLinearGroup.map ρ.toRingHom
  invFun := Matrix.SpecialLinearGroup.map ρ.symm.toRingHom
  left_inv g := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  right_inv g := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  map_mul' := (Matrix.SpecialLinearGroup.map ρ.toRingHom).map_mul

private noncomputable def feomeg_statedSLRingEquiv
    {E E' : Type} [Field E] [Field E'] (ρ : E ≃+* E') :
    ↥(CFSG.Open.StatedSL 2 E) ≃* ↥(CFSG.Open.StatedSL 2 E') :=
  (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 E).symm.trans
    ((feomeg_specialLinearEquiv ρ).trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 E'))

private lemma feomeg_block_omegaIso_statedSL
    (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (f : ℕ) (hc : Nat.card F = 2 ^ f)
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hbf : feomeg_blockForm_minusFourHyp n F ε) :
    Nonempty (↥⁅TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε),
      TauCeti.QuadraticMap.orthogonalGroup (feomeg_blockForm n F ε)⁆ ≃*
      CFSG.Open.StatedSL 2 (GaloisField 2 (2 * f))) := by
  classical
  haveI : FiniteDimensional F ↥(LinearMap.range (Matrix.mulVecLin ε)) := inferInstance
  have hleft : (QuadraticMap.polarBilin (feomeg_blockForm n F ε)).SeparatingLeft :=
    fun x hx => hbf.2.1 x (fun y => by simpa using hx y)
  have hright : (QuadraticMap.polarBilin (feomeg_blockForm n F ε)).SeparatingRight :=
    fun y hy => hbf.2.1 y (fun x => by simpa [QuadraticMap.polar_comm] using hy x)
  have hQ : LinearMap.Nondegenerate (QuadraticMap.polarBilin (feomeg_blockForm n F ε)) :=
    ⟨hleft, hright⟩
  have hts : ∀ U : Submodule F ↥(LinearMap.range (Matrix.mulVecLin ε)),
      Module.finrank F U = Module.finrank F ↥(LinearMap.range (Matrix.mulVecLin ε)) / 2 →
      ∃ u ∈ U, feomeg_blockForm n F ε u ≠ 0 := by
    intro U hU
    by_contra h
    have hzero : ∀ u ∈ U, feomeg_blockForm n F ε u = 0 := by
      intro u hu
      by_contra hq
      exact h ⟨u, hu, hq⟩
    have hle := hbf.2.2 U hzero
    rw [hU, hbf.1] at hle
    omega
  obtain ⟨-, -, -, -, -, hd4, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction
      (feomeg_blockForm n F ε) hQ (Or.inl hbf.1) hts
  obtain ⟨E, _, _, D, ψ, ρ, -, -, hinj, hrange, -⟩ := hd4 hbf.1
  haveI : Finite E := D.finite_E
  haveI : Fintype E := Fintype.ofFinite E
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype (GaloisField 2 (2 * f)) := Fintype.ofFinite _
  have hcardE : Fintype.card E = Fintype.card (GaloisField 2 (2 * f)) := by
    rw [← Nat.card_eq_fintype_card, D.card_E, ← Nat.card_eq_fintype_card, hc,
      GaloisField.card (p := 2) (n := 2 * f)
        (by have := feomeg_one_le F hc; omega),
      ← pow_mul, mul_comm f 2]
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans
    ((MonoidHom.ofInjective hinj).symm.trans
      ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 E).trans
        (feomeg_statedSLRingEquiv (FiniteField.ringEquivOfCardEq hcardE))))⟩

private lemma feomeg_blockCentralizer_commutatorAction_rangeIso
    (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (hn : 3 ≤ n) (f : ℕ)
    (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (Fin n ⊕ Fin n) F))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus n F)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F)))
      (Algebra.adjoin F (Units.val '' S)) ε)
    (hdeg : blockDegree (Algebra.adjoin F (Units.val '' S)) ε < 2) (hrank : ε.rank = 4)
    (hminus : ∀ x y : Fin n ⊕ Fin n → F, Matrix.mulVec ε x = x → Matrix.mulVec ε y = y →
      (Spin.quadPlus n F) x = 0 → (Spin.quadPlus n F) y = 0 → QuadraticMap.polar (Spin.quadPlus n F)
      x y = 0 → ¬ LinearIndependent F ![x, y]) :
    Nonempty (↥((feomeg_blockCentralizer_commutatorAction n F S hε.1).range) ≃*
      CFSG.Open.StatedSL 2 (GaloisField 2 (2 * f))) := by
  have hbf : feomeg_blockForm_minusFourHyp n F ε :=
    feomeg_blockForm_isMinusFour n F hε.2.1 hε.2.2.2.1 hrank hminus
  have hctx : feomeg_blockCentralizerContext n F S ε :=
    ⟨hn, hSU, hS, hodd, hε, hdeg, hrank, hminus⟩
  obtain ⟨φ⟩ := feomeg_blockCentralizer_commutatorAction_rangeIso_omega n F S hε.1 hbf hctx
  obtain ⟨ψ⟩ := feomeg_block_omegaIso_statedSL n F f hc hbf (ε := ε)
  exact ⟨φ.trans ψ⟩

private noncomputable def feomeg_blockCentralizer_commutatorHom
    (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (hn : 3 ≤ n) (f : ℕ)
    (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (Fin n ⊕ Fin n) F))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus n F)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F)))
      (Algebra.adjoin F (Units.val '' S)) ε)
    (hdeg : blockDegree (Algebra.adjoin F (Units.val '' S)) ε < 2) (hrank : ε.rank = 4)
    (hminus : ∀ x y : Fin n ⊕ Fin n → F, Matrix.mulVec ε x = x → Matrix.mulVec ε y = y →
      (Spin.quadPlus n F) x = 0 → (Spin.quadPlus n F) y = 0 → QuadraticMap.polar (Spin.quadPlus n F)
      x y = 0 → ¬ LinearIndependent F ![x, y]) :
    (↥(⁅glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε,
      glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε⁆ :
        Subgroup ↥(spinGroup (Spin.quadPlus n F)))) →*
      CFSG.Open.StatedSL 2 (GaloisField 2 (2 * f)) :=
  (Classical.choice
    (feomeg_blockCentralizer_commutatorAction_rangeIso n F hn f hc S hSU hS hodd hε hdeg hrank
      hminus)).toMonoidHom.comp
  (feomeg_blockCentralizer_commutatorAction n F S hε.1).rangeRestrict

private lemma feomeg_blockCentralizer_commutatorHom_injective
    (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (hn : 3 ≤ n) (f : ℕ)
    (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (Fin n ⊕ Fin n) F))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus n F)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F)))
      (Algebra.adjoin F (Units.val '' S)) ε)
    (hdeg : blockDegree (Algebra.adjoin F (Units.val '' S)) ε < 2) (hrank : ε.rank = 4)
    (hminus : ∀ x y : Fin n ⊕ Fin n → F, Matrix.mulVec ε x = x → Matrix.mulVec ε y = y →
      (Spin.quadPlus n F) x = 0 → (Spin.quadPlus n F) y = 0 → QuadraticMap.polar (Spin.quadPlus n F)
      x y = 0 → ¬ LinearIndependent F ![x, y]) :
    Function.Injective
      (feomeg_blockCentralizer_commutatorHom n F hn f hc S hSU hS hodd hε hdeg hrank hminus) := by
  classical
  have hle : ⁅glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε,
      glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε⁆ ≤
      glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  have h1eid : (1 - ε) * (1 - ε) = 1 - ε := by
    calc (1 - ε) * (1 - ε) = 1 * (1 - ε) - ε * (1 - ε) := by rw [Matrix.sub_mul]
      _ = (1 - ε) - (ε * 1 - ε * ε) := by rw [Matrix.one_mul, Matrix.mul_sub]
      _ = (1 - ε) - (ε - ε) := by rw [Matrix.mul_one, hε.2.1.eq]
      _ = 1 - ε := by abel
  have hact : Function.Injective
      (feomeg_blockCentralizer_commutatorAction n F S hε.1) := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro u hu
    have hu1 : (feomeg_blockCentralizer_commutatorAction n F S hε.1) u = 1 :=
      MonoidHom.mem_ker.mp hu
    have hspec := Classical.choose_spec (feomeg_blockCentralizer_action n F S hε.1)
    have hfixW : ∀ w : ↥(LinearMap.range (Matrix.mulVecLin ε)),
        Matrix.mulVec (Spin.spinMatrix (Spin.quadPlus n F)
          (u : ↥(spinGroup (Spin.quadPlus n F)))) (w : Fin n ⊕ Fin n → F) =
          (w : Fin n ⊕ Fin n → F) := by
      intro w
      have h := congrArg (fun f : (↥(LinearMap.range (Matrix.mulVecLin ε)) ≃ₗ[F]
          ↥(LinearMap.range (Matrix.mulVecLin ε))) => (f w : Fin n ⊕ Fin n → F)) hu1
      have h2 : ((feomeg_blockCentralizer_commutatorAction n F S hε.1) u w :
          Fin n ⊕ Fin n → F) = Matrix.mulVec (Spin.spinMatrix (Spin.quadPlus n F)
            (u : ↥(spinGroup (Spin.quadPlus n F)))) (w : Fin n ⊕ Fin n → F) := by
        change (((Classical.choose (feomeg_blockCentralizer_action n F S hε.1))
          (Subgroup.inclusion hle u)) w : Fin n ⊕ Fin n → F) =
          Matrix.mulVec (Spin.spinMatrix (Spin.quadPlus n F)
            (u : ↥(spinGroup (Spin.quadPlus n F)))) (w : Fin n ⊕ Fin n → F)
        exact hspec (Subgroup.inclusion hle u) w
      rw [h2] at h
      simpa using h
    apply Subtype.ext
    have hspin : (Spin.spinAction (Spin.quadPlus n F))
        (u : ↥(spinGroup (Spin.quadPlus n F))) = 1 := by
      apply LinearEquiv.ext
      intro v
      change (Spin.spinAction (Spin.quadPlus n F)
        (u : ↥(spinGroup (Spin.quadPlus n F)))) v = v
      have hv : v = Matrix.mulVec ε v + Matrix.mulVec (1 - ε) v := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]
        abel
      have heps : (Spin.spinAction (Spin.quadPlus n F)
          (u : ↥(spinGroup (Spin.quadPlus n F)))) (Matrix.mulVec ε v) = Matrix.mulVec ε v := by
        rw [← Spin.spinMatrix_mulVec]
        exact hfixW ⟨Matrix.mulVec ε v, LinearMap.mem_range.mpr ⟨v, rfl⟩⟩
      have hker : (Spin.spinAction (Spin.quadPlus n F)
          (u : ↥(spinGroup (Spin.quadPlus n F)))) (Matrix.mulVec (1 - ε) v) =
          Matrix.mulVec (1 - ε) v := by
        rw [← Spin.spinMatrix_mulVec]
        exact feomeg_blockCentralizer_fixes_ker (Spin.spinMatrix (Spin.quadPlus n F)) S
          (Subgroup.inclusion hle u) (Matrix.mulVec (1 - ε) v)
          (by rw [Matrix.mulVec_mulVec, h1eid])
      rw [hv, map_add, heps, hker]
    have hmat : (Spin.spinMatrix (Spin.quadPlus n F)
        (u : ↥(spinGroup (Spin.quadPlus n F))) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = 1 := by
      apply Matrix.mulVec_injective
      funext v
      rw [Matrix.one_mulVec, Spin.spinMatrix_mulVec]
      simpa using congrArg (fun f : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F) => f v) hspin
    have hkerM : (u : ↥(spinGroup (Spin.quadPlus n F))) ∈
        (Spin.spinMatrix (Spin.quadPlus n F)).ker := by
      rw [MonoidHom.mem_ker]
      exact Units.ext hmat
    rw [Spin.ker_spinMatrix_quadPlus_eq_bot (K := F) (n := n) (CharP.cast_eq_zero F 2)] at hkerM
    exact Subgroup.mem_bot.mp hkerM
  intro x y hxy
  let φ := Classical.choice (feomeg_blockCentralizer_commutatorAction_rangeIso n F hn f hc S hSU
    hS hodd hε hdeg hrank hminus)
  have hφ : Function.Injective φ := φ.injective
  have hxy' : φ ((feomeg_blockCentralizer_commutatorAction n F S hε.1).rangeRestrict x) =
      φ ((feomeg_blockCentralizer_commutatorAction n F S hε.1).rangeRestrict y) := by
    simpa [feomeg_blockCentralizer_commutatorHom, MonoidHom.comp_apply, φ] using hxy
  exact hact (congrArg Subtype.val (hφ hxy'))

private lemma feomeg_blockCentralizer_commutatorHom_surjective
    (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (hn : 3 ≤ n) (f : ℕ)
    (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (Fin n ⊕ Fin n) F))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus n F)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F)))
      (Algebra.adjoin F (Units.val '' S)) ε)
    (hdeg : blockDegree (Algebra.adjoin F (Units.val '' S)) ε < 2) (hrank : ε.rank = 4)
    (hminus : ∀ x y : Fin n ⊕ Fin n → F, Matrix.mulVec ε x = x → Matrix.mulVec ε y = y →
      (Spin.quadPlus n F) x = 0 → (Spin.quadPlus n F) y = 0 → QuadraticMap.polar (Spin.quadPlus n F)
      x y = 0 → ¬ LinearIndependent F ![x, y]) :
    Function.Surjective
      (feomeg_blockCentralizer_commutatorHom n F hn f hc S hSU hS hodd hε hdeg hrank hminus) := by
  intro y
  let φ := Classical.choice (feomeg_blockCentralizer_commutatorAction_rangeIso n F hn f hc S hSU
    hS hodd hε hdeg hrank hminus)
  obtain ⟨r, hr⟩ := φ.surjective y
  obtain ⟨x, hx⟩ :=
    (feomeg_blockCentralizer_commutatorAction n F S hε.1).rangeRestrict_surjective r
  refine ⟨x, ?_⟩
  rw [feomeg_blockCentralizer_commutatorHom, MonoidHom.comp_apply, hx]
  simpa [φ] using hr

private lemma feomeg_blockCentralizer_commutator_iso_dualPair
    (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (hn : 3 ≤ n) (f : ℕ)
    (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (Fin n ⊕ Fin n) F))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus n F)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F)))
      (Algebra.adjoin F (Units.val '' S)) ε)
    (hdeg : blockDegree (Algebra.adjoin F (Units.val '' S)) ε < 2) (hrank : ε.rank = 4)
    (hminus : ∀ x y : Fin n ⊕ Fin n → F, Matrix.mulVec ε x = x → Matrix.mulVec ε y = y →
      (Spin.quadPlus n F) x = 0 → (Spin.quadPlus n F) y = 0 → QuadraticMap.polar (Spin.quadPlus n F)
      x y = 0 → ¬ LinearIndependent F ![x, y]) :
    Nonempty (↥(⁅glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε,
      glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε⁆ :
        Subgroup ↥(spinGroup (Spin.quadPlus n F))) ≃*
      CFSG.Open.StatedSL 2 (GaloisField 2 (2 * f))) := by
  exact ⟨MulEquiv.ofBijective
    (feomeg_blockCentralizer_commutatorHom n F hn f hc S hSU hS hodd hε hdeg hrank hminus)
    ⟨feomeg_blockCentralizer_commutatorHom_injective n F hn f hc S hSU hS hodd hε hdeg hrank
        hminus,
      feomeg_blockCentralizer_commutatorHom_surjective n F hn f hc S hSU hS hodd hε hdeg hrank
        hminus⟩⟩

private lemma feomeg_statedProj_statedSL_two (f : ℕ) :
    Nonempty (CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 (GaloisField 2 (2 * f))) ≃*
      CFSG.Open.StatedSL 2 (GaloisField 2 (2 * f))) := by
  exact ⟨(QuotientGroup.quotientMulEquivOfEq
    (CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot
      (K := GaloisField 2 (2 * f)))).trans QuotientGroup.quotientBot⟩

private lemma feomeg_component_iso
    (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (hn : 3 ≤ n) (f : ℕ)
    (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (Fin n ⊕ Fin n) F))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus n F)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (Spin.quadPlus n F))}
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F)))
      (Algebra.adjoin F (Units.val '' S)) ε)
    (hJε : IsComponentOf J'
      ⁅glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε, glBlockCentralizer
      (Spin.spinMatrix (Spin.quadPlus n F)) S ε⁆)
    (hdeg : blockDegree (Algebra.adjoin F (Units.val '' S)) ε < 2) (hrank : ε.rank = 4)
    (hminus : ∀ x y : Fin n ⊕ Fin n → F, Matrix.mulVec ε x = x → Matrix.mulVec ε y = y →
      (Spin.quadPlus n F) x = 0 → (Spin.quadPlus n F) y = 0 → QuadraticMap.polar (Spin.quadPlus n F)
      x y = 0 → ¬ LinearIndependent F ![x, y]) :
    Nonempty (J' ⧸ Subgroup.center J' ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 (GaloisField 2 (2 * f)))) := by
  obtain ⟨φ⟩ :=
    feomeg_blockCentralizer_commutator_iso_dualPair n F hn f hc S hSU hS hodd hε hdeg hrank hminus
  let ψ := Classical.choice (feomeg_statedProj_statedSL_two f)
  have hf1 : 1 ≤ f := feomeg_one_le F hc
  have hcardK : 4 ≤ Nat.card (GaloisField 2 (2 * f)) := by
    rw [GaloisField.card (p := 2) (n := 2 * f) (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hKsimple : IsSimpleGroup ↥(CFSG.Open.StatedSL 2 (GaloisField 2 (2 * f))) := by
    have hsp : IsSimpleGroup
        (CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 (GaloisField 2 (2 * f)))) :=
      CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL (d := 2)
        (GaloisField 2 (2 * f)) le_rfl (Or.inr (by omega)) (Or.inr (by omega))
    exact (MulEquiv.isSimpleGroup_congr ψ).mp hsp
  have hK₀simple : IsSimpleGroup
      ↥⁅glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε,
        glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε⁆ :=
    (MulEquiv.isSimpleGroup_congr φ).mpr hKsimple
  have hJ'ne : J' ≠ ⊥ := by
    intro hbot
    haveI : Nontrivial (↥J' ⧸ Subgroup.center ↥J') := hJε.2.2.2.toNontrivial
    haveI : Subsingleton (↥J' ⧸ Subgroup.center ↥J') := by rw [hbot]; infer_instance
    exact (not_subsingleton (↥J' ⧸ Subgroup.center ↥J')) inferInstance
  have hJ'eq : J' = ⁅glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε,
      glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε⁆ := by
    rcases CFSG.Assembly.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hJε.2.1 hK₀simple with h | h
    · exact absurd h hJ'ne
    · exact h
  have hZbot : Subgroup.center ↥(CFSG.Open.StatedSL 2 (GaloisField 2 (2 * f))) = ⊥ := by
    rw [← Subgroup.map_center_eq
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 (GaloisField 2 (2 * f))),
      CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars 2 (GaloisField 2 (2 * f)),
      CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot]
  have hZbotK : Subgroup.center ↥⁅glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε,
      glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε⁆ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    apply φ.injective
    rw [map_one]
    have hmem : φ x ∈ (Subgroup.center
        ↥⁅glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε,
          glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε⁆).map φ := ⟨x, hx, rfl⟩
    rw [Subgroup.map_center_eq φ, hZbot, Subgroup.mem_bot] at hmem
    exact hmem
  rw [hJ'eq]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZbotK).trans
    ((QuotientGroup.quotientBot).trans (φ.trans ψ.symm))⟩

theorem ggSixLSevenFieldExtCase_omegaFourMinus_POmegaPlus (n : ℕ) (F : Type) [Field F]
    (hn : 3 ≤ n) (f : ℕ) (hc : Nat.card F = 2 ^ f)
    {X : Type} [Group X] (ψ : ↥(spinGroup (Spin.quadPlus n F)) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _)
    (S : Set (GL (Fin n ⊕ Fin n) F))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus n F)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s)) {J' : Subgroup ↥(spinGroup (Spin.quadPlus n F))}
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F)))
      (Algebra.adjoin F (Units.val '' S)) ε)
    (hJε : IsComponentOf J'
      ⁅glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε, glBlockCentralizer
      (Spin.spinMatrix (Spin.quadPlus n F)) S ε⁆)
    (hdeg : blockDegree (Algebra.adjoin F (Units.val '' S)) ε < 2) (hrank : ε.rank = 4)
    (hminus : ∀ x y : Fin n ⊕ Fin n → F, Matrix.mulVec ε x = x → Matrix.mulVec ε y = y →
      (Spin.quadPlus n F) x = 0 → (Spin.quadPlus n F) y = 0 → QuadraticMap.polar (Spin.quadPlus n F)
      x y = 0 → ¬ LinearIndependent F ![x, y]) :
    GGSixLSevenFieldExtCase (J'.map ψ) .POmegaPlus f := by
  classical
  have hf : 1 ≤ f := feomeg_one_le F hc
  haveI : Finite F := feomeg_finite F hc
  haveI : CharP F 2 := feomeg_charP F hc
  obtain ⟨η⟩ := feomeg_component_iso n F hn f hc S hSU hS hodd hε hJε hdeg hrank hminus
  obtain ⟨ξ⟩ := feomeg_quotientCenter ψ hψ (J' := J') hJε.2.2.1
  refine ⟨.PSL, 2, 2 * f, ?_, ?_, ?_⟩
  · omega
  · refine Or.inl ⟨by decide, ?_⟩
    refine ⟨feomeg_admissible f hf, GaloisField 2 (2 * f), inferInstance, inferInstance, ?_, ?_⟩
    · rw [GaloisField.card 2 (2 * f) (by omega)]
    · exact ⟨ξ.symm.trans η⟩
  · rintro ⟨-, -, h | h⟩ <;> exact absurd h (by decide)

end CFSG.StandardType.ClassicalPosition
