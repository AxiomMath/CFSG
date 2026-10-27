module

public import CFSG.RankThree.GF2n.Stroth80.Sec97FiveLineX
import CFSG.RankThree.GF2n.Smith81.Sec220TvLemmas
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Schur

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.G11.P3Ortho.Om4
open scoped commutatorElement Matrix

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem exists_mem_inf_not_mem_CN_X (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y) :
    ∃ e ∈ LB M Q B ⊓ X, e ∉ hc.CN t := by
  by_contra hno
  push Not at hno
  have hhead := sec97Head_of h34 h311a G M Q Z B hc n t hs X Y hsplit
  have hleN : LB M Q B ⊓ hc.CN t ≤ LB M Q B ⊓ X := inf_le_inf_left _ hhead.1
  have hle : LB M Q B ⊓ X ≤ LB M Q B ⊓ hc.CN t := fun e he => ⟨he.1, hno e he⟩
  have hEq : LB M Q B ⊓ X = LB M Q B ⊓ hc.CN t := le_antisymm hle hleN
  have h1 : (LB M Q B ⊓ hc.CN t).relIndex (LB M Q B ⊓ X) = 1 := by
    rw [hEq]
    exact Subgroup.relIndex_eq_one.mpr le_rfl
  rw [hhead.2] at h1
  have := hc.hyp.q4
  omega

private theorem right_action_data (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2]
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K}
    {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 2 ⊕ Fin 2 → K)}
    {u : Fin 2 ⊕ Fin 2 → K}
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G))
    (hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔
        ∃ c : K, x = c • u)
    {a b : Fin 2 → K} (ha : a ≠ 0) (hb : b ≠ 0) (hu : toMat K u = Matrix.vecMulVec a b)
    (hXeq : (X.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = rightF K)
    {e : G} (he : e ∈ LB M Q B ⊓ X) (heR : e ∈ Rt M (LB M Q B) t) :
    ∃ (Bmat : Matrix.SpecialLinearGroup (Fin 2) K) (C : Matrix (Fin 2) (Fin 2) K),
      rho' K (1, Bmat) = Ψ K (φ ⟨e, heR⟩) ∧
      C = ((Bmat⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ∧
      C.det = 1 ∧ b ᵥ* C = b ∧
      (C = 1 ∨ ∃ u0 : Fin 2 → K, u0 ≠ 0 ∧ 1 - C = Matrix.vecMulVec u0 b) := by
  classical
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt hs.toSec5.mem
  have hHX : ∀ h, h ∈ rightF K ↔
      ∃ s : ↥(Rt M (LB M Q B) t), (s : G) ∈ X ∧ Ψ K (φ s) = h := by
    intro h
    rw [← hXeq]
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  have heMem : Ψ K (φ ⟨e, heR⟩) ∈ rightF K :=
    (hHX _).mpr ⟨⟨e, heR⟩, he.2, rfl⟩
  obtain ⟨Bmat, hB0⟩ := heMem
  have hB : rho' K (1, Bmat) = Ψ K (φ ⟨e, heR⟩) := by simpa using hB0
  have hfix_u : Ψ K (φ ⟨e, heR⟩) (toMat K u) = toMat K u :=
    apply_toMat_u_eq hc φ ψ hψ hnorm u hBiff he.1 heR
  have hMu : toMat K u * (((Bmat⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K)) = toMat K u := by
    rw [← rho'_inr_apply, hB]
    exact hfix_u
  have hbC : b ᵥ* (((Bmat⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K)) = b := by
    have h := hMu
    rw [hu, Matrix.vecMulVec_mul] at h
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact ha (funext hcon)
    funext j
    have h' := congrFun (congrFun h i) j
    simp only [Matrix.vecMulVec_apply] at h'
    exact mul_left_cancel₀ hi h'
  let C : Matrix (Fin 2) (Fin 2) K := ((Bmat⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K)
  have hCdet : C.det = 1 := by
    have := (Bmat⁻¹).det_coe
    simpa [C] using this
  have hbC' : b ᵥ* C = b := by simpa [C] using hbC
  have hCcase : C = 1 ∨ ∃ u0 : Fin 2 → K, u0 ≠ 0 ∧ 1 - C = Matrix.vecMulVec u0 b := by
    by_cases hC1 : C = 1
    · exact Or.inl hC1
    · obtain ⟨u0, hu0, hD⟩ := exists_vecMulVec_one_sub_of_vecMul_eq_self hCdet hb hbC' hC1
      exact Or.inr ⟨u0, hu0, hD⟩
  exact ⟨Bmat, C, hB, rfl, hCdet, hbC', hCcase⟩

private theorem left_action_data (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2]
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K}
    {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 2 ⊕ Fin 2 → K)}
    {u : Fin 2 ⊕ Fin 2 → K}
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G))
    (hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔
        ∃ c : K, x = c • u)
    {a b : Fin 2 → K} (ha : a ≠ 0) (hb : b ≠ 0) (hu : toMat K u = Matrix.vecMulVec a b)
    (hXeq : (X.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = leftF K)
    {e : G} (he : e ∈ LB M Q B ⊓ X) (heR : e ∈ Rt M (LB M Q B) t) :
    ∃ Amat : Matrix.SpecialLinearGroup (Fin 2) K,
      rho' K (Amat, 1) = Ψ K (φ ⟨e, heR⟩) ∧
      ((Amat : Matrix (Fin 2) (Fin 2) K) = 1 ∨
        ∃ u0 : Fin 2 → K, u0 ≠ 0 ∧
          (Amat : Matrix (Fin 2) (Fin 2) K) - 1 = Matrix.vecMulVec a u0) := by
  classical
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt hs.toSec5.mem
  have hHX : ∀ h, h ∈ leftF K ↔
      ∃ s : ↥(Rt M (LB M Q B) t), (s : G) ∈ X ∧ Ψ K (φ s) = h := by
    intro h
    rw [← hXeq]
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  have heMem : Ψ K (φ ⟨e, heR⟩) ∈ leftF K :=
    (hHX _).mpr ⟨⟨e, heR⟩, he.2, rfl⟩
  obtain ⟨Amat, hA0⟩ := heMem
  have hA : rho' K (Amat, 1) = Ψ K (φ ⟨e, heR⟩) := by simpa using hA0
  have hfix_u : Ψ K (φ ⟨e, heR⟩) (toMat K u) = toMat K u :=
    apply_toMat_u_eq hc φ ψ hψ hnorm u hBiff he.1 heR
  have hAu : (Amat : Matrix (Fin 2) (Fin 2) K) * toMat K u = toMat K u := by
    rw [← rho'_inl_apply, hA]
    exact hfix_u
  have hAa : (Amat : Matrix (Fin 2) (Fin 2) K) *ᵥ a = a := by
    have h := hAu
    rw [hu, Matrix.mul_vecMulVec] at h
    obtain ⟨j, hj⟩ : ∃ j, b j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hb (funext hcon)
    funext i
    have h' := congrFun (congrFun h i) j
    simp only [Matrix.vecMulVec_apply] at h'
    exact mul_right_cancel₀ hj h'
  let C : Matrix (Fin 2) (Fin 2) K := (Amat : Matrix (Fin 2) (Fin 2) K)ᵀ
  have hCb : a ᵥ* C = a := by
    rw [Matrix.vecMul_transpose]
    exact hAa
  have hCdet : C.det = 1 := by
    have := Amat.det_coe
    simpa [C] using this
  by_cases hC1 : C = 1
  · refine ⟨Amat, hA, Or.inl ?_⟩
    have h := congrArg Matrix.transpose hC1
    simpa [C] using h
  · obtain ⟨u0, hu0, hD⟩ := exists_vecMulVec_one_sub_of_vecMul_eq_self hCdet ha hCb hC1
    have hD' : 1 - (Amat : Matrix (Fin 2) (Fin 2) K) = Matrix.vecMulVec a u0 := by
      have h := congrArg Matrix.transpose hD
      simpa [C, Matrix.transpose_sub, Matrix.transpose_vecMulVec] using h
    have hA1eq : (Amat : Matrix (Fin 2) (Fin 2) K) - 1 =
        1 - (Amat : Matrix (Fin 2) (Fin 2) K) := by
      ext i j
      rw [Matrix.sub_apply, Matrix.sub_apply, CharTwo.sub_eq_add, CharTwo.sub_eq_add]
      exact add_comm _ _
    exact ⟨Amat, hA, Or.inr ⟨u0, hu0, hA1eq.trans hD'⟩⟩

private theorem comm_le_left (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K}
    {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 2 ⊕ Fin 2 → K)}
    {u : Fin 2 ⊕ Fin 2 → K}
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G))
    (hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔
        ∃ c : K, x = c • u)
    {a b : Fin 2 → K} (ha : a ≠ 0) (hb : b ≠ 0) (hu : toMat K u = Matrix.vecMulVec a b)
    (hYeq : (Y.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = leftF K)
    (hXeq : (X.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = rightF K) :
    ⁅LB M Q B ⊓ X, Vt M (LB M Q B) B Z t⁆ ≤ Uline Z B Y := by
  classical
  have hXR : X ≤ Rt M (LB M Q B) t := by
    obtain ⟨⟨-, hXR, -, -, -, -, -⟩, -, -⟩ := hsplit
    exact hXR
  have hYR : Y ≤ Rt M (LB M Q B) t := by
    obtain ⟨⟨-, -, -, hYR, -, -, -⟩, -, -⟩ := hsplit
    exact hYR
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hHY : ∀ h, h ∈ leftF K ↔
      ∃ s : ↥(Rt M (LB M Q B) t), (s : G) ∈ Y ∧ Ψ K (φ s) = h := by
    intro h
    rw [← hYeq]
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  have hYmem := uline_mem_iff ψ φ hψ hnorm hYR hZV hBV u hBiff hHY
    (actsNat_leftF_outerL (b := b) hb) ha hu
  rw [Subgroup.commutator_le]
  intro e he v hv
  obtain ⟨Bmat, C, hB, hCdef, hCdet, hbC, hCcase⟩ :=
    right_action_data hc hs hψ hnorm hBiff ha hb hu hXeq he (hXR he.2)
  have hc := cmat_comm_eq φ ψ hψ hnorm ⟨e, hXR he.2⟩ ⟨v, hv⟩
  have hΨM : Ψ K (φ ⟨e, hXR he.2⟩) (cmat ψ ⟨v, hv⟩) = cmat ψ ⟨v, hv⟩ * C := by
    rw [← hB, rho'_inr_apply, ← hCdef]
  have hcoord : cmat ψ ⟨⁅e, v⁆, comm_mem_of_le_normalizer hnorm ⟨e, hXR he.2⟩ ⟨v, hv⟩⟩ =
      cmat ψ ⟨v, hv⟩ * (C - 1) := by
    rw [hc, hΨM, Matrix.mul_sub, Matrix.mul_one]
  rcases hCcase with hC1 | ⟨u0, hu0, hD⟩
  · have hzero : cmat ψ ⟨⁅e, v⁆, comm_mem_of_le_normalizer hnorm ⟨e, hXR he.2⟩ ⟨v, hv⟩⟩ =
        0 := by rw [hcoord, hC1, sub_self, Matrix.mul_zero]
    exact Z_le_Uline Z B Y ((cmat_eq_zero_iff ψ _).mp hzero)
  · have hC1eq : C - 1 = 1 - C := by
      ext i j
      rw [Matrix.sub_apply, Matrix.sub_apply, CharTwo.sub_eq_add, CharTwo.sub_eq_add]
      exact add_comm _ _
    have hcoord' : cmat ψ ⟨⁅e, v⁆, comm_mem_of_le_normalizer hnorm ⟨e, hXR he.2⟩ ⟨v, hv⟩⟩ =
        Matrix.vecMulVec (cmat ψ ⟨v, hv⟩ *ᵥ u0) b := by
      rw [hcoord, hC1eq, hD, Matrix.mul_vecMulVec]
    refine (hYmem _).mpr ⟨comm_mem_of_le_normalizer hnorm ⟨e, hXR he.2⟩ ⟨v, hv⟩, ?_⟩
    exact ⟨_, hcoord'.symm⟩

private theorem comm_le_right (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K}
    {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 2 ⊕ Fin 2 → K)}
    {u : Fin 2 ⊕ Fin 2 → K}
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G))
    (hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔
        ∃ c : K, x = c • u)
    {a b : Fin 2 → K} (ha : a ≠ 0) (hb : b ≠ 0) (hu : toMat K u = Matrix.vecMulVec a b)
    (hYeq : (Y.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = rightF K)
    (hXeq : (X.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = leftF K) :
    ⁅LB M Q B ⊓ X, Vt M (LB M Q B) B Z t⁆ ≤ Uline Z B Y := by
  classical
  have hXR : X ≤ Rt M (LB M Q B) t := by
    obtain ⟨⟨-, hXR, -, -, -, -, -⟩, -, -⟩ := hsplit
    exact hXR
  have hYR : Y ≤ Rt M (LB M Q B) t := by
    obtain ⟨⟨-, -, -, hYR, -, -, -⟩, -, -⟩ := hsplit
    exact hYR
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hHY : ∀ h, h ∈ rightF K ↔
      ∃ s : ↥(Rt M (LB M Q B) t), (s : G) ∈ Y ∧ Ψ K (φ s) = h := by
    intro h
    rw [← hYeq]
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  have hYmem := uline_mem_iff ψ φ hψ hnorm hYR hZV hBV u hBiff hHY
    (actsNat_rightF_outerR (a := a) ha) hb hu
  rw [Subgroup.commutator_le]
  intro e he v hv
  obtain ⟨Amat, hA, hAcases⟩ :=
    left_action_data hc hs hψ hnorm hBiff ha hb hu hXeq he (hXR he.2)
  have hc := cmat_comm_eq φ ψ hψ hnorm ⟨e, hXR he.2⟩ ⟨v, hv⟩
  have hΨM : Ψ K (φ ⟨e, hXR he.2⟩) (cmat ψ ⟨v, hv⟩) =
      (Amat : Matrix (Fin 2) (Fin 2) K) * cmat ψ ⟨v, hv⟩ := by
    rw [← hA, rho'_inl_apply]
  have hcoord : cmat ψ ⟨⁅e, v⁆, comm_mem_of_le_normalizer hnorm ⟨e, hXR he.2⟩ ⟨v, hv⟩⟩ =
      ((Amat : Matrix (Fin 2) (Fin 2) K) - 1) * cmat ψ ⟨v, hv⟩ := by
    rw [hc, hΨM, Matrix.sub_mul, Matrix.one_mul]
  rcases hAcases with hA1 | ⟨u0, hu0, hD⟩
  · have hzero : cmat ψ ⟨⁅e, v⁆, comm_mem_of_le_normalizer hnorm ⟨e, hXR he.2⟩ ⟨v, hv⟩⟩ =
        0 := by rw [hcoord, hA1, sub_self, Matrix.zero_mul]
    exact Z_le_Uline Z B Y ((cmat_eq_zero_iff ψ _).mp hzero)
  · have hcoord' : cmat ψ ⟨⁅e, v⁆, comm_mem_of_le_normalizer hnorm ⟨e, hXR he.2⟩ ⟨v, hv⟩⟩ =
        Matrix.vecMulVec a (u0 ᵥ* cmat ψ ⟨v, hv⟩) := by
      rw [hcoord, hD, Matrix.vecMulVec_mul]
    refine (hYmem _).mpr ⟨comm_mem_of_le_normalizer hnorm ⟨e, hXR he.2⟩ ⟨v, hv⟩, ?_⟩
    exact ⟨_, hcoord'.symm⟩


private theorem right_action_data_ne (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2]
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K}
    {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 2 ⊕ Fin 2 → K)}
    {u : Fin 2 ⊕ Fin 2 → K}
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G))
    (hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔
        ∃ c : K, x = c • u)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    {a b : Fin 2 → K} (ha : a ≠ 0) (hb : b ≠ 0) (hu : toMat K u = Matrix.vecMulVec a b)
    (hXeq : (X.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = rightF K)
    {e : G} (he : e ∈ LB M Q B ⊓ X) (heR : e ∈ Rt M (LB M Q B) t) (heN : e ∉ hc.CN t) :
    ∃ (Bmat : Matrix.SpecialLinearGroup (Fin 2) K) (C : Matrix (Fin 2) (Fin 2) K)
      (u0 : Fin 2 → K),
      rho' K (1, Bmat) = Ψ K (φ ⟨e, heR⟩) ∧
      C = ((Bmat⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ∧
      C ≠ 1 ∧ u0 ≠ 0 ∧ 1 - C = Matrix.vecMulVec u0 b := by
  classical
  obtain ⟨Bmat, C, hB, hCdef, -, -, hCcase⟩ :=
    right_action_data hc hs hψ hnorm hBiff ha hb hu hXeq he heR
  have hφne : φ ⟨e, heR⟩ ≠ 1 := by
    intro h1
    apply heN
    have hmem : (⟨e, heR⟩ : ↥(Rt M (LB M Q B) t)) ∈ φ.ker := h1
    rwa [hker, Subgroup.mem_subgroupOf] at hmem
  have hC1 : C ≠ 1 := by
    intro hCeq
    apply hφne
    apply (Ψ K).injective
    have hC1' : ((Bmat⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← hCdef]
      exact hCeq
    have hC1'' : Bmat⁻¹ = 1 := Subtype.ext hC1'
    have hB1 : Bmat = 1 := inv_eq_one.mp hC1''
    have hrho1 : rho' K (1, Bmat) = 1 := by
      rw [hB1]
      exact map_one (rho' K)
    rw [← hB, hrho1]
    exact (map_one (Ψ K)).symm
  obtain ⟨u0, hu0, hD⟩ := hCcase.resolve_left hC1
  exact ⟨Bmat, C, u0, hB, hCdef, hC1, hu0, hD⟩

private theorem left_action_data_ne (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2]
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K}
    {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 2 ⊕ Fin 2 → K)}
    {u : Fin 2 ⊕ Fin 2 → K}
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G))
    (hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔
        ∃ c : K, x = c • u)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    {a b : Fin 2 → K} (ha : a ≠ 0) (hb : b ≠ 0) (hu : toMat K u = Matrix.vecMulVec a b)
    (hXeq : (X.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = leftF K)
    {e : G} (he : e ∈ LB M Q B ⊓ X) (heR : e ∈ Rt M (LB M Q B) t) (heN : e ∉ hc.CN t) :
    ∃ (Amat : Matrix.SpecialLinearGroup (Fin 2) K) (u0 : Fin 2 → K),
      rho' K (Amat, 1) = Ψ K (φ ⟨e, heR⟩) ∧
      (Amat : Matrix (Fin 2) (Fin 2) K) ≠ 1 ∧ u0 ≠ 0 ∧
      (Amat : Matrix (Fin 2) (Fin 2) K) - 1 = Matrix.vecMulVec a u0 := by
  classical
  obtain ⟨Amat, hA, hAcases⟩ :=
    left_action_data hc hs hψ hnorm hBiff ha hb hu hXeq he heR
  have hφne : φ ⟨e, heR⟩ ≠ 1 := by
    intro h1
    apply heN
    have hmem : (⟨e, heR⟩ : ↥(Rt M (LB M Q B) t)) ∈ φ.ker := h1
    rwa [hker, Subgroup.mem_subgroupOf] at hmem
  have hAne : (Amat : Matrix (Fin 2) (Fin 2) K) ≠ 1 := by
    intro hA1
    apply hφne
    apply (Ψ K).injective
    have hA1' : Amat = 1 := Subtype.ext hA1
    have hrho1 : rho' K (Amat, 1) = 1 := by
      rw [hA1']
      exact map_one (rho' K)
    rw [← hA, hrho1]
    exact (map_one (Ψ K)).symm
  obtain ⟨u0, hu0, hD⟩ := hAcases.resolve_left hAne
  exact ⟨Amat, u0, hA, hAne, hu0, hD⟩

private theorem uline_le_comm_left (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K}
    {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 2 ⊕ Fin 2 → K)}
    {u : Fin 2 ⊕ Fin 2 → K}
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G))
    (hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔
        ∃ c : K, x = c • u)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    {a b : Fin 2 → K} (ha : a ≠ 0) (hb : b ≠ 0) (hu : toMat K u = Matrix.vecMulVec a b)
    (hYeq : (Y.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = leftF K)
    (hXeq : (X.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = rightF K) :
    Uline Z B Y ≤ ⁅LB M Q B ⊓ X, Vt M (LB M Q B) B Z t⁆ ⊔ Z := by
  classical
  have hXR : X ≤ Rt M (LB M Q B) t := by
    obtain ⟨⟨-, hXR, -, -, -, -, -⟩, -, -⟩ := hsplit
    exact hXR
  have hYR : Y ≤ Rt M (LB M Q B) t := by
    obtain ⟨⟨-, -, -, hYR, -, -, -⟩, -, -⟩ := hsplit
    exact hYR
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hHY : ∀ h, h ∈ leftF K ↔
      ∃ s : ↥(Rt M (LB M Q B) t), (s : G) ∈ Y ∧ Ψ K (φ s) = h := by
    intro h
    rw [← hYeq]
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  have hYmem := uline_mem_iff ψ φ hψ hnorm hYR hZV hBV u hBiff hHY
    (actsNat_leftF_outerL (b := b) hb) ha hu
  obtain ⟨e, he, heN⟩ := exists_mem_inf_not_mem_CN_X h34 h311a hc hs hsplit
  obtain ⟨Bmat, C, u0, hB, hCdef, hC1, hu0, hD⟩ :=
    right_action_data_ne hc hs hψ hnorm hBiff hker ha hb hu hXeq he (hXR he.2) heN
  have hC1eq : C - 1 = 1 - C := by
    ext i j
    rw [Matrix.sub_apply, Matrix.sub_apply, CharTwo.sub_eq_add, CharTwo.sub_eq_add]
    exact add_comm _ _
  intro x hx
  obtain ⟨hxV, hxrange⟩ := (hYmem x).mp hx
  obtain ⟨w, hw⟩ := hxrange
  obtain ⟨r, hr0⟩ := Smith81.exists_dotProduct_one hu0
  have hr : r ⬝ᵥ u0 = 1 := by rwa [dotProduct_comm] at hr0
  have hM : Matrix.vecMulVec w r * (1 - C) = Matrix.vecMulVec w b := by
    rw [hD, Matrix.vecMulVec_mul, Matrix.vecMul_vecMulVec, hr, one_smul]
  obtain ⟨v, hv⟩ := exists_secVec_eq ψ ((toMat K).symm (Matrix.vecMulVec w r))
  have hcmatv : cmat ψ v = Matrix.vecMulVec w r := by
    unfold cmat
    rw [hv, LinearEquiv.apply_symm_apply]
  have hc := cmat_comm_eq φ ψ hψ hnorm ⟨e, hXR he.2⟩ v
  have hΨM : Ψ K (φ ⟨e, hXR he.2⟩) (cmat ψ v) = cmat ψ v * C := by
    rw [← hB, rho'_inr_apply, ← hCdef]
  have hcoord : cmat ψ ⟨⁅e, (v : G)⁆, comm_mem_of_le_normalizer hnorm ⟨e, hXR he.2⟩ v⟩ =
      cmat ψ v * (C - 1) := by
    rw [hc, hΨM, Matrix.mul_sub, Matrix.mul_one]
  have hcoordx : cmat ψ ⟨⁅e, (v : G)⁆, comm_mem_of_le_normalizer hnorm ⟨e, hXR he.2⟩ v⟩ =
      cmat ψ ⟨x, hxV⟩ := by
    rw [hcoord, hC1eq, hcmatv, hM]
    exact hw
  have hxZ : x * (⁅e, (v : G)⁆)⁻¹ ∈ Z :=
    (cmat_eq_iff ψ ⟨x, hxV⟩ ⟨⁅e, (v : G)⁆,
      comm_mem_of_le_normalizer hnorm ⟨e, hXR he.2⟩ v⟩).mp hcoordx.symm
  have hE : ⁅e, (v : G)⁆ ∈ ⁅LB M Q B ⊓ X, Vt M (LB M Q B) B Z t⁆ :=
    Subgroup.commutator_mem_commutator he v.2
  rw [sup_comm]
  have hzc : (x * (⁅e, (v : G)⁆)⁻¹) * ⁅e, (v : G)⁆ = x := by group
  rw [← hzc]
  exact Subgroup.mul_mem_sup hxZ hE

private theorem uline_le_comm_right (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K}
    {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 2 ⊕ Fin 2 → K)}
    {u : Fin 2 ⊕ Fin 2 → K}
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G))
    (hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔
        ∃ c : K, x = c • u)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    {a b : Fin 2 → K} (ha : a ≠ 0) (hb : b ≠ 0) (hu : toMat K u = Matrix.vecMulVec a b)
    (hYeq : (Y.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = rightF K)
    (hXeq : (X.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = leftF K) :
    Uline Z B Y ≤ ⁅LB M Q B ⊓ X, Vt M (LB M Q B) B Z t⁆ ⊔ Z := by
  classical
  have hXR : X ≤ Rt M (LB M Q B) t := by
    obtain ⟨⟨-, hXR, -, -, -, -, -⟩, -, -⟩ := hsplit
    exact hXR
  have hYR : Y ≤ Rt M (LB M Q B) t := by
    obtain ⟨⟨-, -, -, hYR, -, -, -⟩, -, -⟩ := hsplit
    exact hYR
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hHY : ∀ h, h ∈ rightF K ↔
      ∃ s : ↥(Rt M (LB M Q B) t), (s : G) ∈ Y ∧ Ψ K (φ s) = h := by
    intro h
    rw [← hYeq]
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  have hYmem := uline_mem_iff ψ φ hψ hnorm hYR hZV hBV u hBiff hHY
    (actsNat_rightF_outerR (a := a) ha) hb hu
  obtain ⟨e, he, heN⟩ := exists_mem_inf_not_mem_CN_X h34 h311a hc hs hsplit
  obtain ⟨Amat, u0, hA, hAne, hu0, hD⟩ :=
    left_action_data_ne hc hs hψ hnorm hBiff hker ha hb hu hXeq he (hXR he.2) heN
  intro x hx
  obtain ⟨hxV, hxrange⟩ := (hYmem x).mp hx
  obtain ⟨w, hw⟩ := hxrange
  obtain ⟨r, hr⟩ := Smith81.exists_dotProduct_one hu0
  have hM : (((Amat : Matrix (Fin 2) (Fin 2) K) - 1) * Matrix.vecMulVec r w) =
      Matrix.vecMulVec a w := by
    rw [hD, Matrix.vecMulVec_mul, Matrix.vecMul_vecMulVec, hr, one_smul]
  obtain ⟨v, hv⟩ := exists_secVec_eq ψ ((toMat K).symm (Matrix.vecMulVec r w))
  have hcmatv : cmat ψ v = Matrix.vecMulVec r w := by
    unfold cmat
    rw [hv, LinearEquiv.apply_symm_apply]
  have hc := cmat_comm_eq φ ψ hψ hnorm ⟨e, hXR he.2⟩ v
  have hΨM : Ψ K (φ ⟨e, hXR he.2⟩) (cmat ψ v) =
      (Amat : Matrix (Fin 2) (Fin 2) K) * cmat ψ v := by
    rw [← hA, rho'_inl_apply]
  have hcoord : cmat ψ ⟨⁅e, (v : G)⁆, comm_mem_of_le_normalizer hnorm ⟨e, hXR he.2⟩ v⟩ =
      ((Amat : Matrix (Fin 2) (Fin 2) K) - 1) * cmat ψ v := by
    rw [hc, hΨM, Matrix.sub_mul, Matrix.one_mul]
  have hcoordx : cmat ψ ⟨⁅e, (v : G)⁆, comm_mem_of_le_normalizer hnorm ⟨e, hXR he.2⟩ v⟩ =
      cmat ψ ⟨x, hxV⟩ := by
    rw [hcoord, hcmatv, hM]
    exact hw
  have hxZ : x * (⁅e, (v : G)⁆)⁻¹ ∈ Z :=
    (cmat_eq_iff ψ ⟨x, hxV⟩ ⟨⁅e, (v : G)⁆,
      comm_mem_of_le_normalizer hnorm ⟨e, hXR he.2⟩ v⟩).mp hcoordx.symm
  have hE : ⁅e, (v : G)⁆ ∈ ⁅LB M Q B ⊓ X, Vt M (LB M Q B) B Z t⁆ :=
    Subgroup.commutator_mem_commutator he v.2
  rw [sup_comm]
  have hzc : (x * (⁅e, (v : G)⁆)⁻¹) * ⁅e, (v : G)⁆ = x := by group
  rw [← hzc]
  exact Subgroup.mul_mem_sup hxZ hE

section ComplementAlgebra

variable {K : Type} [Field K]

private theorem exists_not_mem_span_singleton {b : Fin 2 → K} (hb : b ≠ 0) :
    ∃ b' : Fin 2 → K, b' ≠ 0 ∧ b' ∉ (K ∙ b : Submodule K (Fin 2 → K)) := by
  by_cases h0 : b 0 = 0
  · have h1 : b 1 ≠ 0 := by
      intro h1
      exact hb (funext fun i => by fin_cases i <;> simpa [h0, h1])
    refine ⟨Pi.single 0 1, ?_, ?_⟩
    · simp
    · rw [Submodule.mem_span_singleton]
      rintro ⟨c, hc⟩
      have := congrFun hc 0
      simp [h0] at this
  · refine ⟨Pi.single 1 1, ?_, ?_⟩
    · simp
    · rw [Submodule.mem_span_singleton]
      rintro ⟨c, hc⟩
      have hc0 := congrFun hc 0
      simp [Pi.single_apply, h0] at hc0
      have hc1 := congrFun hc 1
      simp [Pi.single_apply, hc0] at hc1

private theorem eq_zero_of_vecMulVec_eq_of_not_mem_span {b b' w w' : Fin 2 → K}
    (hb : b ≠ 0) (hb' : b' ∉ (K ∙ b : Submodule K (Fin 2 → K)))
    (h : Matrix.vecMulVec w b = Matrix.vecMulVec w' b') : w = 0 := by
  funext i
  by_contra hi
  apply hb'
  rw [Submodule.mem_span_singleton]
  have hb'0 : b' ≠ 0 := by
    intro h0
    exact hb' (h0 ▸ Submodule.zero_mem _)
  have hrow : w i • b = w' i • b' := by
    funext j
    have := congrFun (congrFun h i) j
    simpa [Matrix.vecMulVec_apply, smul_eq_mul] using this
  by_cases hwi : w' i = 0
  · have hzero : w i • b = 0 := by rw [hrow, hwi, zero_smul]
    exfalso
    exact hb ((smul_eq_zero.mp hzero).resolve_left hi)
  · refine ⟨w i / w' i, ?_⟩
    have h1 := congrArg (fun v => (w' i)⁻¹ • v) hrow
    rw [smul_smul, smul_smul, inv_mul_cancel₀ hwi, one_smul] at h1
    rw [← h1]
    congr 1
    field_simp [hwi]

end ComplementAlgebra


theorem comm_Vt_E_sup_eq (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) :
    ⁅Vt M (LB M Q B) B Z t, LB M Q B ⊓ X⁆ ⊔ Z = Uline Z B Y := by
  classical
  obtain ⟨K, fK, finK, chK, hn, φ, ψ, u, hK, hrange, hker, hnorm, hψ, hBiff, hW, hdet, hu0⟩ :=
    sec9_coord h34 hc hs
  haveI := hn
  haveI : CharP K 2 := chK
  obtain ⟨a, b, ha, hb, hu⟩ := exists_vecMulVec_of_det_eq_zero hdet hu0
  have hfac := sec97_factor_pair h34 h311a hc hs hsplit hK φ hrange hker
  rw [Subgroup.commutator_comm]
  rcases hfac with ⟨hYeq, hXeq⟩ | ⟨hYeq, hXeq⟩
  · exact le_antisymm
      (sup_le (comm_le_left hc hs hsplit hψ hnorm hBiff ha hb hu hYeq hXeq)
        (Z_le_Uline Z B Y))
      (uline_le_comm_left h34 h311a hc hs hsplit hψ hnorm hBiff hker ha hb hu hYeq hXeq)
  · exact le_antisymm
      (sup_le (comm_le_right hc hs hsplit hψ hnorm hBiff ha hb hu hYeq hXeq)
        (Z_le_Uline Z B Y))
      (uline_le_comm_right h34 h311a hc hs hsplit hψ hnorm hBiff hker ha hb hu hYeq hXeq)

private theorem sup_uline_conj_eq (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {Y : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2]
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 2 ⊕ Fin 2 → K)}
    {x : G} (hxR : x ∈ Rt M (LB M Q B) t)
    (hUV : Uline Z B Y ≤ Vt M (LB M Q B) B Z t)
    (hcardU : Nat.card ↥(Uline Z B Y) = Nat.card Z ^ 3)
    (hinter : Uline Z B Y ⊓ conjSubgroup x (Uline Z B Y) = Z) :
    Uline Z B Y ⊔ conjSubgroup x (Uline Z B Y) = Vt M (LB M Q B) B Z t := by
  classical
  have hUxV : conjSubgroup x (Uline Z B Y) ≤ Vt M (LB M Q B) B Z t := by
    intro y hy
    have hy' : x⁻¹ * y * x ∈ Uline Z B Y := (mem_conjSubgroup).mp hy
    have hy'V : x⁻¹ * y * x ∈ Vt M (LB M Q B) B Z t := hUV hy'
    have hxN := hc.Rt_normalizes_Vt hs.toSec5.mem hxR
    have := (Subgroup.mem_normalizer_iff.mp hxN (x⁻¹ * y * x)).mp hy'V
    rwa [show x * (x⁻¹ * y * x) * x⁻¹ = y by group] at this
  have hcomm : ⁅Uline Z B Y, conjSubgroup x (Uline Z B Y)⁆ ≤ Uline Z B Y := by
    rw [Subgroup.commutator_le]
    intro u hu e he
    exact Z_le_Uline Z B Y (comm_mem_Z_of_secVec ψ ⟨u, hUV hu⟩ ⟨e, hUxV he⟩)
  have hUxNorm : conjSubgroup x (Uline Z B Y) ≤
      Subgroup.normalizer (Uline Z B Y : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hcomm
  have hcardUx : Nat.card ↥(conjSubgroup x (Uline Z B Y)) = Nat.card ↥(Uline Z B Y) :=
    card_conjSubgroup x (Uline Z B Y)
  have hprod := card_sup_mul_card_inf_of_le_normalizer hUxNorm (L := Uline Z B Y)
    (E := conjSubgroup x (Uline Z B Y))
  rw [hinter, hcardU, hcardUx] at hprod
  have hprod' : Nat.card ↥(Uline Z B Y ⊔ conjSubgroup x (Uline Z B Y)) * Nat.card Z =
      Nat.card Z ^ 5 * Nat.card Z := by
    rw [hprod, hcardU]
    ring_nf
  have hq : 0 < Nat.card Z := Nat.card_pos
  have hsupcard : Nat.card ↥(Uline Z B Y ⊔ conjSubgroup x (Uline Z B Y)) =
      Nat.card Z ^ 5 := Nat.eq_of_mul_eq_mul_right hq hprod'
  have hcardV : Nat.card (Vt M (LB M Q B) B Z t) = Nat.card Z ^ 5 := Sec9Hyp.card_V hs
  have hsup_le : Uline Z B Y ⊔ conjSubgroup x (Uline Z B Y) ≤
      Vt M (LB M Q B) B Z t := sup_le hUV hUxV
  refine Subgroup.eq_of_le_of_card_ge hsup_le ?_
  rw [hcardV, hsupcard]

private theorem compl_left_inter (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K}
    {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 2 ⊕ Fin 2 → K)}
    {u : Fin 2 ⊕ Fin 2 → K}
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G))
    (hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔
        ∃ c : K, x = c • u)
    {a b : Fin 2 → K} (ha : a ≠ 0) (hb : b ≠ 0) (hu : toMat K u = Matrix.vecMulVec a b)
    (hYeq : (Y.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = leftF K)
    {x : G} (hxR : x ∈ Rt M (LB M Q B) t) {b' : Fin 2 → K}
    (hb' : b' ∉ (K ∙ b : Submodule K (Fin 2 → K)))
    {Bmat : Matrix.SpecialLinearGroup (Fin 2) K} {C : Matrix.SpecialLinearGroup (Fin 2) K}
    (hBmat : (Bmat : Matrix (Fin 2) (Fin 2) K) *ᵥ b = b')
    (hCinv : C⁻¹ = Bmat.transpose)
    (hΨx : Ψ K (φ ⟨x, hxR⟩) = rho' K (1, C)) :
    Uline Z B Y ⊓ conjSubgroup x (Uline Z B Y) = Z := by
  classical
  have hYR : Y ≤ Rt M (LB M Q B) t := by
    obtain ⟨⟨-, -, -, hYR, -, -, -⟩, -, -⟩ := hsplit
    exact hYR
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt hs.toSec5.mem
  have hHY : ∀ h, h ∈ leftF K ↔
      ∃ s : ↥(Rt M (LB M Q B) t), (s : G) ∈ Y ∧ Ψ K (φ s) = h := by
    intro h
    rw [← hYeq]
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  have hYmem := uline_mem_iff ψ φ hψ hnorm hYR hZV hBV u hBiff hHY
    (actsNat_leftF_outerL (b := b) hb) ha hu
  have hxM : x ∈ M := hc.Rt_le_M t hxR
  have hZs : conjSubgroup x Z = Z := by
    ext z
    rw [mem_conjSubgroup]
    simpa using (Subgroup.mem_normalizer_iff.mp
      (hc.hyp.Z_normal.2 (M.inv_mem hxM)) z).symm
  have hZUx : Z ≤ conjSubgroup x (Uline Z B Y) := by
    have h := Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom) (Z_le_Uline Z B Y)
    have h' : Subgroup.map (MulAut.conj x).toMonoidHom Z = Z := hZs
    rwa [h'] at h
  refine le_antisymm ?_ (le_inf (Z_le_Uline Z B Y) hZUx)
  intro y hy
  obtain ⟨hyU, hyUx⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨hyV, hyRange⟩ := (hYmem y).mp hyU
  obtain ⟨w, hw⟩ := hyRange
  have hy'U : x⁻¹ * y * x ∈ Uline Z B Y := (mem_conjSubgroup).mp hyUx
  obtain ⟨hy'V, hy'Range⟩ := (hYmem _).mp hy'U
  obtain ⟨w', hw'⟩ := hy'Range
  have hrow : cmat ψ ⟨y, hyV⟩ = Matrix.vecMulVec w b := by
    rw [← hw]
    rfl
  have hrow' : cmat ψ ⟨x⁻¹ * y * x, hy'V⟩ = Matrix.vecMulVec w' b := by
    rw [← hw']
    rfl
  have hconj := cmat_conj ψ φ hψ ⟨x, hxR⟩ ⟨x⁻¹ * y * x, hy'V⟩ ⟨y, hyV⟩ (by group)
  have hEq : Matrix.vecMulVec w b = Matrix.vecMulVec w' b' := by
    rw [← hrow, hconj, hΨx, rho'_inr_apply, hrow', Matrix.vecMulVec_mul, hCinv,
      Matrix.SpecialLinearGroup.coe_transpose, Matrix.vecMul_transpose, hBmat]
  have hw0 : w = 0 := eq_zero_of_vecMulVec_eq_of_not_mem_span hb hb' hEq
  have hcm : cmat ψ ⟨y, hyV⟩ = 0 := by rw [hrow, hw0, Matrix.zero_vecMulVec]
  exact (cmat_eq_zero_iff ψ _).mp hcm

private theorem exists_ulineY_compl_left (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K}
    {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 2 ⊕ Fin 2 → K)}
    {u : Fin 2 ⊕ Fin 2 → K}
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G))
    (hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔
        ∃ c : K, x = c • u)
    {a b : Fin 2 → K} (ha : a ≠ 0) (hb : b ≠ 0) (hu : toMat K u = Matrix.vecMulVec a b)
    (hYeq : (Y.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = leftF K)
    (hXeq : (X.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = rightF K) :
    ∃ x ∈ X, Uline Z B Y ⊓ conjSubgroup x (Uline Z B Y) = Z := by
  classical
  obtain ⟨b', hb'0, hb'⟩ := exists_not_mem_span_singleton hb
  obtain ⟨Bmat, hBmat⟩ := exists_sl2_mulVec_eq hb hb'0
  let C : Matrix.SpecialLinearGroup (Fin 2) K :=
    ((Bmat.transpose)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K)
  have hCinv : C⁻¹ = Bmat.transpose := by
    dsimp [C]
    rw [inv_inv]
  have hmem : rho' K (1, C) ∈ rightF K := ⟨C, rfl⟩
  have hmemMap : rho' K (1, C) ∈
      (X.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) := by
    rw [hXeq]
    exact hmem
  obtain ⟨s, hsX, hΨs⟩ := Subgroup.mem_map.mp hmemMap
  have hΨx : Ψ K (φ s) = rho' K (1, C) := hΨs
  have hxR : (s : G) ∈ Rt M (LB M Q B) t := s.2
  exact ⟨(s : G), hsX, compl_left_inter hc hs hsplit hψ hnorm hBiff ha hb hu hYeq hxR
    hb' hBmat hCinv hΨx⟩

private theorem exists_ulineY_compl_right (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K}
    {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin 2 ⊕ Fin 2 → K)}
    {u : Fin 2 ⊕ Fin 2 → K}
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hnorm : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G))
    (hBiff : ∀ x : Fin 2 ⊕ Fin 2 → K,
      (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔
        ∃ c : K, x = c • u)
    {a b : Fin 2 → K} (ha : a ≠ 0) (hb : b ≠ 0) (hu : toMat K u = Matrix.vecMulVec a b)
    (hYeq : (Y.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = rightF K)
    (hXeq : (X.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) = leftF K) :
    ∃ x ∈ X, Uline Z B Y ⊓ conjSubgroup x (Uline Z B Y) = Z := by
  classical
  obtain ⟨⟨-, hXR, -, hYR, -, -, -⟩, -, -⟩ := hsplit
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hHY : ∀ h, h ∈ rightF K ↔
      ∃ s : ↥(Rt M (LB M Q B) t), (s : G) ∈ Y ∧ Ψ K (φ s) = h := by
    intro h
    rw [← hYeq]
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  have hYmem := uline_mem_iff ψ φ hψ hnorm hYR hZV hBV u hBiff hHY
    (actsNat_rightF_outerR (a := a) ha) hb hu
  have hUV : Uline Z B Y ≤ Vt M (LB M Q B) B Z t := fun x hx => ((hYmem x).mp hx).1
  obtain ⟨a', ha'0, ha'⟩ := exists_not_mem_span_singleton ha
  obtain ⟨Amat, hAmat⟩ := exists_sl2_mulVec_eq ha ha'0
  have hmem : rho' K (Amat, 1) ∈ leftF K := ⟨Amat, rfl⟩
  have hmemMap : rho' K (Amat, 1) ∈
      (X.subgroupOf (Rt M (LB M Q B) t)).map ((Ψ K).toMonoidHom.comp φ) := by
    rw [hXeq]
    exact hmem
  obtain ⟨s, hsX, hΨs⟩ := Subgroup.mem_map.mp hmemMap
  have hΨx : Ψ K (φ s) = rho' K (Amat, 1) := hΨs
  have hsM : (s : G) ∈ M := hc.Rt_le_M t s.2
  have hZs : conjSubgroup (s : G) Z = Z := by
    ext z
    rw [mem_conjSubgroup]
    simpa using (Subgroup.mem_normalizer_iff.mp
      (hc.hyp.Z_normal.2 (M.inv_mem hsM)) z).symm
  have hZUx : Z ≤ conjSubgroup (s : G) (Uline Z B Y) := by
    have h := Subgroup.map_mono (f := (MulAut.conj (s : G)).toMonoidHom)
      (Z_le_Uline Z B Y)
    have h' : Subgroup.map (MulAut.conj (s : G)).toMonoidHom Z = Z := hZs
    rwa [h'] at h
  refine ⟨(s : G), hsX, le_antisymm ?_ (le_inf (Z_le_Uline Z B Y) hZUx)⟩
  intro y hy
  obtain ⟨hyU, hyUx⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨hyV, hyRange⟩ := (hYmem y).mp hyU
  obtain ⟨w, hw⟩ := hyRange
  have hy'U : (s : G)⁻¹ * y * (s : G) ∈ Uline Z B Y := (mem_conjSubgroup).mp hyUx
  obtain ⟨hy'V, hy'Range⟩ := (hYmem _).mp hy'U
  obtain ⟨w', hw'⟩ := hy'Range
  have hrow : cmat ψ ⟨y, hyV⟩ = Matrix.vecMulVec a w := by
    rw [← hw]
    rfl
  have hrow' : cmat ψ ⟨(s : G)⁻¹ * y * (s : G), hy'V⟩ = Matrix.vecMulVec a w' := by
    rw [← hw']
    rfl
  have hconj := cmat_conj ψ φ hψ s ⟨(s : G)⁻¹ * y * (s : G), hy'V⟩ ⟨y, hyV⟩
    (by group)
  have hEq : Matrix.vecMulVec a w = Matrix.vecMulVec a' w' := by
    rw [← hrow, hconj, hΨx, rho'_inl_apply, hrow', Matrix.mul_vecMulVec, hAmat]
  have hEq' : Matrix.vecMulVec w a = Matrix.vecMulVec w' a' := by
    have := congrArg Matrix.transpose hEq
    simpa [Matrix.transpose_vecMulVec] using this
  have hw0 : w = 0 := eq_zero_of_vecMulVec_eq_of_not_mem_span ha ha' hEq'
  have hcm : cmat ψ ⟨y, hyV⟩ = 0 := by rw [hrow, hw0, Matrix.vecMulVec_zero]
  exact (cmat_eq_zero_iff ψ _).mp hcm

theorem exists_ulineY_compl (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) :
    ∃ x ∈ X, Uline Z B Y ⊓ conjSubgroup x (Uline Z B Y) = Z ∧
      Uline Z B Y ⊔ conjSubgroup x (Uline Z B Y) = Vt M (LB M Q B) B Z t := by
  classical
  obtain ⟨K, fK, finK, chK, hn, φ, ψ, u, hK, hrange, hker, hnorm, hψ, hBiff, hW, hdet, hu0⟩ :=
    sec9_coord h34 hc hs
  haveI := hn
  haveI : CharP K 2 := chK
  obtain ⟨a, b, ha, hb, hu⟩ := exists_vecMulVec_of_det_eq_zero hdet hu0
  have hfac := sec97_factor_pair h34 h311a hc hs hsplit hK φ hrange hker
  have hXR : X ≤ Rt M (LB M Q B) t := by
    obtain ⟨⟨-, hXR, -, -, -, -, -⟩, -, -⟩ := hsplit
    exact hXR
  have hYR : Y ≤ Rt M (LB M Q B) t := by
    obtain ⟨⟨-, -, -, hYR, -, -, -⟩, -, -⟩ := hsplit
    exact hYR
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  rcases hfac with ⟨hYeq, hXeq⟩ | ⟨hYeq, hXeq⟩
  · obtain ⟨x, hxX, hinter⟩ := exists_ulineY_compl_left hc hs hsplit
      hψ hnorm hBiff ha hb hu hYeq hXeq
    have hHY : ∀ h, h ∈ leftF K ↔
        ∃ s : ↥(Rt M (LB M Q B) t), (s : G) ∈ Y ∧ Ψ K (φ s) = h := by
      intro h
      rw [← hYeq]
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
      exact Iff.rfl
    have hYmem := uline_mem_iff ψ φ hψ hnorm hYR hZV hBV u hBiff hHY
      (actsNat_leftF_outerL (b := b) hb) ha hu
    have hUV : Uline Z B Y ≤ Vt M (LB M Q B) B Z t := fun y hy => ((hYmem y).mp hy).1
    have hcardU : Nat.card ↥(Uline Z B Y) = Nat.card Z ^ 3 :=
      (sec97LineNat_of h34 h311a G M Q Z B hc n t hs X Y hsplit).1
    exact ⟨x, hxX, hinter, sup_uline_conj_eq (K := K) (ψ := ψ) hc hs (hXR hxX) hUV hcardU hinter⟩
  · obtain ⟨x, hxX, hinter⟩ := exists_ulineY_compl_right hc hs hsplit
      hψ hnorm hBiff ha hb hu hYeq hXeq
    have hHY : ∀ h, h ∈ rightF K ↔
        ∃ s : ↥(Rt M (LB M Q B) t), (s : G) ∈ Y ∧ Ψ K (φ s) = h := by
      intro h
      rw [← hYeq]
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
      exact Iff.rfl
    have hYmem := uline_mem_iff ψ φ hψ hnorm hYR hZV hBV u hBiff hHY
      (actsNat_rightF_outerR (a := a) ha) hb hu
    have hUV : Uline Z B Y ≤ Vt M (LB M Q B) B Z t := fun y hy => ((hYmem y).mp hy).1
    have hcardU : Nat.card ↥(Uline Z B Y) = Nat.card Z ^ 3 :=
      (sec97LineNat_of h34 h311a G M Q Z B hc n t hs X Y hsplit).1
    exact ⟨x, hxX, hinter, sup_uline_conj_eq (K := K) (ψ := ψ) hc hs (hXR hxX) hUV hcardU hinter⟩

end HS9

end CFSG.RankThree.GF2n.Stroth80
