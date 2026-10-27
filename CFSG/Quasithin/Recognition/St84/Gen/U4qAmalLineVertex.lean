module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalCoord
public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalLine

import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalSchur
import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalFieldInner
import CFSG.Quasithin.Recognition.St84.Gen.AmalVertexLocal
import CFSG.Quasithin.Recognition.St84.Gen.VertexIsoSylow
import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Gaschutz
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.ClassicalGroups.PCoreSection

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.BorelTits
open scoped MatrixGroups

section Acts

variable {G : Type*} [Group G] {F : Type*} [Field F] {n : ℕ} {Q : Subgroup G}

private theorem actsByMatrix_mul' {β : ↥Q ≃* Multiplicative (Fin n → F)} {p q : G}
    (hq : ∀ x : ↥Q, ∃ y : ↥Q, (y : G) = q * x * q⁻¹) {A B : Matrix (Fin n) (Fin n) F}
    (hA : ActsByMatrix β p A) (hB : ActsByMatrix β q B) : ActsByMatrix β (p * q) (A * B) := by
  intro x y hy
  obtain ⟨z, hz⟩ := hq x
  have hy' : (y : G) = p * z * p⁻¹ := by
    rw [hy, hz]
    group
  rw [hA z y hy', hB x z hz, Matrix.mulVec_mulVec]

private theorem exists_conj_of_mem_normalizer {q : G}
    (hq : q ∈ Subgroup.normalizer (Q : Set G)) (x : ↥Q) :
    ∃ y : ↥Q, (y : G) = q * x * q⁻¹ :=
  ⟨⟨q * x * q⁻¹, (Subgroup.mem_normalizer_iff.mp hq x).mp x.2⟩, rfl⟩

private def actsByMatrixSubgroup (β : ↥Q ≃* Multiplicative (Fin n → F))
    (Γ : Subgroup (GL (Fin n) F)) : Subgroup G where
  carrier := {p | p ∈ Subgroup.normalizer (Q : Set G) ∧
    ∃ M ∈ Γ, ActsByMatrix β p (M : Matrix (Fin n) (Fin n) F)}
  one_mem' := by
    refine ⟨Subgroup.one_mem _, 1, Subgroup.one_mem _, fun x y hy => ?_⟩
    have hxy : y = x := Subtype.ext (by rw [hy]; group)
    rw [hxy, Units.val_one, Matrix.one_mulVec]
  mul_mem' := by
    rintro p q ⟨hp, M, hM, hpM⟩ ⟨hq, N, hN, hqN⟩
    refine ⟨Subgroup.mul_mem _ hp hq, M * N, Subgroup.mul_mem _ hM hN, ?_⟩
    rw [Units.val_mul]
    exact actsByMatrix_mul' (exists_conj_of_mem_normalizer hq) hpM hqN
  inv_mem' := by
    rintro p ⟨hp, M, hM, hpM⟩
    refine ⟨Subgroup.inv_mem _ hp, M⁻¹, Subgroup.inv_mem _ hM, fun x y hy => ?_⟩
    have hx : (x : G) = p * y * p⁻¹ := by
      rw [hy]
      group
    rw [hpM y x hx, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

private theorem mem_actsByMatrixSubgroup {β : ↥Q ≃* Multiplicative (Fin n → F)}
    {Γ : Subgroup (GL (Fin n) F)} {p : G} :
    p ∈ actsByMatrixSubgroup β Γ ↔ p ∈ Subgroup.normalizer (Q : Set G) ∧
      ∃ M ∈ Γ, ActsByMatrix β p (M : Matrix (Fin n) (Fin n) F) :=
  Iff.rfl

end Acts

section Coordinates

variable {G : Type} [Group G] {L1 L2 S : Subgroup G} {f : ℕ} {K : Type} [Field K]
  (c₂ : U4qCoordRight L1 L2 S f K) (hU : UnitaryFieldData 2 f K)

@[expose] noncomputable def U4qCoordRight.hermEquiv (c₂ : U4qCoordRight L1 L2 S f K)
    (hU : UnitaryFieldData 2 f K) : ↥(pCoreOf 2 L2) ≃* Multiplicative ↥(u4Herm hU) :=
  MulEquiv.ofBijective (F := ↥(pCoreOf 2 L2) →* Multiplicative ↥(u4Herm hU))
    { toFun := fun u => Multiplicative.ofAdd ⟨Multiplicative.toAdd (c₂.β u),
        (mem_u4Herm_iff_pow hU).mpr ((c₂.range_iff _).mp ⟨u, rfl⟩)⟩
      map_one' := by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        simp
      map_mul' := fun u v => by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        simp }
    ⟨fun u v huv => c₂.injective_β (Multiplicative.toAdd.injective
        (congrArg (fun X => ((Multiplicative.toAdd X : ↥(u4Herm hU)) :
          Matrix (Fin 2) (Fin 2) K)) huv)),
      fun X => by
        obtain ⟨u, hu⟩ := (c₂.range_iff _).mpr
          ((mem_u4Herm_iff_pow hU).mp (Multiplicative.toAdd X).2)
        exact ⟨u, Multiplicative.toAdd.injective (Subtype.ext hu)⟩⟩

theorem U4qCoordRight.coe_toAdd_hermEquiv (u : ↥(pCoreOf 2 L2)) :
    ((Multiplicative.toAdd (c₂.hermEquiv hU u) : ↥(u4Herm hU)) : Matrix (Fin 2) (Fin 2) K) =
      Multiplicative.toAdd (c₂.β u) :=
  rfl

@[expose] noncomputable def U4qCoordRight.coordEquiv (c₂ : U4qCoordRight L1 L2 S f K)
    (hU : UnitaryFieldData 2 f K) : ↥(pCoreOf 2 L2) ≃* Multiplicative (Fin 4 → hU.fixedField) :=
  (c₂.hermEquiv hU).trans (u4HermCoord hU).toAddEquiv.toMultiplicative

theorem U4qCoordRight.toAdd_coordEquiv (u : ↥(pCoreOf 2 L2)) :
    Multiplicative.toAdd (c₂.coordEquiv hU u) =
      u4HermCoord hU (Multiplicative.toAdd (c₂.hermEquiv hU u)) :=
  rfl

private theorem U4qCoordRight.equivariant_bar (x : ↥L2) (u v : ↥(pCoreOf 2 L2))
    (hv : (v : G) = x * u * x⁻¹) :
    Multiplicative.toAdd (c₂.β v) = (c₂.α x : Matrix (Fin 2) (Fin 2) K) *
      Multiplicative.toAdd (c₂.β u) * ((c₂.α x : Matrix (Fin 2) (Fin 2) K).map hU.bar)ᵀ := by
  have hpow : (fun y : K => y ^ 2 ^ f) = ⇑hU.bar := funext fun y => (hU.bar_apply y).symm
  have h := c₂.equivariant x u v hv
  rw [hpow] at h
  exact h

theorem U4qCoordRight.actsByMatrix_coordEquiv_iff (p : G) (A : Matrix (Fin 2) (Fin 2) K) :
    ActsByMatrix (c₂.coordEquiv hU) p (u4TwistMat hU A) ↔
      ∀ u v : ↥(pCoreOf 2 L2), (v : G) = p * u * p⁻¹ →
        Multiplicative.toAdd (c₂.β v) = A * Multiplicative.toAdd (c₂.β u) * (A.map hU.bar)ᵀ := by
  unfold ActsByMatrix
  refine forall_congr' fun u => forall_congr' fun v => imp_congr_right fun _ => ?_
  rw [c₂.toAdd_coordEquiv hU, c₂.toAdd_coordEquiv hU, u4TwistMat_mulVec,
    (u4HermCoord hU).injective.eq_iff, Subtype.ext_iff, coe_u4TwistLin,
    c₂.coe_toAdd_hermEquiv hU, c₂.coe_toAdd_hermEquiv hU]

theorem U4qCoordRight.actsByMatrix_coordEquiv (x : ↥L2) :
    ActsByMatrix (c₂.coordEquiv hU) (x : G)
      (u4TwistMat hU (c₂.α x : Matrix (Fin 2) (Fin 2) K)) :=
  (c₂.actsByMatrix_coordEquiv_iff hU _ _).mpr fun u v hv => c₂.equivariant_bar hU x u v hv

theorem U4qCoordRight.exists_smul_of_conj {t : G}
    (ht : t ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set G))
    (htL : ∀ x ∈ L2, t * x * t⁻¹ * x⁻¹ ∈ pCoreOf 2 L2) :
    ∃ c : hU.fixedField, c ≠ 0 ∧ ∀ u v : ↥(pCoreOf 2 L2), (v : G) = t * u * t⁻¹ →
      Multiplicative.toAdd (c₂.β v) = (c : K) • Multiplicative.toAdd (c₂.β u) := by
  have hcomm : ∀ a ∈ pCoreOf 2 L2, ∀ b ∈ pCoreOf 2 L2, a * b = b * a := by
    intro a ha b hb
    have h : (⟨a, ha⟩ * ⟨b, hb⟩ : ↥(pCoreOf 2 L2)) = ⟨b, hb⟩ * ⟨a, ha⟩ :=
      c₂.injective_β (by rw [map_mul, map_mul, mul_comm])
    exact congrArg Subtype.val h
  let ψ : MulAut ↥(pCoreOf 2 L2) := (pCoreOf 2 L2).normalizerMonoidHom ⟨t, ht⟩
  have hψ : ∀ u : ↥(pCoreOf 2 L2), ((ψ u : ↥(pCoreOf 2 L2)) : G) = t * u * t⁻¹ := fun u =>
    Subgroup.normalizerMonoidHom_apply_apply_coe (pCoreOf 2 L2) ⟨t, ht⟩ u
  let e := c₂.hermEquiv hU
  let T : ↥(u4Herm hU) →+ ↥(u4Herm hU) := AddMonoidHom.mk'
    (fun X => Multiplicative.toAdd (e (ψ (e.symm (Multiplicative.ofAdd X))))) (by
      intro X Y
      simp only [ofAdd_add, map_mul, toAdd_mul])
  have hTe : ∀ u : ↥(pCoreOf 2 L2),
      T (Multiplicative.toAdd (e u)) = Multiplicative.toAdd (e (ψ u)) := by
    intro u
    simp [T]
  have htw : ∀ (x : ↥L2) (u : ↥(pCoreOf 2 L2)),
      u4TwistLin hU (c₂.α x : Matrix (Fin 2) (Fin 2) K) (Multiplicative.toAdd (e u)) =
        Multiplicative.toAdd (e ⟨(x : G) * u * (x : G)⁻¹,
          CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf x.2 u.2⟩) := by
    intro x u
    apply Subtype.ext
    rw [coe_u4TwistLin, c₂.coe_toAdd_hermEquiv hU, c₂.coe_toAdd_hermEquiv hU,
      c₂.equivariant_bar hU x u ⟨(x : G) * u * (x : G)⁻¹,
        CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf x.2 u.2⟩ rfl]
  have hT : ∀ (A : SL(2, K)) (X : ↥(u4Herm hU)),
      T (u4TwistLin hU (A : Matrix (Fin 2) (Fin 2) K) X) =
        u4TwistLin hU (A : Matrix (Fin 2) (Fin 2) K) (T X) := by
    intro A X
    obtain ⟨x, rfl⟩ := c₂.surjective_α A
    obtain ⟨u, rfl⟩ : ∃ u, Multiplicative.toAdd (e u) = X :=
      ⟨e.symm (Multiplicative.ofAdd X), by simp⟩
    rw [htw, hTe, hTe, htw]
    congr 2
    apply Subtype.ext
    show ((ψ ⟨(x : G) * u * (x : G)⁻¹, _⟩ : ↥(pCoreOf 2 L2)) : G) =
      (x : G) * ((ψ u : ↥(pCoreOf 2 L2)) : G) * (x : G)⁻¹
    rw [hψ, hψ]
    have hq : t * (x : G) * t⁻¹ * (x : G)⁻¹ ∈ pCoreOf 2 L2 := htL x x.2
    have hw : t * u * t⁻¹ ∈ pCoreOf 2 L2 := (Subgroup.mem_normalizer_iff.mp ht u).mp u.2
    have hxw : (x : G) * (t * u * t⁻¹) * (x : G)⁻¹ ∈ pCoreOf 2 L2 :=
      CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf x.2 hw
    have hc := hcomm _ hq _ hxw
    calc t * ((x : G) * u * (x : G)⁻¹) * t⁻¹ =
        (t * (x : G) * t⁻¹ * (x : G)⁻¹) * ((x : G) * (t * u * t⁻¹) * (x : G)⁻¹) *
          (t * (x : G) * t⁻¹ * (x : G)⁻¹)⁻¹ := by group
      _ = (x : G) * (t * u * t⁻¹) * (x : G)⁻¹ := by
        rw [hc]
        group
  obtain ⟨c, hc⟩ := exists_smul_of_comm_u4TwistLin hU T hT
  refine ⟨c, ?_, fun u v hv => ?_⟩
  · rintro rfl
    have hinj : Function.Injective T := by
      intro X Y hXY
      have h1 : Multiplicative.toAdd (e (ψ (e.symm (Multiplicative.ofAdd X)))) =
          Multiplicative.toAdd (e (ψ (e.symm (Multiplicative.ofAdd Y)))) := hXY
      exact Multiplicative.ofAdd.injective
        (e.symm.injective (ψ.injective (e.injective (Multiplicative.toAdd.injective h1))))
    let X₁ : ↥(u4Herm hU) := ⟨1, (mem_u4Herm hU).mpr fun i j => by
      fin_cases i <;> fin_cases j <;> simp⟩
    have h0 : T X₁ = T 0 := by rw [hc, zero_smul, map_zero]
    have h1 := congrArg Subtype.val (hinj h0)
    exact one_ne_zero h1
  · have h1 : ψ u = v := Subtype.ext (by rw [hψ, hv])
    have h2 := congrArg Subtype.val (hc (Multiplicative.toAdd (e u)))
    rw [hTe, h1, Submodule.coe_smul, c₂.coe_toAdd_hermEquiv hU, c₂.coe_toAdd_hermEquiv hU,
      Subfield.smul_def] at h2
    exact h2

end Coordinates

section Vertex

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

theorem U4qLocalData.exists_twist_borelOf_left (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f)) {K : Type} [Field K]
    (c₂ : U4qCoordRight L1 L2 S f K) (hU : UnitaryFieldData 2 f K) {d : G}
    (hd : d ∈ borelOf L1 S) :
    ∃ A : GL (Fin 2) K, A ∈ u4DetFixGL hU ∧
      ActsByMatrix (c₂.coordEquiv hU) d (u4TwistMat hU (A : Matrix (Fin 2) (Fin 2) K)) := by
  haveI := hU.charP
  haveI := hU.finite
  obtain ⟨g, hg, hgx⟩ := hD.exists_inner_borelOf_left hH hS d hd
  have hdQ : d ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 L2 (hH.h2.borel_le hd)
  have hgQ : g ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set G) := le_normalizer_pCoreOf 2 L2 hg
  have ht : g⁻¹ * d ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hgQ) hdQ
  have htL : ∀ x ∈ L2, g⁻¹ * d * x * (g⁻¹ * d)⁻¹ * x⁻¹ ∈ pCoreOf 2 L2 := by
    intro x hx
    have e : g⁻¹ * d * x * (g⁻¹ * d)⁻¹ * x⁻¹ =
        g⁻¹ * (d * x * d⁻¹ * (g * x * g⁻¹)⁻¹) * g⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgQ) _).mp (hgx x hx)
  obtain ⟨c, hc0, hc⟩ := c₂.exists_smul_of_conj hU ht htL
  obtain ⟨μ, hμ⟩ := isSquare_of_charTwo' (c : K)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    apply hc0
    exact Subtype.ext (by rw [hμ, mul_zero]; rfl)
  have hμf : hU.bar μ = μ := by
    have hcf : hU.bar (c : K) = c := (hU.mem_fixedField).mp c.2
    rw [hμ, map_mul] at hcf
    exact CharTwo.sq_inj.mp (by rw [sq, sq]; exact hcf)
  set Ag : Matrix (Fin 2) (Fin 2) K := (c₂.α ⟨g, hg⟩ : Matrix (Fin 2) (Fin 2) K) with hAg
  have hAgdet : Ag.det = 1 := (c₂.α ⟨g, hg⟩).2
  have hdet : (μ • Ag).det = c := by
    rw [Matrix.det_smul, Fintype.card_fin, hAgdet, mul_one, sq, ← hμ]
  let A : GL (Fin 2) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero (μ • Ag) (by
      rw [hdet]
      exact fun h0 => hc0 (Subtype.ext h0))
  have hA : (A : Matrix (Fin 2) (Fin 2) K) = μ • Ag := rfl
  refine ⟨A, ?_, ?_⟩
  · rw [mem_u4DetFixGL, hA, hdet]
    exact (hU.mem_fixedField).mp c.2
  · rw [c₂.actsByMatrix_coordEquiv_iff hU]
    intro u v hv
    let w : ↥(pCoreOf 2 L2) :=
      ⟨g⁻¹ * d * u * (g⁻¹ * d)⁻¹, (Subgroup.mem_normalizer_iff.mp ht u).mp u.2⟩
    have hw := hc u w rfl
    have hvw : (v : G) = g * w * g⁻¹ := by
      rw [hv]
      change d * u * d⁻¹ = g * (g⁻¹ * d * u * (g⁻¹ * d)⁻¹) * g⁻¹
      group
    rw [c₂.equivariant_bar hU ⟨g, hg⟩ w v hvw, hw, hA, ← hAg]
    ext i j
    rw [mul_mul_map_bar_transpose_apply, mul_mul_map_bar_transpose_apply]
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, hμf]
    rw [hμ]
    ring

private theorem U4qCoordLeft.conj_mem_of_upper {F : Type} [Field F]
    (c₁ : U4qCoordLeft L1 L2 S f F) (hSL1 : S ≤ L1) {y : ↥L1}
    (hy : (c₁.α y : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) {s : G} (hs : s ∈ S) :
    (y : G) * s * (y : G)⁻¹ ∈ S := by
  obtain ⟨t, ht⟩ := (c₁.mem_iff ⟨s, hSL1 hs⟩).mp hs
  have hdet : (c₁.α y : Matrix (Fin 2) (Fin 2) F) 0 0 *
      (c₁.α y : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    have h := (c₁.α y).2
    rw [Matrix.det_fin_two, hy, mul_zero, sub_zero] at h
    exact h
  have hmem := (c₁.mem_iff (y * ⟨s, hSL1 hs⟩ * y⁻¹)).mpr
    ⟨(c₁.α y : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * t, by
      rw [map_mul, map_mul, map_inv, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, ht,
        Matrix.adjugate_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hy] <;>
        first | linear_combination hdet | ring⟩
  exact hmem

private theorem U4qLocalData.exists_actsByMatrix_of_mem_u4Gamma2 (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f)) {F K : Type} [Field F]
    [Field K] (c₁ : U4qCoordLeft L1 L2 S f F) (c₂ : U4qCoordRight L1 L2 S f K)
    (hU : UnitaryFieldData 2 f K) {M : GL (Fin 4) hU.fixedField} (hM : M ∈ u4Gamma2 hU) :
    ∃ p ∈ L2 ⊔ borelOf L1 S,
      ActsByMatrix (c₂.coordEquiv hU) p (M : Matrix (Fin 4) (Fin 4) hU.fixedField) := by
  classical
  haveI := hU.charP
  have hSL1 : S ≤ L1 := hD.le_left hH hS
  obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hM
  obtain ⟨ρ, κ, hκ, -, -, hC⟩ := hD.exists_ringEquiv_fixedField hH hS c₁ c₂ hU
  have hκ' : (κ : K) ≠ 0 := fun h0 => hκ (Subtype.ext h0)
  have hδf : hU.bar (A : Matrix (Fin 2) (Fin 2) K).det = (A : Matrix (Fin 2) (Fin 2) K).det := hA
  have hδ0 : (A : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  obtain ⟨a, ha⟩ : ∃ a : F, (ρ a : K) = (A : Matrix (Fin 2) (Fin 2) K).det :=
    ⟨ρ.symm ⟨_, hδf⟩, by rw [RingEquiv.apply_symm_apply]⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hδ0
    rw [← ha, map_zero]
    rfl
  obtain ⟨d, hdα⟩ := c₁.surjective_α ⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two, ha0]⟩
  have hdα' : (c₁.α d : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, a⁻¹] := by rw [hdα]
  have hd10 : (c₁.α d : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    rw [hdα']
    simp
  have hdi10 : (c₁.α d⁻¹ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    rw [map_inv, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hdα']
    simp
  have hdN : (d : G) ∈ Subgroup.normalizer ((S ⊓ L1 : Subgroup G) : Set G) := by
    rw [inf_eq_left.mpr hSL1, Subgroup.mem_normalizer_iff]
    intro s
    refine ⟨fun hs => c₁.conj_mem_of_upper hSL1 hd10 hs, fun hs => ?_⟩
    have h := c₁.conj_mem_of_upper hSL1 hdi10 hs
    have e : ((d⁻¹ : ↥L1) : G) * ((d : G) * s * (d : G)⁻¹) * ((d⁻¹ : ↥L1) : G)⁻¹ = s := by
      rw [Subgroup.coe_inv]
      group
    rwa [e] at h
  have hdB : (d : G) ∈ borelOf L1 S := Subgroup.mem_inf.mpr ⟨d.2, hdN⟩
  obtain ⟨B, hB, hdB'⟩ := hD.exists_twist_borelOf_left hH hS c₂ hU hdB
  have hact := (c₂.actsByMatrix_coordEquiv_iff hU _ _).mp hdB'
  have hdQ : (d : G) ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 L2 (hH.h2.borel_le hdB)
  obtain ⟨z, hz⟩ := (c₂.range_iff (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K)).mpr (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp)
  have hzZ : (z : G) ∈ centerOf (pCoreOf 2 L1) :=
    (c₂.mem_center_iff z).mpr ⟨by rw [hz]; rfl, by rw [hz]; rfl⟩
  have hdz : (z : G) = (d : G) * z * (d : G)⁻¹ := by
    have h := Subgroup.mem_centralizer_iff.mp (hD.center_left d.2) _ hzZ
    rw [← h]
    group
  have hzfix := hact z z hdz
  rw [hz] at hzfix
  have e00 := congrFun (congrFun hzfix 0) 0
  have e11 := congrFun (congrFun hzfix 1) 1
  rw [mul_mul_map_bar_transpose_apply] at e00 e11
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] at e00 e11
  have hB00 : (B : Matrix (Fin 2) (Fin 2) K) 0 0 * hU.bar ((B : Matrix (Fin 2) (Fin 2) K) 0 0) =
      1 := by
    linear_combination -e00
  have hB10 : (B : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have h : (B : Matrix (Fin 2) (Fin 2) K) 1 0 * hU.bar ((B : Matrix (Fin 2) (Fin 2) K) 1 0) =
        0 := by
      linear_combination -e11
    rcases mul_eq_zero.mp h with h0 | h0
    · exact h0
    · exact (map_eq_zero hU.bar).mp h0
  obtain ⟨c₀, hc₀Q, hc₀α⟩ := c₁.exists_pCoreOf_right hH hD hS 1
  have hdc₀Q : ((d * c₀ * d⁻¹ : ↥L1) : G) ∈ pCoreOf 2 L2 :=
    (Subgroup.mem_normalizer_iff.mp hdQ _).mp hc₀Q
  have hdc₀α : (c₁.α (d * c₀ * d⁻¹) : Matrix (Fin 2) (Fin 2) F) = !![1, a * a; 0, 1] := by
    rw [map_mul, map_mul, map_inv, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, hdα', hc₀α]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha0]
  have h1 := hC (c₀ : G) hc₀Q c₀.2
  have h2 := hC ((d * c₀ * d⁻¹ : ↥L1) : G) hdc₀Q (d * c₀ * d⁻¹).2
  have hc₀ : (⟨(c₀ : G), c₀.2⟩ : ↥L1) = c₀ := rfl
  have hdc₀ : (⟨((d * c₀ * d⁻¹ : ↥L1) : G), (d * c₀ * d⁻¹).2⟩ : ↥L1) = d * c₀ * d⁻¹ := rfl
  have hρ1 : (ρ ((c₁.α c₀ : Matrix (Fin 2) (Fin 2) F) 0 1) : K) = 1 := by
    rw [hc₀α]
    simp
  have hρa : (ρ ((c₁.α (d * c₀ * d⁻¹) : Matrix (Fin 2) (Fin 2) F) 0 1) : K) =
      (ρ a : K) * (ρ a : K) := by
    rw [hdc₀α]
    simp
  rw [hc₀, hρ1] at h1
  rw [hdc₀, hρa] at h2
  have h3 := congrFun (congrFun (hact ⟨c₀, hc₀Q⟩ ⟨_, hdc₀Q⟩ rfl) 1) 1
  rw [mul_mul_map_bar_transpose_apply, hB10, map_zero, h1, h2] at h3
  have hB11 : (B : Matrix (Fin 2) (Fin 2) K) 1 1 * hU.bar ((B : Matrix (Fin 2) (Fin 2) K) 1 1) =
      (ρ a : K) * (ρ a : K) := by
    apply mul_left_cancel₀ hκ'
    linear_combination -h3
  have hdetB : (B : Matrix (Fin 2) (Fin 2) K).det = (A : Matrix (Fin 2) (Fin 2) K).det := by
    have hdet : (B : Matrix (Fin 2) (Fin 2) K).det =
        (B : Matrix (Fin 2) (Fin 2) K) 0 0 * (B : Matrix (Fin 2) (Fin 2) K) 1 1 := by
      rw [Matrix.det_fin_two, hB10, mul_zero, sub_zero]
    have hfix : hU.bar (B : Matrix (Fin 2) (Fin 2) K).det = (B : Matrix (Fin 2) (Fin 2) K).det :=
      hB
    have hsq : (B : Matrix (Fin 2) (Fin 2) K).det ^ 2 = (ρ a : K) ^ 2 := by
      calc (B : Matrix (Fin 2) (Fin 2) K).det ^ 2 =
          (B : Matrix (Fin 2) (Fin 2) K).det * hU.bar (B : Matrix (Fin 2) (Fin 2) K).det := by
            rw [hfix, sq]
        _ = ((B : Matrix (Fin 2) (Fin 2) K) 0 0 * hU.bar ((B : Matrix (Fin 2) (Fin 2) K) 0 0)) *
            ((B : Matrix (Fin 2) (Fin 2) K) 1 1 *
              hU.bar ((B : Matrix (Fin 2) (Fin 2) K) 1 1)) := by
            rw [hdet, map_mul]
            ring
        _ = (ρ a : K) ^ 2 := by
            rw [hB00, hB11]
            ring
    rw [← ha]
    exact CharTwo.sq_inj.mp hsq
  have hdetAB : ((A * B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    have h : ((A * B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det *
        (B : Matrix (Fin 2) (Fin 2) K).det = (A : Matrix (Fin 2) (Fin 2) K).det := by
      rw [← Matrix.det_mul, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel_right]
    rw [hdetB] at h
    exact mul_right_cancel₀ hδ0 (h.trans (one_mul _).symm)
  obtain ⟨x, hx⟩ := c₂.surjective_α ⟨((A * B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K),
    hdetAB⟩
  refine ⟨(x : G) * d, Subgroup.mul_mem _ (Subgroup.mem_sup_left x.2)
    (Subgroup.mem_sup_right hdB), ?_⟩
  have hprod := actsByMatrix_mul' (exists_conj_of_mem_normalizer hdQ)
    (c₂.actsByMatrix_coordEquiv hU x) hdB'
  have hxB : (c₂.α x : Matrix (Fin 2) (Fin 2) K) * (B : Matrix (Fin 2) (Fin 2) K) =
      (A : Matrix (Fin 2) (Fin 2) K) := by
    rw [hx]
    change (A : Matrix (Fin 2) (Fin 2) K) * ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      (B : Matrix (Fin 2) (Fin 2) K) = A
    rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  rw [← u4TwistMat_mul, hxB] at hprod
  rw [coe_u4TwistHom]
  exact hprod

omit [Finite G] in
private theorem U4qLocalData.card_centerOf_pCoreOf_left (hD : U4qLocalData L1 L2 S f) :
    Nat.card (centerOf (pCoreOf 2 L1)) = 2 ^ f := by
  have he : centerOf (pCoreOf 2 L1) =
      (Subgroup.center ↥(pCoreOf 2 L1)).map (pCoreOf 2 L1).subtype := by
    ext z
    constructor
    · intro hz
      exact ⟨⟨z, hz.1⟩, Subgroup.mem_center_iff.mpr fun g =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hz.2 g g.2), rfl⟩
    · rintro ⟨z', hz', rfl⟩
      exact ⟨z'.2, Subgroup.mem_centralizer_iff.mpr fun y hy =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hz' ⟨y, hy⟩)⟩
  rw [he, Subgroup.card_map_of_injective (pCoreOf 2 L1).subtype_injective]
  exact hD.special_left.2.2

private theorem U4qLocalData.exists_complement_right (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f)) {F : Type} [Field F]
    (c₁ : U4qCoordLeft L1 L2 S f F) :
    ∃ X : Subgroup G, X ≤ L2 ⊔ bigB L1 L2 S ∧ X ⊓ pCoreOf 2 L2 = ⊥ ∧
      pCoreOf 2 L2 ⊔ X = L2 ⊔ bigB L1 L2 S := by
  classical
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [c₁.card]; positivity)
  haveI := Fintype.ofFinite F
  haveI : CharP F 2 :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, c₁.card])
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSL1 : S ≤ L1 := hD.le_left hH hS
  have hSL2 : S ≤ L2 := hD.le_right hH hS
  obtain ⟨x₀, hx₀⟩ := c₁.surjective_α
    ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩
  have hx₀' : (c₁.α x₀ : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] := by rw [hx₀]
  obtain ⟨E, hE⟩ : ∃ E : Subgroup G,
      E = conjSubgroup (pCoreOf 2 L1 ⊓ pCoreOf 2 L2) (x₀ : G) := ⟨_, rfl⟩
  have hmemE : ∀ y, y ∈ E ↔ (x₀ : G) * y * (x₀ : G)⁻¹ ∈ pCoreOf 2 L1 ⊓ pCoreOf 2 L2 := by
    intro y
    rw [hE]
    exact mem_conjSubgroup_iff
  have hEQ₁ : E ≤ pCoreOf 2 L1 := by
    intro y hy
    have h := CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf (Subgroup.inv_mem _ x₀.2)
      ((hmemE y).mp hy).1
    have e : (x₀ : G)⁻¹ * ((x₀ : G) * y * (x₀ : G)⁻¹) * (x₀ : G)⁻¹⁻¹ = y := by group
    rwa [e] at h
  have hEcard : Nat.card E = 2 ^ (3 * f) := by
    rw [hE, conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj _).injective, hD.card_inf]
  have hEab : C5.ElemAb2 E := by
    rw [hE]
    exact ((C5.isElemAbelian_two_iff.mp hD.isElemAbelian_right).mono inf_le_right).conjSubgroup _
  have hZE : centerOf (pCoreOf 2 L1) ≤ E := by
    intro z hz
    rw [hmemE]
    have hzc : z * (x₀ : G) = (x₀ : G) * z :=
      Subgroup.mem_centralizer_iff.mp (hD.center_left x₀.2) z hz
    have e : (x₀ : G) * z * (x₀ : G)⁻¹ = z := by
      rw [← hzc]
      group
    rw [e]
    exact ⟨hz.1, hD.center_le_right hH hS hz⟩
  have hEQ₂ : E ⊓ pCoreOf 2 L2 ≤ centerOf (pCoreOf 2 L1) := by
    rintro y ⟨hyE, hyQ₂⟩
    have hyQ₁ : y ∈ pCoreOf 2 L1 := hEQ₁ hyE
    have hu := (hmemE y).mp hyE
    have heq := c₁.equivariant x₀ ⟨y, hyQ₁⟩ ⟨_, hu.1⟩ rfl
    rw [hx₀'] at heq
    have h1 : Multiplicative.toAdd (c₁.β ⟨_, hu.1⟩) 1 = 0 := (c₁.mem_inf_iff _).mp hu.2
    have h2 : Multiplicative.toAdd (c₁.β ⟨y, hyQ₁⟩) 1 = 0 := (c₁.mem_inf_iff _).mp hyQ₂
    have h0 : Multiplicative.toAdd (c₁.β ⟨y, hyQ₁⟩) 0 = 0 := by
      rw [heq] at h1
      funext j
      have h := congrFun h1 j
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
    have hker : (⟨y, hyQ₁⟩ : ↥(pCoreOf 2 L1)) ∈ c₁.β.ker := by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      rw [toAdd_one]
      ext i j
      fin_cases i
      · exact congrFun h0 j
      · exact congrFun h2 j
    rw [c₁.ker_β, Subgroup.mem_subgroupOf] at hker
    exact hker
  obtain ⟨C, hCE, hCZ, hCsup⟩ := C5.exists_complement_elemAb2 hEab hZE
  have hCcard : Nat.card C = 2 ^ (2 * f) := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute C (centerOf (pCoreOf 2 L1))
      fun a ha b hb => hEab.1 a (hCE ha) b (hZE hb)).1
    rw [hCsup, hCZ, Subgroup.card_bot, mul_one, hEcard, hD.card_centerOf_pCoreOf_left] at h
    have hpow : 2 ^ (3 * f) = 2 ^ (2 * f) * 2 ^ f := by
      rw [← pow_add]
      ring_nf
    rw [hpow] at h
    exact (Nat.eq_of_mul_eq_mul_right (by positivity) h).symm
  have hCQ₂ : C ⊓ pCoreOf 2 L2 = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxC, hxQ⟩
    have hxCZ : x ∈ C ⊓ centerOf (pCoreOf 2 L1) := ⟨hxC, hEQ₂ ⟨hCE hxC, hxQ⟩⟩
    rwa [hCZ] at hxCZ
  have hCS : C ≤ S := hCE.trans (hEQ₁.trans hH.pCoreOf_le_left)
  have hCN : C ≤ Subgroup.normalizer (pCoreOf 2 L2 : Set G) :=
    hCS.trans (hSL2.trans (le_normalizer_pCoreOf 2 L2))
  have hCsupS : C ⊔ pCoreOf 2 L2 = S := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hCS hH.pCoreOf_le_right) ?_
    have h := C5.card_sup_mul_card_inf_of_le_normalizer hCN
    rw [hCQ₂, Subgroup.card_bot, mul_one, hCcard, hD.card_right, ← pow_add] at h
    rw [h, hS]
    exact le_of_eq (by ring_nf)
  have hQX : pCoreOf 2 L2 ≤ L2 ⊔ bigB L1 L2 S := (pCoreOf_le 2 L2).trans le_sup_left
  have hXQ : L2 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (pCoreOf 2 L2 : Set G) := by
    rw [sup_bigB_right_of_le hSL2]
    exact sup_le (le_normalizer_pCoreOf 2 L2)
      (hH.h2.borel_le.trans (normalizer_le_normalizer_pCoreOf 2 L2))
  have hQab : ∀ a ∈ pCoreOf 2 L2, ∀ b ∈ pCoreOf 2 L2, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hD.isElemAbelian_right.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hQ2 : IsPGroup 2 (pCoreOf 2 L2) := hH.h1.pgroup.to_le hH.pCoreOf_le_right
  obtain ⟨X₀, hX₀P, hX₀inf, hX₀sup⟩ :=
    C5.exists_complement_of_sylow_split (Q := pCoreOf 2 L2) (X := L2 ⊔ bigB L1 L2 S) (P := S)
      (C := C) hQX hXQ hQab hQ2 (isSylowTwoOf_sup_bigB_right_of_le hH hSL1 hSL2) hCS hCQ₂
      hCsupS
  exact ⟨X₀, hX₀P, by rw [inf_comm]; exact hX₀inf, hX₀sup⟩

theorem U4qLocalData.exists_twist_of_mem_sup_bigB (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f)) {K : Type} [Field K]
    (c₂ : U4qCoordRight L1 L2 S f K) (hU : UnitaryFieldData 2 f K) {p : G}
    (hp : p ∈ L2 ⊔ bigB L1 L2 S) :
    ∃ A : GL (Fin 2) K, A ∈ u4DetFixGL hU ∧
      ActsByMatrix (c₂.coordEquiv hU) p (u4TwistMat hU (A : Matrix (Fin 2) (Fin 2) K)) := by
  have hSL2 : S ≤ L2 := hD.le_right hH hS
  have hP : L2 ⊔ bigB L1 L2 S = L2 ⊔ borelOf L1 S := sup_bigB_right_of_le hSL2
  have hsub : L2 ⊔ bigB L1 L2 S ≤ actsByMatrixSubgroup (c₂.coordEquiv hU) (u4Gamma2 hU) := by
    rw [hP]
    refine sup_le (fun x hx => ?_) (fun d hd => ?_)
    · have hA : Matrix.SpecialLinearGroup.toGL (c₂.α ⟨x, hx⟩) ∈ u4DetFixGL hU := by
        rw [mem_u4DetFixGL, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, (c₂.α ⟨x, hx⟩).2,
          map_one]
      exact mem_actsByMatrixSubgroup.mpr ⟨le_normalizer_pCoreOf 2 L2 hx, _,
        u4TwistHom_mem_u4Gamma2 hU hA, c₂.actsByMatrix_coordEquiv hU ⟨x, hx⟩⟩
    · obtain ⟨A, hA, hdA⟩ := hD.exists_twist_borelOf_left hH hS c₂ hU hd
      exact mem_actsByMatrixSubgroup.mpr
        ⟨normalizer_le_normalizer_pCoreOf 2 L2 (hH.h2.borel_le hd), _,
          u4TwistHom_mem_u4Gamma2 hU hA, hdA⟩
  obtain ⟨-, M, hM, hpM⟩ := mem_actsByMatrixSubgroup.mp (hsub hp)
  obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hM
  exact ⟨A, hA, hpM⟩

theorem U4qLocalData.isLinSemidirect_right (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hS : Nat.card S = 2 ^ (6 * f)) {F K : Type} [Field F] [Field K]
    (c₁ : U4qCoordLeft L1 L2 S f F) (c₂ : U4qCoordRight L1 L2 S f K)
    (hU : UnitaryFieldData 2 f K) :
    IsLinSemidirect (L2 ⊔ bigB L1 L2 S) (pCoreOf 2 L2) (u4Gamma2 hU) := by
  have hSL1 : S ≤ L1 := hD.le_left hH hS
  have hSL2 : S ≤ L2 := hD.le_right hH hS
  have hP : L2 ⊔ bigB L1 L2 S = L2 ⊔ borelOf L1 S := sup_bigB_right_of_le hSL2
  have hPnorm : L2 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (pCoreOf 2 L2 : Set G) := by
    rw [hP]
    exact sup_le (le_normalizer_pCoreOf 2 L2)
      (hH.h2.borel_le.trans (normalizer_le_normalizer_pCoreOf 2 L2))
  have hcent : (L2 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer (pCoreOf 2 L2 : Set G) ≤
      pCoreOf 2 L2 := by
    have h := hH.h2.charTwo
    unfold CharTwo at h
    rw [sup_eq_left.mpr hSL2, ← hP, pCoreOf_sup_bigB_right_of_le hH hSL1 hSL2] at h
    exact h
  refine ⟨(pCoreOf_le 2 L2).trans le_sup_left, hPnorm, hcent,
    hD.exists_complement_right hH hS c₁, c₂.coordEquiv hU, fun p hp => ?_, fun M hM => ?_⟩
  · obtain ⟨A, hA, hpA⟩ := hD.exists_twist_of_mem_sup_bigB hH hS c₂ hU hp
    exact ⟨u4TwistHom hU A, u4TwistHom_mem_u4Gamma2 hU hA, hpA⟩
  obtain ⟨p, hp, hpM⟩ := hD.exists_actsByMatrix_of_mem_u4Gamma2 hH hS c₁ c₂ hU hM
  exact ⟨p, hP ▸ hp, hpM⟩

open CFSG.ClassicalGroups.UnitaryFlag CFSG.Quasithin.H13.U4Par in
theorem U4qLocalData.exists_mulEquiv_parP2 (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hS : Nat.card S = 2 ^ (6 * f)) {F K : Type} [Field F] [Field K]
    (c₁ : U4qCoordLeft L1 L2 S f F) (c₂ : U4qCoordRight L1 L2 S f K)
    (hU : UnitaryFieldData 2 f K) :
    ∃ ψ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(parP2 hU),
      (∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ pCoreOf 2 L2 ↔
        ((ψ x : ↥(parP2 hU)) : hypSU hU 2 0) ∈ radQ2 hU) ∧
      (∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ S ↔
        ((ψ x : ↥(parP2 hU)) : hypSU hU 2 0) ∈ hypUnitriangular hU 2 0) ∧
      ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ Subgroup.normalizer (S : Set G) ↔
        ((ψ x : ↥(parP2 hU)) : hypSU hU 2 0) ∈
          Subgroup.normalizer ((hypUnitriangular hU 2 0 : Subgroup (hypSU hU 2 0)) :
            Set (hypSU hU 2 0)) := by
  haveI : Finite K := hU.finite
  exact (hD.isLinSemidirect_right hH hS c₁ c₂ hU).exists_mulEquiv_sylow
    (isLinSemidirect_parP2 hU)
    (isSylowTwoOf_sup_bigB_right_of_le hH (hD.le_left hH hS) (hD.le_right hH hS))
    (isSylowTwoOf_hypUnitriangular_parP2 hU)

end Vertex

end CFSG.Quasithin.F112R.St84

end
