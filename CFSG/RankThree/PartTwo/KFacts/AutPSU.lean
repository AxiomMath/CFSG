module

public import CFSG.RankThree.PartTwo.KFacts.AutKinds
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryAutomorphismRealization
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
public import CFSG.LieType.Universal.Unitary.Clause0
import CFSG.LocalAnalysis.ComponentInitial.ScalarSemilinearNormalizer

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut map_bar_comm)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (restrictAutHom restrictAutHom_apply
  quotientAutHom quotientAutHom_mk)
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism (map_mul_ringEquiv map_one_ringEquiv
  unitary_three_full_semilinear_automorphism_realization)
open Matrix

section CenterDescend

variable (S : Type*) [Group S]

@[expose] noncomputable def centerDescend : MulAut S →* MulAut (S ⧸ Subgroup.center S) where
  toFun σ := QuotientGroup.congr _ _ σ (Subgroup.map_center_eq σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

theorem centerDescend_mk (σ : MulAut S) (x : S) :
    centerDescend S σ (x : S ⧸ Subgroup.center S) = ((σ x : S) : S ⧸ Subgroup.center S) :=
  rfl

end CenterDescend

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] def unitaryIsom3 : Subgroup (GL (Fin 3) K) where
  carrier := {A | ((A : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * A = 1}
  mul_mem' {A B} hA hB := by
    change ((((A * B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).map h.bar)ᵀ * (A * B : GL _ K) =
      1
    rw [Units.val_mul, Matrix.map_mul, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ B.1]
    change _ * ((((A : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * A) * B) = 1
    rw [hA, Matrix.one_mul]
    exact hB
  one_mem' := by
    change (((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
      ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1
    rw [Units.val_one, Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one,
      Matrix.one_mul]
  inv_mem' {A} hA := by
    change ((((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).map h.bar)ᵀ *
      ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1
    have hinv : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((A : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ :=
      Units.inv_eq_of_mul_eq_one_left hA
    have hbb : (((A : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ.map h.bar)ᵀ =
        (A : Matrix (Fin 3) (Fin 3) K) := by
      ext i j
      simp [UnitaryFieldData.bar_bar]
    rw [hinv, hbb, ← hinv, ← Units.val_mul, mul_inv_cancel, Units.val_one]

variable {h}

theorem mem_unitaryIsom3 {A : GL (Fin 3) K} :
    A ∈ unitaryIsom3 h ↔ ((A : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * A = 1 :=
  Iff.rfl

theorem unitarySU_le_unitaryIsom3 : unitarySU p f K 3 ≤ unitaryIsom3 h :=
  fun _ hg => ((mem_unitarySU_iff h).mp hg).2

theorem conj_mem_unitarySU {A : GL (Fin 3) K} (hA : A ∈ unitaryIsom3 h) {g : GL (Fin 3) K}
    (hg : g ∈ unitarySU p f K 3) : A * g * A⁻¹ ∈ unitarySU p f K 3 := by
  refine (mem_unitarySU_iff h).mpr ⟨?_, mul_mem (mul_mem hA (unitarySU_le_unitaryIsom3 hg))
    (inv_mem hA)⟩
  rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj]
  exact ((mem_unitarySU_iff h).mp hg).1

theorem glAut_mem_unitaryIsom3 (σ : K ≃+* K) {A : GL (Fin 3) K} (hA : A ∈ unitaryIsom3 h) :
    glAut σ A ∈ unitaryIsom3 h := by
  rw [mem_unitaryIsom3, coe_glAut]
  have hcomm : ((A : Matrix (Fin 3) (Fin 3) K).map σ).map h.bar =
      ((A : Matrix (Fin 3) (Fin 3) K).map h.bar).map σ := by
    ext i j
    simp [map_bar_comm h σ]
  rw [hcomm, ← transpose_map, ← map_mul_ringEquiv]
  change (((A : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * A).map σ = 1
  rw [hA, map_one_ringEquiv]

theorem glAut_mem_unitarySU (h : UnitaryFieldData p f K) (σ : K ≃+* K) {g : GL (Fin 3) K}
    (hg : g ∈ unitarySU p f K 3) : glAut σ g ∈ unitarySU p f K 3 := by
  refine (mem_unitarySU_iff h).mpr
    ⟨?_, glAut_mem_unitaryIsom3 σ (unitarySU_le_unitaryIsom3 (h := h) hg)⟩
  rw [coe_glAut, ← RingEquiv.mapMatrix_apply, ← RingEquiv.map_det,
    ((mem_unitarySU_iff h).mp hg).1, map_one]

variable (h)

@[expose] noncomputable def suConj : unitaryIsom3 h →* MulAut (unitarySU p f K 3) :=
  restrictAutHom ((MulAut.conj : GL (Fin 3) K →* MulAut (GL (Fin 3) K)).comp
    (unitaryIsom3 h).subtype) (unitarySU p f K 3) fun A _ hg => conj_mem_unitarySU A.2 hg

@[expose] noncomputable def suField (h : UnitaryFieldData p f K) :
    (K ≃+* K) →* MulAut (unitarySU p f K 3) :=
  restrictAutHom glAut (unitarySU p f K 3) fun σ _ hg => glAut_mem_unitarySU h σ hg

variable {h}

theorem coe_suConj (A : unitaryIsom3 h) (g : unitarySU p f K 3) :
    ((suConj h A g : unitarySU p f K 3) : GL (Fin 3) K) = A * g * A⁻¹ :=
  rfl

theorem coe_suField (σ : K ≃+* K) (g : unitarySU p f K 3) :
    ((suField h σ g : unitarySU p f K 3) : GL (Fin 3) K) = glAut σ g :=
  rfl

theorem suConj_mem_unitaryScalars (A : unitaryIsom3 h) {z : unitarySU p f K 3}
    (hz : z ∈ unitaryScalars h 3) : suConj h A z ∈ unitaryScalars h 3 := by
  obtain ⟨c, hc, hc3, hzc⟩ := hz
  refine ⟨c, hc, hc3, ?_⟩
  rw [coe_suConj, hzc, Subgroup.coe_inv, (commute_scalar c _).eq, mul_inv_cancel_right]

theorem suField_mem_unitaryScalars (σ : K ≃+* K) {z : unitarySU p f K 3}
    (hz : z ∈ unitaryScalars h 3) : suField h σ z ∈ unitaryScalars h 3 := by
  obtain ⟨c, hc, hc3, hzc⟩ := hz
  refine ⟨Units.map (σ : K →* K) c, ?_, ?_, ?_⟩
  · rw [Units.coe_map]
    change h.norm (σ (c : K)) = 1
    rw [UnitaryFieldData.norm, ← map_bar_comm, ← map_mul]
    change σ (h.norm (c : K)) = 1
    rw [hc, map_one]
  · rw [← map_pow, hc3, map_one]
  · rw [coe_suField, hzc]
    apply Units.ext
    rw [coe_glAut, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar, scalar_apply,
      scalar_apply, diagonal_map (map_zero σ), Units.coe_map]
    rfl

variable (h)

@[expose] noncomputable def psuConj : unitaryIsom3 h →* MulAut (unitaryPSU h 3) :=
  quotientAutHom (suConj h) (unitaryScalars h 3) fun A _ hz => suConj_mem_unitaryScalars A hz

@[expose] noncomputable def psuField : (K ≃+* K) →* MulAut (unitaryPSU h 3) :=
  quotientAutHom (suField h) (unitaryScalars h 3) fun σ _ hz => suField_mem_unitaryScalars σ hz

variable {h}

theorem psuConj_mk (A : unitaryIsom3 h) (g : unitarySU p f K 3) :
    psuConj h A (g : unitaryPSU h 3) = ((suConj h A g : unitarySU p f K 3) : unitaryPSU h 3) :=
  rfl

theorem psuField_mk (σ : K ≃+* K) (g : unitarySU p f K 3) :
    psuField h σ (g : unitaryPSU h 3) = ((suField h σ g : unitarySU p f K 3) : unitaryPSU h 3) :=
  rfl

theorem conj_mk_eq_psuConj (g : unitarySU p f K 3) :
    MulAut.conj (g : unitaryPSU h 3) = psuConj h ⟨g, unitarySU_le_unitaryIsom3 g.2⟩ := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H y =>
    rw [MulAut.conj_apply, psuConj_mk]
    rfl

variable (h)

@[expose] noncomputable def stdPinnedPSU3 : PinnedAut (unitaryPSU h 3) where
  inndiag := (psuConj h).range
  inn_le := by
    rintro _ ⟨x, rfl⟩
    induction x using QuotientGroup.induction_on with
    | H g => exact ⟨_, (conj_mk_eq_psuConj g).symm⟩
  field := (psuField h).range
  graph := ∅

variable {h}

theorem psuField_mul_psuConj_mul_inv (σ : K ≃+* K) (A : unitaryIsom3 h) :
    psuField h σ * psuConj h A * (psuField h σ)⁻¹ =
      psuConj h ⟨glAut σ A, glAut_mem_unitaryIsom3 σ A.2⟩ := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [← map_inv, MulAut.mul_apply, MulAut.mul_apply, psuField_mk, psuConj_mk, psuField_mk,
      psuConj_mk]
    congr 1
    apply Subtype.ext
    rw [coe_suField, coe_suConj, coe_suField, coe_suConj, map_mul, map_mul, map_inv,
      ← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply, Subgroup.coe_inv, map_inv]
    rfl

theorem exists_psuConj_mul_psuField (hq : 2 < p ^ f) (α : MulAut (unitaryPSU h 3)) :
    ∃ (A : unitaryIsom3 h) (σ : K ≃+* K), α = psuConj h A * psuField h σ := by
  obtain ⟨σ, A, hA, hα⟩ := unitary_three_full_semilinear_automorphism_realization h hq α
  refine ⟨⟨A, hA⟩, σ, ?_⟩
  ext x
  induction x using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨hg, hαg⟩ := hα g
    rw [MulAut.mul_apply, psuField_mk, psuConj_mk]
    exact hαg.trans (congrArg (unitaryProj h 3) (Subtype.ext rfl))

theorem stdPinnedPSU3_stable (hq : 2 < p ^ f) : (stdPinnedPSU3 h).Stable := by
  have := h.finite
  have hcomm : ∀ σ τ : K ≃+* K, psuField h σ * psuField h τ = psuField h τ * psuField h σ :=
    fun σ τ => by rw [← map_mul, ← map_mul, ringAut_mul_comm K σ τ]
  have hconj : ∀ α : MulAut (unitaryPSU h 3), ∃ A : unitaryIsom3 h, ∀ τ : K ≃+* K,
      α * psuField h τ * α⁻¹ = psuConj h A * psuField h τ * (psuConj h A)⁻¹ := by
    intro α
    obtain ⟨A, σ, rfl⟩ := exists_psuConj_mul_psuField hq α
    refine ⟨A, fun τ => ?_⟩
    have h1 := hcomm σ τ
    calc psuConj h A * psuField h σ * psuField h τ * (psuConj h A * psuField h σ)⁻¹ =
        psuConj h A * (psuField h σ * psuField h τ) * (psuField h σ)⁻¹ * (psuConj h A)⁻¹ := by
          group
      _ = psuConj h A * psuField h τ * (psuConj h A)⁻¹ := by rw [h1]; group
  refine ⟨⟨fun d hd α => ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨B, rfl⟩ := hd
    obtain ⟨A, σ, rfl⟩ := exists_psuConj_mul_psuField hq α
    refine ⟨A * ⟨glAut σ B, glAut_mem_unitaryIsom3 σ B.2⟩ * A⁻¹, ?_⟩
    rw [map_mul, map_mul, map_inv, ← psuField_mul_psuConj_mul_inv]
    group
  · rintro α _ ⟨τ, rfl⟩ h1
    obtain ⟨A, hA⟩ := hconj α
    exact ⟨psuField h τ, ⟨τ, rfl⟩, h1, psuConj h A, ⟨A, rfl⟩, hA τ⟩
  · rintro α γ hγ
    exact absurd hγ (Set.notMem_empty γ)
  · rintro α γ φ hγ
    exact absurd hγ (Set.notMem_empty γ)

theorem center_unitarySU_three (hq : 2 < p ^ f) :
    Subgroup.center (unitarySU p f K 3) = unitaryScalars h 3 := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have hcard : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  rw [unitaryScalars_eq h (by norm_num)]
  exact (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hcard le_rfl
    (by intro hh; simp only [Prod.mk.injEq, true_and] at hh; omega)).2

variable (h) in
@[expose] noncomputable def suCenterEquiv (hq : 2 < p ^ f) :
    unitarySU p f K 3 ⧸ Subgroup.center (unitarySU p f K 3) ≃* unitaryPSU h 3 :=
  QuotientGroup.quotientMulEquivOfEq (center_unitarySU_three hq)

section Induced

variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)

variable (h) in
@[expose] def InducesKindPSU3 (x : G) (k : AutKind) : Prop :=
  ∃ e : L ⧸ aschbacherSolvableCore 3 L ≃* unitaryPSU h 3, InducesKind L (stdPinnedPSU3 h) e x k

variable (h) in
@[expose] def InducesKindSU3 (hq : 2 < p ^ f) (x : G) (k : AutKind) : Prop :=
  ∃ e : L ⧸ aschbacherSolvableCore 3 L ≃* unitarySU p f K 3,
    ∃ hx : x ∈ Subgroup.normalizer (L : Set G),
      (stdPinnedPSU3 h).HasKind (MulAut.congr (suCenterEquiv h hq)
        (centerDescend _ (inducedAutHom L e ⟨x, hx⟩))) k

theorem inducesKindPSU3_iff (hq : 2 < p ^ f) (e : L ⧸ aschbacherSolvableCore 3 L ≃* unitaryPSU h 3)
    (x : G) (k : AutKind) :
    InducesKindPSU3 h L x k ↔ InducesKind L (stdPinnedPSU3 h) e x k := by
  constructor
  · rintro ⟨e', h'⟩
    exact (inducesKind_iff_of_stable L (stdPinnedPSU3_stable hq) e' e x k).1 h'
  · intro h'
    exact ⟨e, h'⟩

theorem inducesKindSU3_iff (hq : 2 < p ^ f)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* unitarySU p f K 3) (x : G) (k : AutKind) :
    InducesKindSU3 h L hq x k ↔
      ∃ hx : x ∈ Subgroup.normalizer (L : Set G),
        (stdPinnedPSU3 h).HasKind (MulAut.congr (suCenterEquiv h hq)
          (centerDescend _ (inducedAutHom L e ⟨x, hx⟩))) k := by
  constructor
  · rintro ⟨e', hx, h'⟩
    refine ⟨hx, ?_⟩
    rw [inducedAutHom_eq_conj L e' e, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
    exact ((stdPinnedPSU3_stable hq).hasKind_conj _ _ k).2 h'
  · rintro ⟨hx, h'⟩
    exact ⟨e, hx, h'⟩

end Induced

end CFSG.RankThree.PartTwo.KFacts
