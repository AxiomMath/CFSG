module

public import CFSG.Quasithin.Vol2.KGFact1296Id
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL4L5
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsL52Q1
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActual
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.FFC4Real
public import CFSG.Quasithin.Vol2.Ch12Sec1H91
public import CFSG.Quasithin.Vol2.Ch12Sec2Statements
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma6One
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Walter.Defs
public import Certificates.Certificate8026Base

public section

namespace CFSG.Quasithin.H13.KG1296

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.L239.L52 CFSG.Quasithin.SLnTwo
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
  CFSG.ComponentClassification.CatalogueBGraphForm

local notation "SL₅" => SpecialLinearGroup (Fin 5) (ZMod 2)
local notation "M₅" => Matrix (Fin 5) (Fin 5) (ZMod 2)

section General

variable {n : ℕ}

theorem vecMul_transvection {i j : Fin n} (hij : i ≠ j) (f : Fin n → ZMod 2) :
    f ᵥ* ((SpecialLinearGroup.transvection hij (1 : ZMod 2) : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = f + Pi.single j (f i) := by
  rw [SpecialLinearGroup.transvection_coe, Matrix.vecMul_add, Matrix.vecMul_one]
  congr 1
  ext k
  by_cases hk : k = j
  · subst hk
    simp [Matrix.vecMul, dotProduct, Matrix.single_apply]
  · simp [Matrix.vecMul, dotProduct, Ne.symm hk, hk]

theorem eq_single_of_ne_zero {v : Fin n → ZMod 2} {k : Fin n} (hv : v ≠ 0)
    (h : ∀ j, j ≠ k → v j = 0) : v = Pi.single k 1 := by
  have hk : v k = 1 := by
    rcases zmod_two_cases (v k) with h0 | h1
    · exfalso
      apply hv
      funext j
      by_cases hj : j = k
      · rw [hj, h0, Pi.zero_apply]
      · exact h j hj
    · exact h1
  funext j
  by_cases hj : j = k
  · rw [hj, hk, Pi.single_eq_same]
  · rw [h j hj, Pi.single_eq_of_ne hj]

theorem slConjugation_eq (A : GL (Fin n) (ZMod 2)) (y : SpecialLinearGroup (Fin n) (ZMod 2)) :
    slConjugation n (ZMod 2) A y = (slEquivGL n).symm A * y * ((slEquivGL n).symm A)⁻¹ := by
  apply Subtype.ext
  have haA : (((slEquivGL n).symm A : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = (A : Matrix (Fin n) (Fin n) (ZMod 2)) := by
    rw [← coe_slEquivGL, MulEquiv.apply_symm_apply]
  have hainv : ((((slEquivGL n).symm A)⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) =
      ((A⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
    rw [← coe_slEquivGL, map_inv, MulEquiv.apply_symm_apply]
  rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    haA, hainv]

theorem coe_conj_graph_transvection (A : GL (Fin n) (ZMod 2)) {P Q : Fin n} (hPQ : P ≠ Q)
    (r s : Fin n) :
    ((slConjugation n (ZMod 2) A (slGraphAut n (ZMod 2)
        (SpecialLinearGroup.transvection hPQ (1 : ZMod 2))) : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) r s =
      (1 : Matrix (Fin n) (Fin n) (ZMod 2)) r s +
        (A : Matrix (Fin n) (Fin n) (ZMod 2)) r Q *
          ((A⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) P s := by
  have ht : (SpecialLinearGroup.transvection hPQ (1 : ZMod 2))⁻¹ =
      SpecialLinearGroup.transvection hPQ (1 : ZMod 2) :=
    inv_eq_of_mul_eq_one_right (transvection_mul_self hPQ)
  rw [coe_slConjugation, slGraphAut_matrix, ht, SpecialLinearGroup.transvection_coe,
    Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.add_apply, Matrix.single_eq_single_vecMulVec_single, mul_vecMulVec, vecMulVec_mul,
    vecMulVec_apply, Matrix.mulVec_single_one, Matrix.single_one_vecMul, Matrix.col_apply,
    Matrix.row_apply]

end General

abbrev Ct : Subgroup SL₅ := Subgroup.centralizer ({transvection15} : Set SL₅)

theorem coe_transvection15_eq :
    ((transvection15 : SL₅) : M₅) = 1 + vecMulVec (Pi.single 0 1) (Pi.single 4 1) := by
  rw [transvection15, SpecialLinearGroup.transvection_coe,
    Matrix.single_eq_single_vecMulVec_single]

theorem mem_Ct_iff {x : SL₅} :
    x ∈ Ct ↔ (x : M₅) *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧
      Pi.single 4 1 ᵥ* (x : M₅) = Pi.single 4 1 := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 := congrArg (fun y : SL₅ => (y : M₅)) h
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_transvection15_eq, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, mul_vecMulVec, vecMulVec_mul] at h1
    have h2 := add_left_cancel h1
    have hcol : ∀ i, ((x : M₅) *ᵥ Pi.single 0 1) i =
        (Pi.single 0 1 : Fin 5 → ZMod 2) i * (Pi.single 4 1 ᵥ* (x : M₅)) 4 := fun i => by
      have := congrFun (congrFun h2 i) 4
      rw [vecMulVec_apply, vecMulVec_apply, Pi.single_eq_same, mul_one] at this
      exact this
    have hrow : ∀ j, (Pi.single 4 1 ᵥ* (x : M₅)) j =
        ((x : M₅) *ᵥ Pi.single 0 1) 0 * (Pi.single 4 1 : Fin 5 → ZMod 2) j := fun j => by
      have := congrFun (congrFun h2 0) j
      rw [vecMulVec_apply, vecMulVec_apply, Pi.single_eq_same, one_mul] at this
      exact this.symm
    have hl : ((x : M₅) *ᵥ Pi.single 0 1) 0 = (Pi.single 4 1 ᵥ* (x : M₅)) 4 := by
      rw [hcol 0, Pi.single_eq_same, one_mul]
    have h1' : ((x : M₅) *ᵥ Pi.single 0 1) 0 = 1 := by
      rcases zmod_two_cases (((x : M₅) *ᵥ Pi.single 0 1) 0) with h0 | h0
      · exfalso
        have hz : (x : M₅) *ᵥ Pi.single 0 1 = 0 := funext fun i => by
          rw [hcol i, ← hl, h0, mul_zero, Pi.zero_apply]
        have hdet := Matrix.exists_mulVec_eq_zero_iff.1 ⟨Pi.single 0 1, fun h => by
          have := congrFun h 0
          rw [Pi.single_eq_same, Pi.zero_apply] at this
          exact one_ne_zero this, hz⟩
        rw [x.2] at hdet
        exact one_ne_zero hdet
      · exact h0
    refine ⟨funext fun i => ?_, funext fun j => ?_⟩
    · rw [hcol i, ← hl, h1', mul_one]
    · rw [hrow j, h1', one_mul]
  · rintro ⟨h1, h2⟩
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_transvection15_eq, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, mul_vecMulVec, vecMulVec_mul, h1, h2]

theorem Ct_le_Pone : Ct ≤ Pone 5 := fun x hx =>
  mem_Pone_of_col (k := 4) fun i => by
    have := congrFun (mem_Ct_iff.1 hx).1 i
    rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] at this
    exact this

theorem Ct_eq : Ct = flagStabilizer 5 (ZMod 2) {1, 4} := by
  ext x
  rw [mem_Ct_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine mem_flagStabilizer_of_entries fun k l c hc hl hk => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl
    · have := congrFun h1 k
      rw [Matrix.mulVec_single_one, Matrix.col_apply,
        Pi.single_eq_of_ne (show k ≠ 0 from fun h => by rw [h] at hk; simp at hk)] at this
      rwa [show l = 0 from Fin.ext (by omega)]
    · have := congrFun h2 l
      rw [Matrix.single_one_vecMul, Matrix.row_apply,
        Pi.single_eq_of_ne (show l ≠ 4 from fun h => by rw [h] at hl; simp at hl)] at this
      rwa [show k = 4 from Fin.ext (by omega)]
  · intro hx
    have h00 : blkAt 0 1 (by norm_num) (x : M₅) = 1 :=
      blkAt_one_eq_one (Nat.card_zmod 2) _ 0 (by norm_num) (blockLeft_zero _ 1)
        (blockRight_of_cut (Or.inr (by simp))) ⟨x, hx⟩
    have h44 : blkAt 4 1 (by norm_num) (x : M₅) = 1 :=
      blkAt_one_eq_one (Nat.card_zmod 2) _ 4 (by norm_num) (blockLeft_of_cut 1 (Or.inr (by simp)))
        (blockRight_top _ (by norm_num)) ⟨x, hx⟩
    have h00' : (x : M₅) 0 0 = 1 := congrFun (congrFun h00 0) 0
    have h44' : (x : M₅) 4 4 = 1 := congrFun (congrFun h44 0) 0
    refine ⟨funext fun i => ?_, funext fun j => ?_⟩
    · rw [Matrix.mulVec_single_one, Matrix.col_apply]
      by_cases hi : i = 0
      · rw [hi, h00', Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hi]
        exact stabilizer_entries (mem_flagStabilizer.1 hx 1 (by simp)) (l := 0) (by simp)
          (by have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h); omega)
    · rw [Matrix.single_one_vecMul, Matrix.row_apply]
      by_cases hj : j = 4
      · rw [hj, h44', Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hj]
        exact stabilizer_entries (mem_flagStabilizer.1 hx 4 (by simp)) (k := 4)
          (by have : (j : ℕ) ≠ 4 := fun h => hj (Fin.ext h); omega) (by simp)

theorem transvection_mem_Ct {i j : Fin 5} (hij : i ≠ j) (hj : j ≠ 0) (hi : i ≠ 4) :
    SpecialLinearGroup.transvection hij (1 : ZMod 2) ∈ Ct := by
  refine mem_Ct_iff.2 ⟨?_, ?_⟩
  · rw [mulVec_transvection, Pi.single_eq_of_ne hj, Pi.single_zero, add_zero]
  · rw [vecMul_transvection, Pi.single_eq_of_ne hi, Pi.single_zero, add_zero]

theorem fixed_Ct {v : Fin 5 → ZMod 2} (h : ∀ x ∈ Ct, (x : M₅) *ᵥ v = v) (j : Fin 5)
    (hj : j ≠ 0) : v j = 0 := by
  have := h _ (transvection_mem_Ct (Ne.symm hj) hj (by decide))
  rw [mulVec_transvection] at this
  have h2 := congrFun this 0
  simpa using h2

theorem fixed_row_Ct {f : Fin 5 → ZMod 2} (h : ∀ x ∈ Ct, f ᵥ* (x : M₅) = f) (i : Fin 5)
    (hi : i ≠ 4) : f i = 0 := by
  have := h _ (transvection_mem_Ct hi (by decide) hi)
  rw [vecMul_transvection] at this
  have h2 := congrFun this 4
  simpa using h2

theorem mem_Ct_of_normalizes {g : SL₅} (h : ∀ x ∈ Ct, g * x * g⁻¹ ∈ Ct) : g ∈ Ct := by
  set v : Fin 5 → ZMod 2 := ((g⁻¹ : SL₅) : M₅) *ᵥ Pi.single 0 1 with hv
  have hgv : (g : M₅) *ᵥ v = Pi.single 0 1 := by
    rw [hv, Matrix.mulVec_mulVec, coe_mul_inv, Matrix.one_mulVec]
  have hconj : ∀ y : M₅, ((g⁻¹ : SL₅) : M₅) * ((g : M₅) * y * ((g⁻¹ : SL₅) : M₅)) =
      y * ((g⁻¹ : SL₅) : M₅) := fun y => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, coe_inv_mul, Matrix.one_mul]
  have hfix : ∀ x ∈ Ct, (x : M₅) *ᵥ v = v := by
    intro x hx
    have h1 := (mem_Ct_iff.1 (h x hx)).1
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h1
    calc (x : M₅) *ᵥ v = ((x : M₅) * ((g⁻¹ : SL₅) : M₅)) *ᵥ Pi.single 0 1 := by
          rw [hv, Matrix.mulVec_mulVec]
      _ = (((g⁻¹ : SL₅) : M₅) * ((g : M₅) * (x : M₅) * ((g⁻¹ : SL₅) : M₅))) *ᵥ
            Pi.single 0 1 := by rw [hconj]
      _ = ((g⁻¹ : SL₅) : M₅) *ᵥ (((g : M₅) * (x : M₅) * ((g⁻¹ : SL₅) : M₅)) *ᵥ
            Pi.single 0 1) := by rw [Matrix.mulVec_mulVec]
      _ = v := by rw [h1]
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0, Matrix.mulVec_zero] at hgv
    have := congrFun hgv 0
    rw [Pi.single_eq_same, Pi.zero_apply] at this
    exact zero_ne_one this
  have hve := eq_single_of_ne_zero hv0 (fixed_Ct hfix)
  set f : Fin 5 → ZMod 2 := Pi.single 4 1 ᵥ* (g : M₅) with hf
  have hconj' : ∀ y : M₅, (g : M₅) * y * ((g⁻¹ : SL₅) : M₅) * (g : M₅) = (g : M₅) * y := fun y => by
    rw [Matrix.mul_assoc, coe_inv_mul, Matrix.mul_one]
  have hfix' : ∀ x ∈ Ct, f ᵥ* (x : M₅) = f := by
    intro x hx
    have h2 := (mem_Ct_iff.1 (h x hx)).2
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h2
    calc f ᵥ* (x : M₅) = Pi.single 4 1 ᵥ* ((g : M₅) * (x : M₅)) := by
          rw [hf, Matrix.vecMul_vecMul]
      _ = Pi.single 4 1 ᵥ* ((g : M₅) * (x : M₅) * ((g⁻¹ : SL₅) : M₅) * (g : M₅)) := by
          rw [hconj']
      _ = (Pi.single 4 1 ᵥ* ((g : M₅) * (x : M₅) * ((g⁻¹ : SL₅) : M₅))) ᵥ* (g : M₅) := by
          rw [Matrix.vecMul_vecMul]
      _ = f := by rw [h2]
  have hf0 : f ≠ 0 := by
    intro h0
    have : f ᵥ* ((g⁻¹ : SL₅) : M₅) = Pi.single 4 1 := by
      rw [hf, Matrix.vecMul_vecMul, coe_mul_inv, Matrix.vecMul_one]
    rw [h0, Matrix.zero_vecMul] at this
    have := congrFun this 4
    rw [Pi.single_eq_same, Pi.zero_apply] at this
    exact zero_ne_one this
  have hfe := eq_single_of_ne_zero hf0 (fixed_row_Ct hfix')
  refine mem_Ct_iff.2 ⟨?_, hfe⟩
  have h1 := hgv
  rw [hve] at h1
  exact h1

@[expose] noncomputable def qCt : ↥Ct →* SpecialLinearGroup (Fin 3) (ZMod 2) :=
  (q1 (ZMod 2) (Nat.card_zmod 2)).comp (Subgroup.inclusion Ct_eq.le)

theorem qCt_apply (x : ↥Ct) (p q : Fin 3) :
    ((qCt x : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) p q =
      ((x : SL₅) : M₅) ⟨1 + p, by omega⟩ ⟨1 + q, by omega⟩ := rfl

theorem qCt_surjective : Function.Surjective qCt := by
  intro M
  obtain ⟨y, hy⟩ := q1_surjective (K := ZMod 2) (Nat.card_zmod 2) M
  exact ⟨⟨y, by rw [Ct_eq]; exact y.2⟩, hy⟩

theorem qCt_eq_one_of_mem_pCoreOf {x : SL₅} (hx : x ∈ pCoreOf 2 Ct) :
    qCt ⟨x, CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx⟩ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := ((pCoreOf 2 Ct).subgroupOf Ct).map qCt with hN
  have hNn : N.Normal := by
    refine Subgroup.Normal.map ⟨fun y hy z => ?_⟩ _ qCt_surjective
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact (Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ z.2) _).1 hy
  have hN2 : IsPGroup 2 N :=
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).comap_subtype).map _
  have hbot := CFSG.Quasithin.H13.KGH91.NatCoord.eq_bot_of_normal_isPGroup (n := 3) le_rfl hN2
  have hmem : qCt ⟨x, CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx⟩ ∈ N := ⟨_, hx, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hmem

theorem mid_eq_of_mul_inv_mem {x y : SL₅} (hx : x ∈ Ct) (hy : y ∈ Ct)
    (h : y * x⁻¹ ∈ pCoreOf 2 Ct) (p q : Fin 3) :
    (y : M₅) ⟨1 + p, by omega⟩ ⟨1 + q, by omega⟩ =
      (x : M₅) ⟨1 + p, by omega⟩ ⟨1 + q, by omega⟩ := by
  have h1 := qCt_eq_one_of_mem_pCoreOf h
  have h2 : qCt ⟨y, hy⟩ = qCt ⟨x, hx⟩ := by
    have e : (⟨y * x⁻¹, CFSG.LieType.BorelTits.pCoreOf_le 2 _ h⟩ : ↥Ct) =
        ⟨y, hy⟩ * (⟨x, hx⟩ : ↥Ct)⁻¹ := rfl
    rw [e, map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  rw [← qCt_apply ⟨y, hy⟩, ← qCt_apply ⟨x, hx⟩, h2]

theorem innClosed_Ct : InnClosed Ct := by
  intro α hα hα2
  obtain ⟨A, ε, hε, rfl⟩ := exists_conj_graph (by norm_num) α
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · rw [pow_zero, mul_one] at hα ⊢
    have haC : (slEquivGL 5).symm A ∈ Ct :=
      mem_Ct_of_normalizes fun x hx => slConjugation_eq A x ▸ hα x hx
    exact ⟨_, haC, MulEquiv.ext fun g => slConjugation_eq A g⟩
  · exfalso
    rw [pow_one] at hα hα2
    have key : ∀ {P Q : Fin 5} (hPQ : P ≠ Q), Q ≠ 0 → P ≠ 4 → ∀ p q : Fin 3,
        (A : M₅) ⟨1 + p, by omega⟩ Q *
          ((A⁻¹ : GL (Fin 5) (ZMod 2)) : M₅) P ⟨1 + q, by omega⟩ =
        ((SpecialLinearGroup.transvection hPQ (1 : ZMod 2) : SL₅) : M₅) ⟨1 + p, by omega⟩
          ⟨1 + q, by omega⟩ - (1 : M₅) ⟨1 + p, by omega⟩ ⟨1 + q, by omega⟩ := by
      intro P Q hPQ hQ hP p q
      have hx := transvection_mem_Ct hPQ hQ hP
      have h := mid_eq_of_mul_inv_mem hx (hα _ hx) (hα2 _ hx) p q
      rw [MulAut.mul_apply, coe_conj_graph_transvection] at h
      rw [← h]
      ring
    have h1 := key (P := 1) (Q := 2) (by decide) (by decide) (by decide) 0 1
    have h2 := key (P := 1) (Q := 2) (by decide) (by decide) (by decide) 2 1
    have h3 := key (P := 3) (Q := 2) (by decide) (by decide) (by decide) 2 1
    simp only [SpecialLinearGroup.transvection_coe] at h1 h2 h3
    norm_num [Matrix.one_apply, Matrix.single_apply] at h1 h2 h3
    rcases h2 with h2 | h2 <;> simp_all

theorem graphFun_transvection15 : BinaryParabolic.graphFun transvection15 = transvection15 := by
  have ht : transvection15 * transvection15 = 1 :=
    transvection_mul_self (show (0 : Fin 5) ≠ 4 by decide)
  apply Subtype.ext
  rw [BinaryParabolic.coe_graphFun, inv_eq_of_mul_eq_one_right ht]
  decide

theorem map_graphAut_Ct : Ct.map (BinaryParabolic.graphAut 5).toMonoidHom = Ct := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  show BinaryParabolic.graphFun x * transvection15 = transvection15 * BinaryParabolic.graphFun x ↔
    x * transvection15 = transvection15 * x
  constructor
  · intro h
    have := congrArg BinaryParabolic.graphFun h
    rwa [BinaryParabolic.graphFun_mul, BinaryParabolic.graphFun_mul,
      BinaryParabolic.graphFun_graphFun, graphFun_transvection15] at this
  · intro h
    rw [← graphFun_transvection15, ← BinaryParabolic.graphFun_mul,
      ← BinaryParabolic.graphFun_mul, h]

theorem Ct_le_graph_Pone : Ct ≤ (Pone 5).map (BinaryParabolic.graphAut 5).toMonoidHom :=
  map_graphAut_Ct ▸ Subgroup.map_mono Ct_le_Pone

theorem not_Pone_le_normalizer_Ct : ¬ Pone 5 ≤ Subgroup.normalizer (Ct : Set SL₅) := by
  intro h
  have hg := transvection_mem_Pone (n := 5) (by norm_num) (show (4 : Fin 5) ≠ 3 by decide)
    (by decide)
  have hC := mem_Ct_of_normalizes fun x hx => (Subgroup.mem_normalizer_iff.1 (h hg) x).1 hx
  have h2 := (mem_Ct_iff.1 hC).2
  rw [vecMul_transvection] at h2
  have := congrFun h2 3
  simp at this

theorem not_graph_Pone_le_normalizer_Ct :
    ¬ (Pone 5).map (BinaryParabolic.graphAut 5).toMonoidHom ≤
      Subgroup.normalizer (Ct : Set SL₅) := by
  intro h
  apply not_Pone_le_normalizer_Ct
  have := map_le_normalizer_map (BinaryParabolic.graphAut 5) h
  rwa [map_graphAut_map_graphAut, map_graphAut_Ct] at this

end CFSG.Quasithin.H13.KG1296
