module

public import CFSG.OddTranspositions.PartFour.Fourteen.ModelO4Minus
import all CFSG.OddTranspositions.PartFour.Fourteen.ModelO4Minus
import CFSG.Quasithin.Vol2.Ch11SecBK10H
import CFSG.CGT.Timmesfeld75.L2AutInvol
import CFSG.GroupTheory.CommutatorIndexTwo
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs
public import CFSG.LocalAnalysis.WeakClosure81.SevenFour
public import CFSG.LocalAnalysis.WeakClosure81.SevenNineDefs
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.Quasithin.Vol2.Ch11SecBK10A

public section

namespace CFSG.OddTranspositions.PartFour

open Matrix

local notation "x[" c "]" =>
  Matrix.SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c

variable {K : Type} [Field K] [CharP K 2] (D : HermInvol K)

theorem slGL_map (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    D.slGL (Matrix.SpecialLinearGroup.map D.σ.toRingHom A) = D.Rg * D.slGL A * D.Rg := by
  have hcoe : ((Matrix.SpecialLinearGroup.map D.σ.toRingHom A :
      Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (A : Matrix (Fin 2) (Fin 2) K).map D.σ := by
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    rfl
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, D.slGL_coe, D.slGL_coe, D.Rg_coe, hcoe, D.matOf_map_σ]

theorem slGL_injective (h4 : 4 ≤ Nat.card K) : Function.Injective D.slGL := by
  have hker : ∀ A : Matrix.SpecialLinearGroup (Fin 2) K, D.slGL A = 1 → A = 1 := by
    intro A hA
    have h1 : D.psiN (QuotientGroup.mk A) = 1 := by
      rw [D.psiN_mk]; exact hA
    have h2 : QuotientGroup.mk A = 1 :=
      D.psiN_injective h4 (h1.trans (map_one D.psiN).symm)
    have h3 : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) :=
      (QuotientGroup.eq_one_iff A).mp h2
    rw [CFSG.Quasithin.Vol2.Ch11.SecD.BK10.L2.center_sl_eq_bot, Subgroup.mem_bot] at h3
    exact h3
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro A hA
  rw [Subgroup.mem_bot]
  exact hker A (MonoidHom.mem_ker.mp hA)

@[expose] noncomputable def minusN :
    Subgroup ↥(CFSG.PGLModel.orthogonalMinus 1 D.F D.b D.c) :=
  D.slGL.range.subgroupOf (CFSG.PGLModel.orthogonalMinus 1 D.F D.b D.c)

@[expose] noncomputable def minusNHom :
    Matrix.SpecialLinearGroup (Fin 2) K →* ↥(minusN D) where
  toFun A := ⟨⟨D.slGL A, D.slGL_mem_orth A⟩, ⟨A, rfl⟩⟩
  map_one' := Subtype.ext (Subtype.ext (map_one D.slGL))
  map_mul' A B := Subtype.ext (Subtype.ext (map_mul D.slGL A B))

@[expose] noncomputable def minusNEquiv (h4 : 4 ≤ Nat.card K) :
    Matrix.SpecialLinearGroup (Fin 2) K ≃* ↥(minusN D) :=
  MulEquiv.ofBijective (minusNHom D)
    ⟨fun A B h => slGL_injective D h4 (congrArg (fun x : ↥(minusN D) =>
      ((x.1 : ↥(CFSG.PGLModel.orthogonalMinus 1 D.F D.b D.c)) : GL HermInvol.Ix D.F)) h),
     fun x => by
      obtain ⟨A, hA⟩ := x.2
      exact ⟨A, Subtype.ext (Subtype.ext hA)⟩⟩

theorem natCard_orth_eq_two_mul [Finite K] :
    Nat.card ↥(CFSG.PGLModel.orthogonalMinus 1 D.F D.b D.c) =
      2 * Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) =
      Nat.card K * (Nat.card K ^ 2 - 1) := CFSG.GorensteinWalter.sl2_card_formula K
  have hqpos : 0 < Nat.card ↥D.F := Nat.card_pos
  have hq2 : 1 ≤ Nat.card ↥D.F ^ 2 := Nat.one_le_pow _ _ hqpos
  have hq4 : 1 ≤ (Nat.card ↥D.F ^ 2) ^ 2 := Nat.one_le_pow _ _ hq2
  have h1 : ((Nat.card ↥(CFSG.PGLModel.orthogonalMinus 1 D.F D.b D.c) : ℕ) : ℤ) =
      2 * (Nat.card ↥D.F : ℤ) ^ 2 *
        (((Nat.card ↥D.F : ℤ) ^ 2 + 1) * ((Nat.card ↥D.F : ℤ) ^ 2 - 1)) := D.natCard_orth
  have h2 : ((Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) : ℕ) : ℤ) =
      (Nat.card ↥D.F : ℤ) ^ 2 * (((Nat.card ↥D.F : ℤ) ^ 2) ^ 2 - 1) := by
    rw [hSL, D.natCard_K]
    push_cast [hq4]
    ring
  have h3 : ((Nat.card ↥(CFSG.PGLModel.orthogonalMinus 1 D.F D.b D.c) : ℕ) : ℤ) =
      ((2 * Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) : ℕ) : ℤ) := by
    push_cast
    rw [h1, h2]
    ring
  exact Nat.cast_injective h3

theorem index_minusN [Finite K] (h4 : 4 ≤ Nat.card K) : (minusN D).index = 2 := by
  have hcardN : Nat.card ↥(minusN D) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Nat.card_congr (minusNEquiv D h4).toEquiv.symm
  have hcard := Subgroup.card_mul_index (minusN D)
  rw [hcardN, natCard_orth_eq_two_mul D] at hcard
  have hpos : 0 < Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := Nat.card_pos
  have h2 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) * (minusN D).index =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) * 2 := by
    rw [hcard, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hpos h2

theorem commutator_minusN_eq_top [Finite K] (h4 : 4 ≤ Nat.card K) :
    commutator ↥(minusN D) = ⊤ := by
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.ClassicalInvolution.sl2_isPerfect h4
  have htop : Subgroup.map (minusNEquiv D h4).toMonoidHom (⊤ :
      Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) = ⊤ :=
    Subgroup.map_top_of_surjective _ (minusNEquiv D h4).surjective
  have hcomm : ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)),
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K))⁆ =
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) :=
    hperf.commutator_eq_top
  have hmap := Subgroup.map_commutator (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K))
    (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) (minusNEquiv D h4).toMonoidHom
  rw [hcomm] at hmap
  rw [htop] at hmap
  exact hmap.symm

theorem commutator_orthogonalMinus_one [Finite K] (h4 : 4 ≤ Nat.card K) :
    commutator ↥(CFSG.PGLModel.orthogonalMinus 1 D.F D.b D.c) = minusN D :=
  CFSG.GroupTheory.commutator_eq_of_index_two_of_commutator_eq_top (index_minusN D h4)
    (commutator_minusN_eq_top D h4)

namespace HermInvol

@[expose] noncomputable def RgO : ↥(CFSG.PGLModel.orthogonalMinus 1 D.F D.b D.c) :=
  ⟨D.Rg, D.Rg_mem_orth⟩

end HermInvol

theorem RgO_not_mem_minusN (h4 : 4 ≤ Nat.card K) : D.RgO ∉ minusN D := by
  intro h
  rw [minusN, Subgroup.mem_subgroupOf, MonoidHom.mem_range] at h
  obtain ⟨Y, hY⟩ := h
  have hY' : D.slGL Y = D.Rg := hY
  have hcomm : ∀ A : Matrix.SpecialLinearGroup (Fin 2) K,
      Matrix.SpecialLinearGroup.map D.σ.toRingHom A = Y * A * Y⁻¹ := by
    intro A
    apply slGL_injective D h4
    rw [slGL_map D A, map_mul, map_mul, map_inv, hY', D.Rg_inv]
  have hstep : ∀ (i j : Fin 2) (hij : i ≠ j),
      Commute (Matrix.single i j (1 : K)) (Y : Matrix (Fin 2) (Fin 2) K) := by
    intro i j hij
    have h1 : Matrix.SpecialLinearGroup.transvection hij 1 * Y =
        Y * Matrix.SpecialLinearGroup.transvection hij 1 := by
      have h' : Matrix.SpecialLinearGroup.transvection hij (1 : K) =
          Y * Matrix.SpecialLinearGroup.transvection hij 1 * Y⁻¹ := by
        simpa [Matrix.SpecialLinearGroup.map_transvection] using
          hcomm (Matrix.SpecialLinearGroup.transvection hij 1)
      conv_lhs => rw [h']
      group
    have hmat := congrArg (fun Z : Matrix.SpecialLinearGroup (Fin 2) K =>
      (Z : Matrix (Fin 2) (Fin 2) K)) h1
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mul, Matrix.one_mul,
      Matrix.mul_add, Matrix.mul_one] at hmat
    exact add_left_cancel hmat
  obtain ⟨r, hr⟩ := Matrix.mem_range_scalar_of_commute_single
    (M := (Y : Matrix (Fin 2) (Fin 2) K)) (fun i j hij => by
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hstep 0 1 (by decide)
      · exact hstep 1 0 (by decide)
      · exact absurd rfl hij)
  have hr1 : r = 1 := by
    have hdet : (Matrix.scalar (Fin 2) r).det = 1 := by rw [hr]; exact Y.det_coe
    rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hdet
    exact CharTwo.sq_inj.mp (by rw [hdet, one_pow])
  have hY1 : Y = 1 := by
    apply Subtype.ext
    rw [← hr, hr1, Matrix.scalar_apply, Matrix.SpecialLinearGroup.coe_one,
      ← Matrix.smul_one_eq_diagonal, one_smul]
  have hAξ : Matrix.SpecialLinearGroup.map D.σ.toRingHom x[D.ξ] = x[D.ξ] := by
    have h' := hcomm x[D.ξ]
    rw [hY1] at h'
    simpa using h'
  refine D.hξ ?_
  have h1 : x[D.σ D.ξ] = x[D.ξ] := by
    simpa [Matrix.SpecialLinearGroup.map_transvection] using hAξ
  simpa [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.single_apply]
    using congrArg (fun Z : Matrix.SpecialLinearGroup (Fin 2) K =>
      (Z : Matrix (Fin 2) (Fin 2) K) 0 1) h1

theorem isConj_RgO_of_mul_self_eq_one [Finite K] (h4 : 4 ≤ Nat.card K)
    {t : ↥(CFSG.PGLModel.orthogonalMinus 1 D.F D.b D.c)} (ht : t * t = 1)
    (htN : t ∉ minusN D) : IsConj D.RgO t := by
  have hidx : (minusN D).index = 2 := index_minusN D h4
  have htRg : t * D.RgO ∈ minusN D := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    exact ⟨fun h => absurd h htN, fun h => absurd h (RgO_not_mem_minusN D h4)⟩
  rw [minusN, Subgroup.mem_subgroupOf, MonoidHom.mem_range] at htRg
  obtain ⟨Y, hY⟩ := htRg
  have hY' : D.slGL Y = (t : GL HermInvol.Ix D.F) * D.Rg := by
    rw [hY]
    rfl
  have ht_eq : (t : GL HermInvol.Ix D.F) = D.slGL Y * D.Rg := by
    calc (t : GL HermInvol.Ix D.F) = (t : GL HermInvol.Ix D.F) * (D.Rg * D.Rg) := by
          rw [D.Rg_mul_self, mul_one]
      _ = ((t : GL HermInvol.Ix D.F) * D.Rg) * D.Rg := by group
      _ = D.slGL Y * D.Rg := by rw [← hY']
  have hsq : D.slGL (Y * Matrix.SpecialLinearGroup.map D.σ.toRingHom Y) = 1 := by
    have h : (D.slGL Y * D.Rg) * (D.slGL Y * D.Rg) = 1 := by
      have h' := congrArg (fun z : ↥(CFSG.PGLModel.orthogonalMinus 1 D.F D.b D.c) =>
        (z : GL HermInvol.Ix D.F)) ht
      simpa [Subgroup.coe_mul, ht_eq] using h'
    calc D.slGL (Y * Matrix.SpecialLinearGroup.map D.σ.toRingHom Y)
        = D.slGL Y * D.slGL (Matrix.SpecialLinearGroup.map D.σ.toRingHom Y) := by
          rw [map_mul]
      _ = D.slGL Y * (D.Rg * D.slGL Y * D.Rg) := by rw [slGL_map]
      _ = (D.slGL Y * D.Rg) * (D.slGL Y * D.Rg) := by group
      _ = 1 := h
  have hYmap : Y * Matrix.SpecialLinearGroup.map D.σ.toRingHom Y = 1 :=
    slGL_injective D h4 (by rw [hsq, map_one])
  have hσ : D.σ ≠ RingEquiv.refl K := by
    intro h
    exact D.hξ (by rw [h]; rfl)
  obtain ⟨k, hk⟩ := CFSG.CGT.Timmesfeld75.aiv_exists_sl2FieldAut_eq_mul hσ D.σσ (g := Y) hYmap
  have hk' : Matrix.SpecialLinearGroup.map D.σ.toRingHom k = k * Y := hk
  have hYk : Y = k⁻¹ * Matrix.SpecialLinearGroup.map D.σ.toRingHom k := by
    rw [hk']; group
  have hYgl : D.slGL Y = (D.slGL k)⁻¹ * (D.Rg * D.slGL k * D.Rg) := by
    rw [hYk, map_mul, map_inv, slGL_map]
  let c : ↥(CFSG.PGLModel.orthogonalMinus 1 D.F D.b D.c) :=
    ⟨D.slGL k⁻¹, D.slGL_mem_orth k⁻¹⟩
  let u : (↥(CFSG.PGLModel.orthogonalMinus 1 D.F D.b D.c))ˣ :=
    ⟨c, c⁻¹, by group, by group⟩
  refine isConj_iff.mpr ⟨u, ?_⟩
  show c * D.RgO * c⁻¹ = t
  apply Subtype.ext
  show (D.slGL k⁻¹ * D.Rg * (D.slGL k⁻¹)⁻¹ : GL HermInvol.Ix D.F) =
    (t : GL HermInvol.Ix D.F)
  rw [ht_eq, map_inv, inv_inv, hYgl]
  calc (D.slGL k)⁻¹ * D.Rg * D.slGL k
      = (D.slGL k)⁻¹ * D.Rg * D.slGL k * (D.Rg * D.Rg) := by rw [D.Rg_mul_self, mul_one]
    _ = (D.slGL k)⁻¹ * (D.Rg * D.slGL k * D.Rg) * D.Rg := by group

namespace HermInvol

@[expose] noncomputable def unitO (a : D.F) :
    ↥(CFSG.PGLModel.orthogonalMinus 1 D.F D.b D.c) :=
  ⟨D.slGL x[(a : K)], D.slGL_mem_orth _⟩

@[expose] noncomputable def outerUnit (a : D.F) :
    ↥(CFSG.PGLModel.orthogonalMinus 1 D.F D.b D.c) :=
  D.unitO a * D.RgO

end HermInvol

theorem outerUnit_eq (a : D.F) : D.outerUnit a = D.unitO a * D.RgO := rfl

theorem Rg_mul_slGL_transvection (a : D.F) :
    D.Rg * D.slGL x[(a : K)] * D.Rg = D.slGL x[(a : K)] := by
  rw [← slGL_map, Matrix.SpecialLinearGroup.map_transvection,
    show D.σ.toRingHom (a : K) = (a : K) from D.σ_coe a]

theorem unitO_mul (a b : D.F) : D.unitO a * D.unitO b = D.unitO (a + b) := by
  apply Subtype.ext
  show D.slGL x[(a : K)] * D.slGL x[(b : K)] = D.slGL x[((a + b : D.F) : K)]
  rw [← map_mul, ← Matrix.SpecialLinearGroup.transvection_add]
  rfl

theorem unitO_zero : D.unitO 0 = 1 := by
  apply Subtype.ext
  show D.slGL x[((0 : D.F) : K)] = 1
  have h : x[((0 : D.F) : K)] = 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp
  rw [h, map_one]

theorem unitO_mul_self (a : D.F) : D.unitO a * D.unitO a = 1 := by
  have h : (a + a : D.F) = 0 := by
    apply Subtype.ext
    push_cast
    exact CharTwo.add_self_eq_zero _
  rw [unitO_mul, h, unitO_zero]

theorem outerUnit_mul (a b : D.F) : D.outerUnit a * D.outerUnit b = D.unitO (a + b) := by
  apply Subtype.ext
  show (D.slGL x[(a : K)] * D.Rg) * (D.slGL x[(b : K)] * D.Rg) = D.slGL x[((a + b : D.F) : K)]
  calc (D.slGL x[(a : K)] * D.Rg) * (D.slGL x[(b : K)] * D.Rg)
      = D.slGL x[(a : K)] * (D.Rg * D.slGL x[(b : K)] * D.Rg) := by group
    _ = D.slGL x[(a : K)] * D.slGL x[(b : K)] := by rw [Rg_mul_slGL_transvection]
    _ = D.slGL (x[(a : K)] * x[(b : K)]) := by rw [map_mul]
    _ = D.slGL x[((a + b : D.F) : K)] := by
        rw [← Matrix.SpecialLinearGroup.transvection_add]
        rfl

theorem outerUnit_mul_self (a : D.F) : D.outerUnit a * D.outerUnit a = 1 := by
  have h : (a + a : D.F) = 0 := by
    apply Subtype.ext
    push_cast
    exact CharTwo.add_self_eq_zero _
  rw [outerUnit_mul, h, unitO_zero]

theorem outerUnit_notMem (h4 : 4 ≤ Nat.card K) (a : D.F) : D.outerUnit a ∉ minusN D := by
  intro h
  have hA : D.unitO a ∈ minusN D := ⟨x[(a : K)], rfl⟩
  have hRg : D.RgO ∈ minusN D := by
    have h' : (D.unitO a)⁻¹ * D.outerUnit a ∈ minusN D :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hA) h
    have heq : (D.unitO a)⁻¹ * D.outerUnit a = D.RgO := by
      apply Subtype.ext
      show ((D.slGL x[(a : K)])⁻¹ * (D.slGL x[(a : K)] * D.Rg) : GL _ _) = D.Rg
      group
    rwa [heq] at h'
  exact RgO_not_mem_minusN D h4 hRg

theorem isConj_outerUnit [Finite K] (h4 : 4 ≤ Nat.card K) (a : D.F) :
    IsConj D.RgO (D.outerUnit a) :=
  isConj_RgO_of_mul_self_eq_one D h4 (outerUnit_mul_self D a) (outerUnit_notMem D h4 a)

theorem outerUnit_comm (a b : D.F) : Commute (D.outerUnit a) (D.outerUnit b) := by
  change D.outerUnit a * D.outerUnit b = D.outerUnit b * D.outerUnit a
  rw [outerUnit_mul]
  conv_rhs => rw [outerUnit_mul]
  rw [add_comm]

theorem outerUnit_zero : D.outerUnit 0 = D.RgO := by
  rw [outerUnit_eq, unitO_zero, one_mul]

theorem outerUnit_ne_RgO (h4 : 4 ≤ Nat.card K) {a : D.F} (ha : a ≠ 0) :
    D.outerUnit a ≠ D.RgO := by
  intro h
  have h1 : D.slGL x[(a : K)] = 1 := by
    have h2 : D.slGL x[(a : K)] * D.Rg = 1 * D.Rg := by
      rw [one_mul]
      calc D.slGL x[(a : K)] * D.Rg = (D.outerUnit a : GL _ _) := rfl
        _ = (D.RgO : GL _ _) := by rw [h]
        _ = D.Rg := rfl
    exact mul_right_cancel h2
  have h3 : x[(a : K)] = 1 := slGL_injective D h4 (by rw [h1, map_one])
  have h4' : (a : K) = 0 := by
    have h5 := congrArg (fun Z : Matrix.SpecialLinearGroup (Fin 2) K =>
      (Z : Matrix (Fin 2) (Fin 2) K) 0 1) h3
    simpa [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.single_apply]
      using h5
  exact ha (Subtype.ext (by simpa using h4'))

theorem exists_triple_RgO [Finite K] (h4 : 4 ≤ Nat.card K) {ω : D.F} (hω0 : ω ≠ 0)
    (hω1 : ω ≠ 1) :
    ∃ Λ : Set ↥(CFSG.PGLModel.orthogonalMinus 1 D.F D.b D.c),
      Λ ⊆ {y | IsConj D.RgO y} ∧
        (∀ a ∈ Λ, ∀ b ∈ Λ, Commute a b) ∧ ∃ v ∈ Λ, v ∈ Subgroup.closure (Λ \ {v}) := by
  have h1ω : (1 : D.F) + ω ≠ 0 := by
    intro h
    apply hω1
    have h' : ω = -1 := by linear_combination h
    rwa [CharTwo.neg_eq] at h'
  refine ⟨{D.outerUnit 0, D.outerUnit 1, D.outerUnit ω, D.outerUnit (1 + ω)}, ?_, ?_,
    D.outerUnit 0, Or.inl rfl, ?_⟩
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl <;> exact isConj_outerUnit D h4 _
  · intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      exact outerUnit_comm D _ _
  · have hmem : ∀ a : D.F, a ≠ 0 → (a = 1 ∨ a = ω ∨ a = 1 + ω) →
        D.outerUnit a ∈ Subgroup.closure (({D.outerUnit 0, D.outerUnit 1, D.outerUnit ω,
          D.outerUnit (1 + ω)} : Set ↥(CFSG.PGLModel.orthogonalMinus 1 D.F D.b D.c)) \
          {D.outerUnit 0}) := by
      intro a ha h
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · rcases h with rfl | rfl | rfl <;> simp
      · rw [Set.mem_singleton_iff, outerUnit_zero]
        exact outerUnit_ne_RgO D h4 ha
    have h0 : D.outerUnit 1 * D.outerUnit ω * D.outerUnit (1 + ω) = D.outerUnit 0 := by
      rw [outerUnit_mul, outerUnit_eq (D := D) (1 + ω), ← mul_assoc, unitO_mul_self, one_mul,
        outerUnit_zero]
    have h := Subgroup.mul_mem _ (Subgroup.mul_mem _ (hmem 1 one_ne_zero (Or.inl rfl))
      (hmem ω hω0 (Or.inr (Or.inl rfl)))) (hmem _ h1ω (Or.inr (Or.inr rfl)))
    rwa [h0] at h

end CFSG.OddTranspositions.PartFour
