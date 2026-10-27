module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalLocal

import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldUnipotent
import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryNorm
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance
import CFSG.ClassicalGroups.PCoreSection
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.Quasithin.Recognition.St84.Gen.AmalVertexLocal

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

section Structures

variable {G : Type*} [Group G]

structure U4qCoordLeft (L1 L2 S : Subgroup G) (f : ℕ) (F : Type*) [Field F] where
  α : ↥L1 →* SL(2, F)
  β : ↥(pCoreOf 2 L1) →* Multiplicative (Matrix (Fin 2) (Fin 2) F)
  card : Nat.card F = 2 ^ f
  surjective_α : Function.Surjective α
  eq_one_iff : ∀ x : ↥L1, α x = 1 ↔ (x : G) ∈ pCoreOf 2 L1
  surjective_β : Function.Surjective β
  ker_β : β.ker = (centerOf (pCoreOf 2 L1)).subgroupOf (pCoreOf 2 L1)
  equivariant : ∀ (x : ↥L1) (u v : ↥(pCoreOf 2 L1)), (v : G) = x * u * x⁻¹ →
    Multiplicative.toAdd (β v) = (α x : Matrix (Fin 2) (Fin 2) F) * Multiplicative.toAdd (β u)
  mem_iff : ∀ x : ↥L1, (x : G) ∈ S ↔ ∃ t : F, (α x : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1]
  mem_inf_iff : ∀ u : ↥(pCoreOf 2 L1),
    (u : G) ∈ pCoreOf 2 L2 ↔ Multiplicative.toAdd (β u) 1 = 0

structure U4qCoordRight (L1 L2 S : Subgroup G) (f : ℕ) (K : Type*) [Field K] where
  α : ↥L2 →* SL(2, K)
  β : ↥(pCoreOf 2 L2) →* Multiplicative (Matrix (Fin 2) (Fin 2) K)
  card : Nat.card K = 2 ^ (2 * f)
  surjective_α : Function.Surjective α
  eq_one_iff : ∀ x : ↥L2, α x = 1 ↔ (x : G) ∈ pCoreOf 2 L2
  injective_β : Function.Injective β
  range_iff : ∀ X : Matrix (Fin 2) (Fin 2) K,
    (∃ u, Multiplicative.toAdd (β u) = X) ↔ X.map (· ^ 2 ^ f) = X.transpose
  equivariant : ∀ (x : ↥L2) (u v : ↥(pCoreOf 2 L2)), (v : G) = x * u * x⁻¹ →
    Multiplicative.toAdd (β v) = (α x : Matrix (Fin 2) (Fin 2) K) *
      Multiplicative.toAdd (β u) * ((α x : Matrix (Fin 2) (Fin 2) K).map (· ^ 2 ^ f)).transpose
  mem_iff : ∀ x : ↥L2, (x : G) ∈ S ↔ ∃ t : K, (α x : Matrix (Fin 2) (Fin 2) K) = !![1, t; 0, 1]
  mem_center_iff : ∀ u : ↥(pCoreOf 2 L2), (u : G) ∈ centerOf (pCoreOf 2 L1) ↔
    Multiplicative.toAdd (β u) 0 1 = 0 ∧ Multiplicative.toAdd (β u) 1 1 = 0
  mem_inf_iff : ∀ u : ↥(pCoreOf 2 L2),
    (u : G) ∈ pCoreOf 2 L1 ↔ Multiplicative.toAdd (β u) 1 1 = 0

end Structures

section Matrices

variable {F : Type*} [Field F]

private theorem mem_upperU_iff {g : SL(2, F)} :
    g ∈ (upperUnipotent (F := F)).range ↔
      ∃ t : F, (g : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := by
  rw [← sl2_fixes_first_iff (F := F) g]
  constructor
  · intro h
    have h0 := congrFun h 0
    rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec] at h0
    have h00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by simpa using h0
    have h1 := congrFun h 1
    rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec] at h1
    have h10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by simpa using h1
    have h11 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
      have hdet : (g : Matrix (Fin 2) (Fin 2) F).det = 1 := g.2
      rw [Matrix.det_fin_two, h00, h10] at hdet
      simpa using hdet
    refine ⟨(g : Matrix (Fin 2) (Fin 2) F) 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]
  · rintro ⟨t, ht⟩
    rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, ht]
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private def uSL (t : F) : SL(2, F) := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

private theorem coe_uSL (t : F) : (uSL t : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := rfl

theorem unitriangular_mul_row_zero (t : F) (X : Matrix (Fin 2) (Fin 2) F) :
    (!![1, t; 0, 1] * X) 0 = X 0 + t • X 1 := by
  funext j
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem unitriangular_mul_row_one (t : F) (X : Matrix (Fin 2) (Fin 2) F) :
    (!![1, t; 0, 1] * X) 1 = X 1 := by
  funext j
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem unitriangular_mul_mul_map_transpose (f : ℕ) (t : F) (Y : Matrix (Fin 2) (Fin 2) F) :
    !![1, t; 0, 1] * Y * ((!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) F).map (· ^ 2 ^ f)).transpose =
      !![Y 0 0 + t * Y 1 0 + (Y 0 1 + t * Y 1 1) * t ^ 2 ^ f, Y 0 1 + t * Y 1 1;
        Y 1 0 + Y 1 1 * t ^ 2 ^ f, Y 1 1] := by
  have h0 : (0 : F) ^ 2 ^ f = 0 := zero_pow (pow_ne_zero _ two_ne_zero)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, h0] <;> ring

private theorem eq_zero_of_forall_unitriangular {f : ℕ} {t₀ : F} (ht₀ : t₀ ^ 2 ^ f ≠ t₀)
    (Y : Matrix (Fin 2) (Fin 2) F)
    (hfix : ∀ t : F, !![1, t; 0, 1] * Y *
      ((!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) F).map (· ^ 2 ^ f)).transpose = Y) :
    Y 0 1 = 0 ∧ Y 1 1 = 0 := by
  have e1 := congrFun (congrFun (hfix 1) 0) 1
  have e2 := congrFun (congrFun (hfix 1) 0) 0
  have e3 := congrFun (congrFun (hfix t₀) 0) 0
  rw [unitriangular_mul_mul_map_transpose] at e1 e2 e3
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, one_mul, one_pow,
    mul_one] at e1 e2 e3
  have h11 : Y 1 1 = 0 := by linear_combination e1
  have h01 : Y 0 1 * (t₀ ^ 2 ^ f - t₀) = 0 := by
    linear_combination e3 - t₀ * e2 - (t₀ * t₀ ^ 2 ^ f - t₀) * h11
  exact ⟨(mul_eq_zero.mp h01).resolve_right (sub_ne_zero.mpr ht₀), h11⟩

end Matrices

section Hermitian

variable {K : Type*} [Field K] {f : ℕ}

private theorem pow_eq_bar (hU : UnitaryFieldData 2 f K) :
    (fun x : K => x ^ 2 ^ f) = ⇑hU.bar :=
  funext fun x => (hU.bar_apply x).symm

private theorem herm_mul_mul (hU : UnitaryFieldData 2 f K) (P Y : Matrix (Fin 2) (Fin 2) K)
    (hY : Y.map (· ^ 2 ^ f) = Y.transpose) :
    (P * Y * (P.map (· ^ 2 ^ f)).transpose).map (· ^ 2 ^ f) =
      (P * Y * (P.map (· ^ 2 ^ f)).transpose).transpose := by
  rw [pow_eq_bar hU] at hY ⊢
  rw [Matrix.map_mul, Matrix.map_mul, hY, Matrix.transpose_map, Matrix.map_map]
  have hbb : (⇑hU.bar ∘ ⇑hU.bar) = id := funext hU.bar_bar
  rw [hbb, Matrix.map_id, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc]

private theorem conj_herm_equivariant (hU : UnitaryFieldData 2 f K) (X A : SL(2, K))
    (B : Matrix (Fin 2) (Fin 2) K) :
    (X : Matrix (Fin 2) (Fin 2) K) * ((A : Matrix (Fin 2) (Fin 2) K) * B *
        ((A : Matrix (Fin 2) (Fin 2) K).map (· ^ 2 ^ f)).transpose *
        ((X : Matrix (Fin 2) (Fin 2) K).map (· ^ 2 ^ f)).transpose) =
      ((X * A * X⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
        ((X : Matrix (Fin 2) (Fin 2) K) * (B *
          ((X : Matrix (Fin 2) (Fin 2) K).map (· ^ 2 ^ f)).transpose)) *
        (((X * A * X⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).map (· ^ 2 ^ f)).transpose := by
  have h1 : ((X⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * (X : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [pow_eq_bar hU]
  have h2 : ((X : Matrix (Fin 2) (Fin 2) K).map ⇑hU.bar).transpose *
      (((X⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).map ⇑hU.bar).transpose = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.transpose_one]
  have hc1 : ∀ Y : Matrix (Fin 2) (Fin 2) K,
      ((X⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * ((X : Matrix (Fin 2) (Fin 2) K) * Y) = Y := by
    intro Y
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hc2 : ∀ Y : Matrix (Fin 2) (Fin 2) K,
      ((X : Matrix (Fin 2) (Fin 2) K).map ⇑hU.bar).transpose *
        ((((X⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).map ⇑hU.bar).transpose * Y) = Y := by
    intro Y
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.map_mul, Matrix.transpose_mul,
    Matrix.mul_assoc, hc1, hc2]

end Hermitian

variable {G : Type} [Group G] [Finite G]

private theorem exists_conj_mem_iff {L S : Subgroup G} {F : Type*} [Field F] [Finite F]
    [CharP F 2] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hS : IsSylowTwoOf S L)
    (α : ↥L →* SL(2, F)) (hα : Function.Surjective α) (hker : IsPGroup 2 α.ker) :
    ∃ X : SL(2, F), ∀ x : ↥L, (x : G) ∈ S ↔
      ∃ t : F, ((X * α x * X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := by
  classical
  have hS2 : IsPGroup 2 (S.subgroupOf L) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  obtain ⟨x, hx⟩ := pgroup_sl2_conjugate_unipotent ((S.subgroupOf L).map α) (hS2.map α)
  let X : SL(2, F) := x⁻¹
  let α' : ↥L →* SL(2, F) := (MulAut.conj X).toMonoidHom.comp α
  have hα' : ∀ y, α' y = X * α y * X⁻¹ := fun y => rfl
  have hker' : α'.ker = α.ker := by
    ext y
    simp only [MonoidHom.mem_ker, hα']
    constructor
    · intro h
      calc α y = X⁻¹ * (X * α y * X⁻¹) * X := by group
        _ = 1 := by rw [h]; group
    · intro h
      rw [h]
      group
  have hle : (S.subgroupOf L).map α' ≤ (upperUnipotent (F := F)).range := by
    have hmap : (S.subgroupOf L).map α' =
        ((S.subgroupOf L).map α).map (MulAut.conj X).toMonoidHom := by
      rw [Subgroup.map_map]
    rw [hmap]
    simpa [X] using hx
  let P : Sylow 2 ↥L := hS2.toSylow hS.2.2
  have hU2 : IsPGroup 2 (upperUnipotent (F := F)).range :=
    IsPGroup.of_card (n := n) (by rw [upperUnipotent_card, hF])
  have hPle : (P : Subgroup ↥L) ≤ (upperUnipotent (F := F)).range.comap α' :=
    fun y hy => hle (Subgroup.mem_map_of_mem α' hy)
  have hH : (upperUnipotent (F := F)).range.comap α' = S.subgroupOf L :=
    P.is_maximal' (hU2.comap_of_ker_isPGroup α' (hker' ▸ hker)) hPle
  refine ⟨X, fun y => ?_⟩
  rw [← hα', ← mem_upperU_iff, ← Subgroup.mem_comap, hH, Subgroup.mem_subgroupOf]

private theorem card_le_card_ker_mul {A M : Type*} [Group A] [Group M] [Finite A] [Finite M]
    (φ : A →* M) (W : Subgroup A) (R : Set M) (hR : ∀ w ∈ W, φ w ∈ R) :
    Nat.card W ≤ Nat.card φ.ker * Nat.card R := by
  classical
  let ψ : ↥W →* M := φ.comp W.subtype
  rw [← Subgroup.card_ker_mul_card_range ψ]
  apply Nat.mul_le_mul
  · refine Nat.card_le_card_of_injective (fun k => ⟨((k : ↥W) : A), k.2⟩) ?_
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun k : φ.ker => (k : A)) h))
  · refine Nat.card_le_card_of_injective (fun m => ⟨(m : M), ?_⟩) ?_
    · obtain ⟨w, hw⟩ := m.2
      rw [← hw]
      exact hR w w.2
    · intro a b h
      exact Subtype.ext (congrArg (fun m : ↥R => (m : M)) h)

private theorem exists_alpha_eq_of_card {L S H Q : Subgroup G} {F : Type*} [Field F] [Finite F]
    (α : ↥L →* SL(2, F)) (hker : ∀ x : ↥L, α x = 1 ↔ (x : G) ∈ Q)
    (hmem : ∀ x : ↥L, (x : G) ∈ S → ∃ t : F, (α x : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1])
    (hHS : H ≤ S) (hHL : H ≤ L) (hcard : Nat.card ↥(Q ⊓ H) * Nat.card F = Nat.card H)
    (t : F) :
    ∃ x : ↥L, (x : G) ∈ H ∧ (α x : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := by
  classical
  let ψ : ↥H →* SL(2, F) := α.comp (Subgroup.inclusion hHL)
  have hkercard : Nat.card ψ.ker = Nat.card ↥(Q ⊓ H) := by
    have hk : ψ.ker = (Q ⊓ H).subgroupOf H := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      change α (Subgroup.inclusion hHL x) = 1 ↔ _
      rw [hker]
      exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩
    rw [hk]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hrangecard : Nat.card ψ.range = Nat.card F := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hkercard, ← hcard] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  have hle : ψ.range ≤ (upperUnipotent (F := F)).range := by
    rintro _ ⟨x, rfl⟩
    exact mem_upperU_iff.mpr (hmem _ (hHS x.2))
  have hEq : ψ.range = (upperUnipotent (F := F)).range :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hrangecard, upperUnipotent_card])
  have hmemU : uSL t ∈ (upperUnipotent (F := F)).range := mem_upperU_iff.mpr ⟨t, coe_uSL t⟩
  rw [← hEq] at hmemU
  obtain ⟨x, hx⟩ := hmemU
  refine ⟨Subgroup.inclusion hHL x, x.2, ?_⟩
  change ((ψ x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = _
  rw [hx, coe_uSL]

variable {L1 L2 S : Subgroup G} {f : ℕ}

private theorem U4qLocalData.card_centerOf_left (hD : U4qLocalData L1 L2 S f) :
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

theorem U4qLocalData.commutator_pCoreOf_left_mem_centerOf (hD : U4qLocalData L1 L2 S f)
    {a u : G} (ha : a ∈ pCoreOf 2 L1) (hu : u ∈ pCoreOf 2 L1) :
    a * u * a⁻¹ * u⁻¹ ∈ centerOf (pCoreOf 2 L1) := by
  obtain ⟨F, hField, hFintype, -, α, -, -, β, -, hβker, -⟩ := hD.twoNat_left
  letI := hField
  have hU := hD.blockU_left
  let a' : ↥(blockU L1) := ⟨a, hU ▸ ha⟩
  let u' : ↥(blockU L1) := ⟨u, hU ▸ hu⟩
  have hk : a' * u' * a'⁻¹ * u'⁻¹ ∈ β.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [mul_comm (β a') (β u')]
    group
  rw [hβker, Subgroup.mem_subgroupOf, hD.blockZ_left] at hk
  exact hk

theorem U4qLocalData.exists_pCoreOf_right_inv_mul_mem (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f)) {s : G} (hs : s ∈ S) :
    ∃ c ∈ pCoreOf 2 L2, c⁻¹ * s ∈ pCoreOf 2 L1 := by
  classical
  obtain ⟨F, hField, hFintype, hFcard, α, -, hker, -⟩ := hD.twoNat_left
  letI := hField
  letI := hFintype
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hFcard
  have hSL1 : S ≤ L1 := hD.le_left hH hS
  have hQ2L1 : pCoreOf 2 L2 ≤ L1 := hH.pCoreOf_le_right.trans hSL1
  have hmemker : ∀ y : ↥L1, α y = 1 ↔ (y : G) ∈ pCoreOf 2 L1 := by
    intro y
    rw [CFSG.mem_openPCoreOf_iff, ← hker, MonoidHom.mem_ker]
  let ψ : ↥(pCoreOf 2 L2) →* SL(2, F) := α.comp (Subgroup.inclusion hQ2L1)
  let A : Subgroup SL(2, F) := (S.subgroupOf L1).map α
  have hA2 : IsPGroup 2 A := by
    have hS2 : IsPGroup 2 (S.subgroupOf L1) :=
      hH.h1.pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hSL1).symm
    exact hS2.map α
  have hAcard : Nat.card A ≤ 2 ^ f := by
    have h := pgroup_sl2_card_le A hA2
    rwa [Nat.card_eq_fintype_card (α := F), hFcard] at h
  have hrange_le : ψ.range ≤ A := by
    rintro _ ⟨c, rfl⟩
    exact ⟨Subgroup.inclusion hQ2L1 c, hH.pCoreOf_le_right c.2, rfl⟩
  have hkercard : Nat.card ψ.ker = 2 ^ (3 * f) := by
    have hk : ψ.ker = (pCoreOf 2 L1 ⊓ pCoreOf 2 L2).subgroupOf (pCoreOf 2 L2) := by
      ext c
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      change α (Subgroup.inclusion hQ2L1 c) = 1 ↔ _
      rw [hmemker]
      exact ⟨fun h => ⟨h, c.2⟩, fun h => h.1⟩
    rw [hk, ← hD.card_inf]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hrangecard : Nat.card ψ.range = 2 ^ f := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hkercard, hD.card_right, show 4 * f = 3 * f + f by ring, pow_add] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  have hEq : ψ.range = A :=
    Subgroup.eq_of_le_of_card_ge hrange_le (by rw [hrangecard]; exact hAcard)
  have hsA : α ⟨s, hSL1 hs⟩ ∈ ψ.range := hEq ▸ ⟨⟨s, hSL1 hs⟩, hs, rfl⟩
  obtain ⟨c, hc⟩ := hsA
  refine ⟨c, c.2, ?_⟩
  have h1 : α ((Subgroup.inclusion hQ2L1 c)⁻¹ * ⟨s, hSL1 hs⟩) = 1 := by
    rw [map_mul, map_inv]
    change (ψ c)⁻¹ * _ = 1
    rw [hc, inv_mul_cancel]
  exact (hmemker _).mp h1

theorem U4qLocalData.commutator_inf_mem_centerOf (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f)) {s u : G} (hs : s ∈ S)
    (hu : u ∈ pCoreOf 2 L1 ⊓ pCoreOf 2 L2) :
    s * u * s⁻¹ * u⁻¹ ∈ centerOf (pCoreOf 2 L1) := by
  obtain ⟨c, hc, ha⟩ := hD.exists_pCoreOf_right_inv_mul_mem hH hS hs
  have hz := hD.commutator_pCoreOf_left_mem_centerOf ha hu.1
  have hcL1 : c ∈ L1 := (hH.pCoreOf_le_right.trans (hD.le_left hH hS)) hc
  have hcz : c * ((c⁻¹ * s) * u * (c⁻¹ * s)⁻¹ * u⁻¹) * c⁻¹ =
      (c⁻¹ * s) * u * (c⁻¹ * s)⁻¹ * u⁻¹ := by
    have h := Subgroup.mem_centralizer_iff.mp (hD.center_left hcL1) _ hz
    rw [← h]
    group
  have hcu : c * u * c⁻¹ = u := by
    have h := congrArg Subtype.val
      (hD.isElemAbelian_right.1.is_comm.comm ⟨c, hc⟩ ⟨u, hu.2⟩)
    change c * u = u * c at h
    rw [h]
    group
  have hcalc : s * u * s⁻¹ * u⁻¹ = (c * ((c⁻¹ * s) * u * (c⁻¹ * s)⁻¹ * u⁻¹) * c⁻¹) *
      (c * u * c⁻¹) * u⁻¹ := by group
  rw [hcalc, hcz, hcu]
  simpa using hz

private theorem charTwo_vertex_left (hH : Hyp111 L1 L2 S) : CharTwo L1 := by
  have hle : L1 ≤ L1 ⊔ S ⊔ borelOf L2 S := le_sup_left.trans le_sup_left
  refine CharTwo.of_normal hH.h1.charTwo hle ?_
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  exact sup_le (sup_le Subgroup.le_normalizer hH.h1.normalizes) hH.h1.borel_le

theorem U4qLocalData.exists_coordLeft (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hS : Nat.card S = 2 ^ (6 * f)) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F), Nonempty (U4qCoordLeft L1 L2 S f F) := by
  classical
  obtain ⟨F, hField, hFintype, hFcard, α₀, hα₀, hker₀, β₀, hβ₀, hβker₀, hβeq₀⟩ := hD.twoNat_left
  letI := hField
  letI := hFintype
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hFcard
  have hFcard' : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hFcard]
  have hSL1 : S ≤ L1 := hD.le_left hH hS
  have hSyl : IsSylowTwoOf S L1 := by
    have h := hH.h1.sylow
    rwa [inf_eq_left.mpr hSL1] at h
  obtain ⟨X, hX⟩ := exists_conj_mem_iff hFcard' hSyl α₀ hα₀
    (by rw [hker₀]; exact CFSG.pCore_isPGroup)
  let α : ↥L1 →* SL(2, F) := (MulAut.conj X).toMonoidHom.comp α₀
  have hαapp : ∀ y, α y = X * α₀ y * X⁻¹ := fun y => rfl
  have hαsurj : Function.Surjective α := (MulAut.conj X).surjective.comp hα₀
  have hα1 : ∀ y : ↥L1, α y = 1 ↔ (y : G) ∈ pCoreOf 2 L1 := by
    intro y
    rw [hαapp, CFSG.mem_openPCoreOf_iff, ← hker₀, MonoidHom.mem_ker]
    constructor
    · intro h
      calc α₀ y = X⁻¹ * (X * α₀ y * X⁻¹) * X := by group
        _ = 1 := by rw [h]; group
    · intro h
      rw [h]
      group
  let eU : ↥(pCoreOf 2 L1) ≃* ↥(blockU L1) := MulEquiv.subgroupCongr hD.blockU_left.symm
  have heU : ∀ u : ↥(pCoreOf 2 L1), ((eU u : ↥(blockU L1)) : G) = u := fun u => rfl
  let Xm : Matrix (Fin 2) (Fin 2) F := (X : Matrix (Fin 2) (Fin 2) F)
  let Xi : Matrix (Fin 2) (Fin 2) F := ((X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
  have hXX : Xi * Xm = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hXX' : Xm * Xi = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  let lX : Multiplicative (Matrix (Fin 2) (Fin 2) F) →*
      Multiplicative (Matrix (Fin 2) (Fin 2) F) :=
    AddMonoidHom.toMultiplicative (AddMonoidHom.mulLeft Xm)
  let β : ↥(pCoreOf 2 L1) →* Multiplicative (Matrix (Fin 2) (Fin 2) F) :=
    lX.comp (β₀.comp eU.toMonoidHom)
  have hβapp : ∀ u, Multiplicative.toAdd (β u) = Xm * Multiplicative.toAdd (β₀ (eU u)) :=
    fun u => rfl
  have hβsurj : Function.Surjective β := by
    intro M
    obtain ⟨u₀, hu₀⟩ := hβ₀ (Multiplicative.ofAdd (Xi * Multiplicative.toAdd M))
    refine ⟨eU.symm u₀, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hβapp, MulEquiv.apply_symm_apply, hu₀, toAdd_ofAdd, ← Matrix.mul_assoc, hXX',
      Matrix.one_mul]
  have hβ1 : ∀ u, β u = 1 ↔ β₀ (eU u) = 1 := by
    intro u
    constructor
    · intro h
      have h' : Xm * Multiplicative.toAdd (β₀ (eU u)) = 0 := by
        rw [← hβapp, h]
        rfl
      have h'' : Multiplicative.toAdd (β₀ (eU u)) = 0 := by
        have h3 := congrArg (fun M => Xi * M) h'
        simp only [← Matrix.mul_assoc, hXX, Matrix.one_mul, Matrix.mul_zero] at h3
        exact h3
      exact Multiplicative.toAdd.injective h''
    · intro h
      apply Multiplicative.toAdd.injective
      rw [hβapp, h]
      simp
  have hβker : β.ker = (centerOf (pCoreOf 2 L1)).subgroupOf (pCoreOf 2 L1) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hD.blockZ_left, hβ1, ← MonoidHom.mem_ker,
      hβker₀, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  have hβeq : ∀ (x : ↥L1) (u v : ↥(pCoreOf 2 L1)), (v : G) = x * u * x⁻¹ →
      Multiplicative.toAdd (β v) =
        (α x : Matrix (Fin 2) (Fin 2) F) * Multiplicative.toAdd (β u) := by
    intro x u v hv
    have h0 := hβeq₀ x (eU u) (eU v) (by rw [heU, heU]; exact hv)
    rw [hβapp, hβapp, h0, hαapp, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul]
    change Xm * ((α₀ x : Matrix (Fin 2) (Fin 2) F) * _) =
      Xm * (α₀ x : Matrix (Fin 2) (Fin 2) F) * Xi * (Xm * _)
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Xi Xm, hXX, Matrix.one_mul]
  have hfwd : ∀ u : ↥(pCoreOf 2 L1), (u : G) ∈ pCoreOf 2 L2 →
      Multiplicative.toAdd (β u) 1 = 0 := by
    intro u hu2
    obtain ⟨s₁, hs₁⟩ := hαsurj (uSL 1)
    have hs₁S : (s₁ : G) ∈ S := (hX s₁).mpr ⟨1, by rw [← hαapp, hs₁, coe_uSL]⟩
    let v : ↥(pCoreOf 2 L1) :=
      ⟨s₁ * u * s₁⁻¹, CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf s₁.2 u.2⟩
    have hcomm := hD.commutator_inf_mem_centerOf hH hS hs₁S ⟨u.2, hu2⟩
    have hvu : v * u⁻¹ ∈ β.ker := by
      rw [hβker, Subgroup.mem_subgroupOf]
      exact hcomm
    have hβv : β v = β u := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hvu
      exact hvu
    have heq := hβeq s₁ u v rfl
    rw [hβv, hs₁, coe_uSL] at heq
    have h0 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0) heq
    simp only [unitriangular_mul_row_zero, one_smul] at h0
    have h0' : Multiplicative.toAdd (β u) 0 + 0 =
        Multiplicative.toAdd (β u) 0 + Multiplicative.toAdd (β u) 1 := by
      rw [add_zero]
      exact h0
    exact (add_left_cancel h0').symm
  let W : Subgroup ↥(pCoreOf 2 L1) :=
    { carrier := {u | Multiplicative.toAdd (β u) 1 = 0}
      one_mem' := by
        change Multiplicative.toAdd (β 1) 1 = 0
        rw [map_one]
        rfl
      mul_mem' := by
        intro a b ha hb
        change Multiplicative.toAdd (β (a * b)) 1 = 0
        change Multiplicative.toAdd (β a) 1 = 0 at ha
        change Multiplicative.toAdd (β b) 1 = 0 at hb
        rw [map_mul, toAdd_mul]
        funext j
        have hja := congrFun ha j
        have hjb := congrFun hb j
        simp only [Pi.zero_apply] at hja hjb ⊢
        rw [Matrix.add_apply, hja, hjb, add_zero]
      inv_mem' := by
        intro a ha
        change Multiplicative.toAdd (β a⁻¹) 1 = 0
        change Multiplicative.toAdd (β a) 1 = 0 at ha
        rw [map_inv, toAdd_inv]
        funext j
        have hja := congrFun ha j
        simp only [Pi.zero_apply] at hja ⊢
        rw [Matrix.neg_apply, hja, neg_zero] }
  let R : Set (Multiplicative (Matrix (Fin 2) (Fin 2) F)) :=
    {M | Multiplicative.toAdd M 1 = 0}
  have hRcard : Nat.card R ≤ 2 ^ (2 * f) := by
    have hfun : Nat.card (Fin 2 → F) = 2 ^ (2 * f) := by
      rw [Nat.card_fun, Nat.card_fin, hFcard', ← pow_mul']
    rw [← hfun]
    refine Nat.card_le_card_of_injective
      (fun M : ↥R => Multiplicative.toAdd (M : Multiplicative (Matrix (Fin 2) (Fin 2) F)) 0) ?_
    intro M N h
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · exact h
    · change Multiplicative.toAdd (M : Multiplicative (Matrix (Fin 2) (Fin 2) F)) 1 =
        Multiplicative.toAdd (N : Multiplicative (Matrix (Fin 2) (Fin 2) F)) 1
      rw [show Multiplicative.toAdd (M : Multiplicative (Matrix (Fin 2) (Fin 2) F)) 1 = 0 from M.2,
        show Multiplicative.toAdd (N : Multiplicative (Matrix (Fin 2) (Fin 2) F)) 1 = 0 from N.2]
  have hkercard : Nat.card β.ker = 2 ^ f := by
    rw [hβker, ← hD.card_centerOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hWcard : Nat.card W ≤ 2 ^ (3 * f) := by
    calc Nat.card W ≤ Nat.card β.ker * Nat.card R := card_le_card_ker_mul β W R fun w hw => hw
      _ ≤ 2 ^ f * 2 ^ (2 * f) := by rw [hkercard]; exact Nat.mul_le_mul_left _ hRcard
      _ = 2 ^ (3 * f) := by rw [← pow_add]; ring_nf
  have hℓle : (pCoreOf 2 L1 ⊓ pCoreOf 2 L2).subgroupOf (pCoreOf 2 L1) ≤ W :=
    fun u hu => hfwd u hu.2
  have hℓcard : Nat.card ↥((pCoreOf 2 L1 ⊓ pCoreOf 2 L2).subgroupOf (pCoreOf 2 L1)) =
      2 ^ (3 * f) := by
    rw [← hD.card_inf]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hℓW : (pCoreOf 2 L1 ⊓ pCoreOf 2 L2).subgroupOf (pCoreOf 2 L1) = W :=
    Subgroup.eq_of_le_of_card_ge hℓle (by rw [hℓcard]; exact hWcard)
  have hbwd : ∀ u : ↥(pCoreOf 2 L1), Multiplicative.toAdd (β u) 1 = 0 →
      (u : G) ∈ pCoreOf 2 L2 := by
    intro u hu
    have hu' : u ∈ W := hu
    rw [← hℓW, Subgroup.mem_subgroupOf] at hu'
    exact hu'.2
  exact ⟨F, hField, hFintype, ⟨⟨α, β, hFcard', hαsurj, hα1, hβsurj, hβker, hβeq, hX,
    fun u => ⟨hfwd u, hbwd u⟩⟩⟩⟩

theorem U4qLocalData.exists_coordRight (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hS : Nat.card S = 2 ^ (6 * f)) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K), Nonempty (U4qCoordRight L1 L2 S f K) := by
  classical
  obtain ⟨K, hField, hFintype, hKcard, α₀, hα₀, hker₀, β₀, hβrange₀, hβker₀, hβeq₀⟩ :=
    hD.omega_right
  letI := hField
  letI := hFintype
  haveI : CharP K 2 := charP_of_card_eq_prime_pow hKcard
  have hKcard' : Nat.card K = 2 ^ (2 * f) := by rw [Nat.card_eq_fintype_card, hKcard]
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hD.one_le, hKcard'⟩
  have hSL2 : S ≤ L2 := hD.le_right hH hS
  have hSL1 : S ≤ L1 := hD.le_left hH hS
  have hSyl : IsSylowTwoOf S L2 := by
    have h := hH.h2.sylow
    rwa [inf_eq_left.mpr hSL2] at h
  obtain ⟨X, hX⟩ := exists_conj_mem_iff hKcard' hSyl α₀ hα₀
    (by rw [hker₀]; exact CFSG.pCore_isPGroup)
  let α : ↥L2 →* SL(2, K) := (MulAut.conj X).toMonoidHom.comp α₀
  have hαapp : ∀ y, α y = X * α₀ y * X⁻¹ := fun y => rfl
  have hαsurj : Function.Surjective α := (MulAut.conj X).surjective.comp hα₀
  have hα1 : ∀ y : ↥L2, α y = 1 ↔ (y : G) ∈ pCoreOf 2 L2 := by
    intro y
    rw [hαapp, CFSG.mem_openPCoreOf_iff, ← hker₀, MonoidHom.mem_ker]
    constructor
    · intro h
      calc α₀ y = X⁻¹ * (X * α₀ y * X⁻¹) * X := by group
        _ = 1 := by rw [h]; group
    · intro h
      rw [h]
      group
  let eU : ↥(pCoreOf 2 L2) ≃* ↥(blockU L2) := MulEquiv.subgroupCongr hD.blockU_right.symm
  have heU : ∀ u : ↥(pCoreOf 2 L2), ((eU u : ↥(blockU L2)) : G) = u := fun u => rfl
  let Xm : Matrix (Fin 2) (Fin 2) K := (X : Matrix (Fin 2) (Fin 2) K)
  let Xi : Matrix (Fin 2) (Fin 2) K := ((X⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
  let Wm : Matrix (Fin 2) (Fin 2) K := (Xm.map (· ^ 2 ^ f)).transpose
  let Wi : Matrix (Fin 2) (Fin 2) K := (Xi.map (· ^ 2 ^ f)).transpose
  have hXX : Xi * Xm = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hXX' : Xm * Xi = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hWW : Wm * Wi = 1 := by
    change (Xm.map (· ^ 2 ^ f)).transpose * (Xi.map (· ^ 2 ^ f)).transpose = 1
    rw [pow_eq_bar hU, ← Matrix.transpose_mul, ← Matrix.map_mul, hXX,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  have hWW' : Wi * Wm = 1 := by
    change (Xi.map (· ^ 2 ^ f)).transpose * (Xm.map (· ^ 2 ^ f)).transpose = 1
    rw [pow_eq_bar hU, ← Matrix.transpose_mul, ← Matrix.map_mul, hXX',
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  let cX : Multiplicative (Matrix (Fin 2) (Fin 2) K) →*
      Multiplicative (Matrix (Fin 2) (Fin 2) K) :=
    AddMonoidHom.toMultiplicative ((AddMonoidHom.mulLeft Xm).comp (AddMonoidHom.mulRight Wm))
  let β : ↥(pCoreOf 2 L2) →* Multiplicative (Matrix (Fin 2) (Fin 2) K) :=
    cX.comp (β₀.comp eU.toMonoidHom)
  have hβapp : ∀ u, Multiplicative.toAdd (β u) =
      Xm * (Multiplicative.toAdd (β₀ (eU u)) * Wm) := fun u => rfl
  have hβ₀inj : Function.Injective β₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, hβker₀, hD.blockZ_right, Subgroup.bot_subgroupOf]
  have hcancel : ∀ B : Matrix (Fin 2) (Fin 2) K, Xi * (Xm * (B * Wm)) * Wi = B := by
    intro B
    rw [← Matrix.mul_assoc Xi, hXX, Matrix.one_mul, Matrix.mul_assoc, hWW, Matrix.mul_one]
  have hβinj : Function.Injective β := by
    intro u v h
    have h1 : Multiplicative.toAdd (β u) = Multiplicative.toAdd (β v) := congrArg _ h
    rw [hβapp, hβapp] at h1
    have h2 : Multiplicative.toAdd (β₀ (eU u)) = Multiplicative.toAdd (β₀ (eU v)) := by
      rw [← hcancel (Multiplicative.toAdd (β₀ (eU u))), h1, hcancel]
    exact eU.injective (hβ₀inj (Multiplicative.toAdd.injective h2))
  have hrange : ∀ Y : Matrix (Fin 2) (Fin 2) K,
      (∃ u, Multiplicative.toAdd (β u) = Y) ↔ Y.map (· ^ 2 ^ f) = Y.transpose := by
    intro Y
    constructor
    · rintro ⟨u, rfl⟩
      rw [hβapp, ← Matrix.mul_assoc]
      exact herm_mul_mul hU Xm _ ((hβrange₀ _).mp ⟨eU u, rfl⟩)
    · intro hY
      obtain ⟨u₀, hu₀⟩ := (hβrange₀ (Xi * Y * Wi)).mpr (herm_mul_mul hU Xi Y hY)
      refine ⟨eU.symm u₀, ?_⟩
      rw [hβapp, MulEquiv.apply_symm_apply, hu₀]
      simp only [Matrix.mul_assoc]
      rw [hWW', Matrix.mul_one, ← Matrix.mul_assoc, hXX', Matrix.one_mul]
  have hβeq : ∀ (x : ↥L2) (u v : ↥(pCoreOf 2 L2)), (v : G) = x * u * x⁻¹ →
      Multiplicative.toAdd (β v) = (α x : Matrix (Fin 2) (Fin 2) K) *
        Multiplicative.toAdd (β u) *
          ((α x : Matrix (Fin 2) (Fin 2) K).map (· ^ 2 ^ f)).transpose := by
    intro x u v hv
    have h0 := hβeq₀ x (eU u) (eU v) (by rw [heU, heU]; exact hv)
    rw [hβapp, hβapp, h0, hαapp]
    exact conj_herm_equivariant hU X (α₀ x) _
  have hHerm : ∀ u, (Multiplicative.toAdd (β u)).map (· ^ 2 ^ f) =
      (Multiplicative.toAdd (β u)).transpose := fun u => (hrange _).mp ⟨u, rfl⟩
  have hsec : ∀ t : K, ∃ s : ↥L2, (s : G) ∈ S ∧
      (α s : Matrix (Fin 2) (Fin 2) K) = !![1, t; 0, 1] := by
    intro t
    obtain ⟨s, hs⟩ := hαsurj (uSL t)
    exact ⟨s, (hX s).mpr ⟨t, by rw [← hαapp, hs, coe_uSL]⟩, by rw [hs, coe_uSL]⟩
  obtain ⟨t₀, ht₀⟩ := hU.exists_bar_ne
  rw [hU.bar_apply] at ht₀
  have hcenter : ∀ u : ↥(pCoreOf 2 L2), (u : G) ∈ centerOf (pCoreOf 2 L1) ↔
      Multiplicative.toAdd (β u) 0 1 = 0 ∧ Multiplicative.toAdd (β u) 1 1 = 0 := by
    intro u
    constructor
    · intro hu
      have hfix : ∀ t : K, !![1, t; 0, 1] * Multiplicative.toAdd (β u) *
          ((!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) K).map (· ^ 2 ^ f)).transpose =
            Multiplicative.toAdd (β u) := by
        intro t
        obtain ⟨s, hsS, hs⟩ := hsec t
        have hcomm : (s : G) * u * (s : G)⁻¹ = u := by
          have h := Subgroup.mem_centralizer_iff.mp (hD.center_left (hSL1 hsS)) _ hu
          rw [← h]
          group
        have h := hβeq s u u hcomm.symm
        rw [hs] at h
        exact h.symm
      exact eq_zero_of_forall_unitriangular ht₀ _ hfix
    · rintro ⟨h01, h11⟩
      have h10 : Multiplicative.toAdd (β u) 1 0 = 0 := by
        have h := congrFun (congrFun (hHerm u) 0) 1
        simp only [Matrix.map_apply, Matrix.transpose_apply, h01] at h
        rw [← h]
        exact zero_pow (pow_ne_zero _ two_ne_zero)
      have hcomm : ∀ s ∈ S, s * (u : G) * s⁻¹ = u := by
        intro s hs
        obtain ⟨t, ht⟩ := (hX ⟨s, hSL2 hs⟩).mp hs
        let v : ↥(pCoreOf 2 L2) :=
          ⟨s * u * s⁻¹, CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf (hSL2 hs) u.2⟩
        have hv := hβeq ⟨s, hSL2 hs⟩ u v rfl
        rw [show (α ⟨s, hSL2 hs⟩ : Matrix (Fin 2) (Fin 2) K) = !![1, t; 0, 1] by
          rw [hαapp]; exact ht, unitriangular_mul_mul_map_transpose, h01, h11, h10] at hv
        have hvu : v = u := by
          apply hβinj
          apply Multiplicative.toAdd.injective
          rw [hv]
          ext i j
          fin_cases i <;> fin_cases j <;> simp [h01, h11, h10]
        exact congrArg Subtype.val hvu
      have huL1 : (u : G) ∈ L1 := hSL1 (hH.pCoreOf_le_right u.2)
      have huC : (u : G) ∈ Subgroup.centralizer (pCoreOf 2 L1 : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have h := hcomm y (hH.pCoreOf_le_left hy)
        calc y * (u : G) = y * u * y⁻¹ * y := by group
          _ = u * y := by rw [h]
      exact ⟨charTwo_vertex_left hH ⟨huL1, huC⟩, huC⟩
  have hfwd : ∀ u : ↥(pCoreOf 2 L2), (u : G) ∈ pCoreOf 2 L1 →
      Multiplicative.toAdd (β u) 1 1 = 0 := by
    intro u hu1
    obtain ⟨s, hsS, hs⟩ := hsec 1
    let v : ↥(pCoreOf 2 L2) :=
      ⟨s * u * s⁻¹, CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf s.2 u.2⟩
    have hv := hβeq s u v rfl
    rw [hs, unitriangular_mul_mul_map_transpose] at hv
    have hw : ((v * u⁻¹ : ↥(pCoreOf 2 L2)) : G) ∈ centerOf (pCoreOf 2 L1) :=
      hD.commutator_inf_mem_centerOf hH hS hsS ⟨hu1, u.2⟩
    have h01 := ((hcenter (v * u⁻¹)).mp hw).1
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hv] at h01
    simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_cons, one_mul] at h01
    linear_combination h01
  have hRcard : Nat.card {M : Multiplicative (Matrix (Fin 2) (Fin 2) K) //
      Multiplicative.toAdd M 1 1 = 0 ∧
        (Multiplicative.toAdd M).map (· ^ 2 ^ f) = (Multiplicative.toAdd M).transpose} ≤
      2 ^ (3 * f) := by
    have hcard : Nat.card (hU.fixedField × K) = 2 ^ (3 * f) := by
      rw [Nat.card_prod, hU.card_fixedField, hKcard', ← pow_add]
      ring_nf
    rw [← hcard]
    refine Nat.card_le_card_of_injective (fun M => (⟨Multiplicative.toAdd M.1 0 0, ?_⟩,
      Multiplicative.toAdd M.1 0 1)) ?_
    · rw [hU.mem_fixedField, hU.bar_apply]
      have h := congrFun (congrFun M.2.2 0) 0
      simpa only [Matrix.map_apply, Matrix.transpose_apply] using h
    · intro M N h
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      have hM := congrFun (congrFun M.2.2 0) 1
      have hN := congrFun (congrFun N.2.2 0) 1
      simp only [Matrix.map_apply, Matrix.transpose_apply] at hM hN
      ext i j
      fin_cases i <;> fin_cases j
      · exact h.1
      · exact h.2
      · change Multiplicative.toAdd M.1 1 0 = Multiplicative.toAdd N.1 1 0
        rw [← hM, ← hN, h.2]
      · change Multiplicative.toAdd M.1 1 1 = Multiplicative.toAdd N.1 1 1
        rw [M.2.1, N.2.1]
  let W : Subgroup ↥(pCoreOf 2 L2) :=
    { carrier := {u | Multiplicative.toAdd (β u) 1 1 = 0}
      one_mem' := by
        change Multiplicative.toAdd (β 1) 1 1 = 0
        rw [map_one]
        rfl
      mul_mem' := by
        intro a b ha hb
        change Multiplicative.toAdd (β (a * b)) 1 1 = 0
        change Multiplicative.toAdd (β a) 1 1 = 0 at ha
        change Multiplicative.toAdd (β b) 1 1 = 0 at hb
        rw [map_mul, toAdd_mul, Matrix.add_apply, ha, hb, add_zero]
      inv_mem' := by
        intro a ha
        change Multiplicative.toAdd (β a⁻¹) 1 1 = 0
        change Multiplicative.toAdd (β a) 1 1 = 0 at ha
        rw [map_inv, toAdd_inv, Matrix.neg_apply, ha, neg_zero] }
  have hkercard : Nat.card β.ker = 1 := by
    rw [(MonoidHom.ker_eq_bot_iff β).mpr hβinj, Subgroup.card_bot]
  have hWcard : Nat.card W ≤ 2 ^ (3 * f) := by
    calc Nat.card W ≤ Nat.card β.ker * Nat.card {M : Multiplicative (Matrix (Fin 2) (Fin 2) K) |
        Multiplicative.toAdd M 1 1 = 0 ∧
          (Multiplicative.toAdd M).map (· ^ 2 ^ f) = (Multiplicative.toAdd M).transpose} :=
          card_le_card_ker_mul β W _ fun w hw => ⟨hw, hHerm w⟩
      _ ≤ 2 ^ (3 * f) := by rw [hkercard, one_mul]; exact hRcard
  have hℓle : (pCoreOf 2 L1 ⊓ pCoreOf 2 L2).subgroupOf (pCoreOf 2 L2) ≤ W :=
    fun u hu => hfwd u hu.1
  have hℓcard : Nat.card ↥((pCoreOf 2 L1 ⊓ pCoreOf 2 L2).subgroupOf (pCoreOf 2 L2)) =
      2 ^ (3 * f) := by
    rw [← hD.card_inf]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hℓW : (pCoreOf 2 L1 ⊓ pCoreOf 2 L2).subgroupOf (pCoreOf 2 L2) = W :=
    Subgroup.eq_of_le_of_card_ge hℓle (by rw [hℓcard]; exact hWcard)
  have hbwd : ∀ u : ↥(pCoreOf 2 L2), Multiplicative.toAdd (β u) 1 1 = 0 →
      (u : G) ∈ pCoreOf 2 L1 := by
    intro u hu
    have hu' : u ∈ W := hu
    rw [← hℓW, Subgroup.mem_subgroupOf] at hu'
    exact hu'.1
  exact ⟨K, hField, hFintype, ⟨⟨α, β, hKcard', hαsurj, hα1, hβinj, hrange, hβeq, hX, hcenter,
    fun u => ⟨hfwd u, hbwd u⟩⟩⟩⟩

theorem U4qCoordLeft.exists_pCoreOf_right {F : Type*} [Field F] (c₁ : U4qCoordLeft L1 L2 S f F)
    (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f))
    (t : F) :
    ∃ x : ↥L1, (x : G) ∈ pCoreOf 2 L2 ∧ (c₁.α x : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := by
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [c₁.card]; positivity)
  refine exists_alpha_eq_of_card c₁.α c₁.eq_one_iff (fun x hx => (c₁.mem_iff x).mp hx)
    hH.pCoreOf_le_right (hH.pCoreOf_le_right.trans (hD.le_left hH hS)) ?_ t
  rw [c₁.card, hD.card_inf, hD.card_right, ← pow_add]
  ring_nf

theorem U4qCoordRight.exists_pCoreOf_left {K : Type*} [Field K]
    (c₂ : U4qCoordRight L1 L2 S f K) (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hS : Nat.card S = 2 ^ (6 * f)) (t : K) :
    ∃ x : ↥L2, (x : G) ∈ pCoreOf 2 L1 ∧ (c₂.α x : Matrix (Fin 2) (Fin 2) K) = !![1, t; 0, 1] := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [c₂.card]; positivity)
  refine exists_alpha_eq_of_card c₂.α c₂.eq_one_iff (fun x hx => (c₂.mem_iff x).mp hx)
    hH.pCoreOf_le_left (hH.pCoreOf_le_left.trans (hD.le_right hH hS)) ?_ t
  rw [c₂.card, inf_comm, hD.card_inf, hD.card_left, ← pow_add]
  ring_nf

end CFSG.Quasithin.F112R.St84

end
