module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalLocal

import CFSG.Quasithin.Recognition.St84.Gen.AmalVertexLocal
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldUnipotent
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
import CFSG.GroupTheory.PCore.NormalPCoreOf
import CFSG.CGT.Timmesfeld75.L2Sylow

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
open CFSG.LieType.BorelTits CFSG.CGT.Timmesfeld75
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open scoped MatrixGroups

section Generic

variable {G : Type} [Group G]

theorem eq_of_relIndex_le_two_of_conj_fixedPointFree {Q W N : Subgroup G} [Finite Q]
    (hQW : Q ≤ Subgroup.normalizer (W : Set G)) {d : G}
    (hdQ : d ∈ Subgroup.normalizer (Q : Set G)) (hdW : d ∈ Subgroup.normalizer (W : Set G))
    (hfix : ∀ x ∈ Q, d * x * d⁻¹ * x⁻¹ ∈ W → x ∈ W) (hNQ : N ≤ Q) (hWN : W ≤ N)
    (hdN : d ∈ Subgroup.normalizer (N : Set G)) (hidx : N.relIndex Q ≤ 2) : N = Q := by
  have h0 : (N.subgroupOf Q).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h12 : N.relIndex Q = 1 ∨ N.relIndex Q = 2 := by
    change (N.subgroupOf Q).index = 1 ∨ (N.subgroupOf Q).index = 2
    change (N.subgroupOf Q).index ≤ 2 at hidx
    omega
  rcases h12 with h1 | h2
  · exact le_antisymm hNQ (Subgroup.relIndex_eq_one.mp h1)
  haveI : (W.subgroupOf Q).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hQW
  let c : ↥Q →* ↥Q :=
    { toFun := fun u => ⟨d * u * d⁻¹, (Subgroup.mem_normalizer_iff.mp hdQ u).mp u.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun u v => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hc : ∀ u : ↥Q, ((c u : ↥Q) : G) = d * u * d⁻¹ := fun u => rfl
  let φ : ↥Q ⧸ W.subgroupOf Q →* ↥Q ⧸ W.subgroupOf Q :=
    QuotientGroup.map _ _ c fun u hu => by
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hc]
      exact (Subgroup.mem_normalizer_iff.mp hdW u).mp hu
  have hφ : ∀ u : ↥Q, φ (u : ↥Q ⧸ W.subgroupOf Q) = (c u : ↥Q ⧸ W.subgroupOf Q) :=
    fun u => QuotientGroup.map_mk _ _ _ _ u
  have hfree : MonoidHom.FixedPointFree φ := by
    intro g hg
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective g
    rw [hφ, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hg
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    refine hfix u u.2 ?_
    have h := (Subgroup.mem_normalizer_iff.mp (hQW u.2) _).mp (W.inv_mem hg)
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hc] at h
    convert h using 1
    group
  refine le_antisymm hNQ fun x hx => ?_
  obtain ⟨g, hg⟩ :=
    hfree.commutatorMap_surjective (QuotientGroup.mk (⟨x, hx⟩ : ↥Q) : ↥Q ⧸ W.subgroupOf Q)
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective g
  rw [MonoidHom.commutatorMap_apply, hφ, ← QuotientGroup.mk_div, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at hg
  have hcu : ((u / c u : ↥Q) : G) ∈ N := by
    have hmem : u / c u ∈ N.subgroupOf Q := by
      rw [div_eq_mul_inv, Subgroup.mul_mem_iff_of_index_two h2, inv_mem_iff,
        Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hc]
      exact Subgroup.mem_normalizer_iff.mp hdN u
    exact hmem
  have hxe : x = ((u / c u : ↥Q) : G) * (((u / c u)⁻¹ * ⟨x, hx⟩ : ↥Q) : G) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [hxe]
  exact N.mul_mem hcu (hWN hg)

private theorem commutator_mem_of_index_le_two_U4qExt {X : Type*} [Group X] [Finite X]
    {H : Subgroup X} (h : H.index ≤ 2) (a b : X) : a * b * a⁻¹ * b⁻¹ ∈ H := by
  have h0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (show H.index = 1 ∨ H.index = 2 by omega) with h1 | h2
  · rw [Subgroup.index_eq_one.mp h1]
    exact Subgroup.mem_top _
  · rw [Subgroup.mul_mem_iff_of_index_two h2, Subgroup.mul_mem_iff_of_index_two h2,
      Subgroup.mul_mem_iff_of_index_two h2, inv_mem_iff, inv_mem_iff]
    tauto

private theorem relIndex_inf_le_U4qExt [Finite G] {Q S L : Subgroup G} (hQS : Q ≤ S) :
    (Q ⊓ L).relIndex Q ≤ (S ⊓ L).relIndex S := by
  rw [Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_left]
  exact Subgroup.relIndex_le_of_le_right hQS Subgroup.index_ne_zero_of_finite

private theorem card_mul_card_le_U4qExt [Finite G] (A B : Subgroup G) :
    Nat.card A * Nat.card B ≤ Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) := by
  have h1 := Subgroup.relIndex_mul_card A B
  have h2 := Subgroup.relIndex_mul_card A (A ⊔ B)
  have h3 : A.relIndex B ≤ A.relIndex (A ⊔ B) :=
    Subgroup.relIndex_le_of_le_right le_sup_right Subgroup.index_ne_zero_of_finite
  rw [inf_sup_self] at h2
  rw [← h1, ← h2]
  calc Nat.card A * (A.relIndex B * Nat.card ↥(A ⊓ B))
      = A.relIndex B * Nat.card A * Nat.card ↥(A ⊓ B) := by ring
    _ ≤ A.relIndex (A ⊔ B) * Nat.card A * Nat.card ↥(A ⊓ B) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h3)

private theorem charTwo_sup_of_le_U4qExt [Finite G] {Li B S S₀ : Subgroup G}
    (hC : CharTwo (Li ⊔ S ⊔ B))
    (hS₀ : S₀ ≤ S) (hLi : S ≤ Subgroup.normalizer (Li : Set G))
    (hS₀n : S ≤ Subgroup.normalizer (S₀ : Set G)) (hB : S ≤ Subgroup.normalizer (B : Set G)) :
    CharTwo (Li ⊔ S₀ ⊔ B) := by
  have hle : Li ⊔ S₀ ⊔ B ≤ Li ⊔ S ⊔ B := sup_le_sup_right (sup_le_sup_left hS₀ Li) B
  refine CharTwo.of_normal hC hle ?_
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  have hSN : S ≤ Subgroup.normalizer ((Li ⊔ S₀ ⊔ B : Subgroup G) : Set G) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hLi hs, hS₀n hs⟩, hB hs⟩
  exact sup_le (sup_le ((le_sup_left.trans le_sup_left).trans Subgroup.le_normalizer) hSN)
    (le_sup_right.trans Subgroup.le_normalizer)

end Generic

section Torus

private def diagSLU4qExt {F : Type} [Field F] (a : Fˣ) : SL(2, F) :=
  ⟨!![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two]⟩

private theorem coe_diagSLU4qExt {F : Type} [Field F] (a : Fˣ) :
    ((diagSLU4qExt a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      !![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)] :=
  rfl

private theorem diagSLU4qExt_mem_borel {F : Type} [Field F] (a : Fˣ) :
    diagSLU4qExt a ∈ borel F := by
  rw [mem_borel_iff]
  change (!![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)] : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  simp

private theorem range_upperUnipotent_le_utri_U4qExt {F : Type} [Field F] :
    (upperUnipotent (F := F)).range ≤ utri F := by
  intro g hg
  have h := (sl2_fixes_first_iff g).mpr hg
  change Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) F) (Pi.single 0 1) = Pi.single 0 1 at h
  rw [Matrix.mulVec_single_one] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Matrix.transpose_apply, Pi.single_eq_same] at h0
  simp only [Matrix.transpose_apply, ne_eq, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one,
    not_false_eq_true, Pi.single_eq_of_ne] at h1
  exact mem_utri_entries.mpr ⟨h1, h0⟩

variable {G : Type} [Group G]

private theorem exists_conj_mem_utri_iff_U4qExt [Finite G] {L T : Subgroup G} {F : Type}
    [Field F] [Finite F] [CharP F 2] (hT : IsSylowTwoOf T L) (α : ↥L →* SL(2, F))
    (hker : IsPGroup 2 α.ker) :
    ∃ X : SL(2, F), ∀ x : ↥L, (x : G) ∈ T ↔ X * α x * X⁻¹ ∈ utri F := by
  classical
  have hT2 : IsPGroup 2 (T.subgroupOf L) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  obtain ⟨x, hx⟩ := pgroup_sl2_conjugate_unipotent ((T.subgroupOf L).map α) (hT2.map α)
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
  have hle : (T.subgroupOf L).map α' ≤ utri F := by
    have hmap : (T.subgroupOf L).map α' =
        ((T.subgroupOf L).map α).map (MulAut.conj X).toMonoidHom := by
      rw [Subgroup.map_map]
    rw [hmap]
    exact (show _ ≤ (upperUnipotent (F := F)).range by simpa [X] using hx).trans
      range_upperUnipotent_le_utri_U4qExt
  let P : Sylow 2 ↥L := hT2.toSylow hT.2.2
  have hPle : (P : Subgroup ↥L) ≤ (utri F).comap α' :=
    fun y hy => hle (Subgroup.mem_map_of_mem α' hy)
  have hH : (utri F).comap α' = T.subgroupOf L :=
    P.is_maximal' (isPGroup_utri.comap_of_ker_isPGroup α' (hker' ▸ hker)) hPle
  refine ⟨X, fun y => ?_⟩
  rw [← hα', ← Subgroup.mem_comap, hH, Subgroup.mem_subgroupOf]

private theorem conj_mem_of_mem_borel_U4qExt {L T : Subgroup G} {F : Type} [Field F]
    (hTL : T ≤ L) (α : ↥L →* SL(2, F)) {X : SL(2, F)}
    (hX : ∀ x : ↥L, (x : G) ∈ T ↔ X * α x * X⁻¹ ∈ utri F) {g : ↥L}
    (hg : X * α g * X⁻¹ ∈ borel F) {y : G} (hy : y ∈ T) :
    (g : G) * y * (g : G)⁻¹ ∈ T := by
  have hyL : y ∈ L := hTL hy
  set y' : ↥L := ⟨y, hyL⟩ with hy'
  have h1 : X * α y' * X⁻¹ ∈ utri F := (hX y').mp hy
  have h2 := conj_mem_utri_of_mem_borel hg h1
  have e : X * α g * X⁻¹ * (X * α y' * X⁻¹) * (X * α g * X⁻¹)⁻¹ =
      X * α (g * y' * g⁻¹) * X⁻¹ := by
    simp only [map_mul, map_inv]
    group
  rw [e] at h2
  have h3 : ((g * y' * g⁻¹ : ↥L) : G) ∈ T := (hX (g * y' * g⁻¹)).mpr h2
  simpa [hy'] using h3

private theorem exists_mem_normalizer_conj_eq_diag_U4qExt [Finite G] {L T : Subgroup G}
    {F : Type} [Field F] [Finite F] [CharP F 2] (hT : IsSylowTwoOf T L) (α : ↥L →* SL(2, F))
    (hα : Function.Surjective α) (hker : IsPGroup 2 α.ker) (a : Fˣ) :
    ∃ (X : SL(2, F)) (d : ↥L), (d : G) ∈ Subgroup.normalizer (T : Set G) ∧
      X * α d * X⁻¹ = diagSLU4qExt a := by
  obtain ⟨X, hX⟩ := exists_conj_mem_utri_iff_U4qExt hT α hker
  obtain ⟨d, hd⟩ := hα (X⁻¹ * diagSLU4qExt a * X)
  have hD : X * α d * X⁻¹ = diagSLU4qExt a := by
    rw [hd]
    group
  have hDb : X * α d * X⁻¹ ∈ borel F := by
    rw [hD]
    exact diagSLU4qExt_mem_borel a
  have hDb' : X * α d⁻¹ * X⁻¹ ∈ borel F := by
    have e : X * α d⁻¹ * X⁻¹ = (X * α d * X⁻¹)⁻¹ := by
      rw [map_inv]
      group
    rw [e]
    exact inv_mem hDb
  refine ⟨X, d, Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩, hD⟩
  · exact conj_mem_of_mem_borel_U4qExt hT.1 α hX hDb hy
  · have h := conj_mem_of_mem_borel_U4qExt hT.1 α hX hDb' hy
    have e : ((d⁻¹ : ↥L) : G) * ((d : G) * y * (d : G)⁻¹) * ((d⁻¹ : ↥L) : G)⁻¹ = y := by
      rw [Subgroup.coe_inv]
      group
    rwa [e] at h

end Torus

section Fixed

private theorem eq_zero_of_mul_eq_self_U4qExt {K : Type} [Field K] {a x : K} (ha : a ≠ 1)
    (h : a * x = x) : x = 0 := by
  have h' : (a - 1) * x = 0 := by rw [sub_mul, h, one_mul, sub_self]
  exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr ha)

private theorem mul_eq_diag_mul_U4qExt {F : Type} [Field F] {X A : SL(2, F)} {a : Fˣ}
    (hXA : X * A * X⁻¹ = diagSLU4qExt a) :
    (X : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) =
      !![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)] * (X : Matrix (Fin 2) (Fin 2) F) := by
  have h : X * A = diagSLU4qExt a * X := by
    rw [← hXA]
    group
  rw [← coe_diagSLU4qExt, ← Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.SpecialLinearGroup.coe_mul, h]

private theorem eq_zero_of_mul_eq_U4qExt {F : Type} [Field F] {X A : SL(2, F)} {s : Fˣ}
    (hs : s ≠ 1) (hXA : X * A * X⁻¹ = diagSLU4qExt s) {Y : Matrix (Fin 2) (Fin 2) F}
    (hY : (A : Matrix (Fin 2) (Fin 2) F) * Y = Y) : Y = 0 := by
  have hs1 : (s : F) ≠ 1 := fun h => hs (Units.ext h)
  have hs2 : ((s⁻¹ : Fˣ) : F) ≠ 1 := fun h => hs (inv_eq_one.mp (Units.ext h))
  set M : Matrix (Fin 2) (Fin 2) F := (X : Matrix (Fin 2) (Fin 2) F) * Y with hM
  have hDM : !![(s : F), 0; 0, ((s⁻¹ : Fˣ) : F)] * M = M := by
    rw [hM, ← Matrix.mul_assoc, ← mul_eq_diag_mul_U4qExt hXA, Matrix.mul_assoc, hY]
  have e : ∀ i j, (!![(s : F), 0; 0, ((s⁻¹ : Fˣ) : F)] * M) i j = M i j := fun i j => by
    rw [hDM]
  have hM0 : M = 0 := by
    ext i j
    fin_cases i
    · have h := e 0 j
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Matrix.head_cons, zero_mul, add_zero] at h
      exact eq_zero_of_mul_eq_self_U4qExt hs1 h
    · have h := e 1 j
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Matrix.head_cons, zero_mul, zero_add] at h
      exact eq_zero_of_mul_eq_self_U4qExt hs2 h
  have hYM : Y = ((X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * M := by
    rw [hM, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
  rw [hYM, hM0, Matrix.mul_zero]

private theorem diag_mul_mul_map_transpose_U4qExt {K : Type} [Field K] (σ : K →+* K) (a b : K)
    (M : Matrix (Fin 2) (Fin 2) K) :
    !![a, 0; 0, b] * M * ((!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) K).map σ).transpose =
      !![a * M 0 0 * σ a, a * M 0 1 * σ b; b * M 1 0 * σ a, b * M 1 1 * σ b] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.vecMul, dotProduct, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff] <;> ring

private theorem eq_zero_of_conj_herm_eq_U4qExt {K : Type} [Field K] (σ : K →+* K)
    {X A : SL(2, K)} {t : Kˣ} (h1 : (t : K) * σ t ≠ 1) (h2 : σ t ≠ t)
    (hXA : X * A * X⁻¹ = diagSLU4qExt t) {Y : Matrix (Fin 2) (Fin 2) K}
    (hY : (A : Matrix (Fin 2) (Fin 2) K) * Y *
      ((A : Matrix (Fin 2) (Fin 2) K).map σ).transpose = Y) : Y = 0 := by
  set Xm : Matrix (Fin 2) (Fin 2) K := (X : Matrix (Fin 2) (Fin 2) K) with hXm
  set Dm : Matrix (Fin 2) (Fin 2) K := !![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)] with hDm
  have hXA' : Xm * (A : Matrix (Fin 2) (Fin 2) K) = Dm * Xm := mul_eq_diag_mul_U4qExt hXA
  set M : Matrix (Fin 2) (Fin 2) K := Xm * Y * (Xm.map σ).transpose with hM
  have hDM : Dm * M * (Dm.map σ).transpose = M := by
    calc Dm * M * (Dm.map σ).transpose
        = (Dm * Xm) * Y * ((Dm * Xm).map σ).transpose := by
          rw [Matrix.map_mul, Matrix.transpose_mul, hM]
          simp only [Matrix.mul_assoc]
      _ = (Xm * (A : Matrix (Fin 2) (Fin 2) K)) * Y *
          ((Xm * (A : Matrix (Fin 2) (Fin 2) K)).map σ).transpose := by rw [hXA']
      _ = Xm * ((A : Matrix (Fin 2) (Fin 2) K) * Y *
          ((A : Matrix (Fin 2) (Fin 2) K).map σ).transpose) * (Xm.map σ).transpose := by
          rw [Matrix.map_mul, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = M := by rw [hY]
  rw [hDm, diag_mul_mul_map_transpose_U4qExt] at hDM
  have ht : (t : K) * ((t⁻¹ : Kˣ) : K) = 1 := Units.mul_inv t
  have hσ : σ t * σ ((t⁻¹ : Kˣ) : K) = 1 := by rw [← map_mul, ht, map_one]
  have e00 := congrFun (congrFun hDM 0) 0
  have e01 := congrFun (congrFun hDM 0) 1
  have e10 := congrFun (congrFun hDM 1) 0
  have e11 := congrFun (congrFun hDM 1) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] at e00 e01 e10 e11
  have h2' : σ t - t ≠ 0 := sub_ne_zero.mpr h2
  have hM00 : M 0 0 = 0 :=
    eq_zero_of_mul_eq_self_U4qExt h1 (by linear_combination e00)
  have hM11 : M 1 1 = 0 :=
    eq_zero_of_mul_eq_self_U4qExt h1 (by
      linear_combination (-((t : K) * σ t)) * e11 + (M 1 1 * σ t * σ ((t⁻¹ : Kˣ) : K)) * ht +
        M 1 1 * hσ)
  have hM01 : M 0 1 = 0 := by
    have h : (σ t - t) * M 0 1 = 0 := by
      linear_combination (-(σ t)) * e01 + ((t : K) * M 0 1) * hσ
    exact (mul_eq_zero.mp h).resolve_left h2'
  have hM10 : M 1 0 = 0 := by
    have h : (σ t - t) * M 1 0 = 0 := by
      linear_combination (t : K) * e10 - (M 1 0 * σ t) * ht
    exact (mul_eq_zero.mp h).resolve_left h2'
  have hM0 : M = 0 := by
    ext i j
    fin_cases i <;> fin_cases j
    · exact hM00
    · exact hM01
    · exact hM10
    · exact hM11
  have hXi : ((X⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * Xm = 1 := by
    rw [hXm, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hXi' : (Xm.map σ).transpose *
      (((X⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).map σ).transpose = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hXi, Matrix.map_one _ (map_zero σ) (map_one σ),
      Matrix.transpose_one]
  have hYM : Y = ((X⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * M *
      (((X⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).map σ).transpose := by
    rw [hM]
    calc Y = (((X⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * Xm) * Y *
          ((Xm.map σ).transpose *
            (((X⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).map σ).transpose) := by
          rw [hXi, hXi', Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [hYM, hM0, Matrix.mul_zero, Matrix.zero_mul]

end Fixed

section Fields

private theorem exists_unit_ne_one_U4qExt {F : Type} [Field F] [Fintype F] {f : ℕ} (hf : 2 ≤ f)
    (hF : Fintype.card F = 2 ^ f) : ∃ s : Fˣ, s ≠ 1 := by
  have hq : 4 ≤ 2 ^ f :=
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h : 1 < Nat.card Fˣ := by
    rw [Nat.card_units, Nat.card_eq_fintype_card, hF]
    omega
  haveI : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp h
  exact exists_ne 1

private theorem exists_unit_pow_ne_U4qExt {K : Type} [Field K] [Fintype K] {f : ℕ} (hf : 2 ≤ f)
    (hK : Fintype.card K = 2 ^ (2 * f)) :
    ∃ t : Kˣ, (t : K) * (t : K) ^ 2 ^ f ≠ 1 ∧ (t : K) ^ 2 ^ f ≠ t := by
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf t = 2 ^ f * 2 ^ f - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ht, Nat.card_units, Nat.card_eq_fintype_card, hK,
      two_mul, pow_add]
  have hq : 4 ≤ 2 ^ f :=
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hqq : 4 * 2 ^ f ≤ 2 ^ f * 2 ^ f := Nat.mul_le_mul_right _ hq
  refine ⟨t, fun h => ?_, fun h => ?_⟩
  · have h' : t ^ (2 ^ f + 1) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ, mul_comm]
      exact h
    have hle := Nat.le_of_dvd (by omega) (hord ▸ orderOf_dvd_of_pow_eq_one h')
    generalize 2 ^ f * 2 ^ f = Q at hle hqq
    omega
  · have h1 : t ^ (2 ^ f) = t := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact h)
    have h' : t ^ (2 ^ f - 1) = 1 := by
      have e : t ^ (2 ^ f - 1) * t = 1 * t := by
        rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, h1, one_mul]
      exact mul_right_cancel e
    have hle := Nat.le_of_dvd (by omega) (hord ▸ orderOf_dvd_of_pow_eq_one h')
    generalize 2 ^ f * 2 ^ f = Q at hle hqq
    omega

end Fields

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

theorem U4qLocalData.card_inf_left_of_ext (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f) :
    Nat.card ↥(S ⊓ L1) = 2 ^ (6 * f) := by
  rw [IsSylowTwoOf.card_eq hH.h1.sylow, hD.twoPart_left]

theorem U4qLocalData.card_inf_right_of_ext (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) : Nat.card ↥(S ⊓ L2) = 2 ^ (6 * f) := by
  rw [IsSylowTwoOf.card_eq hH.h2.sylow, hD.twoPart_right]

private theorem relIndex_eq_two_U4qExt {X : Subgroup G} (hXS : X ≤ S)
    (hX : Nat.card X = 2 ^ (6 * f)) (hS2 : Nat.card S = 2 * 2 ^ (6 * f)) : X.relIndex S = 2 := by
  have h := Subgroup.relIndex_mul_card X S
  rw [inf_eq_left.mpr hXS, hX, hS2] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h

theorem U4qLocalData.relIndex_inf_left_of_ext (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS2 : Nat.card S = 2 * 2 ^ (6 * f)) :
    (S ⊓ L1).relIndex S = 2 :=
  relIndex_eq_two_U4qExt inf_le_left (hD.card_inf_left_of_ext hH) hS2

theorem U4qLocalData.relIndex_inf_right_of_ext (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS2 : Nat.card S = 2 * 2 ^ (6 * f)) :
    (S ⊓ L2).relIndex S = 2 :=
  relIndex_eq_two_U4qExt inf_le_left (hD.card_inf_right_of_ext hH) hS2

private theorem mem_normalizer_bot_U4qExt (x : G) :
    x ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) :=
  Subgroup.le_normalizer_of_normal (H := ⊥) (K := ⊤) (Subgroup.mem_top x)

theorem U4qLocalData.pCoreOf_right_le_left_of_ext (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hf : 2 ≤ f) (hS2 : Nat.card S = 2 * 2 ^ (6 * f)) :
    pCoreOf 2 L2 ≤ L1 := by
  classical
  obtain ⟨K, hKfield, hKfin, hKcard, α, hα, hker, β, -, hβker, hβeq⟩ := hD.omega_right
  letI := hKfield
  letI := hKfin
  haveI : CharP K 2 := charP_of_card_eq_prime_pow hKcard
  obtain ⟨t, ht1, ht2⟩ := exists_unit_pow_ne_U4qExt hf hKcard
  obtain ⟨X, d, hdN, hdX⟩ := exists_mem_normalizer_conj_eq_diag_U4qExt hH.h2.sylow α hα
    (by rw [hker]; exact CFSG.pCore_isPGroup) t
  have hdB : (d : G) ∈ borelOf L2 S := ⟨d.2, hdN⟩
  have hdL1 : (d : G) ∈ Subgroup.normalizer (L1 : Set G) := hH.h1.borel_le hdB
  have hdQ : (d : G) ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set G) :=
    le_normalizer_pCoreOf 2 L2 d.2
  have hfix : ∀ x ∈ pCoreOf 2 L2, (d : G) * x * (d : G)⁻¹ * x⁻¹ ∈ (⊥ : Subgroup G) →
      x ∈ (⊥ : Subgroup G) := by
    intro x hx hxd
    rw [Subgroup.mem_bot, mul_inv_eq_one] at hxd
    have hxU : x ∈ blockU L2 := by
      rw [hD.blockU_right]
      exact hx
    have hY := hβeq d ⟨x, hxU⟩ ⟨x, hxU⟩ hxd.symm
    have h0 : Multiplicative.toAdd (β ⟨x, hxU⟩) = 0 :=
      eq_zero_of_conj_herm_eq_U4qExt (iterateFrobenius K 2 f) ht1 ht2 hdX hY.symm
    have hk : (⟨x, hxU⟩ : ↥(blockU L2)) ∈ β.ker := by
      rw [MonoidHom.mem_ker]
      exact h0
    rw [hβker, Subgroup.mem_subgroupOf, hD.blockZ_right] at hk
    exact hk
  have hidx : (pCoreOf 2 L2 ⊓ L1).relIndex (pCoreOf 2 L2) ≤ 2 :=
    (relIndex_inf_le_U4qExt hH.pCoreOf_le_right).trans
      (hD.relIndex_inf_left_of_ext hH hS2).le
  have hN := eq_of_relIndex_le_two_of_conj_fixedPointFree
    (fun x _ => mem_normalizer_bot_U4qExt x) hdQ (mem_normalizer_bot_U4qExt _) hfix inf_le_left
    bot_le (Subgroup.inf_normalizer_le_normalizer_inf ⟨hdQ, hdL1⟩) hidx
  exact inf_eq_left.mp hN

private theorem U4qLocalData.commutator_eq_center_of_ext (hD : U4qLocalData L1 L2 S f) :
    commutator ↥(pCoreOf 2 L1) = Subgroup.center ↥(pCoreOf 2 L1) := by
  rcases hD.special_left.1.2 with ⟨hab, -⟩ | ⟨hc, -, -⟩
  · exfalso
    have hcen : Subgroup.center ↥(pCoreOf 2 L1) = ⊤ :=
      (Subgroup.eq_top_iff' _).mpr fun x =>
        Subgroup.mem_center_iff.mpr fun g => hab.is_comm.comm g x
    have hZ := hD.special_left.2.2
    rw [hcen, Subgroup.card_top, hD.special_left.2.1] at hZ
    have hf := hD.one_le
    have hlt : 2 ^ f < (2 ^ f) ^ (1 + 2 * 2) := by
      calc 2 ^ f = (2 ^ f) ^ 1 := (pow_one _).symm
        _ < (2 ^ f) ^ (1 + 2 * 2) :=
          Nat.pow_lt_pow_right (Nat.one_lt_two_pow (by omega)) (by norm_num)
    omega
  · exact hc

private theorem U4qLocalData.centerOf_le_of_relIndex_le_two (hD : U4qLocalData L1 L2 S f)
    {N : Subgroup G} (hN : N.relIndex (pCoreOf 2 L1) ≤ 2) : centerOf (pCoreOf 2 L1) ≤ N := by
  intro z hz
  have hzc : (⟨z, hz.1⟩ : ↥(pCoreOf 2 L1)) ∈ commutator ↥(pCoreOf 2 L1) := by
    rw [hD.commutator_eq_center_of_ext]
    exact Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hz.2 y y.2)
  have key : commutator ↥(pCoreOf 2 L1) ≤ N.subgroupOf (pCoreOf 2 L1) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def]
    exact commutator_mem_of_index_le_two_U4qExt hN a b
  exact key hzc

theorem U4qLocalData.pCoreOf_left_le_right_of_ext (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hf : 2 ≤ f) (hS2 : Nat.card S = 2 * 2 ^ (6 * f)) :
    pCoreOf 2 L1 ≤ L2 := by
  classical
  obtain ⟨F, hFfield, hFfin, hFcard, α, hα, hker, β, -, hβker, hβeq⟩ := hD.twoNat_left
  letI := hFfield
  letI := hFfin
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hFcard
  obtain ⟨s, hs⟩ := exists_unit_ne_one_U4qExt hf hFcard
  obtain ⟨X, d, hdN, hdX⟩ := exists_mem_normalizer_conj_eq_diag_U4qExt hH.h1.sylow α hα
    (by rw [hker]; exact CFSG.pCore_isPGroup) s
  have hdB : (d : G) ∈ borelOf L1 S := ⟨d.2, hdN⟩
  have hdL2 : (d : G) ∈ Subgroup.normalizer (L2 : Set G) := hH.h2.borel_le hdB
  have hdQ : (d : G) ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
    le_normalizer_pCoreOf 2 L1 d.2
  have hQZ : pCoreOf 2 L1 ≤ Subgroup.normalizer (centerOf (pCoreOf 2 L1) : Set G) := by
    intro a ha
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp hz.2 a ha).symm
  have hdZ : (d : G) ∈ Subgroup.normalizer (centerOf (pCoreOf 2 L1) : Set G) :=
    Subgroup.centralizer_le_normalizer _ (hD.center_left d.2)
  have hfix : ∀ x ∈ pCoreOf 2 L1, (d : G) * x * (d : G)⁻¹ * x⁻¹ ∈ centerOf (pCoreOf 2 L1) →
      x ∈ centerOf (pCoreOf 2 L1) := by
    intro x hx hxd
    have hxU : x ∈ blockU L1 := by
      rw [hD.blockU_left]
      exact hx
    have hvU : (d : G) * x * (d : G)⁻¹ ∈ blockU L1 := by
      rw [hD.blockU_left]
      exact (Subgroup.mem_normalizer_iff.mp hdQ x).mp hx
    have hE := hβeq d ⟨x, hxU⟩ ⟨_, hvU⟩ rfl
    have hk : (⟨_, hvU⟩ : ↥(blockU L1)) * (⟨x, hxU⟩ : ↥(blockU L1))⁻¹ ∈ β.ker := by
      rw [hβker, Subgroup.mem_subgroupOf, hD.blockZ_left]
      exact hxd
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hk
    rw [hk] at hE
    have h0 : Multiplicative.toAdd (β ⟨x, hxU⟩) = 0 := eq_zero_of_mul_eq_U4qExt hs hdX hE.symm
    have hu : (⟨x, hxU⟩ : ↥(blockU L1)) ∈ β.ker := by
      rw [MonoidHom.mem_ker]
      exact h0
    rw [hβker, Subgroup.mem_subgroupOf, hD.blockZ_left] at hu
    exact hu
  have hidx : (pCoreOf 2 L1 ⊓ L2).relIndex (pCoreOf 2 L1) ≤ 2 :=
    (relIndex_inf_le_U4qExt hH.pCoreOf_le_left).trans
      (hD.relIndex_inf_right_of_ext hH hS2).le
  have hN := eq_of_relIndex_le_two_of_conj_fixedPointFree hQZ hdQ hdZ hfix inf_le_left
    (hD.centerOf_le_of_relIndex_le_two hidx)
    (Subgroup.inf_normalizer_le_normalizer_inf ⟨hdQ, hdL2⟩) hidx
  exact inf_eq_left.mp hN

private theorem U4qLocalData.card_sup_ge_of_ext (hD : U4qLocalData L1 L2 S f) :
    2 ^ (6 * f) ≤ Nat.card ↥(pCoreOf 2 L1 ⊔ pCoreOf 2 L2) := by
  have h := card_mul_card_le_U4qExt (pCoreOf 2 L1) (pCoreOf 2 L2)
  rw [hD.card_left, hD.card_right, hD.card_inf,
    show 2 ^ (5 * f) * 2 ^ (4 * f) = 2 ^ (6 * f) * 2 ^ (3 * f) by
      rw [← pow_add, ← pow_add]; ring_nf] at h
  exact Nat.le_of_mul_le_mul_right h (by positivity)

theorem U4qLocalData.inf_left_eq_sup_of_ext (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hf : 2 ≤ f) (hS2 : Nat.card S = 2 * 2 ^ (6 * f)) :
    S ⊓ L1 = pCoreOf 2 L1 ⊔ pCoreOf 2 L2 := by
  have hle : pCoreOf 2 L1 ⊔ pCoreOf 2 L2 ≤ S ⊓ L1 :=
    sup_le (le_inf hH.pCoreOf_le_left (pCoreOf_le 2 L1))
      (le_inf hH.pCoreOf_le_right (hD.pCoreOf_right_le_left_of_ext hH hf hS2))
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hD.card_inf_left_of_ext hH]
  exact hD.card_sup_ge_of_ext

theorem U4qLocalData.inf_right_eq_sup_of_ext (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hf : 2 ≤ f) (hS2 : Nat.card S = 2 * 2 ^ (6 * f)) :
    S ⊓ L2 = pCoreOf 2 L1 ⊔ pCoreOf 2 L2 := by
  have hle : pCoreOf 2 L1 ⊔ pCoreOf 2 L2 ≤ S ⊓ L2 :=
    sup_le (le_inf hH.pCoreOf_le_left (hD.pCoreOf_left_le_right_of_ext hH hf hS2))
      (le_inf hH.pCoreOf_le_right (pCoreOf_le 2 L2))
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hD.card_inf_right_of_ext hH]
  exact hD.card_sup_ge_of_ext

private theorem U4qLocalData.inf_inf_right_of_ext (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hf : 2 ≤ f) (hS2 : Nat.card S = 2 * 2 ^ (6 * f)) :
    S ⊓ L1 ⊓ L2 = S ⊓ L2 := by
  rw [hD.inf_left_eq_sup_of_ext hH hf hS2, ← hD.inf_right_eq_sup_of_ext hH hf hS2, inf_assoc,
    inf_idem]

omit [Finite G] in
theorem borelOf_inf_self (L S : Subgroup G) : borelOf L (S ⊓ L) = borelOf L S := by
  rw [borelOf, borelOf, inf_assoc, inf_idem]

theorem U4qLocalData.borelOf_right_inf_of_ext (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hf : 2 ≤ f) (hS2 : Nat.card S = 2 * 2 ^ (6 * f)) :
    borelOf L2 (S ⊓ L1) = borelOf L2 S := by
  rw [borelOf, borelOf, hD.inf_inf_right_of_ext hH hf hS2]

theorem U4qLocalData.hyp111_inf_of_ext (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hf : 2 ≤ f) (hS2 : Nat.card S = 2 * 2 ^ (6 * f)) : Hyp111 L1 L2 (S ⊓ L1) := by
  have e1 := borelOf_inf_self L1 S
  have e2 := hD.borelOf_right_inf_of_ext hH hf hS2
  have hinf := hD.inf_inf_right_of_ext hH hf hS2
  have hSN0 : S ≤ Subgroup.normalizer ((S ⊓ L1 : Subgroup G) : Set G) :=
    le_normalizer_inf_of_le hH.h1.normalizes
  have hp : IsPGroup 2 ↥(S ⊓ L1) := hH.h1.pgroup.to_le inf_le_left
  refine ⟨⟨inferInstance, hp, inf_le_right.trans Subgroup.le_normalizer, ?_, hH.h1.listed, ?_,
    ?_⟩, ⟨inferInstance, hp, inf_le_left.trans hH.h2.normalizes, ?_, hH.h2.listed, ?_, ?_⟩, ?_⟩
  · rw [inf_assoc, inf_idem]
    exact hH.h1.sylow
  · rw [e2]
    exact hH.h1.borel_le
  · rw [e2]
    exact charTwo_sup_of_le_U4qExt hH.h1.charTwo inf_le_left hH.h1.normalizes hSN0
      (le_normalizer_borelOf hH.h2.normalizes)
  · rw [hinf]
    exact hH.h2.sylow
  · rw [e1]
    exact hH.h2.borel_le
  · rw [e1]
    exact charTwo_sup_of_le_U4qExt hH.h2.charTwo inf_le_left hH.h2.normalizes hSN0
      (le_normalizer_borelOf hH.h1.normalizes)
  · have hX : L1 ⊔ L2 ⊔ S ⊓ L1 ≤ L1 ⊔ L2 ⊔ S := sup_le_sup_left inf_le_left _
    have hN : L1 ⊔ L2 ⊔ S ≤ Subgroup.normalizer ((L1 ⊔ L2 ⊔ S ⊓ L1 : Subgroup G) : Set G) := by
      refine sup_le (sup_le ?_ ?_) ?_
      · exact (le_sup_left.trans le_sup_left).trans Subgroup.le_normalizer
      · exact (le_sup_right.trans le_sup_left).trans Subgroup.le_normalizer
      · intro s hs
        exact Subgroup.inf_normalizer_le_normalizer_sup _ _
          ⟨Subgroup.inf_normalizer_le_normalizer_sup _ _
            ⟨hH.h1.normalizes hs, hH.h2.normalizes hs⟩, hSN0 hs⟩
    have h := CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hX hN
    rw [hH.o2] at h
    exact le_bot_iff.mp h

theorem U4qLocalData.inf_left_of_ext (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f) :
    U4qLocalData L1 L2 (S ⊓ L1) f :=
  { hD with card_S := Or.inl (hD.card_inf_left_of_ext hH) }

theorem U4qLocalData.bigB_eq_sup_of_ext (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hf : 2 ≤ f) (hS2 : Nat.card S = 2 * 2 ^ (6 * f)) :
    bigB L1 L2 S = bigB L1 L2 (S ⊓ L1) ⊔ S := by
  rw [bigB, bigB, borelOf_inf_self, hD.borelOf_right_inf_of_ext hH hf hS2,
    sup_assoc (borelOf L1 S ⊔ borelOf L2 S) (S ⊓ L1) S,
    sup_eq_right.mpr (inf_le_left : S ⊓ L1 ≤ S)]

theorem U4qLocalData.sup_bigB_left_of_ext (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hf : 2 ≤ f) (hS2 : Nat.card S = 2 * 2 ^ (6 * f)) :
    L1 ⊔ bigB L1 L2 S = L1 ⊔ bigB L1 L2 (S ⊓ L1) ⊔ S := by
  rw [hD.bigB_eq_sup_of_ext hH hf hS2, sup_assoc]

theorem U4qLocalData.sup_bigB_right_of_ext (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hf : 2 ≤ f) (hS2 : Nat.card S = 2 * 2 ^ (6 * f)) :
    L2 ⊔ bigB L1 L2 S = L2 ⊔ bigB L1 L2 (S ⊓ L1) ⊔ S := by
  rw [hD.bigB_eq_sup_of_ext hH hf hS2, sup_assoc]

omit [Finite G] in
theorem normal_subgroupOf_inf_left_of_hyp111 (hH : Hyp111 L1 L2 S) :
    ((S ⊓ L1).subgroupOf S).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
    (le_normalizer_inf_of_le hH.h1.normalizes)

theorem U4qLocalData.le_normalizer_bigB_inf_of_ext (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hf : 2 ≤ f) (hS2 : Nat.card S = 2 * 2 ^ (6 * f)) :
    S ≤ Subgroup.normalizer ((bigB L1 L2 (S ⊓ L1) : Subgroup G) : Set G) := by
  rw [bigB, borelOf_inf_self, hD.borelOf_right_inf_of_ext hH hf hS2]
  intro s hs
  exact Subgroup.inf_normalizer_le_normalizer_sup _ _
    ⟨Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨le_normalizer_borelOf hH.h1.normalizes hs, le_normalizer_borelOf hH.h2.normalizes hs⟩,
      le_normalizer_inf_of_le hH.h1.normalizes hs⟩

theorem U4qLocalData.le_normalizer_sup_bigB_left_of_ext (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hf : 2 ≤ f) (hS2 : Nat.card S = 2 * 2 ^ (6 * f)) :
    S ≤ Subgroup.normalizer ((L1 ⊔ bigB L1 L2 (S ⊓ L1) : Subgroup G) : Set G) := fun _ hs =>
  Subgroup.inf_normalizer_le_normalizer_sup _ _
    ⟨hH.h1.normalizes hs, hD.le_normalizer_bigB_inf_of_ext hH hf hS2 hs⟩

theorem U4qLocalData.le_normalizer_sup_bigB_right_of_ext (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hf : 2 ≤ f) (hS2 : Nat.card S = 2 * 2 ^ (6 * f)) :
    S ≤ Subgroup.normalizer ((L2 ⊔ bigB L1 L2 (S ⊓ L1) : Subgroup G) : Set G) := fun _ hs =>
  Subgroup.inf_normalizer_le_normalizer_sup _ _
    ⟨hH.h2.normalizes hs, hD.le_normalizer_bigB_inf_of_ext hH hf hS2 hs⟩

structure U4qExtLocalReduction {G : Type} [Group G] (L1 L2 S : Subgroup G) (f : ℕ) : Prop where
  pCoreOf_right_le : pCoreOf 2 L2 ≤ L1
  pCoreOf_left_le : pCoreOf 2 L1 ≤ L2
  inf_left_eq : S ⊓ L1 = pCoreOf 2 L1 ⊔ pCoreOf 2 L2
  inf_right_eq : S ⊓ L2 = pCoreOf 2 L1 ⊔ pCoreOf 2 L2
  card_inf : Nat.card ↥(S ⊓ L1) = 2 ^ (6 * f)
  hyp : Hyp111 L1 L2 (S ⊓ L1)
  data : U4qLocalData L1 L2 (S ⊓ L1) f
  borelOf_left : borelOf L1 (S ⊓ L1) = borelOf L1 S
  borelOf_right : borelOf L2 (S ⊓ L1) = borelOf L2 S
  bigB_eq : bigB L1 L2 S = bigB L1 L2 (S ⊓ L1) ⊔ S
  sup_bigB_left : L1 ⊔ bigB L1 L2 S = L1 ⊔ bigB L1 L2 (S ⊓ L1) ⊔ S
  sup_bigB_right : L2 ⊔ bigB L1 L2 S = L2 ⊔ bigB L1 L2 (S ⊓ L1) ⊔ S
  normal : ((S ⊓ L1).subgroupOf S).Normal
  relIndex_eq : (S ⊓ L1).relIndex S = 2
  le_normalizer_bigB : S ≤ Subgroup.normalizer ((bigB L1 L2 (S ⊓ L1) : Subgroup G) : Set G)
  le_normalizer_sup_left :
    S ≤ Subgroup.normalizer ((L1 ⊔ bigB L1 L2 (S ⊓ L1) : Subgroup G) : Set G)
  le_normalizer_sup_right :
    S ≤ Subgroup.normalizer ((L2 ⊔ bigB L1 L2 (S ⊓ L1) : Subgroup G) : Set G)

theorem U4qLocalData.extension_reduction (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hf : 2 ≤ f) (hS2 : Nat.card S = 2 * 2 ^ (6 * f)) : U4qExtLocalReduction L1 L2 S f where
  pCoreOf_right_le := hD.pCoreOf_right_le_left_of_ext hH hf hS2
  pCoreOf_left_le := hD.pCoreOf_left_le_right_of_ext hH hf hS2
  inf_left_eq := hD.inf_left_eq_sup_of_ext hH hf hS2
  inf_right_eq := hD.inf_right_eq_sup_of_ext hH hf hS2
  card_inf := hD.card_inf_left_of_ext hH
  hyp := hD.hyp111_inf_of_ext hH hf hS2
  data := hD.inf_left_of_ext hH
  borelOf_left := borelOf_inf_self L1 S
  borelOf_right := hD.borelOf_right_inf_of_ext hH hf hS2
  bigB_eq := hD.bigB_eq_sup_of_ext hH hf hS2
  sup_bigB_left := hD.sup_bigB_left_of_ext hH hf hS2
  sup_bigB_right := hD.sup_bigB_right_of_ext hH hf hS2
  normal := normal_subgroupOf_inf_left_of_hyp111 hH
  relIndex_eq := hD.relIndex_inf_left_of_ext hH hS2
  le_normalizer_bigB := hD.le_normalizer_bigB_inf_of_ext hH hf hS2
  le_normalizer_sup_left := hD.le_normalizer_sup_bigB_left_of_ext hH hf hS2
  le_normalizer_sup_right := hD.le_normalizer_sup_bigB_right_of_ext hH hf hS2

end CFSG.Quasithin.F112R.St84

end
