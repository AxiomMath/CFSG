module

public import CFSG.RankThree.PartTwo.Sec21.Item228Insp2ProofMat
public import CFSG.RankThree.PartTwo.Sec21.Item228Insp2ProofConj
public import CFSG.RankThree.PartTwo.Sec21.Item22Statements
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDiag
import CFSG.RankThree.PartTwo.Sec21.Item222ProofCases
import CFSG.RankThree.PartTwo.Sec4.LThreePiRank

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item228Insp2Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.RankThree.PartTwo.Sec4 (diagUnits coe_diagUnits diagUnits_mul)
open Matrix

section Field

variable {K : Type} [Field K]

theorem slConjugation_scalar (c : Kˣ) :
    slConjugation 3 K (GeneralLinearGroup.scalar (Fin 3) c) = 1 := by
  ext M : 1
  apply ext_of_coe
  rw [coe_slConjugation, MulAut.one_apply, ← map_inv, GeneralLinearGroup.coe_scalar,
    GeneralLinearGroup.coe_scalar, scalar_apply, scalar_apply]
  ext i j
  rw [mul_diagonal, diagonal_mul, Units.val_inv_eq_inv_val]
  field_simp

theorem eq_scalar_mul_diagUnits {g : GL (Fin 3) K} (hg : (g : Matrix (Fin 3) (Fin 3) K).IsDiag) :
    ∃ c s t : Kˣ, g = GeneralLinearGroup.scalar (Fin 3) c * diagUnits 1 s t := by
  have h0 := CFSG.RankThree.PartTwo.Sec4.Res417Frame.apply_self_ne_zero_of_isDiag hg 0
  have h1 := CFSG.RankThree.PartTwo.Sec4.Res417Frame.apply_self_ne_zero_of_isDiag hg 1
  have h2 := CFSG.RankThree.PartTwo.Sec4.Res417Frame.apply_self_ne_zero_of_isDiag hg 2
  refine ⟨Units.mk0 _ h0, Units.mk0 _ (div_ne_zero h1 h0), Units.mk0 _ (div_ne_zero h2 h0), ?_⟩
  apply Units.ext
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_diagUnits, scalar_apply,
    diagonal_mul_diagonal]
  conv_lhs => rw [← hg.diagonal_diag]
  congr 1
  funext i
  fin_cases i <;> simp [diag_apply] <;> field_simp

theorem diagUnits_pow_three (s t : Kˣ) :
    diagUnits 1 s t ^ 3 = diagUnits 1 (s ^ 3) (t ^ 3) := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_diagUnits, coe_diagUnits, diagonal_pow]
  congr 1
  funext i
  fin_cases i <;> simp

theorem eq_one_of_slConjugation_diagUnits_eq_one {s t : Kˣ}
    (h : slConjugation 3 K (diagUnits 1 s t) = 1) : s = 1 ∧ t = 1 := by
  obtain ⟨r, hr⟩ := mem_range_scalar_of_slConjugation_eq_one h
  rw [coe_diagUnits, scalar_apply] at hr
  have h0 := congrFun (congrFun hr 0) 0
  have h1 := congrFun (congrFun hr 1) 1
  have h2 := congrFun (congrFun hr 2) 2
  simp only [diagonal_apply_eq] at h0 h1 h2
  change r = (1 : K) at h0
  change r = (s : K) at h1
  change r = (t : K) at h2
  exact ⟨Units.ext (by rw [← h1, h0, Units.val_one]), Units.ext (by rw [← h2, h0, Units.val_one])⟩

end Field

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]

theorem exists_primitiveRoot_three {m : ℕ} (hm0 : 0 < m) (hme : Even m) :
    ∃ ω : GaloisField 2 m, IsPrimitiveRoot ω 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card (GaloisField 2 m)ˣ := by
    rw [Nat.card_units, GaloisField.card 2 m hm0.ne']
    have h := Nat.pow_sub_one_dvd_pow_sub_one (x := 2) (even_iff_two_dvd.mp hme)
    simpa using h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  refine ⟨(z : GaloisField 2 m), ?_⟩
  have h := IsPrimitiveRoot.orderOf z
  rw [hz] at h
  exact IsPrimitiveRoot.coe_units_iff.mpr h

theorem exists_iso_tZero {X A : Subgroup G} (ι₀ : X ≃* Matrix.SpecialLinearGroup (Fin 3) K)
    (h3 : ((3 : ℕ) : K) ≠ 0) {ω : K} (hω : IsPrimitiveRoot ω 3)
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (hAX9 : Nat.card (A ⊓ X : Subgroup G) = 3 ^ 2) :
    ∃ ι : X ≃* Matrix.SpecialLinearGroup (Fin 3) K,
      (∀ y ∈ tZero K, ((ι.symm y : X) : G) ∈ A) ∧ ∀ x : X, (x : G) ∈ A → ι x ∈ tZero K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E : Subgroup X := A.subgroupOf X with hE
  have hEcard : Nat.card E = 9 := by
    rw [hE, ← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ X ≤ X)).toEquiv, hAX9]
    norm_num
  have hexp : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    exact Subtype.ext (by rw [Subgroup.coe_pow]; exact hAe.2 _ (Subgroup.mem_subgroupOf.mp hx))
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    have h := hAe.1.is_comm.comm ⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩
      ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩
    have h' : (x : G) * y = y * x := congrArg Subtype.val h
    exact Subtype.ext h'
  obtain ⟨x₁, hx₁E, hx₁1, x₂, hx₂E, hx₂n⟩ :=
    Sec4.exists_independent_of_three_lt_card E hexp (by rw [hEcard]; norm_num)
  have hcl : Subgroup.closure {x₁, x₂} = E := by
    have hle : Subgroup.closure {x₁, x₂} ≤ E := by
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      exacts [hx₁E, hx₂E]
    apply Subgroup.eq_of_le_of_card_ge hle
    have hlt : Subgroup.zpowers x₁ < Subgroup.closure {x₁, x₂} := by
      refine lt_of_le_of_ne
        (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert _ _))) fun h => ?_
      apply hx₂n
      rw [h]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    have h3' : Nat.card (Subgroup.zpowers x₁) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (hexp x₁ hx₁E) hx₁1
    have hlt' := Subgroup.card_lt_of_lt hlt
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hEcard, show (9 : ℕ) = 3 ^ 2 by norm_num] at hdvd
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    rw [hEcard, hk']
    rw [h3', hk'] at hlt'
    interval_cases k
    · norm_num at hlt'
    · norm_num at hlt'
    · norm_num
  have hM : ∀ x ∈ E,
      ((ι₀ x : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    intro x hx
    rw [← Matrix.SpecialLinearGroup.coe_pow, ← map_pow, hexp x hx, map_one,
      Matrix.SpecialLinearGroup.coe_one]
  have hMc : Commute ((ι₀ x₁ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      ((ι₀ x₂ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    show _ * _ = _ * _
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, ← map_mul,
      ← map_mul, hcomm x₁ hx₁E x₂ hx₂E]
  obtain ⟨Q, hQ, α, β, hα, hβ⟩ :=
    Sec15.KSL3Two.exists_conj_diag (p := 3) h3 hω (hM x₁ hx₁E) (hM x₂ hx₂E) hMc
  set Qu : GL (Fin 3) K := hQ.unit with hQu
  have hQQ : ((Qu⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Q = 1 := by
    rw [hQu]
    exact hQ.val_inv_mul
  set ι : X ≃* Matrix.SpecialLinearGroup (Fin 3) K := ι₀.trans (slConjugation 3 K Qu⁻¹) with hι
  have hιc : ∀ x : X, ((ι x : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((Qu⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((ι₀ x : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Q := by
    intro x
    rw [hι, MulEquiv.trans_apply, coe_slConjugation, inv_inv, hQu, IsUnit.unit_spec]
  have hdiagE : ∀ x ∈ E, ι x ∈ diagSL K := by
    have hS : Subgroup.closure {x₁, x₂} ≤ (diagSL K).comap ι.toMonoidHom := by
      rw [Subgroup.closure_le]
      intro y hy
      rcases hy with hy | hy
      · rw [hy]
        show (ι x₁ : Matrix (Fin 3) (Fin 3) K).IsDiag
        rw [hιc, Matrix.mul_assoc, hα, ← Matrix.mul_assoc, hQQ, Matrix.one_mul]
        exact isDiag_diagonal _
      · rw [Set.mem_singleton_iff.mp hy]
        show (ι x₂ : Matrix (Fin 3) (Fin 3) K).IsDiag
        rw [hιc, Matrix.mul_assoc, hβ, ← Matrix.mul_assoc, hQQ, Matrix.one_mul]
        exact isDiag_diagonal _
    intro x hx
    rw [← hcl] at hx
    exact hS hx
  have hT : ∀ x : X, (x : G) ∈ A → ι x ∈ tZero K := by
    intro x hx
    have hxE : x ∈ E := Subgroup.mem_subgroupOf.mpr hx
    exact ⟨hdiagE x hxE, by rw [← map_pow, hexp x hxE, map_one]⟩
  have hET : E.map ι.toMonoidHom = tZero K := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact hT x (Subgroup.mem_subgroupOf.mp hx)
    · rw [Subgroup.card_map_of_injective ι.injective, hEcard]
      exact card_tZero_le
  refine ⟨ι, fun y hy => ?_, hT⟩
  rw [← hET] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  exact Subgroup.mem_subgroupOf.mp hx

theorem exists_diagUnits_of_tZero {X A : Subgroup G} (ι : X ≃* Matrix.SpecialLinearGroup (Fin 3) K)
    (hθ : LocalRank.aschbacherSolvableCore 3 X = ⊥) {ω : K} (hω : IsPrimitiveRoot ω 3)
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hTA : ∀ y ∈ tZero K, ((ι.symm y : X) : G) ∈ A)
    (hnf : ∀ a ∈ A, ¬ KFacts.InducesKindSL 3 K X a .field) {a : G} (ha : a ∈ A) :
    ∃ s t : Kˣ, s ^ 3 = 1 ∧ t ^ 3 = 1 ∧
      actSL ι ⟨a, hAX ha⟩ = slConjugation 3 K (diagUnits 1 s t) := by
  have ha3 : a ^ 3 = 1 := hAe.2 a ha
  obtain ⟨g, hg⟩ := exists_actSL_eq_slConjugation ι hθ (hAX ha) ha3 (hnf a ha)
  set z₀ : X := ι.symm (regSL hω) with hz₀
  have hz₀A : (z₀ : G) ∈ A := hTA _ (regSL_mem_tZero hω)
  have hfix : actSL ι ⟨a, hAX ha⟩ (ι z₀) = ι z₀ := by
    apply actSL_apply_eq
    have h := hAe.1.is_comm.comm ⟨a, ha⟩ ⟨(z₀ : G), hz₀A⟩
    have h' : a * (z₀ : G) = (z₀ : G) * a := congrArg Subtype.val h
    change (z₀ : G) = a * z₀ * a⁻¹
    rw [h', mul_inv_cancel_right]
  rw [hg, hz₀, MulEquiv.apply_symm_apply] at hfix
  have hgd : ((g : Matrix (Fin 3) (Fin 3) K)).IsDiag := by
    apply isDiag_of_commute_regSL hω
    have h1 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 3) K =>
      (M : Matrix (Fin 3) (Fin 3) K)) hfix
    simp only [coe_slConjugation, coe_regSL] at h1
    have hgg : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (g : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (g : Matrix (Fin 3) (Fin 3) K) * diagonal ![1, ω, ω ^ 2] =
        (g : Matrix (Fin 3) (Fin 3) K) * diagonal ![1, ω, ω ^ 2] *
          ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) := by
          rw [Matrix.mul_assoc _ _ (g : Matrix (Fin 3) (Fin 3) K), hgg, Matrix.mul_one]
      _ = diagonal ![1, ω, ω ^ 2] * (g : Matrix (Fin 3) (Fin 3) K) := by rw [h1]
  obtain ⟨c, s, t, hgst⟩ := eq_scalar_mul_diagUnits hgd
  have hD : actSL ι ⟨a, hAX ha⟩ = slConjugation 3 K (diagUnits 1 s t) := by
    rw [hg, hgst, map_mul, slConjugation_scalar, one_mul]
  have hD3 : slConjugation 3 K (diagUnits 1 (s ^ 3) (t ^ 3)) = 1 := by
    rw [← diagUnits_pow_three, map_pow, ← hD, ← map_pow]
    have : (⟨a, hAX ha⟩ : Subgroup.normalizer (X : Set G)) ^ 3 = 1 :=
      Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact ha3)
    rw [this, map_one]
  obtain ⟨hs, ht⟩ := eq_one_of_slConjugation_diagUnits_eq_one hD3
  exact ⟨s, t, hs, ht, hD⟩

theorem exists_normalForm {X A : Subgroup G} {m : ℕ} (hm0 : 0 < m) (hme : Even m)
    (eX : X ≃* SL3 m) (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hAX9 : Nat.card (A ⊓ X : Subgroup G) = 3 ^ 2)
    (hnf : ∀ a ∈ A, ¬ KFacts.InducesKindSL 3 (GaloisField 2 m) X a .field)
    {ω : GaloisField 2 m} (hω : IsPrimitiveRoot ω 3) :
    ∃ ι : X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 m),
      (∀ y ∈ tZero (GaloisField 2 m), ((ι.symm y : X) : G) ∈ A) ∧
      (∀ x : X, (x : G) ∈ A → ι x ∈ tZero (GaloisField 2 m)) ∧
      ∀ a (ha : a ∈ A), ∃ s t : (GaloisField 2 m)ˣ, s ^ 3 = 1 ∧ t ^ 3 = 1 ∧
        actSL ι ⟨a, hAX ha⟩ = slConjugation 3 (GaloisField 2 m) (diagUnits 1 s t) := by
  have hθ : aschbacherSolvableCore 3 X = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp
      (Item222Proof.inSubgroup_theta_eq_bot_of_mulEquiv_SL3 hm0 hme eX)
  have h2 : (2 : GaloisField 2 m) = 0 := CharTwo.two_eq_zero
  have h3 : ((3 : ℕ) : GaloisField 2 m) ≠ 0 := by
    intro h
    have h' : (3 : GaloisField 2 m) = 0 := by exact_mod_cast h
    have : (1 : GaloisField 2 m) = 0 := by linear_combination h' - h2
    exact one_ne_zero this
  obtain ⟨ι, hTA, hT⟩ := exists_iso_tZero eX h3 hω hAe hAX9
  exact ⟨ι, hTA, hT, fun a ha => exists_diagUnits_of_tZero ι hθ hω hAe hAX hTA hnf ha⟩

end CFSG.RankThree.PartTwo.Sec21.Item228Insp2Proof
