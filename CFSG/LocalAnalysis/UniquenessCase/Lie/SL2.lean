module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.RankOne
public import CFSG.LocalAnalysis.EvenBN.Common.SL2Torus
public import CFSG.Timmesfeld.RankOne.Defs
import CFSG.Timmesfeld.ARS.NaturalModule
import CFSG.RankThree.PartTwo.KFacts.K71Borel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.EvenBN.Common CFSG.SL2MinimalFaithful Subgroup Matrix
open scoped MatrixGroups

section Semilinear

theorem uc22pwr1_semilinear {K : Type} [Field K] [Finite K] (f : K ≃+ K)
    (h : ∀ c : Kˣ, ∃ d : K, ∀ x : K, f ((c : K) * x) = d * f x) :
    ∃ (a : Kˣ) (σ : K ≃+* K), ∀ x : K, f x = a * σ x := by
  have hf0 : f 0 = 0 := map_zero _
  have hf1 : f 1 ≠ 0 := fun h1 => one_ne_zero (f.injective (h1.trans hf0.symm))
  have hmul : ∀ c x : K, (f 1)⁻¹ * f (c * x) = ((f 1)⁻¹ * f c) * ((f 1)⁻¹ * f x) := by
    intro c x
    by_cases hc : c = 0
    · rw [hc, zero_mul, hf0, mul_zero, zero_mul]
    · obtain ⟨d, hd⟩ := h (Units.mk0 c hc)
      have h1 := hd 1
      rw [Units.val_mk0, mul_one] at h1
      rw [Units.val_mk0] at hd
      rw [hd, h1]
      field_simp
  let σr : K →+* K :=
    { toFun := fun x => (f 1)⁻¹ * f x
      map_one' := inv_mul_cancel₀ hf1
      map_mul' := hmul
      map_zero' := by rw [hf0, mul_zero]
      map_add' := fun x y => by rw [map_add, mul_add] }
  refine ⟨Units.mk0 _ hf1, RingEquiv.ofBijective σr
    ⟨σr.injective, Finite.surjective_of_injective σr.injective⟩, fun x => ?_⟩
  change f x = f 1 * ((f 1)⁻¹ * f x)
  rw [mul_inv_cancel_left₀ hf1]

end Semilinear


section Borel

variable {k : Type} [Field k]

theorem uc22pwr1_mem_normalizer_aut {X : Type} [Group X] (φ : MulAut X) {S : Subgroup X}
    (hS : ∀ y, y ∈ S ↔ φ y ∈ S) {x : X} (hx : x ∈ normalizer (S : Set X)) :
    φ x ∈ normalizer (S : Set X) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro y
  obtain ⟨y', rfl⟩ : ∃ y', φ y' = y := ⟨φ⁻¹ y, MulAut.apply_inv_self X φ y⟩
  have e : φ x * φ y' * (φ x)⁻¹ = φ (x * y' * x⁻¹) := by simp [map_mul, map_inv]
  rw [e, ← hS, ← hS]
  exact hx y'

theorem uc22pwr1_unipotent_inj {x y : k} (h : unipotent x = unipotent y) : x = y := by
  simpa [coe_unipotent] using
    congrArg (fun A : SL(2, k) => (A : Matrix (Fin 2) (Fin 2) k) 0 1) h

theorem uc22pwr1_unipotent_conj (c z : k) : unipotent c * unipotent z * (unipotent c)⁻¹ = unipotent z := by
  rw [mul_inv_eq_iff_eq_mul, ← unipotent_add, ← unipotent_add, add_comm]

theorem uc22pwr1_sl2_lowerLeft {g : SL(2, k)} (hg : g ∈ normalizer (upperSL k : Set SL(2, k))) :
    (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := by
  obtain ⟨p, q, r, s, h, rfl⟩ := exists_eq_mkSL g
  obtain ⟨c, hc⟩ := mem_upperSL_iff.1
    ((Subgroup.mem_normalizer_iff.1 hg (unipotent 1)).1 (unipotent_mem_upperSL 1))
  have h1 : ((unipotent c : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 0 =
      ((mkSL p q r s h * unipotent 1 * (mkSL p q r s h)⁻¹ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 0 := by
    rw [hc]
  rw [coe_mkSL_conj_unipotent h 1] at h1
  simp [coe_unipotent] at h1
  simpa [coe_mkSL] using h1

theorem uc22pwr1_sl2_decomp {g : SL(2, k)} (hg : g ∈ normalizer (upperSL k : Set SL(2, k))) :
    ∃ (c : k) (ν : kˣ), g = unipotent c * diagSL ν := by
  have hr := uc22pwr1_sl2_lowerLeft hg
  obtain ⟨p, q, r, s, h, rfl⟩ := exists_eq_mkSL g
  have hr' : r = 0 := by simpa [coe_mkSL] using hr
  subst hr'
  have hps : p * s = 1 := by linear_combination h
  have hp : p ≠ 0 := left_ne_zero_of_mul_eq_one hps
  have hs : s = p⁻¹ := eq_inv_of_mul_eq_one_right hps
  subst hs
  refine ⟨q * p, Units.mk0 p hp, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_mkSL, coe_unipotent, coe_diagSL, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem uc22pwr1_sl2_frob [Finite k] [CharP k 2] (ψ : MulAut SL(2, k))
    (hψ : ∀ x, x ∈ upperSL k ↔ ψ x ∈ upperSL k) :
    ∃ i : ℕ, ∀ s : kˣ, ∃ c : k, ψ (diagSL s) = unipotent c * (diagSL s) ^ 2 ^ i := by
  have hex : ∀ x : k, ∃ y : k, unipotent y = ψ (unipotent x) := fun x =>
    mem_upperSL_iff.1 ((hψ _).1 (unipotent_mem_upperSL x))
  choose ϑ hϑ using hex
  have hϑadd : ∀ x y, ϑ (x + y) = ϑ x + ϑ y := by
    intro x y
    apply uc22pwr1_unipotent_inj
    rw [hϑ, unipotent_add, unipotent_add, map_mul, hϑ, hϑ]
  have hϑ0 : ϑ 0 = 0 := by
    apply uc22pwr1_unipotent_inj
    rw [hϑ, unipotent_zero, map_one]
  have hϑinj : Function.Injective ϑ := by
    intro x y hxy
    apply uc22pwr1_unipotent_inj
    apply ψ.injective
    rw [← hϑ, ← hϑ, hxy]
  let ϑh : k →+ k := { toFun := ϑ, map_zero' := hϑ0, map_add' := hϑadd }
  let ϑe : k ≃+ k := AddEquiv.ofBijective ϑh ⟨hϑinj, Finite.injective_iff_surjective.1 hϑinj⟩
  have hN : ∀ s : kˣ, ψ (diagSL s) ∈ normalizer (upperSL k : Set SL(2, k)) := fun s =>
    uc22pwr1_mem_normalizer_aut ψ hψ (torusSL_le_normalizer_upperSL (diagSL_mem_torusSL s))
  have hrel : ∀ s : kˣ, ∃ (c : k) (ν : kˣ), ψ (diagSL s) = unipotent c * diagSL ν ∧
      ∀ x, ϑ ((s : k) ^ 2 * x) = (ν : k) ^ 2 * ϑ x := by
    intro s
    obtain ⟨c, ν, hcν⟩ := uc22pwr1_sl2_decomp (hN s)
    refine ⟨c, ν, hcν, fun x => ?_⟩
    apply uc22pwr1_unipotent_inj
    rw [hϑ, ← diagSL_conj_unipotent s x, map_mul, map_mul, map_inv, hcν, ← hϑ x]
    have e : unipotent c * diagSL ν * unipotent (ϑ x) * (unipotent c * diagSL ν)⁻¹ =
        unipotent c * (diagSL ν * unipotent (ϑ x) * (diagSL ν)⁻¹) * (unipotent c)⁻¹ := by
      simp only [_root_.mul_inv_rev, mul_assoc]
    rw [e, diagSL_conj_unipotent, uc22pwr1_unipotent_conj]
  have hsemi : ∀ c : kˣ, ∃ d : k, ∀ x, ϑe ((c : k) * x) = d * ϑe x := by
    intro c
    obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq k 2) (c : k)
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact c.ne_zero (by simpa using hr)
    obtain ⟨c', ν, -, hν⟩ := hrel (Units.mk0 r hr0)
    refine ⟨(ν : k) ^ 2, fun x => ?_⟩
    have hc : (c : k) = ((Units.mk0 r hr0 : kˣ) : k) ^ 2 := by rw [Units.val_mk0, sq]; exact hr
    rw [hc]
    exact hν x
  obtain ⟨a, σ, hσ⟩ := uc22pwr1_semilinear ϑe hsemi
  obtain ⟨i, hi⟩ := uc22pwlie_ringEquiv_pow σ
  refine ⟨i, fun s => ?_⟩
  obtain ⟨c, ν, hcν, hν⟩ := hrel s
  have hνσ : (ν : k) = (s : k) ^ 2 ^ i := by
    have h1 := hν 1
    rw [mul_one] at h1
    have h2 : (a : k) * σ ((s : k) ^ 2) = (ν : k) ^ 2 * ((a : k) * σ 1) := by
      rw [← hσ, ← hσ]
      exact h1
    rw [map_one, mul_one, map_pow] at h2
    have h3 : σ (s : k) ^ 2 = (ν : k) ^ 2 := by
      have h4 : (a : k) * σ (s : k) ^ 2 = (a : k) * (ν : k) ^ 2 := by rw [h2, mul_comm]
      exact mul_left_cancel₀ a.ne_zero h4
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h3 with h5 | h5
    · rw [← h5, hi]
    · rw [← CharTwo.neg_eq (ν : k), ← h5, hi]
  refine ⟨c, ?_⟩
  have hνu : ν = s ^ 2 ^ i := Units.ext (by rw [hνσ, Units.val_pow_eq_pow_val])
  rw [hcν, hνu]
  congr 1
  exact (map_pow (diagSLHom (k := k)) s (2 ^ i))

end Borel

section Datum

variable {k : Type} [Field k]

theorem uc22pwr1_upperSL_eq : upperSL k = CFSG.Timmesfeld.upperUnipotent k := by
  ext g
  rw [mem_upperSL_iff, CFSG.Timmesfeld.RankOne.mem_upperUnipotent_iff]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩

theorem uc22pwr1_lowerSL_eq : lowerSL k = CFSG.Timmesfeld.lowerUnipotent k := by
  ext g
  rw [mem_lowerSL_iff, CFSG.Timmesfeld.RankOne.mem_lowerUnipotent_iff]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩

theorem uc22pwr1_datum_sl2 [Finite k] [CharP k 2] {n : ℕ} (hk : Nat.card k = 2 ^ n) :
    UC22pwR1Datum SL(2, k) (upperSL k) n := by
  have hT : Nat.card (torusSL k) = 2 ^ n - 1 := by rw [card_torusSL, hk]
  refine ⟨torusSL k, weylSL k, ?_, ?_, torusSL_le_normalizer_upperSL, fun p _ hp => hT ▸ hp,
    by rw [pow_two]; exact weylSL_mul_self, ?_, ?_, ?_⟩
  · exact isCyclic_of_surjective (diagSLHom (k := k)).rangeRestrict
      (diagSLHom (k := k)).rangeRestrict_surjective
  · rw [hT, ← hk]
    exact odd_card_sub_one
  · rintro _ ⟨μ, rfl⟩ -
    rw [diagSLHom_apply, weylSL_conj_diagSL, diagSL_inv]
  · refine eq_top_iff.2 ?_
    rw [← CFSG.Timmesfeld.ARS.NaturalModule.upperUnipotent_sup_lowerUnipotent (K := k),
      ← uc22pwr1_upperSL_eq, ← uc22pwr1_lowerSL_eq]
    refine sup_le (fun g hg => Subgroup.mem_sup_left (Subgroup.le_normalizer hg)) (fun g hg => ?_)
    obtain ⟨c, rfl⟩ := mem_lowerSL_iff.1 hg
    rw [← weylSL_conj_unipotent c]
    exact mul_mem (mul_mem (Subgroup.mem_sup_right (mem_zpowers _))
      (Subgroup.mem_sup_left (Subgroup.le_normalizer (unipotent_mem_upperSL c))))
      (inv_mem (Subgroup.mem_sup_right (mem_zpowers _)))
  · intro ψ hψ
    obtain ⟨i, hi⟩ := uc22pwr1_sl2_frob ψ hψ
    refine ⟨i, ?_⟩
    rintro _ ⟨s, rfl⟩ -
    obtain ⟨c, hc⟩ := hi s
    exact ⟨unipotent c, unipotent_mem_upperSL c, by rw [diagSLHom_apply, hc]⟩

end Datum

theorem uc22pwr1_concl_of_isL2G {X : Type} [Group X] [Finite X] {n : ℕ} (h : IsL2 X n) (U : Sylow 2 X)
    {P : Type} [Group P] (hP : IsPGroup 2 P) (ψ : P →* MulAut X)
    (hψ : ∀ (g : P) (x : X), x ∈ (U : Subgroup X) ↔ ψ g x ∈ (U : Subgroup X)) {m' : ℕ} (hm' : Odd m')
    {e : ℕ} (hnem : n = 2 ^ e * m') :
    ∃ E : Subgroup X, uc22pwlie_ConclAt uc22pwr1_shape X (U : Subgroup X) P ψ n m' E ∧
      uc22pwlie_Gal (U : Subgroup X) E ψ := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e₁⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  haveI : CharP K 2 := uc22pwlie_charP_two hK
  let e₀ : X ≃* SL(2, K) := e₁.trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
      (CFSG.Timmesfeld.RankOne.psl2EquivSL2 K))
  have hD : UC22pwR1Datum SL(2, K) (CFSG.RankThree.PartTwo.KFacts.sylowUpperUnipotent :
      Sylow 2 SL(2, K)) n := by
    rw [CFSG.RankThree.PartTwo.KFacts.coe_sylowUpperUnipotent, ← uc22pwr1_upperSL_eq]
    exact uc22pwr1_datum_sl2 hK
  exact uc22pwr1_concl_of_datum_sylowG e₀ U _ hD hP ψ hψ hm' hnem

theorem uc22pwr1_concl_of_isL2 {X : Type} [Group X] [Finite X] {n : ℕ} (h : IsL2 X n) (U : Sylow 2 X)
    {P : Type} [Group P] (hP : IsPGroup 2 P) (ψ : P →* MulAut X)
    (hψ : ∀ (g : P) (x : X), x ∈ (U : Subgroup X) ↔ ψ g x ∈ (U : Subgroup X)) {m' : ℕ} (hm' : Odd m')
    {e : ℕ} (hnem : n = 2 ^ e * m') :
    uc22pwlie_Concl uc22pwr1_shape X (U : Subgroup X) P ψ n m' := by
  obtain ⟨E, hE, -⟩ := uc22pwr1_concl_of_isL2G h U hP ψ hψ hm' hnem
  exact ⟨E, hE⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
