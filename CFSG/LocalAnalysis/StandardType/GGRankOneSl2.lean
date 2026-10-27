module

public import CFSG.LieType.Steinberg.PartB
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSUExc
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneCard
public import Mathlib.GroupTheory.Sylow
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.RankOneXfer

open CFSG.LieType.Steinberg CFSG.StandardType.PsiDiagChar

section Basic

variable {k : Type*} [Field k]

private lemma sl2Upper_mul_aux (a b : k) : sl2Upper a * sl2Upper b = sl2Upper (a + b) := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, Matrix.mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp
  ring

@[expose] def sl2UpperUniSub (F : Type*) [Field F] :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) where
  carrier := Set.range (sl2Upper : F → Matrix.SpecialLinearGroup (Fin 2) F)
  one_mem' := by
    rw [Set.mem_range]
    exact ⟨0, by
      ext i j
      simp only [coe_sl2Upper, Matrix.SpecialLinearGroup.coe_one]
      fin_cases i <;> fin_cases j <;> simp⟩
  mul_mem' := by
    intro a b ha hb
    rw [Set.mem_range] at ha hb ⊢
    obtain ⟨u, rfl⟩ := ha
    obtain ⟨v, rfl⟩ := hb
    exact ⟨u + v, by
      ext i j
      simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, Matrix.mul_fin_two]
      fin_cases i <;> fin_cases j <;> simp
      ring⟩
  inv_mem' := by
    intro x hx
    rw [Set.mem_range] at hx ⊢
    obtain ⟨a, rfl⟩ := hx
    exact ⟨-a, by
      ext i j
      rw [Matrix.SpecialLinearGroup.coe_inv, coe_sl2Upper, Matrix.adjugate_fin_two, coe_sl2Upper]
      fin_cases i <;> fin_cases j <;> simp⟩

theorem mem_sl2UpperUniSub_iff {M : Matrix.SpecialLinearGroup (Fin 2) k} :
    M ∈ sl2UpperUniSub k ↔ ∃ c : k, sl2Upper c = M :=
  Iff.rfl

theorem sl2Upper_mul_sl2Upper (a b : k) : sl2Upper a * sl2Upper b = sl2Upper (a + b) :=
  sl2Upper_mul_aux a b

theorem sl2Diag_conj_sl2Upper (a : kˣ) (c : k) :
    sl2Diag a * sl2Upper c * (sl2Diag a)⁻¹ = sl2Upper ((a : k) ^ 2 * c) := by
  rw [sl2Diag_mul_upper, mul_assoc, mul_inv_cancel, mul_one]

theorem exists_sq_conj_of_conj_upper {τ : Matrix.SpecialLinearGroup (Fin 2) k}
    (h : ∀ c : k, ∃ c' : k, τ * sl2Upper c * τ⁻¹ = sl2Upper c') :
    ∃ a : kˣ, ∀ c : k, τ * sl2Upper c * τ⁻¹ = sl2Upper ((a : k) ^ 2 * c) := by
  have hinv : (τ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) k).val =
      !![τ.val 1 1, -τ.val 0 1; -τ.val 1 0, τ.val 0 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have hentry : (τ * sl2Upper (1 : k) * τ⁻¹).val 1 0 = -(τ 1 0) ^ 2 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hinv,
      coe_sl2Upper]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  obtain ⟨c', hc'⟩ := h 1
  have hzero : (τ * sl2Upper (1 : k) * τ⁻¹).val 1 0 = 0 := by
    rw [hc']
    simp [coe_sl2Upper]
  rw [hentry] at hzero
  have h10 : τ 1 0 = 0 := sq_eq_zero_iff.mp (neg_eq_zero.mp hzero)
  obtain ⟨a, b, ha, hτ⟩ :=
    Matrix.SpecialLinearGroup.fin_two_exists_eq_mk_of_apply_zero_one_eq_zero τ h10
  refine ⟨Units.mk0 a ha, ?_⟩
  intro c
  have hA : τ = sl2Diag (Units.mk0 a ha) * sl2Upper (a⁻¹ * b) := by
    rw [hτ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_sl2Diag, coe_sl2Upper, Units.val_mk0, Matrix.mul_fin_two]
    all_goals field_simp
  rw [hA, Units.val_mk0 ha]
  have hcomm : sl2Upper (a⁻¹ * b) * sl2Upper c = sl2Upper c * sl2Upper (a⁻¹ * b) := by
    rw [sl2Upper_mul_sl2Upper, sl2Upper_mul_sl2Upper, add_comm]
  have hfix : sl2Upper (a⁻¹ * b) * sl2Upper c * (sl2Upper (a⁻¹ * b))⁻¹ = sl2Upper c := by
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hconj : sl2Diag (Units.mk0 a ha) * sl2Upper c * (sl2Diag (Units.mk0 a ha))⁻¹ =
      sl2Upper (a ^ 2 * c) := by
    rw [sl2Diag_conj_sl2Upper, Units.val_mk0 ha]
  rw [mul_inv_rev]
  calc sl2Diag (Units.mk0 a ha) * sl2Upper (a⁻¹ * b) * sl2Upper c *
        ((sl2Upper (a⁻¹ * b))⁻¹ * (sl2Diag (Units.mk0 a ha))⁻¹)
      = sl2Diag (Units.mk0 a ha) * (sl2Upper (a⁻¹ * b) * sl2Upper c *
          (sl2Upper (a⁻¹ * b))⁻¹) * (sl2Diag (Units.mk0 a ha))⁻¹ := by group
    _ = sl2Diag (Units.mk0 a ha) * sl2Upper c * (sl2Diag (Units.mk0 a ha))⁻¹ := by rw [hfix]
    _ = sl2Upper (a ^ 2 * c) := hconj

theorem sl2_weyl_mul_inv (t : kˣ) :
    sl2Upper (t : k) * sl2Lower (-((t⁻¹ : kˣ) : k)) * sl2Upper (t : k) *
        (sl2Upper (1 : k) * sl2Lower (-(1 : k)) * sl2Upper (1 : k))⁻¹ = sl2Diag t := by
  have hW : sl2Upper (t : k) * sl2Lower (-((t⁻¹ : kˣ) : k)) * sl2Upper (t : k) =
      sl2Diag t * (sl2Upper (1 : k) * sl2Lower (-(1 : k)) * sl2Upper (1 : k)) := by
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Lower, coe_sl2Diag,
      Matrix.mul_fin_two]
    fin_cases i <;> fin_cases j <;> simp <;> field_simp
  rw [hW, mul_assoc, mul_inv_cancel, mul_one]

theorem closure_sl2Upper_sl2Lower_eq_top :
    Subgroup.closure (Set.range (sl2Upper : k → Matrix.SpecialLinearGroup (Fin 2) k) ∪
      Set.range (sl2Lower : k → Matrix.SpecialLinearGroup (Fin 2) k)) = ⊤ := by
  rw [eq_top_iff]
  rw [← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    (ι := Fin 2) (K := k)]
  apply Subgroup.closure_mono
  rintro _ ⟨t, rfl⟩
  obtain ⟨i, j, hij, c⟩ := t
  rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact Or.inl ⟨c, by
      ext p q
      fin_cases p <;> fin_cases q <;>
        simp [Matrix.SpecialLinearGroup.transvection_coe, coe_sl2Upper, Matrix.single_apply]⟩
  · exact Or.inr ⟨c, by
      ext p q
      fin_cases p <;> fin_cases q <;>
        simp [Matrix.SpecialLinearGroup.transvection_coe, coe_sl2Lower, Matrix.single_apply]⟩
  · exact absurd rfl hij

end Basic

section Sylow

variable {k k' : Type*} [Field k] [Finite k] [CharP k 2] [Field k'] [Finite k'] [CharP k' 2]

private lemma ggCard_eq_two_pow (F : Type*) [Field F] [Finite F] [CharP F 2] :
    ∃ n : ℕ, 1 ≤ n ∧ Nat.card F = 2 ^ n := by
  haveI := Fintype.ofFinite F
  obtain ⟨n, -, hq⟩ := FiniteField.card F 2
  exact ⟨(n : ℕ), n.2, by rw [Nat.card_eq_fintype_card, hq]⟩

private lemma ggCard_two_pow_factorization (F : Type*) [Field F] [Finite F] [CharP F 2] :
    Nat.card F = 2 ^ (Nat.card F).factorization 2 := by
  obtain ⟨n, -, hcard⟩ := ggCard_eq_two_pow F
  rw [hcard, Nat.factorization_pow_self Nat.prime_two]

private lemma ggNotTwoDvd_pow_two_sq_sub_one (n : ℕ) (hn : 1 ≤ n) :
    ¬2 ∣ (2 ^ n) ^ 2 - 1 := by
  intro h
  have h1 : 2 ∣ (2 ^ n) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
  have hle : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have h2 : (2 ^ n) ^ 2 - ((2 ^ n) ^ 2 - 1) = 1 := by omega
  have hd := Nat.dvd_sub h1 h
  rw [h2] at hd
  exact (by norm_num : ¬2 ∣ 1) hd

private lemma ggNotTwoDvd_card_sq_sub_one (F : Type*) [Field F] [Finite F] [CharP F 2] :
    ¬2 ∣ Nat.card F ^ 2 - 1 := by
  obtain ⟨n, hn, hcard⟩ := ggCard_eq_two_pow F
  rw [hcard]
  exact ggNotTwoDvd_pow_two_sq_sub_one n hn

private lemma ggSL2_card_univ (F : Type*) [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  haveI := Fintype.ofFinite F
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  rw [Matrix.card_SL_field (n := 2) (𝔽 := F), Fin.prod_univ_two, Nat.card_eq_fintype_card]
  norm_num
  have hqpos : 0 < Fintype.card F - 1 := by omega
  have hsub : Fintype.card F ^ 2 - Fintype.card F =
      Fintype.card F * (Fintype.card F - 1) := by
    rw [pow_two, Nat.mul_sub_left_distrib, Nat.mul_one]
  rw [hsub, ← mul_assoc, Nat.mul_div_cancel _ hqpos, mul_comm]

theorem card_sl2UpperUniSub (F : Type*) [Field F] :
    Nat.card (sl2UpperUniSub F) = Nat.card F := by
  have hinj : Function.Injective (sl2Upper : F → Matrix.SpecialLinearGroup (Fin 2) F) := by
    intro a b h
    have h' := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F => A.val 0 1) h
    simpa [CFSG.LieType.Steinberg.coe_sl2Upper] using h'
  have e : F ≃ sl2UpperUniSub F :=
    Equiv.ofInjective (sl2Upper : F → Matrix.SpecialLinearGroup (Fin 2) F) hinj
  exact (Nat.card_congr e).symm

theorem exists_conj_sl2UpperUniSub_map_eq {S : Type*} [Group S]
    (Φ : Matrix.SpecialLinearGroup (Fin 2) k →* S)
    (Φ' : Matrix.SpecialLinearGroup (Fin 2) k' →* S)
    (hΦ : Function.Injective Φ) (hΦ' : Function.Injective Φ') (hr : Φ.range = Φ'.range) :
    ∃ σ : Matrix.SpecialLinearGroup (Fin 2) k,
      (sl2UpperUniSub k).map (Φ.comp (MulAut.conj σ).toMonoidHom) =
        (sl2UpperUniSub k').map Φ' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let R := Φ.range
  let Φ'R : Matrix.SpecialLinearGroup (Fin 2) k' →* R :=
    Φ'.codRestrict R fun x => by
      rw [show R = Φ.range from rfl, hr]
      exact ⟨x, rfl⟩
  let Y : Subgroup R := (sl2UpperUniSub k).map Φ.rangeRestrict
  let Z : Subgroup R := (sl2UpperUniSub k').map Φ'R
  haveI : Finite R := Finite.of_surjective Φ.rangeRestrict Φ.rangeRestrict_surjective
  have hΦ'R : Function.Injective Φ'R := by
    intro x y h
    apply hΦ'
    have h' := congrArg (fun z : R => (z : S)) h
    simpa [Φ'R] using h'
  have hYcard_k : Nat.card Y = Nat.card k := by
    change Nat.card ((sl2UpperUniSub k).map Φ.rangeRestrict) = Nat.card k
    rw [Subgroup.card_map_of_injective (MonoidHom.rangeRestrict_injective_iff.mpr hΦ),
      card_sl2UpperUniSub k]
  have hZcard_k : Nat.card Z = Nat.card k' := by
    change Nat.card ((sl2UpperUniSub k').map Φ'R) = Nat.card k'
    rw [Subgroup.card_map_of_injective hΦ'R, card_sl2UpperUniSub k']
  have hRcard : Nat.card R = Nat.card k * (Nat.card k ^ 2 - 1) := by
    have h1 : Nat.card R = Nat.card (Matrix.SpecialLinearGroup (Fin 2) k) :=
      (Nat.card_congr (MonoidHom.ofInjective hΦ).toEquiv).symm
    rw [h1, ggSL2_card_univ k]
  have hRfac : (Nat.card R).factorization 2 = (Nat.card k).factorization 2 := by
    rw [hRcard]
    have hodd : ¬2 ∣ Nat.card k ^ 2 - 1 := ggNotTwoDvd_card_sq_sub_one k
    rw [Nat.factorization_mul (Nat.card_pos.ne') (by intro h0; rw [h0] at hodd; exact hodd (dvd_zero 2)),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hodd, add_zero]
  have hRcard' : Nat.card R = Nat.card k' * (Nat.card k' ^ 2 - 1) := by
    have h1 : Nat.card R = Nat.card (Matrix.SpecialLinearGroup (Fin 2) k') := by
      have h2 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) k') = Nat.card Φ'.range :=
        Nat.card_congr (MonoidHom.ofInjective hΦ').toEquiv
      rw [h2, ← hr]
    rw [h1, ggSL2_card_univ k']
  have hRfac' : (Nat.card R).factorization 2 = (Nat.card k').factorization 2 := by
    rw [hRcard']
    have hodd : ¬2 ∣ Nat.card k' ^ 2 - 1 := ggNotTwoDvd_card_sq_sub_one k'
    rw [Nat.factorization_mul (Nat.card_pos.ne') (by intro h0; rw [h0] at hodd; exact hodd (dvd_zero 2)),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hodd, add_zero]
  have hYcard : Nat.card Y = 2 ^ (Nat.card R).factorization 2 := by
    rw [hYcard_k, hRfac]
    exact ggCard_two_pow_factorization k
  have hZcard : Nat.card Z = 2 ^ (Nat.card R).factorization 2 := by
    rw [hZcard_k, hRfac']
    exact ggCard_two_pow_factorization k'
  haveI : Finite (Sylow 2 R) :=
    Sylow.finite_of_finiteIndex (Sylow.ofCard Y hYcard)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq R (Sylow.ofCard Y hYcard) (Sylow.ofCard Z hZcard)
  have hconj : Z = Y.map (MulAut.conj g).toMonoidHom := by
    change (Sylow.ofCard Z hZcard : Subgroup R) =
      (Sylow.ofCard Y hYcard : Subgroup R).map (MulAut.conj g).toMonoidHom
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.mp g.2
  refine ⟨σ, ?_⟩
  have hcomp : (R.subtype.comp (MulAut.conj g).toMonoidHom).comp Φ.rangeRestrict =
      Φ.comp (MulAut.conj σ).toMonoidHom := by
    ext y
    show R.subtype ((MulAut.conj g) (Φ.rangeRestrict y)) = Φ ((MulAut.conj σ) y)
    rw [MulAut.conj_apply, MulAut.conj_apply]
    show (↑(g * Φ.rangeRestrict y * g⁻¹) : S) = Φ (σ * y * σ⁻¹)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.coe_rangeRestrict, ← hσ,
      map_mul, map_inv]
  have hZmap : Z.map R.subtype = (sl2UpperUniSub k').map Φ' := by
    change ((sl2UpperUniSub k').map Φ'R).map R.subtype = (sl2UpperUniSub k').map Φ'
    rw [Subgroup.map_map, show R.subtype.comp Φ'R = Φ' from by ext x; rfl]
  have hfinal : Z.map R.subtype =
      (sl2UpperUniSub k).map (Φ.comp (MulAut.conj σ).toMonoidHom) := by
    rw [hconj, Subgroup.map_map]
    rw [show Y = (sl2UpperUniSub k).map Φ.rangeRestrict from rfl, Subgroup.map_map, hcomp]
  exact hfinal.symm.trans hZmap

end Sylow

end CFSG.StandardType.RankOneXfer
