module

public import CFSG.RankThree.PartTwo.Sec4.Statements
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL3Aut
import CFSG.Quasithin.Background.RonanE628RCount
import CFSG.RankThree.PartTwo.Sec14.Item1413Res7ProofHess
import CFSG.RankThree.PartTwo.Sec4.Item419ThetaProofTools
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs
import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3AutLin
import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3AutUni

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck159

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec14

private theorem hessMulConj {M : Type*} [Group M] (F : MulAut M) (x : M) :
    F * MulAut.conj x = MulAut.conj (F x) * F := by
  ext y
  simp [MulAut.conj_apply]

private theorem hessConjCommute {M : Type*} [Group M] {e e' : M} (hee : e * e' = e' * e)
    {F F' : MulAut M} (hF : F e' = e') (hF' : F' e = e) (hFF : F * F' = F' * F) :
    (MulAut.conj e * F) * (MulAut.conj e' * F') = (MulAut.conj e' * F') * (MulAut.conj e * F) := by
  have h1 : (MulAut.conj e * F) * (MulAut.conj e' * F') = MulAut.conj (e * e') * (F * F') := by
    calc (MulAut.conj e * F) * (MulAut.conj e' * F')
        = MulAut.conj e * (F * MulAut.conj e') * F' := by simp only [mul_assoc]
      _ = MulAut.conj e * (MulAut.conj e' * F) * F' := by rw [hessMulConj, hF]
      _ = MulAut.conj (e * e') * (F * F') := by rw [map_mul]; simp only [mul_assoc]
  have h2 : (MulAut.conj e' * F') * (MulAut.conj e * F) = MulAut.conj (e' * e) * (F' * F) := by
    calc (MulAut.conj e' * F') * (MulAut.conj e * F)
        = MulAut.conj e' * (F' * MulAut.conj e) * F := by simp only [mul_assoc]
      _ = MulAut.conj e' * (MulAut.conj e * F') * F := by rw [hessMulConj, hF']
      _ = MulAut.conj (e' * e) * (F' * F) := by rw [map_mul]; simp only [mul_assoc]
  rw [h1, h2, hee, hFF]

private theorem hessCommuteOfDecomp {M : Type*} [Group M] {d c : M} (hdc : d * c = c * d)
    {S : Set (MulAut M)} (hS : ∀ F ∈ S, ∀ F' ∈ S, F * F' = F' * F)
    (hSd : ∀ F ∈ S, F d = d) (hSc : ∀ F ∈ S, F c = c) {β γ : MulAut M}
    (hβ : ∃ (k j : ℕ), ∃ F ∈ S, β = MulAut.conj (d ^ k * c ^ j) * F)
    (hγ : ∃ (k j : ℕ), ∃ F ∈ S, γ = MulAut.conj (d ^ k * c ^ j) * F) : β * γ = γ * β := by
  obtain ⟨k, j, F, hF, rfl⟩ := hβ
  obtain ⟨k', j', F', hF', rfl⟩ := hγ
  have hfix : ∀ F : MulAut M, F ∈ S → ∀ k j : ℕ, F (d ^ k * c ^ j) = d ^ k * c ^ j := by
    intro F hF k j
    rw [map_mul, map_pow, map_pow, hSd F hF, hSc F hF]
  have hcomm : (d ^ k * c ^ j) * (d ^ k' * c ^ j') = (d ^ k' * c ^ j') * (d ^ k * c ^ j) := by
    have hd : Commute d c := hdc
    exact ((((Commute.refl d).pow_pow k k').mul_right (hd.pow_pow k j')).mul_left
      (((hd.symm).pow_pow j k').mul_right ((Commute.refl c).pow_pow j j'))).eq
  exact hessConjCommute hcomm (hfix F hF k' j') (hfix F' hF' k j) (hS F hF F' hF')

section Field

variable {K : Type} [Field K] {τ : K}

private theorem hessSqAddAddOne (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) : τ ^ 2 + τ + 1 = 0 := by
  have h : (τ - 1) * (τ ^ 2 + τ + 1) = 0 := by linear_combination hτ
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hτ1)

private theorem hessApplyEqOrSq (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (σ : K ≃+* K) :
    σ τ = τ ∨ σ τ = τ ^ 2 := by
  have h0 := hessSqAddAddOne hτ hτ1
  have ha : (σ τ) ^ 2 + σ τ + 1 = 0 := by
    have := congrArg σ h0
    simpa [map_add, map_pow] using this
  have h : (σ τ - τ) * (σ τ - τ ^ 2) = 0 := by linear_combination ha - σ τ * h0 + hτ
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

private theorem hessApplyEqOfOdd (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (σ : K ≃+* K)
    (hσ : Odd (orderOf σ)) : σ τ = τ := by
  rcases hessApplyEqOrSq hτ hτ1 σ with h | h
  · exact h
  · have h2 : (σ ^ 2) τ = τ := by
      rw [sq, RingAut.mul_apply, h, map_pow, h, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num,
        pow_add, hτ, one_mul, pow_one]
    have h2k : ∀ k : ℕ, (σ ^ (2 * k)) τ = τ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, RingAut.mul_apply, h2, ih]
    obtain ⟨k, hk⟩ := hσ
    have h1 : σ ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one σ
    have := congrArg (fun f : K ≃+* K => f τ) h1
    simp only [pow_succ', RingAut.mul_apply, h2k, RingAut.one_apply] at this
    exact this

end Field

section Linear

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartTwo.Sec17.Proof17Res7

variable {K : Type} [Field K] {τ : K}

private theorem hessFieldAutD (hτ : τ ^ 3 = 1) {σ : K ≃+* K} (hσ : σ τ = τ) :
    fieldAut 3 K σ (proj 3 K (dSL hτ)) = proj 3 K (dSL hτ) := by
  rw [fieldAut_proj]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dSL, coe_diagTau, hσ]

private theorem hessFieldAutC (σ : K ≃+* K) :
    fieldAut 3 K σ (proj 3 K cSL) = proj 3 K cSL := by
  rw [fieldAut_proj]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cSL, coe_cycThree]

private theorem hessDecompLinear [Finite K] (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {β : MulAut (projectiveSL 3 K)} {n : ℕ} (hn : Odd n) (hβ : β ^ n = 1)
    (hd : β (proj 3 K (dSL hτ)) = proj 3 K (dSL hτ)) (hc : β (proj 3 K cSL) = proj 3 K cSL) :
    ∃ (m j : ℕ) (σ : K ≃+* K), σ τ = τ ∧
      β = MulAut.conj (proj 3 K (dSL hτ) ^ m * proj 3 K cSL ^ j) * fieldAut 3 K σ := by
  obtain ⟨A, σ, hAσ, hodd⟩ := CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.kaL3_pow_semilinear hn hβ
  have hστ : σ τ = τ := hessApplyEqOfOdd hτ hτ1 σ hodd
  have hd' : conjAut 3 K A (proj 3 K (dSL hτ)) = proj 3 K (dSL hτ) := by
    have := hd
    rw [hAσ, MulAut.mul_apply, hessFieldAutD hτ hστ] at this
    exact this
  have hc' : conjAut 3 K A (proj 3 K cSL) = proj 3 K cSL := by
    have := hc
    rw [hAσ, MulAut.mul_apply, hessFieldAutC] at this
    exact this
  obtain ⟨u, hu⟩ := exists_scalar_of_conjAut_eq hd'
  obtain ⟨v, hv⟩ := exists_scalar_of_conjAut_eq hc'
  rw [toGL_dSL] at hu
  rw [toGL_cSL] at hv
  obtain ⟨s, m, j, hA⟩ := exists_eq_of_conj_hessian hτ hτ1 hu hv
  refine ⟨m, j, σ, hστ, ?_⟩
  have : conjAut 3 K A = MulAut.conj (proj 3 K (dSL hτ) ^ m * proj 3 K cSL ^ j) := by
    rw [hA, map_mul, map_mul, conjAut_scalar, one_mul, map_pow, map_pow, ← toGL_dSL hτ,
      ← toGL_cSL, conjAut_toGL, conjAut_toGL, map_mul, map_pow, map_pow]
  rw [hAσ, this]

private theorem hessCommuteLinear [Finite K] (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (hdc : proj 3 K (dSL hτ) * proj 3 K cSL = proj 3 K cSL * proj 3 K (dSL hτ))
    {β γ : MulAut (projectiveSL 3 K)} {n n' : ℕ} (hn : Odd n) (hβ : β ^ n = 1)
    (hn' : Odd n') (hγ : γ ^ n' = 1)
    (hβd : β (proj 3 K (dSL hτ)) = proj 3 K (dSL hτ)) (hβc : β (proj 3 K cSL) = proj 3 K cSL)
    (hγd : γ (proj 3 K (dSL hτ)) = proj 3 K (dSL hτ)) (hγc : γ (proj 3 K cSL) = proj 3 K cSL) :
    β * γ = γ * β := by
  obtain ⟨m, j, σ, hσ, rfl⟩ := hessDecompLinear hτ hτ1 hn hβ hβd hβc
  obtain ⟨m', j', σ', hσ', rfl⟩ := hessDecompLinear hτ hτ1 hn' hγ hγd hγc
  refine hessCommuteOfDecomp hdc
    (S := {F | ∃ σ : K ≃+* K, σ τ = τ ∧ F = fieldAut 3 K σ}) ?_ ?_ ?_
    ⟨m, j, _, ⟨σ, hσ, rfl⟩, rfl⟩ ⟨m', j', _, ⟨σ', hσ', rfl⟩, rfl⟩
  · rintro _ ⟨σ, -, rfl⟩ _ ⟨σ', -, rfl⟩
    rw [← map_mul, ← map_mul, ringAut_mul_comm K σ σ']
  · rintro _ ⟨σ, hσ, rfl⟩
    exact hessFieldAutD hτ hσ
  · rintro _ ⟨σ, -, rfl⟩
    exact hessFieldAutC σ

end Linear

section Unitary

open CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.Sec17.Proof17Res7
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {K : Type} [Field K] {p f : ℕ} {τ : K}

private theorem hessGlAutD (hτ : τ ^ 3 = 1) {σ : K ≃+* K} (hσ : σ τ = τ) :
    glAut σ (diagTau hτ) = diagTau hτ := by
  apply Units.ext
  rw [coe_glAut, coe_diagTau]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hσ]

private theorem hessGlAutC (σ : K ≃+* K) : glAut σ (cycThree : GL (Fin 3) K) = cycThree := by
  apply Units.ext
  rw [coe_glAut, coe_cycThree]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem hessPsuFieldD (h : UnitaryFieldData p f K) (hτ : τ ^ 3 = 1) {σ : K ≃+* K}
    (hσ : σ τ = τ) {dU : unitarySU p f K 3} (hdU : (dU : GL (Fin 3) K) = diagTau hτ) :
    psuField h σ (dU : unitaryPSU h 3) = (dU : unitaryPSU h 3) := by
  rw [psuField_mk]
  congr 1
  apply Subtype.ext
  rw [coe_suField, hdU, hessGlAutD hτ hσ]

private theorem hessPsuFieldC (h : UnitaryFieldData p f K) (σ : K ≃+* K)
    {cU : unitarySU p f K 3} (hcU : (cU : GL (Fin 3) K) = cycThree) :
    psuField h σ (cU : unitaryPSU h 3) = (cU : unitaryPSU h 3) := by
  rw [psuField_mk]
  congr 1
  apply Subtype.ext
  rw [coe_suField, hcU, hessGlAutC]

private theorem hessDecompUnitary (h : UnitaryFieldData p f K) (hq : 2 < p ^ f) (hτ : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) {dU cU : unitarySU p f K 3} (hdU : (dU : GL (Fin 3) K) = diagTau hτ)
    (hcU : (cU : GL (Fin 3) K) = cycThree) {β : MulAut (unitaryPSU h 3)}
    (hd : β (dU : unitaryPSU h 3) = (dU : unitaryPSU h 3))
    (hc : β (cU : unitaryPSU h 3) = (cU : unitaryPSU h 3)) :
    ∃ (m j : ℕ) (σ : K ≃+* K), σ τ = τ ∧
      β = MulAut.conj ((dU : unitaryPSU h 3) ^ m * (cU : unitaryPSU h 3) ^ j) *
        psuField h σ := by
  obtain ⟨A, σ, hβ⟩ := exists_psuConj_mul_psuField hq β
  rcases hessApplyEqOrSq hτ hτ1 σ with hστ | hστ
  · have hd' : psuConj h A (dU : unitaryPSU h 3) = (dU : unitaryPSU h 3) := by
      have := hd
      rw [hβ, MulAut.mul_apply, hessPsuFieldD h hτ hστ hdU] at this
      exact this
    have hc' : psuConj h A (cU : unitaryPSU h 3) = (cU : unitaryPSU h 3) := by
      have := hc
      rw [hβ, MulAut.mul_apply, hessPsuFieldC h σ hcU] at this
      exact this
    rw [psuConj_mk] at hd' hc'
    obtain ⟨u, hu⟩ := exists_scalar_of_unitaryProj_eq hd'
    obtain ⟨v, hv⟩ := exists_scalar_of_unitaryProj_eq hc'
    rw [coe_suConj, hdU] at hu
    rw [coe_suConj, hcU] at hv
    obtain ⟨s, m, j, hA⟩ := exists_eq_of_conj_hessian hτ hτ1 hu hv
    refine ⟨m, j, σ, hστ, ?_⟩
    have hconj : psuConj h A =
        MulAut.conj ((dU : unitaryPSU h 3) ^ m * (cU : unitaryPSU h 3) ^ j) := by
      ext x
      induction x using QuotientGroup.induction_on with
      | H g =>
        rw [psuConj_mk, MulAut.conj_apply]
        have e : ((dU : unitaryPSU h 3) ^ m * (cU : unitaryPSU h 3) ^ j) =
            ((dU ^ m * cU ^ j : unitarySU p f K 3) : unitaryPSU h 3) := by
          rw [QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_pow]
        rw [e, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        apply Subtype.ext
        have hA' : (A : GL (Fin 3) K) =
            Matrix.GeneralLinearGroup.scalar (Fin 3) s * (diagTau hτ ^ m * cycThree ^ j) := by
          rw [hA, mul_assoc]
        rw [coe_suConj]
        simp only [Subgroup.coe_inv, hA', scalar_mul_conj, Subgroup.coe_mul, Subgroup.coe_pow,
          hdU, hcU]
    rw [hβ, hconj]
  · exfalso
    have hτ4 : σ (τ ^ 2) = τ := by
      rw [map_pow, hστ, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hτ, one_mul, pow_one]
    have hσd : (glAut σ (dU : GL (Fin 3) K) : GL (Fin 3) K) = (diagTau hτ)⁻¹ := by
      apply Units.ext
      rw [coe_glAut, hdU, coe_diagTau, coe_diagTau_inv hτ]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hστ, hτ4]
    have hσc : (glAut σ (cU : GL (Fin 3) K) : GL (Fin 3) K) = cycThree := by
      rw [hcU]
      exact hessGlAutC σ
    have hd' := hd
    have hc' := hc
    rw [hβ, MulAut.mul_apply, psuField_mk, psuConj_mk] at hd' hc'
    obtain ⟨u, hu⟩ := exists_scalar_of_unitaryProj_eq hd'
    obtain ⟨v, hv⟩ := exists_scalar_of_unitaryProj_eq hc'
    rw [coe_suConj, coe_suField, hσd, hdU] at hu
    rw [coe_suConj, coe_suField, hσc, hcU] at hv
    exact false_of_conj_inv_hessian hτ hτ1 hu hv

private theorem hessCommuteUnitary (h : UnitaryFieldData p f K) (hq : 2 < p ^ f) (hτ : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) {dU cU : unitarySU p f K 3} (hdU : (dU : GL (Fin 3) K) = diagTau hτ)
    (hcU : (cU : GL (Fin 3) K) = cycThree)
    (hdc : (dU : unitaryPSU h 3) * (cU : unitaryPSU h 3) =
      (cU : unitaryPSU h 3) * (dU : unitaryPSU h 3)) {β γ : MulAut (unitaryPSU h 3)}
    (hβd : β (dU : unitaryPSU h 3) = (dU : unitaryPSU h 3))
    (hβc : β (cU : unitaryPSU h 3) = (cU : unitaryPSU h 3))
    (hγd : γ (dU : unitaryPSU h 3) = (dU : unitaryPSU h 3))
    (hγc : γ (cU : unitaryPSU h 3) = (cU : unitaryPSU h 3)) : β * γ = γ * β := by
  have := h.finite
  obtain ⟨m, j, σ, hσ, rfl⟩ := hessDecompUnitary h hq hτ hτ1 hdU hcU hβd hβc
  obtain ⟨m', j', σ', hσ', rfl⟩ := hessDecompUnitary h hq hτ hτ1 hdU hcU hγd hγc
  refine hessCommuteOfDecomp hdc
    (S := {F | ∃ σ : K ≃+* K, σ τ = τ ∧ F = psuField h σ}) ?_ ?_ ?_
    ⟨m, j, _, ⟨σ, hσ, rfl⟩, rfl⟩ ⟨m', j', _, ⟨σ', hσ', rfl⟩, rfl⟩
  · rintro _ ⟨σ, -, rfl⟩ _ ⟨σ', -, rfl⟩
    rw [← map_mul, ← map_mul, ringAut_mul_comm K σ σ']
  · rintro _ ⟨σ, hσ, rfl⟩
    exact hessPsuFieldD h hτ hσ hdU
  · rintro _ ⟨σ, -, rfl⟩
    exact hessPsuFieldC h σ hcU

end Unitary

section Order72

variable {X : Type} [Group X] [Finite X]

private theorem hessFactorization72 : (72 : ℕ).factorization 2 = 3 := by
  have h72 : (72 : ℕ) = 2 ^ 3 * 9 := by norm_num
  rw [h72, Nat.factorization_mul (pow_ne_zero _ two_ne_zero) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

private theorem hessNormal72 {E : Subgroup X} (hX : Nat.card X = 72) (hE9 : Nat.card E = 9)
    (htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁) : E.Normal := by
  obtain ⟨⟨v₀, hv₀⟩, hv₀1⟩ : ∃ x : E, x ≠ 1 := by
    have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [hE9]; norm_num)
    exact exists_ne 1
  have hv₀1' : v₀ ≠ 1 := fun h => hv₀1 (Subtype.ext h)
  have h8 : Nat.card E - 1 ∣ Nat.card (Subgroup.normalizer (E : Set X)) :=
    CFSG.Quasithin.RonanE628.rc_card_sub_one_dvd hv₀ hv₀1' (fun w hw hw1 => by
      obtain ⟨n, hn, hnw⟩ := htr v₀ hv₀ hv₀1' w hw hw1
      refine ⟨n⁻¹, inv_mem hn, ?_⟩
      rw [inv_inv, ← hnw]) le_rfl
  have h9 : Nat.card E ∣ Nat.card (Subgroup.normalizer (E : Set X)) :=
    Subgroup.card_dvd_of_le Subgroup.le_normalizer
  have hdvd : Nat.card (Subgroup.normalizer (E : Set X)) ∣ 72 :=
    hX ▸ Subgroup.card_subgroup_dvd_card _
  rw [hE9] at h8 h9
  have h72 : 72 ∣ Nat.card (Subgroup.normalizer (E : Set X)) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 8 9) h8 h9
  have htop : Subgroup.normalizer (E : Set X) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [hX]; exact Nat.dvd_antisymm hdvd h72)
  exact Subgroup.normalizer_eq_top_iff.mp htop

private theorem hessConjOfFix72 (hX : Nat.card X = 72) {E : Subgroup X} [hEn : E.Normal]
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE9 : Nat.card E = 9)
    (hC : ∀ y : X, (∀ b ∈ E, y * b = b * y) → y ∈ E) {α : MulAut X}
    (hα : ∀ b ∈ E, α b = b) : ∃ e ∈ E, α = MulAut.conj e := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 2 X) := inferInstance
  have hQ8 : Nat.card (Q : Subgroup X) = 8 := by
    rw [Sylow.card_eq_multiplicity, hX, hessFactorization72]
    norm_num
  have hEQ : E ⊓ (Q : Subgroup X) = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    have h1 : Nat.card (E ⊓ (Q : Subgroup X) : Subgroup X) ∣ Nat.card E :=
      Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card (E ⊓ (Q : Subgroup X) : Subgroup X) ∣ Nat.card (Q : Subgroup X) :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [hE9] at h1
    rw [hQ8] at h2
    exact Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 9 8) h1 h2
  have hsup : E ⊔ (Q : Subgroup X) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have h9 : 9 ∣ Nat.card (E ⊔ (Q : Subgroup X) : Subgroup X) :=
      hE9 ▸ Subgroup.card_dvd_of_le le_sup_left
    have h8 : 8 ∣ Nat.card (E ⊔ (Q : Subgroup X) : Subgroup X) :=
      hQ8 ▸ Subgroup.card_dvd_of_le le_sup_right
    have h72 : 72 ∣ Nat.card (E ⊔ (Q : Subgroup X) : Subgroup X) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 8 9) h8 h9
    have hle : Nat.card (E ⊔ (Q : Subgroup X) : Subgroup X) ∣ 72 :=
      hX ▸ Subgroup.card_subgroup_dvd_card _
    rw [hX]
    exact Nat.dvd_antisymm hle h72
  have hfac : ∀ x : X, ∃ e ∈ E, ∃ q ∈ (Q : Subgroup X), e * q = x := fun x =>
    Subgroup.mem_sup_of_normal_left.mp (hsup ▸ Subgroup.mem_top x)
  have hQ'8 : Nat.card ((Q : Subgroup X).map α.toMonoidHom) =
      2 ^ (Nat.card X).factorization 2 := by
    rw [Subgroup.card_map_of_injective α.injective, hQ8, hX, hessFactorization72]
    norm_num
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq X Q
    (Sylow.ofCard ((Q : Subgroup X).map α.toMonoidHom) hQ'8)
  have hαQ : ∀ q ∈ (Q : Subgroup X), k⁻¹ * α q * k ∈ (Q : Subgroup X) := by
    intro q hq
    have h1 : α q ∈ ((Sylow.ofCard ((Q : Subgroup X).map α.toMonoidHom) hQ'8 : Sylow 2 X) :
        Subgroup X) := ⟨q, hq, rfl⟩
    rw [← hk, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨s, hs, hsq⟩ := h1
    have hsq' : k * s * k⁻¹ = α q := by simpa [MulAut.smul_def, MulAut.conj_apply] using hsq
    have : k⁻¹ * α q * k = s := by rw [← hsq']; group
    rw [this]
    exact hs
  obtain ⟨e, he, q₀, hq₀, hk'⟩ := hfac k
  set α' : MulAut X := MulAut.conj e⁻¹ * α with hα'
  have hα'apply : ∀ z : X, α' z = e⁻¹ * α z * e := by
    intro z
    simp [hα', MulAut.conj_apply]
  have hα'Q : ∀ q ∈ (Q : Subgroup X), α' q ∈ (Q : Subgroup X) := by
    intro q hq
    have h := hαQ q hq
    have : α' q = q₀ * (k⁻¹ * α q * k) * q₀⁻¹ := by
      rw [hα'apply, ← hk']
      group
    rw [this]
    exact mul_mem (mul_mem hq₀ h) (inv_mem hq₀)
  have hα'E : ∀ b ∈ E, α' b = b := by
    intro b hb
    rw [hα'apply, hα b hb]
    have := hEc e⁻¹ (inv_mem he) b hb
    calc e⁻¹ * b * e = b * e⁻¹ * e := by rw [this]
      _ = b := by group
  have hα'Q' : ∀ q ∈ (Q : Subgroup X), α' q = q := by
    intro q hq
    have hyQ : (α' q)⁻¹ * q ∈ (Q : Subgroup X) := mul_mem (inv_mem (hα'Q q hq)) hq
    have hyC : ∀ b ∈ E, ((α' q)⁻¹ * q) * b = b * ((α' q)⁻¹ * q) := by
      intro b hb
      have hqb : q * b * q⁻¹ ∈ E := hEn.conj_mem b hb q
      have h1 : α' (q * b * q⁻¹) = q * b * q⁻¹ := hα'E _ hqb
      rw [map_mul, map_mul, map_inv, hα'E b hb] at h1
      calc (α' q)⁻¹ * q * b = (α' q)⁻¹ * (q * b * q⁻¹) * q := by group
        _ = (α' q)⁻¹ * (α' q * b * (α' q)⁻¹) * q := by rw [h1]
        _ = b * ((α' q)⁻¹ * q) := by group
    have hyE := hC _ hyC
    have hy1 : (α' q)⁻¹ * q = 1 :=
      Subgroup.mem_bot.mp (hEQ ▸ (Subgroup.mem_inf.mpr ⟨hyE, hyQ⟩))
    exact inv_mul_eq_one.mp hy1
  have hα'1 : α' = 1 := by
    ext x
    obtain ⟨e₁, he₁, q₁, hq₁, rfl⟩ := hfac x
    rw [map_mul, hα'E e₁ he₁, hα'Q' q₁ hq₁]
    rfl
  refine ⟨e, he, ?_⟩
  have : α = MulAut.conj e * α' := by
    rw [hα', ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  rw [this, hα'1, mul_one]

private theorem hessCommuteOrder72 (hX : Nat.card X = 72) {E : Subgroup X}
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE9 : Nat.card E = 9)
    (htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁)
    (hC : ∀ y : X, (∀ b ∈ E, y * b = b * y) → y ∈ E) {σ τ : MulAut X}
    (hσ : ∀ b ∈ E, σ b = b) (hτ : ∀ b ∈ E, τ b = b) : σ * τ = τ * σ := by
  haveI := hessNormal72 hX hE9 htr
  obtain ⟨e, he, rfl⟩ := hessConjOfFix72 hX hEc hE9 hC hσ
  obtain ⟨e', he', rfl⟩ := hessConjOfFix72 hX hEc hE9 hC hτ
  rw [← map_mul, ← map_mul, hEc e he e' he']

end Order72

section Main

open CFSG.RankThree.PartTwo.Sec17.Proof17Res7 CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem hessTransport {M X : Type} [Group M] [Group X] (Ψ : M ≃* X) {dM cM : M}
    {E : Subgroup X} (hdE : Ψ dM ∈ E) (hcE : Ψ cM ∈ E)
    (hM : ∀ β γ : MulAut M, (∃ k : ℕ, β ^ 3 ^ k = 1) → (∃ k : ℕ, γ ^ 3 ^ k = 1) →
      β dM = dM → β cM = cM → γ dM = dM → γ cM = cM → β * γ = γ * β)
    {σ τ : MulAut X} (hσ : ∃ k : ℕ, σ ^ 3 ^ k = 1) (hτ : ∃ k : ℕ, τ ^ 3 ^ k = 1)
    (hσE : ∀ b ∈ E, σ b = b) (hτE : ∀ b ∈ E, τ b = b) : σ * τ = τ * σ := by
  have hT : ∀ (α : MulAut X) (m : M), Ψ m ∈ E → (∀ b ∈ E, α b = b) →
      MulAut.congr Ψ.symm α m = m := by
    intro α m hm hα
    have h : MulAut.congr Ψ.symm α m = Ψ.symm (α (Ψ m)) := rfl
    rw [h, hα _ hm, MulEquiv.symm_apply_apply]
  have hpow : ∀ α : MulAut X, (∃ k : ℕ, α ^ 3 ^ k = 1) →
      ∃ k : ℕ, (MulAut.congr Ψ.symm α) ^ 3 ^ k = 1 := by
    rintro α ⟨k, hk⟩
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  have h := hM _ _ (hpow σ hσ) (hpow τ hτ) (hT σ dM hdE hσE) (hT σ cM hcE hσE)
    (hT τ dM hdE hτE) (hT τ cM hcE hτE)
  apply (MulAut.congr Ψ.symm).injective
  rw [map_mul, map_mul]
  exact h

theorem commute_of_fix_hessian {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (hiso : Sec4.IsoLThreePi X p e) {E : Subgroup X}
    (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁)
    {σ τ : MulAut X} (hσ : ∃ k : ℕ, σ ^ 3 ^ k = 1) (hτ : ∃ k : ℕ, τ ^ 3 ^ k = 1)
    (hσE : ∀ b ∈ E, σ b = b) (hτE : ∀ b ∈ E, τ b = b) : σ * τ = τ * σ := by
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  by_cases hq2 : p ^ e = 2
  ·
    have hp2 : p = 2 := by
      have hdvd : p ∣ 2 := hq2 ▸ dvd_pow_self p (by omega : e ≠ 0)
      exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hdvd
    subst hp2
    have he1 : e = 1 := by
      have : 2 ^ e = 2 ^ 1 := by rw [hq2, pow_one]
      exact Nat.pow_right_injective (le_refl 2) this
    subst he1
    have hX : Nat.card X = 72 := by
      rcases hiso with ⟨h1, -⟩ | ⟨-, ⟨φ⟩⟩
      · norm_num at h1
      · rw [Nat.card_congr φ.toEquiv]
        exact Sec4.Item419ThetaProof.card_projSU_three_two_one
    exact hessCommuteOrder72 hX hEc hE9 htr
      (fun y hy => Proof1413Res7.mem_of_commute_hessian he hiso hEe hE9 htr hy) hσE hτE
  · obtain ⟨π, K, _, hK, hq, τ', hτ', hτ1, dM, cM, hdM, hcM, hdc, -, -, -, Φ, hΦE⟩ :=
      Res8Hess.exists_hessian_equiv he hiso hEe hE9 htr
    have := hK.finite
    have hdE : Φ dM ∈ E := hΦE ▸ ⟨dM, Subgroup.mem_sup_left (Subgroup.mem_zpowers dM), rfl⟩
    have hcE : Φ cM ∈ E := hΦE ▸ ⟨cM, Subgroup.mem_sup_right (Subgroup.mem_zpowers cM), rfl⟩
    cases π
    ·
      have h := hK.unitary
      have hq' : 2 < p ^ e := by
        have : 1 < p ^ e := Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt
        omega
      let dU : unitarySU p e K 3 :=
        ⟨diagTau hτ', diagTau_mem_slPi (π := false) (fun _ => h) (fun _ => hq) hτ'⟩
      let cU : unitarySU p e K 3 := ⟨cycThree, cycThree_mem_slPi (π := false) (fun _ => h)⟩
      have hΦd : unitaryModelEquiv h (dU : unitaryPSU h 3) = dM :=
        Subtype.ext (by rw [coe_unitaryModelEquiv_mk, hdM])
      have hΦc : unitaryModelEquiv h (cU : unitaryPSU h 3) = cM :=
        Subtype.ext (by rw [coe_unitaryModelEquiv_mk, hcM])
      have hdc' : (dU : unitaryPSU h 3) * (cU : unitaryPSU h 3) =
          (cU : unitaryPSU h 3) * (dU : unitaryPSU h 3) :=
        (unitaryModelEquiv h).injective (by rw [map_mul, map_mul, hΦd, hΦc]; exact hdc)
      refine hessTransport ((unitaryModelEquiv h).trans Φ) (dM := (dU : unitaryPSU h 3))
        (cM := (cU : unitaryPSU h 3)) ?_ ?_ ?_ hσ hτ hσE hτE
      · rw [MulEquiv.trans_apply, hΦd]
        exact hdE
      · rw [MulEquiv.trans_apply, hΦc]
        exact hcE
      · intro β γ _ _ hβd hβc hγd hγc
        exact hessCommuteUnitary h hq' hτ' hτ1 (dU := dU) (cU := cU) rfl rfl hdc' hβd hβc hγd hγc
    ·
      have hΦd : linearModelEquiv (p ^ e) (proj 3 K (dSL hτ')) = dM :=
        Subtype.ext (by rw [coe_linearModelEquiv_proj, toGL_dSL, hdM])
      have hΦc : linearModelEquiv (p ^ e) (proj 3 K cSL) = cM :=
        Subtype.ext (by rw [coe_linearModelEquiv_proj, toGL_cSL, hcM])
      have hdc' : proj 3 K (dSL hτ') * proj 3 K cSL = proj 3 K cSL * proj 3 K (dSL hτ') :=
        (linearModelEquiv (p ^ e)).injective (by rw [map_mul, map_mul, hΦd, hΦc]; exact hdc)
      refine hessTransport ((linearModelEquiv (p ^ e)).trans Φ)
        (dM := proj 3 K (dSL hτ')) (cM := proj 3 K cSL) ?_ ?_ ?_ hσ hτ hσE hτE
      · rw [MulEquiv.trans_apply, hΦd]
        exact hdE
      · rw [MulEquiv.trans_apply, hΦc]
        exact hcE
      · rintro β γ ⟨k, hk⟩ ⟨k', hk'⟩ hβd hβc hγd hγc
        exact hessCommuteLinear hτ' hτ1 hdc' (Odd.pow (by decide)) hk (Odd.pow (by decide)) hk'
          hβd hβc hγd hγc

theorem false_of_commutator_hessian {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (hiso : Sec4.IsoLThreePi X p e) (hZ : Subgroup.center X = ⊥)
    {E : Subgroup X} (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁)
    {N : Type} [Group N] (act : N →* MulAut X) {c w : N}
    (hc : ∃ k : ℕ, c ^ 3 ^ k = 1) (hw : ∃ k : ℕ, w ^ 3 ^ k = 1)
    (hcE : ∀ b ∈ E, act c b = b) (hwE : ∀ b ∈ E, act w b = b)
    {e₀ : X} (he₀ : e₀ ∈ E) (he₀1 : e₀ ≠ 1) (hcomm : act (c * w * c⁻¹ * w⁻¹) = MulAut.conj e₀) :
    False := by
  have hσ : ∃ k : ℕ, (act c) ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hc
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  have hτ : ∃ k : ℕ, (act w) ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hw
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  have h := commute_of_fix_hessian he hiso hEe hE9 htr hσ hτ hcE hwE
  have h1 : act (c * w * c⁻¹ * w⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    calc act c * act w * (act c)⁻¹ * (act w)⁻¹
        = (act c * act w) * (act c)⁻¹ * (act w)⁻¹ := by group
      _ = (act w * act c) * (act c)⁻¹ * (act w)⁻¹ := by rw [h]
      _ = 1 := by group
  rw [h1] at hcomm
  have h3 : e₀ ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h4 := congrArg (fun φ : MulAut X => φ g) hcomm
    simp only [MulAut.one_apply, MulAut.conj_apply] at h4
    calc g * e₀ = (e₀ * g * e₀⁻¹) * e₀ := by rw [← h4]
      _ = e₀ * g := by group
  rw [hZ] at h3
  exact he₀1 ((Subgroup.mem_bot).mp h3)

end Main

end CFSG.RankThree.PartTwo.Sec15.Liebeck159
