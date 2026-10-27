module

public import CFSG.RankThree.PartOne.S11d.OrthCaseH
public import CFSG.RankThree.PartOne.S11d.PSUModel

public section

namespace CFSG.RankThree.PartOne

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.RankThree.OrthogonalInvolutions CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedSL StatedSU StatedProj StatedScalars)
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne.Sec66T (lieModel_classical_iff centerQuotientEquivSelf)

section Extraction

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] (R : QuadraticForm K W) (hR : (polarBilin R).Nondegenerate)

theorem nonsplit_quasisimple_dicksonDerived (hd : finrank K W = 4 ∨ finrank K W = 6)
    (hts : ∀ U : Submodule K W, finrank K U = finrank K W / 2 → ∃ u ∈ U, R u ≠ 0) :
    CFSG.IsQuasisimple ↥(orthDerived R) ∧ DicksonDerived R hR := by
  obtain ⟨hs, hp, hna, hidx, -, -, -⟩ := even_minus_four_six_actual_derived_extraction R hR hd hts
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  refine ⟨?_, fun g hg => mem_orthDerived_of_dicksonHom_eq_one hR hidx hg⟩
  have := hs
  exact isQuasisimple_of_simple_nonabelian hna

end Extraction

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {R : QuadraticForm K W} {G : Type} [Group G]

theorem lieModel_quotient_of_statedSU4 {E : Type} [Field E] {f : ℕ} (h : UnitaryFieldData 2 f E)
    (e : G ≃* StatedSU 4 (2 ^ f) E) : LieModel (G ⧸ Subgroup.center G) .PSU 4 2 f := by
  have hfin := h.finite
  have hF : Nat.card E = (2 ^ f) ^ 2 := h.card_eq_sq
  have hnq : ((4 : ℕ), 2 ^ f) ≠ (3, 2) := by
    intro hc
    have := congrArg Prod.fst hc
    simp at this
  obtain ⟨-, hZc⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF
    (by norm_num) hnq
  exact (lieModel_classical_iff (by decide)).mpr ⟨⟨Nat.prime_two, h.one_le, by norm_num, hnq⟩,
    E, inferInstance, inferInstance, hF,
    ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans
      (QuotientGroup.quotientMulEquivOfEq hZc)⟩⟩

theorem lieModel_quotient_of_SL2 {E : Type} [Field E] [Finite E] [CharP E 2] {g : ℕ}
    (hE : Nat.card E = 2 ^ g) (hg : 2 ≤ g) (e : G ≃* Matrix.SpecialLinearGroup (Fin 2) E) :
    LieModel (G ⧸ Subgroup.center G) .PSL 2 2 g := by
  have hZ : Subgroup.center G = ⊥ := by
    have h1 := Subgroup.map_center_eq e
    rw [center_SL2_eq_bot'] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  obtain ⟨ψ⟩ := nonempty_SL2_mulEquiv_statedProj' (F := E)
  refine (lieModel_classical_iff (by decide)).mpr ⟨⟨Nat.prime_two, by omega, le_rfl,
    fun hc => ?_, fun hc => ?_⟩, E, inferInstance, inferInstance, hE,
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans (e.trans ψ)⟩⟩
  · have h1 : (2 : ℕ) ^ g = 2 := (Prod.mk.inj hc).2
    have : (4 : ℕ) ≤ 2 ^ g := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
    omega
  · have h1 : (2 : ℕ) ^ g = 3 := (Prod.mk.inj hc).2
    have : (4 : ℕ) ≤ 2 ^ g := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
    omega

theorem exists_lieModel_nonsplit (hd : finrank K W = 4 ∨ finrank K W = 6)
    (hts : ∀ U : Submodule K W, finrank K U = finrank K W / 2 → ∃ u ∈ U, R u ≠ 0)
    (hR : (polarBilin R).Nondegenerate) {f : ℕ} (hf : 2 ≤ f) (hcard : Nat.card K = 2 ^ f)
    (φ : G ≃* ↥(orthDerived R)) :
    ∃ (t' : StatedLieTag) (n' g : ℕ), 2 ≤ g ∧
      LieModel (G ⧸ Subgroup.center G) t' n' 2 g ∧ (g = 2 * f ∨ g = f) := by
  obtain ⟨-, -, -, -, -, h4, h6⟩ := even_minus_four_six_actual_derived_extraction R hR hd hts
  rcases hd with hd4 | hd6
  · obtain ⟨E, _, _, D, ψ, ρ, -, -, hinj, hrange, -⟩ := h4 hd4
    have : CharP E 2 := charP_two_of_algebra (K := K)
    have hEfin : Finite E := by
      have : Nat.card E = Nat.card K ^ 2 := D.card_E
      exact Nat.finite_of_card_ne_zero (by rw [this]; exact pow_ne_zero 2 Nat.card_pos.ne')
    have hE : Nat.card E = 2 ^ (2 * f) := by rw [D.card_E, hcard, ← pow_mul, mul_comm]
    let e : G ≃* Matrix.SpecialLinearGroup (Fin 2) E :=
      φ.trans ((MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hinj).symm)
    exact ⟨.PSL, 2, 2 * f, by omega, lieModel_quotient_of_SL2 hE (by omega) e, Or.inl rfl⟩
  · obtain ⟨E, _, _, D, ψ, ρ, -, -, hinj, hrange, -⟩ := h6 hd6
    have : CharP E 2 := charP_two_of_algebra (K := K)
    obtain ⟨f₁, h, hK, hbar⟩ := D.exists_unitaryFieldData
    have hff : f₁ = f := Nat.pow_right_injective (le_refl 2) (hK.symm.trans hcard)
    subst hff
    obtain ⟨θ⟩ := D.nonempty_sixSU_mulEquiv h hbar
    let e : G ≃* StatedSU 4 (2 ^ f₁) E :=
      (φ.trans ((MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hinj).symm)).trans
        θ
    exact ⟨.PSU, 4, f₁, hf, lieModel_quotient_of_statedSU4 h e, Or.inr rfl⟩

end Model

section Good

variable {K : Type} [Field K] [Finite K] [CharP K 2] {k : Subfield K} {σ : K ≃+* K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)}

theorem orth_good_nonsplit (hσk : ∀ c, c ∈ k ↔ σ c = c) (hext : IsExtension k Q₀ Q)
    (hQS : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v)) (hQ : (polarBilin Q).Nondegenerate)
    (hK : 4 ≤ Nat.card K) (hσ : ∃ c, σ c ≠ c) {α : MulAut (ProjOrthDerived Q)}
    (hα : ActsBySemilinear Q (coordinateFieldMap d σ) α) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x : (Fin d → K) ≃ₗ[K] (Fin d → K)} (hxΩ : x ∈ orthDerived Q) (hx : OddOrderIsometry Q p x)
    (hSx : ∀ v, coordinateFieldMap d σ (x v) = x (coordinateFieldMap d σ v))
    (hmult : ∀ h ∈ primaryFactors x.toLinearMap, h ≠ X - 1 →
      primaryMultiplicity x.toLinearMap h ≤ 1)
    (hd : finrank K (fixedSpace x) = 4 ∨ finrank K (fixedSpace x) = 6)
    (hts : ∀ U : Submodule K (fixedSpace x), finrank K U = finrank K (fixedSpace x) / 2 →
      ∃ u ∈ U, (Q.comp (fixedSpace x).subtype) u ≠ 0) {f₀ : ℕ} (hf₀ : 1 ≤ f₀)
    (hcard : Nat.card K = 2 ^ (p * f₀)) :
    GoodConclusion p (ProjOrthDerived Q) α (piOrth Q ⟨x, hxΩ⟩) := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have h4 : 4 ≤ finrank K (fixedSpace x) := by omega
  have : Nontrivial (Fin d → K) := nontrivial_of_four_le_finrank_fixed h4
  have hWnd := hx.polarBilin_fixed_nondegenerate
  have : Nontrivial (fixedSpace x) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨hq, hD⟩ := nonsplit_quasisimple_dicksonDerived (Q.comp (fixedSpace x).subtype) hWnd hd hts
  have hp2' : 2 ≤ p * f₀ := le_trans hp.two_le (Nat.le_mul_of_pos_right p hf₀)
  have hmodel : ∃ (t' : StatedLieTag) (n' f' : ℕ), 1 ≤ f' ∧
      LieModel (↥(fixedComponentImage Q x) ⧸ Subgroup.center ↥(fixedComponentImage Q x)) t' n' 2
        (p * f') := by
    obtain ⟨t', n', g, hg, hmod, hgf⟩ := exists_lieModel_nonsplit hd hts hWnd hp2' hcard
      (fixedComponentImageEquiv hQ hx)
    rcases hgf with rfl | rfl
    · exact ⟨t', n', 2 * f₀, by omega, by rwa [show p * (2 * f₀) = 2 * (p * f₀) by ring]⟩
    · exact ⟨t', n', f₀, hf₀, hmod⟩
  exact orth_good_of_single hQ hK hodd hσ (coordinateFieldMap d σ) (coordinateFieldMap_smul σ) hQS
    hα hxΩ hx hmult h4 hD
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv (fixedComponentImageEquiv hQ hx).symm hq) hmodel
    (exists_rational_eichler_pair k hσk hext hQS hK hodd hx hx.pow_eq_one hSx h4)

end Good

end CFSG.RankThree.PartOne
