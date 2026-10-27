module

public import CFSG.LocalAnalysis.StandardType.GGSpNsRootGenDefs
import CFSG.ClassicalGroups.Alternating.Generation
import CFSG.ClassicalGroups.Alternating.SteinbergBQTransvectionConjugation
import CFSG.ClassicalGroups.Alternating.TransvectionGeneration
import CFSG.ClassicalGroups.Orthogonal.Transitive
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173UniOmega
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentOrthFixed
import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
import CFSG.GroupTheory.WeirSylow.OrthogonalTypes
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
import CFSG.Holt.Fixed
import CFSG.LieType.SeitzGeneration.HyperLinear
import CFSG.LieType.SeitzGeneration.OrthCubeBlocks
import CFSG.LieType.SeitzGeneration.OrthExLift
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLInner
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentLayer
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
import CFSG.LocalAnalysis.SignalizerFunctor
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.RankThree.PartOne.CTP.SeitzLinear
import CFSG.RankThree.PartOne.FOC.CompCommutator
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.StandardType.SpNsRootGen

open QuadraticMap CFSG.ClassicalGroups.Alternating CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Classical2
open LinearMap (BilinForm)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

private theorem eq_top_of_forall_Tsp_mem {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {B : BilinForm K W} (hB : B.IsAlt) (hBn : B.Nondegenerate)
    {H : Subgroup (Gsp B)} (hT : ∀ v c, Tsp hB v c ∈ H) : H = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hg : (g : LinearMap.GeneralLinearGroup K W) ∈ bilinIsometryGroup B := g.2
  have hle : bilinIsometryGroup B ≤ H.map (bilinIsometryGroup B).subtype := by
    conv_lhs => rw [alternating_transvection_generation hB hBn]
    rw [Subgroup.closure_le]
    rintro _ ⟨a, c, rfl⟩
    exact ⟨Tsp hB a c, hT a c, rfl⟩
  obtain ⟨h, hh, hval⟩ := hle hg
  have hgh : h = g := Subtype.ext hval
  rwa [hgh] at hh

private theorem Tsp_conj {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    {B : BilinForm K W} (hB : B.IsAlt) (g : Gsp B) (v : W) (c : K) :
    Tsp hB (g.app v) c = g * Tsp hB v c * g⁻¹ := by
  refine Subtype.ext ?_
  have h := SteinbergBQ.symplecticTransvection_conj hB
    (g := (g : LinearMap.GeneralLinearGroup K W)) (fun x y => g.2 x y) v c
  simpa only [Tsp, Subgroup.coe_mul, Subgroup.coe_inv, Gsp.app] using h.symm

private theorem Tsp_app_mem_of_mem {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    {B : BilinForm K W} (hB : B.IsAlt) {H : Subgroup (Gsp B)} {g : Gsp B} (hg : g ∈ H)
    {v : W} {c : K} (h : Tsp hB v c ∈ H) : Tsp hB (g.app v) c ∈ H := by
  rw [Tsp_conj hB g v c]
  exact mul_mem (mul_mem hg h) (inv_mem hg)

private theorem Tsp_mem_of_app_mem {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    {B : BilinForm K W} (hB : B.IsAlt) {H : Subgroup (Gsp B)} {g : Gsp B} (hg : g ∈ H)
    {v : W} {c : K} (h : Tsp hB (g.app v) c ∈ H) : Tsp hB v c ∈ H := by
  have hconj := Tsp_conj hB g⁻¹ (g.app v) c
  rw [Gsp.app_inv_app, inv_inv] at hconj
  rw [hconj]
  exact mul_mem (mul_mem (inv_mem hg) h) hg

private theorem Tsp_zero {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    {B : BilinForm K W} (hB : B.IsAlt) (c : K) : Tsp hB (0 : W) c = 1 := by
  refine Subtype.ext (Units.ext (LinearMap.ext fun x => ?_))
  simp [Tsp, symplecticTransvection_apply]

theorem range_omegaToGsp_sup_gspFixPerp_eq_top {Q : QuadraticForm F V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hF4 : 4 ≤ Nat.card F) {ℓ : ℕ}
    (hdim : Module.finrank F V = 2 * ℓ) (hℓ : 3 ≤ ℓ) {U : Submodule F V}
    (hU2 : Module.finrank F U = 2)
    (hUn : (QuadraticMap.polarBilin (Q.comp U.subtype)).Nondegenerate)
    (hU : ∀ u ∈ U, Q u = 0 → u = 0) :
    (omegaToGsp Q).range ⊔ gspFixPerp (QuadraticMap.polarBilin Q) U = ⊤ := by
  classical
  let B : BilinForm F V := QuadraticMap.polarBilin Q
  change (omegaToGsp Q).range ⊔ gspFixPerp B U = ⊤
  have hB : B.IsAlt := fun v => by
    change QuadraticMap.polarBilin Q v v = 0
    rw [polarBilin_apply_apply, polar_self, two_smul, CharTwo.add_self_eq_zero]
  have hrefl : B.IsRefl := hB.isRefl
  have hEqU : QuadraticMap.polarBilin (Q.comp U.subtype) = B.restrict U := by
    refine LinearMap.ext₂ fun x y => ?_
    rw [polarBilin_apply_apply]
    change polar Q (x : V) (y : V) = polarBilin Q (x : V) (y : V)
    rw [polarBilin_apply_apply]
  have hUrestrict : (B.restrict U).Nondegenerate := by rw [← hEqU]; exact hUn
  have hcompl : IsCompl U (B.orthogonal U) :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl hUrestrict
  have hUnd : (B.restrict (B.orthogonal U)).Nondegenerate :=
    (LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hrefl).mpr (by
      rw [LinearMap.BilinForm.orthogonal_orthogonal hQ hrefl U]
      exact hcompl.symm)
  have hexU : ∃ u ∈ U, u ≠ 0 :=
    exists_ne_zero_of_one_le_finrank (T := U) (by omega)
  obtain ⟨P, hP⟩ :=
    CFSG.AGLEmbedding.ToralCensus.exists_two_hypPairs (K := F) (W := V) (Q := Q) hQ
      (show 6 ≤ Module.finrank F V by rw [hdim]; omega)
  have horth : (P 0).Orth (P 1) := hP 0 1 (by decide)
  have hE : orthDerived Q = elementaryGroup Q :=
    CFSG.LocalAnalysis.GLTheoremA.T173U.orthDerived_eq_elementaryGroup_of_three_le hQ hℓ hdim
  let H : Subgroup (Gsp B) := (omegaToGsp Q).range ⊔ gspFixPerp B U
  change H = ⊤
  have homega : (omegaToGsp Q).range ≤ H := le_sup_left
  have hfix : gspFixPerp B U ≤ H := le_sup_right
  have hcase2 : ∀ (v : V), Q v ≠ 0 → ∀ c : F, Tsp hB v c ∈ H := by
    intro v hv c
    obtain ⟨u, huU, hu0⟩ := hexU
    have hQu : Q u ≠ 0 := fun h => hu0 (hU u huU h)
    obtain ⟨l, hl⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) (Q v / Q u)
    have hl0 : l ≠ 0 := by
      intro h0
      exact div_ne_zero hv hQu (by rw [h0] at hl; simpa using hl)
    have hQlu : Q (l • u) = Q v := by
      rw [map_smul_eq_sq, pow_two, ← hl, div_mul_cancel₀ _ hQu]
    have hl0' : l • u ≠ 0 := smul_ne_zero hl0 hu0
    have hv0 : v ≠ 0 := fun h => hv (by rw [h]; exact map_zero Q)
    obtain ⟨g, hgE, hgx⟩ := exists_mem_elementaryGroup_apply_eq hQ horth hl0' hv0 hQlu
    have hgO : g ∈ orthDerived Q := by rw [hE]; exact hgE
    have hωH : omegaToGsp Q ⟨g, hgO⟩ ∈ H := homega ⟨⟨g, hgO⟩, rfl⟩
    have hTspU : Tsp hB (l • u) c ∈ H :=
      hfix (Tsp_mem_gspFixPerp (B := B) hB (U.smul_mem l huU) c)
    have hωapp : (omegaToGsp Q ⟨g, hgO⟩).app (l • u) = v := by
      rw [omegaToGsp_app]
      exact hgx
    have h := Tsp_app_mem_of_mem hB hωH hTspU
    rwa [hωapp] at h
  have hcase3 : ∀ (v : V), Q v = 0 → v ∉ B.orthogonal U → ∀ c : F, Tsp hB v c ∈ H := by
    intro v hv hvperp c
    have hBvu : ∃ u ∈ U, B v u ≠ 0 := by
      by_contra h
      apply hvperp
      refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun u hu => ?_
      by_contra hne
      exact h ⟨u, hu, fun hvu => hne (by rw [← hB.neg_eq v u, hvu, neg_zero])⟩
    obtain ⟨u, huU, hvu⟩ := hBvu
    set u' : V := (B v u)⁻¹ • u with hu'def
    have hu'U : u' ∈ U := U.smul_mem _ huU
    have hu'0 : u' ≠ 0 := smul_ne_zero (inv_ne_zero hvu) (fun h => hvu (by rw [h, map_zero]))
    have hBvu' : B v u' = 1 := by
      rw [hu'def, map_smul, smul_eq_mul, inv_mul_cancel₀ hvu]
    have hQu' : Q u' ≠ 0 := fun h => hu'0 (hU u' hu'U h)
    obtain ⟨s, hs0, hs1⟩ := exists_ne_zero_ne_one_of_two_lt_card (K := F) (by omega)
    obtain ⟨d, hd0, hdQu⟩ : ∃ d : F, d ≠ 0 ∧ d * Q u' ≠ 1 := by
      by_cases hQ0 : Q u' = 0
      · exact ⟨1, one_ne_zero, by rw [hQ0, mul_zero]; exact zero_ne_one⟩
      · refine ⟨s * (Q u')⁻¹, mul_ne_zero hs0 (inv_ne_zero hQ0), ?_⟩
        rw [mul_assoc, inv_mul_cancel₀ hQ0, mul_one]
        exact hs1
    set w : V := v + d • u' with hwdef
    have hTspu : (Tsp hB u' d).app v = w := by
      simp [Tsp_app, hBvu', hwdef]
    have hpolar : polar Q v (d • u') = d * B v u' := by
      rw [polar_smul_right_eq Q d v u']
      change d * polar Q v u' = d * polarBilin Q v u'
      rw [polarBilin_apply_apply]
    have hQw : Q w ≠ 0 := by
      intro h
      rw [hwdef, QuadraticMap.map_add Q, map_smul_eq_sq, hv, zero_add, hpolar, hBvu',
        mul_one] at h
      have h1 : d * (d * Q u' + 1) = 0 := by linear_combination h
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact hd0 h2
      · refine hdQu ?_
        have h3 : d * Q u' = -1 := by linear_combination h2
        rwa [CharTwo.neg_eq] at h3
    have hgu : Tsp hB u' d ∈ H :=
      hfix (Tsp_mem_gspFixPerp (B := B) hB hu'U d)
    have hwTsp : Tsp hB ((Tsp hB u' d).app v) c ∈ H := by
      rw [hTspu]
      exact hcase2 w hQw c
    exact Tsp_mem_of_app_mem hB hgu hwTsp
  have hcase4 : ∀ (v : V), Q v = 0 → v ∈ B.orthogonal U → ∀ c : F, Tsp hB v c ∈ H := by
    intro v hv hvperp c
    by_cases hv0 : v = 0
    · rw [hv0, Tsp_zero hB c]
      exact one_mem H
    obtain ⟨w', hw'perp, hBvw'⟩ :=
      exists_mem_apply_eq_of_restrict_nondegenerate hUnd hvperp hv0 1
    obtain ⟨u0, hu0U, hu00⟩ := hexU
    have hQu0 : Q u0 ≠ 0 := fun h => hu00 (hU u0 hu0U h)
    obtain ⟨x0, hx0U, hBux0⟩ :=
      exists_mem_apply_eq_of_restrict_nondegenerate hUrestrict hu0U hu00 1
    obtain ⟨s, hs0, hs1⟩ := exists_ne_zero_ne_one_of_two_lt_card (K := F) (by omega)
    obtain ⟨l, hl0, hlQ⟩ : ∃ l : F, l ≠ 0 ∧ l ^ 2 * Q u0 ≠ Q w' := by
      by_cases hw' : Q w' = 0
      · exact ⟨1, one_ne_zero, by rw [hw']; simpa using hQu0⟩
      · obtain ⟨l, hl⟩ :=
          FiniteField.isSquare_of_char_two (ringChar.eq F 2) (s * (Q w' / Q u0))
        refine ⟨l, ?_, ?_⟩
        · intro h0
          have hne : s * (Q w' / Q u0) ≠ 0 := mul_ne_zero hs0 (div_ne_zero hw' hQu0)
          exact hne (by rw [h0] at hl; simpa using hl)
        · rw [pow_two, ← hl]
          intro h
          have h1 : s * (Q w' / Q u0) * Q u0 = Q w' := h
          rw [mul_assoc, div_mul_cancel₀ _ hQu0] at h1
          exact hs1 (mul_right_cancel₀ hw' (by simpa using h1))
    set w : V := w' + l • u0 with hwdef
    have hw'x0 : B w' x0 = 0 := by
      rw [← hB.neg_eq x0 w', (LinearMap.BilinForm.mem_orthogonal_iff.mp hw'perp) x0 hx0U,
        neg_zero]
    have hw'u0 : B w' u0 = 0 := by
      rw [← hB.neg_eq u0 w', (LinearMap.BilinForm.mem_orthogonal_iff.mp hw'perp) u0 hu0U,
        neg_zero]
    have hvx0 : B v x0 = 0 := by
      rw [← hB.neg_eq x0 v, (LinearMap.BilinForm.mem_orthogonal_iff.mp hvperp) x0 hx0U,
        neg_zero]
    have hvu0 : B v u0 = 0 := by
      rw [← hB.neg_eq u0 v, (LinearMap.BilinForm.mem_orthogonal_iff.mp hvperp) u0 hu0U,
        neg_zero]
    have hBw : B w x0 = l := by
      rw [hwdef, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, hw'x0,
        hBux0, smul_eq_mul, mul_one, zero_add]
    have hwperp : w ∉ B.orthogonal U := by
      intro hmem
      have hzero : B w x0 = 0 := by
        rw [← hB.neg_eq x0 w, (LinearMap.BilinForm.mem_orthogonal_iff.mp hmem) x0 hx0U,
          neg_zero]
      rw [hBw] at hzero
      exact hl0 hzero
    have hBvw : B v w = 1 := by
      rw [hwdef, map_add, hBvw', map_smul, hvu0, smul_zero, add_zero]
    have hpol : polar Q w' u0 = B w' u0 := by
      change polar Q w' u0 = polarBilin Q w' u0
      rw [polarBilin_apply_apply]
    have hQw : Q w ≠ 0 := by
      intro h
      rw [hwdef, QuadraticMap.map_add Q, map_smul_eq_sq, polar_smul_right_eq Q l w' u0,
        hpol, hw'u0, mul_zero, add_zero] at h
      have h1 : l ^ 2 * Q u0 = -Q w' := by linear_combination h
      rw [CharTwo.neg_eq] at h1
      exact hlQ h1
    have hTw : Tsp hB w 1 ∈ H := hcase2 w hQw 1
    have hgv : (Tsp hB w 1).app v = v + w := by
      rw [Tsp_app, hBvw, mul_one, one_smul]
    have hvwperp : v + w ∉ B.orthogonal U := by
      intro hmem
      have hzero : B (v + w) x0 = 0 := by
        rw [← hB.neg_eq x0 (v + w),
          (LinearMap.BilinForm.mem_orthogonal_iff.mp hmem) x0 hx0U, neg_zero]
      have hone : B (v + w) x0 = l := by
        rw [map_add, LinearMap.add_apply, hvx0, hBw, zero_add]
      rw [hone] at hzero
      exact hl0 hzero
    have hTvw : Tsp hB (v + w) c ∈ H := by
      by_cases hq : Q (v + w) = 0
      · exact hcase3 (v + w) hq hvwperp c
      · exact hcase2 (v + w) hq c
    have hgvTsp : Tsp hB ((Tsp hB w 1).app v) c ∈ H := by
      rw [hgv]
      exact hTvw
    exact Tsp_mem_of_app_mem hB hTw hgvTsp
  exact eq_top_of_forall_Tsp_mem hB hQ fun v c => by
    by_cases hv : Q v = 0
    · by_cases hperp : v ∈ B.orthogonal U
      · exact hcase4 v hv hperp c
      · exact hcase3 v hv hperp c
    · exact hcase2 v hv c

end CFSG.StandardType.SpNsRootGen

end
