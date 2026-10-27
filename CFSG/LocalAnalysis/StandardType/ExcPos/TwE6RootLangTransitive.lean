module

public import CFSG.LocalAnalysis.StandardType.ExcPos.StableOppositePairLang
public import CFSG.LocalAnalysis.StandardType.ExcPos.UnitDefs
import CFSG.RankThree.Chevalley.SteinbergBNG2QPlusLocalCore
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField

public noncomputable section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.GGFinModel


theorem langDatum_step_mem_adjointGroup {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    (D : LangDatum τ L) {g : ModGL τ L} (hg : g ∈ adjointGroup τ L) :
    D.step g ∈ adjointGroup τ L := by
  obtain ⟨Fr, -, P, hP, hΦ⟩ := D.steinberg
  obtain ⟨w, hn⟩ := D.n_weyl
  have hn' : D.n ∈ adjointGroup τ L := hn ▸ canonicalRep_mem_adjointGroup _ L w
  have hFg : Units.map (entrywiseHom Fr) g ∈ adjointGroup τ L :=
    CFSG.RankThree.Chevalley.SteinbergBN.units_map_entrywiseHom_mem_adjointGroup Fr hg
  have hP' : P * Units.map (entrywiseHom Fr) g * P⁻¹ ∈ adjointGroup τ L := by
    rcases hP with rfl | ⟨t, h, rfl⟩
    · simpa using hFg
    · subst h
      have h1 := conj_mem_adjointGroup_of_map_eq (Q := diagramMap t L ^ (1 : ℤ))
        (map_conj_diagramMap_zpow (L := L) t 1) _ hFg
      rw [zpow_one] at h1
      exact h1
  show D.n * D.Φ g * D.n⁻¹ ∈ adjointGroup τ L
  rw [hΦ g]
  exact mul_mem (mul_mem hn' hP') (inv_mem hn')

theorem langDatum_step_eq_frobTwistGL {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {r e : ℕ}
    [Fact r.Prime] [CharP L r] (D : LangDatum τ L) (hq : D.q = r ^ e) :
    ∃ Q : ModGL τ L, ∀ g, D.step g = frobTwistGL τ L r e Q g := by
  obtain ⟨Fr, hFr, P, -, hΦ⟩ := D.steinberg
  have hFrE : Fr = iterateFrobenius L r e :=
    RingHom.ext fun c => by rw [hFr, iterateFrobenius_def, hq]
  refine ⟨D.n * P, fun g => ?_⟩
  rw [frobTwistGL_apply]
  show D.n * D.Φ g * D.n⁻¹ = _
  rw [hΦ g, hFrE]
  change D.n * (P * entrywiseFrobGL τ L r e g * P⁻¹) * D.n⁻¹ = _
  group

theorem exists_conj_stableOppositePair {f : ℕ} (hf : 1 ≤ f) (Δ : LangDatum Tag.E6 GGL)
    (hq : Δ.q = 2 ^ f) {α α' : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (hα' : IsRoot Tag.E6 α') {w w' : ModGL Tag.E6 GGL} (hw : w ∈ adjointGroup Tag.E6 GGL)
    (hw' : w' ∈ adjointGroup Tag.E6 GGL)
    (h1 : (excCurve α w).map Δ.step = excCurve α w)
    (h2 : (excCurve (-α) w).map Δ.step = excCurve (-α) w)
    (h1' : (excCurve α' w').map Δ.step = excCurve α' w')
    (h2' : (excCurve (-α') w').map Δ.step = excCurve (-α') w') :
    ∃ h ∈ Δ.model, (excCurve α w).map (MulAut.conj h).toMonoidHom = excCurve α' w' ∧
      (excCurve (-α) w).map (MulAut.conj h).toMonoidHom = excCurve (-α') w' := by
  obtain ⟨Q, hQ⟩ := langDatum_step_eq_frobTwistGL (r := 2) (e := f) Δ hq
  have hstep : Δ.step = frobTwistGL Tag.E6 GGL 2 f Q := MonoidHom.ext hQ
  have hFA : ∀ g ∈ adjointGroup Tag.E6 GGL,
      frobTwistGL Tag.E6 GGL 2 f Q g ∈ adjointGroup Tag.E6 GGL := by
    intro g hg
    rw [← hstep]
    exact langDatum_step_mem_adjointGroup Δ hg
  rw [hstep] at h1 h2 h1' h2'
  obtain ⟨h, hh, hfix, hc1, hc2⟩ := exists_frobTwist_fixed_conj_opposite_pair (Or.inl rfl) 2 hf Q hFA
    hα hα' hw hw' h1 h2 h1' h2'
  refine ⟨h, Δ.mem_model.2 ⟨hh, ?_⟩, hc1, hc2⟩
  have hs : Δ.step h = h := (hQ h).trans hfix
  exact hs

end CFSG.StandardType.LieKnownR2.ExcPos
