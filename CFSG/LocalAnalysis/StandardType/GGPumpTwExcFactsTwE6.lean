module

public import CFSG.LocalAnalysis.StandardType.GGPumpTwExcTwE6
public import CFSG.LocalAnalysis.StandardType.GGR4PumpTwKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGTableB
import CFSG.LocalAnalysis.StandardType.GGL45E67Center
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6RankOuter
import CFSG.LocalAnalysis.StandardType.GGIrred937TwE6Transport
import CFSG.LocalAnalysis.StandardType.GGF4AutWeyl
import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcOutdiag

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional

private theorem l04fHE4b_autOrderAt_of_mulEquiv {p : ℕ} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') (h : KGA.GGF4AutOrderAt p R') : KGA.GGF4AutOrderAt p R := by
  intro E hE hr
  let E' := E.map e.toMonoidHom
  have hE' : IsElemAbelian p E' := TableB.isElemAbelian_map hE e.toMonoidHom
  have hcardE : Nat.card E' = Nat.card E := Subgroup.card_map_of_injective e.injective
  have hr' : p ^ 4 ≤ Nat.card E' := hr.trans hcardE.ge
  obtain ⟨hcard', h1152'⟩ := h E' hE' hr'
  refine ⟨hcardE.symm.trans hcard', ?_⟩
  have hmap := F4AutWeyl.ggAutomizer_map_eq e.injective ⊤ E
    (show E.map e.toMonoidHom = E' from rfl)
  rw [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at hmap
  have hcardAut : Nat.card (ggAutomizer ⊤ E') = Nat.card (ggAutomizer ⊤ E) := by
    rw [hmap]
    exact Subgroup.card_map_of_injective (MulAut.congr _).injective
  exact hcardAut.symm.trans h1152'

private theorem l04fHE4b_autOrderAt_recipe
    {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (h3 : ¬ 3 ∣ 2 ^ f + 1) :
    KGA.GGF4AutOrderAt 3 (TwE6Delta.RecipeR K f) := by
  have hchar : CharP K 2 := charP_two_of_card (m := f * 2) (by rw [hK, pow_mul])
  have := Fintype.ofFinite K
  have := Fintype.ofFinite (GaloisField 2 (2 * f))
  set σ : K →+* K := iterateFrobenius K 2 f with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ f := fun c => iterateFrobenius_def 2 f c
  have hcard : Fintype.card (GaloisField 2 (2 * f)) = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf, hK]
  set τ := FiniteField.ringEquivOfCardEq hcard with hτdef
  have hτ : ∀ c : GaloisField 2 (2 * f), τ (frobQ 2 f c) = σ (τ c) := fun c => by
    rw [frobQ_apply, hσ, map_pow]
  obtain ⟨e⟩ := TwE6Rank.exists_mulEquiv_graphFixedRootGroup (K := K) (n := f) hf hK σ hσ
  obtain ⟨e₂⟩ := Irred937.graphFixedRootGroup_mulEquiv_of_ringEquiv
    (K := GaloisField 2 (2 * f)) (K' := K) τ (frobQ 2 f) σ (fun c => (hτ c).symm)
  have hgf : KGA.GGF4AutOrderAt 3
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) :=
    ggPumpTwExc_autOrderAt_twE6 hf h3
  have hKσ : KGA.GGF4AutOrderAt 3 ↥(graphFixedRootGroup TwistTag.E6 K σ) :=
    l04fHE4b_autOrderAt_of_mulEquiv e₂.symm hgf
  exact l04fHE4b_autOrderAt_of_mulEquiv e hKσ

theorem ggPumpTwExc_facts_twE6
    {f : ℕ} (hf : 1 ≤ f) (h3 : 3 ∣ 2 ^ f - 1) :
    LargeEvenLabelAll ⟨.twE6, 0, f⟩ fun R _ I _ =>
      Subgroup.center R = ⊥ ∧ GGCenterPrime 3 R ∧ GGOutdiagPrime 3 R I ∧
        KGA.GGF4AutOrderAt 3 R := by
  refine TwE6Delta.labelAll rfl ?_
  intro K _ _ hK
  have h3' : ¬ 3 ∣ 2 ^ f + 1 := by
    intro h
    have hd : 3 ∣ 2 := by
      have h1 : 3 ∣ 2 ^ f + 1 - (2 ^ f - 1) := Nat.dvd_sub h h3
      have h2 : 2 ^ f + 1 - (2 ^ f - 1) = 2 := by
        have hpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
        omega
      rwa [h2] at h1
    have := Nat.le_of_dvd (by norm_num : 0 < 2) hd
    omega
  have hcop : Nat.Coprime 3 (Nat.gcd 3 (2 ^ f + 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right 3 (2 ^ f + 1))
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3')
  refine ⟨TwE6Delta.center_recipeR_eq_bot hf hK,
    ggCenterPrime_twE6_of_coprime hf hK Nat.prime_three (by norm_num) hcop, ?_, ?_⟩
  · have hsub : TwE6Delta.RecipeI K f ⊆ LargeEvenInnSet (TwE6Delta.RecipeR K f) :=
      chevIDImage_subset_inn fun a ha =>
        CFSG.LocalAnalysis.GLTheoremA.K155X.diagHom_mem_twE6_of_not_three_dvd hf hK h3' ha
    intro φ hφ _
    exact hsub hφ
  · exact l04fHE4b_autOrderAt_recipe hf hK h3'

end CFSG.StandardType

end
