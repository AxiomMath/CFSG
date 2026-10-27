module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixDefs
public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate120
public import Certificates.Certificate123
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFixGapTriD4
import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownChevGeom
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldVacOther

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.GLTheoremA


theorem ggRawFieldFixStd_triD4_recipe {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (r : ℕ) :
    GGRawFieldFixStd p ⟨.triD4, r, n / p⟩ (GGTriD4R n K) (GGTriD4ID n K)
      (LargeEvenChevFieldImage LargeEvenCartanD4 K
        (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)) := by
  intro hS hna f hf hord
  have hF := Y10GField.innFree_of_ggRawInnField
    (RawAutTri.ggRawInnField_triD4 hn K hK hp.one_lt.ne') hS hna
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    omega
  have hchev : ChevalleyExceptionalModel (GGTriD4R n K) .trialityD4 2 n :=
    ⟨⟨Nat.prime_two, hn, rfl⟩, twistedChevalleyModel_largeEven .D4 hK⟩
  obtain ⟨K', _, _, σ, hcard', hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hn hchev.2
  have hfp : f ^ p = 1 := hord ▸ pow_orderOf_eq_one f
  have hβp : MulAut.congr e f ^ p = 1 := by rw [← map_pow, hfp, map_one]
  have hβout : MulAut.congr e f ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (graphFixedRootGroup TwistTag.D4 K' σ.toRingHom) :=
    fun hin => hF f hf hord ((FQ.congr_mem_range_conj e f).1 hin)
  obtain ⟨f₀, k₀, hk₀F, hk₀fin, σ₀, hf0, hk₀card, hσ₀, hp3', ⟨eα⟩⟩ :=
    FR.trialityD4_outer_fixed_equiv Nat.prime_two hn hp hp5 K' hcard' σ hσ (MulAut.congr e f)
      hβp hβout
  have hf1 : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h0 | h0
    · rw [h0, mul_zero] at hf0
      omega
    · exact h0
  have hdiv : n / p = f₀ := by rw [hf0, Nat.mul_div_cancel_left _ hp.pos]
  obtain ⟨σ', hσ'', hσ'ord, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two hf1 k₀ hk₀card
  obtain ⟨eR⟩ := FR.recipe_equiv_graph k₀ f₀ hf1 hk₀card σ' hσ''
  have e₁ : ↥(FP.fixSub f) ≃* ↥(graphFixedRootGroup TwistTag.D4 k₀ σ₀.toRingHom) :=
    (FR.fixSubEquivCongr e f).trans eα
  have hj : p % 3 = 1 ∨ p % 3 = 2 := by omega
  have e₂ : Nonempty (↥(graphFixedRootGroup TwistTag.D4 k₀ σ₀.toRingHom) ≃*
      ↥(graphFixedRootGroup TwistTag.D4 k₀ σ'.toRingHom)) := by
    rcases hj with hj | hj
    · have : σ₀ = σ' := RingEquiv.ext fun c => by rw [hσ₀, hσ'', hj, pow_one]
      subst this
      exact ⟨MulEquiv.refl _⟩
    · have hσ3 : σ' ^ 3 = 1 := by
        have := pow_orderOf_eq_one σ'
        rwa [hσ'ord] at this
      obtain ⟨eo⟩ := FR.graph_orientation_equiv k₀ σ' hσ3
      have : σ₀ = σ' ^ 2 := RingEquiv.ext fun c => by
        rw [hσ₀, hj, show (σ' ^ 2) c = σ' (σ' c) by rw [pow_two]; rfl, hσ'', hσ'', sq (2 ^ f₀),
          pow_mul]
      subst this
      exact ⟨eo.symm⟩
  obtain ⟨e₂⟩ := e₂
  rw [hdiv]
  have hchev₀ : ChevalleyExceptionalModel
      (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 k₀ LargeEvenRhoD4 f₀))
      .trialityD4 2 f₀ :=
    ⟨⟨Nat.prime_two, hf1, rfl⟩, twistedChevalleyModel_largeEven .D4 hk₀card⟩
  obtain ⟨hs₀, hna₀⟩ := Y10GField.triD4_model_simple hchev₀
  have := hS
  have := hs₀
  have hZ : Subgroup.center (GGTriD4R n K) = ⊥ := by
    refine TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative fun h => ?_
    obtain ⟨a, b, hab⟩ := hna
    exact hab (h.is_comm.comm a b)
  have hfix : FP.fixSub f = ggFixSub f := Subgroup.ext fun _ => Iff.rfl
  obtain ⟨θ₀, hθ₀⟩ := ggFixGeom_of_inn hna₀ hZ
    (fun φ hφ => TableBExcSmallRest.chevIDImage_subset_inn_triD4 hn K hK hφ)
    (fun _ ⟨x, hx⟩ => hx ▸ conj_mem_chevIDImage _ x)
    (((e₁.trans e₂).trans eR.symm).symm.trans (MulEquiv.subgroupCongr hfix))
  exact ⟨k₀, inferInstance, inferInstance, hk₀card, hs₀, hna₀, θ₀, hθ₀⟩

theorem ggFieldFixKnown_triD4 : GGFieldFixKnown fun p lab => lab.tag = .triD4 ∧ p ≠ 3 := by
  intro p lab hp hp2 hlab ⟨ht, hp3⟩
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  exact recipeTwisted_and (fun K _ _ hK => ggRawFieldFixStd_triD4_recipe hn hK hp hp2 hp3 l) hQ

end CFSG.StandardType

end
