module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusLift
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6ThreeTorus
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6ThreeSC
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6ThreeNormalizer
import CFSG.LocalAnalysis.StandardType.GGIrred937TwE6
import CFSG.LocalAnalysis.StandardType.GGIrred937TwE6Transport
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6RankOuter
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937TwE6Inn
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937TwE6Center
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6SplitLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional

private theorem excPlusFrameModelOn_twE6Three_gf
    {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1) :
    GGExcPlusFrameModelOn .F4 3 4
      (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) := by
  classical
  obtain ⟨ζ, hζ, -, hζo, -⟩ := ExcFrames.exists_threeFrame hf h3
  have hFinj := ExcFrames.twE6ThreeFrameHom_injective hf h3 hζo hζ
  choose m hm using fun i => Irred937.exists_normalizer_realization_twE6 hf h3 hζo hζ i
  intro E hE hcard hsc
  have hEsc : ∀ c ∈ Subgroup.centralizer (E : Set
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))), c ^ 3 = 1 →
        c ∈ E :=
    fun c hc hc3 => hsc c (fun e he => (Subgroup.mem_centralizer_iff.mp hc e he).symm) hc3
  obtain ⟨c, hc⟩ := ExcFrames.twistedE6ThreeSCReference_holds hf h3 hζo hζ hE hcard hEsc
  refine ⟨(MulAut.conj c).toMonoidHom.comp (ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ),
    fun i => c * m i * c⁻¹, (MulAut.conj c).injective.comp hFinj,
    by rw [MonoidHom.range_comp, hc], ?_, ?_⟩
  · intro i s
    have h1 := hm i s
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← h1]
    group
  · intro g hg
    rw [hc, ← Subgroup.map_equiv_normalizer_eq] at hg
    obtain ⟨x, hx, rfl⟩ := hg
    have hxs : ∀ s, x * ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ s * x⁻¹ ∈
        (ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ).range :=
      fun s => (Subgroup.mem_normalizer_iff.mp hx _).mp ⟨s, rfl⟩
    have hxM := ExcFrames.mem_graphFixedRootMonomial_of_normalizes_twE6ThreeFrame hf h3 hζo hζ hxs
    refine ⟨foldedWeylEquiv TwistTag.E6
      ⟨graphFixedRootWeylHom TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)
        ⟨(x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hxM⟩,
        (graphFixedRootWeylHom_range TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)).le
          ⟨⟨(x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hxM⟩, rfl⟩⟩, fun s => ?_⟩
    have h1 := ExcFrames.twE6ThreeFrameHom_conj hf h3 hζo hζ hxM s
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h2 : x * ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ (Multiplicative.ofAdd s) * x⁻¹ =
        ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ (Multiplicative.ofAdd (TableBExc.torusAct .F4 3
          (foldedWeylEquiv TwistTag.E6
            ⟨graphFixedRootWeylHom TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)
              ⟨(x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hxM⟩,
              (graphFixedRootWeylHom_range TwistTag.E6 (GaloisField 2 (2 * f))
                (frobQ 2 f)).le ⟨⟨(x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hxM⟩,
                  rfl⟩⟩) s)) :=
      Subtype.ext (by simpa using h1)
    rw [show c * x * c⁻¹ * (c * ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ (Multiplicative.ofAdd s) *
        c⁻¹) * (c * x * c⁻¹)⁻¹ =
        c * (x * ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ (Multiplicative.ofAdd s) * x⁻¹) * c⁻¹ by
      group, h2]

theorem ggTorusReflGenW_twE6Three
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (h3 : 3 ∣ 2 ^ n - 1) :
    GGTorusReflGenW 3 4 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  have hchar : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  set σ : K →+* K := iterateFrobenius K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  have := Fintype.ofFinite K
  have := Fintype.ofFinite (GaloisField 2 (2 * n))
  have hcard : Fintype.card (GaloisField 2 (2 * n)) = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      CFSG.LieType.Universal.card_galoisField_two_mul 2 n hn, hK]
  set τ := FiniteField.ringEquivOfCardEq hcard with hτdef
  have hτ : ∀ c : GaloisField 2 (2 * n), τ (frobQ 2 n c) = σ (τ c) := fun c => by
    rw [frobQ_apply, hσ, map_pow]
  obtain ⟨e⟩ := TwE6Rank.exists_mulEquiv_graphFixedRootGroup (K := K) hn hK σ hσ
  obtain ⟨e₂⟩ := Irred937.graphFixedRootGroup_mulEquiv_of_ringEquiv
    (K := GaloisField 2 (2 * n)) (K' := K) τ (frobQ 2 n) σ (fun c => (hτ c).symm)
  have h3' : ¬ 3 ∣ 2 ^ n + 1 := by
    intro h
    have hd : 3 ∣ 2 := by
      have h1 : 3 ∣ 2 ^ n + 1 - (2 ^ n - 1) := Nat.dvd_sub h h3
      have h2 : 2 ^ n + 1 - (2 ^ n - 1) = 2 := by
        have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        omega
      rwa [h2] at h1
    have := Nat.le_of_dvd (by norm_num : 0 < 2) hd
    omega
  exact ggTorusReflGenW_of_excPlusModel Nat.prime_three (by norm_num)
    (ggExcPlusWeylModelSCr_of_frameModelOn Nat.prime_three
      (TwE6Delta.center_recipeR_eq_bot hn hK)
      (fun φ hφ _ => TwE6Delta.recipeI_subset_inn_of_not_dvd hn hK h3' hφ)
      (TwE6Delta.ggCenterPrime_three_twE6 hn hK h3')
      ((excPlusFrameModelOn_twE6Three_gf hn h3').of_mulEquiv (e.trans e₂.symm)))

theorem largeEvenLabelAll_reflGenW_twE6Three
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
      ∃ r, GGTorusLift 3 r R ∧ GGTorusReflGenW 3 r R I) :=
  TwE6Delta.labelAll h.1 fun _ _ _ hK _ _ =>
    ⟨4, ggTorusLift_twE6Dvd_holds hlab.1 hK Nat.prime_three (by norm_num) h.2,
      ggTorusReflGenW_twE6Three hlab.1 hK h.2⟩

end CFSG.StandardType

end
