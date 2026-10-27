module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNInvol
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
public import Certificates.Certificate8033
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNF4Frame
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNE6Frame
import CFSG.LocalAnalysis.StandardType.GGIrred937TwE6
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Split
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Exceptional

theorem ggTorusInvolFrameElt_twE6Three
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (h3 : 3 ∣ 2 ^ n - 1) : GGTorusInvolFrameElt 3 4 (TwE6Delta.RecipeR K n) := by
  have : CharP K 2 := charP_two_of_card (show Nat.card K = 2 ^ (n * 2) by rw [hK, pow_mul])
  set σ : K →+* K := iterateFrobenius K 2 n
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  have := Fintype.ofFinite K
  have := Fintype.ofFinite (GaloisField 2 (2 * n))
  have hcard : Fintype.card (GaloisField 2 (2 * n)) = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      CFSG.LieType.Universal.card_galoisField_two_mul 2 n hn, hK]
  set τ := FiniteField.ringEquivOfCardEq hcard
  have hτ : ∀ c : GaloisField 2 (2 * n), τ (frobQ 2 n c) = σ (τ c) := fun c => by
    rw [frobQ_apply, hσ, map_pow]
  obtain ⟨e⟩ := TwE6Rank.exists_mulEquiv_graphFixedRootGroup (K := K) hn hK σ hσ
  obtain ⟨e₂⟩ := Irred937.graphFixedRootGroup_mulEquiv_of_ringEquiv τ (frobQ 2 n) σ
    fun c => (hτ c).symm
  have h3' : ¬ 3 ∣ 2 ^ n + 1 := fun h => by
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  refine ggTorusInvolFrameElt_of_mulEquiv (e.trans e₂.symm) ?_
  obtain ⟨ζ, hζ, -, hζo, -⟩ := ExcFrames.exists_threeFrame hn h3'
  choose m hm using fun i => Irred937.exists_normalizer_realization_twE6 hn h3' hζo hζ i
  exact ggTorusInvolFrameElt_of_conj (ExcFrames.twE6ThreeFrameHom hn h3' ζ hζ)
    (ExcFrames.twE6ThreeFrameHom_injective hn h3' hζo hζ)
    (exists_involFrame_torusAct_F4 Nat.prime_three (by decide) _ m hm)
    fun E hE hr _ hsc => ExcFrames.twistedE6ThreeSCReference_holds hn h3' hζo hζ hE hr
      fun c hc hc3 => hsc c (fun x hx => ((Subgroup.mem_centralizer_iff.mp hc) x hx).symm) hc3

theorem ggTorusInvolFrameElt_twE6Split
    {K : Type} [Field K] [Finite K] {n p : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n - 1) (r : ℕ) :
    GGTorusInvolFrameElt p r (TwE6Delta.RecipeR K n) := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨k, _, _, _, ι, hk, hι⟩ := exists_injective_f4_recipeR hn hK
  have hpk : p ∣ Nat.card k - 1 := by rw [hk]; exact hpn
  have := TwE6Delta.finite_recipeR (K := K) hK
  obtain ⟨s, m, hs, hm⟩ := exists_order_p_inverting_sl2_split hp hp2 hpk
  obtain ⟨e, he, s₁, ⟨h₁, h₁', w₁, hw₁⟩, s₂, ⟨h₂, h₂', w₂, hw₂⟩, h4⟩ :=
    exists_involFrame_F4 hp hp2 hs hm
  have hinj : Function.Injective (ι.comp e) := hι.comp he
  have hcard : Nat.card (ι.comp e).range = p ^ 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hw : ∀ (w : adjointGroup .F4 k) (t : MulAut (Multiplicative (Fin 4 → ZMod p))),
      (∀ f, w * e f * w⁻¹ = e (t f)) → ∀ f, ι w * (ι.comp e) f * (ι w)⁻¹ = (ι.comp e) (t f) :=
    fun w t h f => by rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_mul,
      ← map_mul, h]
  exact ggTorusInvolFrameElt_of_conj (ι.comp e) hinj
    ⟨s₁, ⟨h₁, h₁', ι w₁, hw w₁ s₁ hw₁⟩, s₂, ⟨h₂, h₂', ι w₂, hw w₂ s₂ hw₂⟩, h4⟩
    fun E hE _ _ hsc => exists_conj_eq_of_selfCentralizing_of_sylowTorus hp
      (sylowTorus_recipeR_split hn hK hp hp5 hpn) (ExcFrames.isElemAbelian_range_frame _) hcard
      hE hsc

end CFSG.StandardType

end
