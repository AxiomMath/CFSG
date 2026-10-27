module

public import CFSG.LocalAnalysis.StandardType.GGTwE6SplitRootGenModel
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6RankOuter
public import CFSG.LocalAnalysis.StandardType.GGIrred937TwE6Transport
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6ThreeSC
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Split
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType.TwE6SplitRootGen

open CFSG.Assembly TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional

theorem ggTorusModelAt_recipeR_twE6Split_three
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (h3 : 3 ∣ 2 ^ n - 1) {E : Subgroup (TwE6Delta.RecipeR K n)} (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ 4 ≤ Nat.card E)
    (hsc : ∀ g : TwE6Delta.RecipeR K n, (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E) :
    GGTorusModelAt 3 E := by
  classical
  have hchar : CharP K 2 :=
    charP_two_of_card (show Nat.card K = 2 ^ (n * 2) by rw [hK, pow_mul])
  set σ : K →+* K := iterateFrobenius K 2 n
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  have := Fintype.ofFinite K
  have := Fintype.ofFinite (GaloisField 2 (2 * n))
  have hcardK : Fintype.card (GaloisField 2 (2 * n)) = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      CFSG.LieType.Universal.card_galoisField_two_mul 2 n hn, hK]
  set τ := FiniteField.ringEquivOfCardEq hcardK
  have hτ : ∀ c : GaloisField 2 (2 * n), τ (frobQ 2 n c) = σ (τ c) := fun c => by
    rw [frobQ_apply, hσ, map_pow]
  obtain ⟨e⟩ := TwE6Rank.exists_mulEquiv_graphFixedRootGroup (K := K) hn hK σ hσ
  obtain ⟨e₂⟩ := Irred937.graphFixedRootGroup_mulEquiv_of_ringEquiv (K := GaloisField 2 (2 * n))
    (K' := K) τ (frobQ 2 n) σ fun c => (hτ c).symm
  have h3' : ¬ 3 ∣ 2 ^ n + 1 := fun h => by
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  obtain ⟨ζ, hζ, -, hζo, -⟩ := ExcFrames.exists_threeFrame hn h3'
  have hζσ : frobQ 2 n (ζ : GaloisField 2 (2 * n)) = (ζ : GaloisField 2 (2 * n)) := by
    rw [frobQ_apply]
    obtain ⟨k, hk⟩ := h3
    have hone : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hpow : 2 ^ n = 3 * k + 1 := by omega
    have hζ3 : (ζ : GaloisField 2 (2 * n)) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]
    rw [hpow, pow_succ, pow_mul, hζ3, one_pow, one_mul]
  let φ : TwE6Delta.RecipeR K n ≃*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * n))
        (frobQ 2 n)) := e.trans e₂.symm
  let E' : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * n))
      (frobQ 2 n)) := E.map φ.toMonoidHom
  have hE' : IsElemAbelian 3 E' := CFSG.Open.IsElemAbelian.map hE φ.toMonoidHom
  have hcard' : 3 ^ 4 ≤ Nat.card E' := by
    show 3 ^ 4 ≤ Nat.card (E.map φ.toMonoidHom)
    rw [Subgroup.card_map_of_injective φ.injective]
    exact hcard
  have hsc' : ∀ c ∈ Subgroup.centralizer (E' : Set
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * n)) (frobQ 2 n))),
      c ^ 3 = 1 → c ∈ E' := by
    intro c hc hc3
    obtain ⟨g, rfl⟩ := φ.surjective c
    show φ g ∈ E.map φ.toMonoidHom
    refine Subgroup.mem_map_of_mem φ.toMonoidHom (hsc g ?_ ?_)
    · intro x hx
      refine φ.injective ?_
      rw [map_mul, map_mul]
      exact ((Subgroup.mem_centralizer_iff.mp hc) (φ x) (Subgroup.mem_map_of_mem _ hx)).symm
    · refine φ.injective ?_
      rw [map_pow, hc3, map_one]
  obtain ⟨c, hc⟩ := ExcFrames.twistedE6ThreeSCReference_holds hn h3' hζo hζ hE' hcard' hsc'
  have hframe : ExcFrames.twE6ThreeFrameHom hn h3' ζ hζ =
      ExcFrames.twE6SplitFrameHom (frobQ 2 n) ζ hζ hζσ := by
    refine MonoidHom.ext fun s => Subtype.ext ?_
    rfl
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmodel' : GGTorusModelAt 3 E' := by
    rw [hc, hframe]
    exact (ggTorusModelAt_range_twE6SplitFrameHom (K := GaloisField 2 (2 * n))
      (frobQ 2 n) (by decide) hζo hζ hζσ).map (MulAut.conj c)
  have hback : E'.map φ.symm.toMonoidHom = E := by
    show (E.map φ.toMonoidHom).map φ.symm.toMonoidHom = E
    rw [Subgroup.map_map]
    have hcomp : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id _ := by
      ext x
      exact φ.symm_apply_apply x
    rw [hcomp, Subgroup.map_id]
  rw [← hback]
  exact hmodel'.map φ.symm

end CFSG.StandardType.TwE6SplitRootGen

end
