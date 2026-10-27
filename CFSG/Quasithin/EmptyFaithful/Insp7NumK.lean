module

public import CFSG.Quasithin.EmptyFaithful.Insp7NumH
public import CFSG.RankThree.PartTwo.KFacts.AutSz
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115EvenL2
public import Certificates.Certificate113
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped MatrixGroups

namespace Insp7

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

@[expose] def TwoInner (L : Type) [Group L] : Prop :=
  ∀ (α : MulAut L) (m : ℕ), α ^ (2 ^ m) = 1 → α ∈ Inn L

theorem TwoInner.of_mulEquiv {L S : Type} [Group L] [Group S] (e : L ≃* S) (h : TwoInner S) :
    TwoInner L := by
  intro α m hα
  have h1 : (MulAut.congr e α) ^ (2 ^ m) = 1 := by
    rw [← map_pow, hα, map_one]
  have h2 := h _ m h1
  have h3 := CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e
  rw [← h3] at h2
  obtain ⟨β, hβ, hβα⟩ := h2
  have : β = α := (MulAut.congr e).injective hβα
  rw [← this]
  exact hβ

theorem card_dvd_of_twoInner {L Gc : Type} [Group L] [Finite L] [Group Gc]
    (ρ : Gc →* MulAut L) (hρ : Function.Injective ρ) (h : TwoInner L) (Ŝ : Subgroup Gc)
    (hŜ : IsPGroup 2 Ŝ) : Nat.card Ŝ ∣ Nat.card L := by
  have hle : Ŝ.map ρ ≤ Inn L := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨m, hm⟩ := hŜ ⟨x, hx⟩
    have h1 : x ^ (2 ^ m) = 1 := congrArg Subtype.val hm
    apply h _ m
    rw [← map_pow, h1, map_one]
  have h1 : Nat.card (Ŝ.map ρ) ∣ Nat.card (Inn L) := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective hρ] at h1
  have h2 : Nat.card (Inn L) = Nat.card (L ⧸ Subgroup.center L) := by
    rw [← ker_conj_eq_center]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange (MulAut.conj : L →* MulAut L)).toEquiv).symm
  rw [h2] at h1
  exact h1.trans (Subgroup.index_dvd_card (Subgroup.center L))

theorem numFactAt_of_twoInner {F : ∀ (L : Type) [Group L], Prop}
    (hF : ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → F L →
      TwoInner L ∧ ¬ 2 ^ 7 ∣ Nat.card L) : NumFactAt F := by
  intro L _ _ hq hFL z _ _ Gc _ _ ρ hρ _ ž _ Ŝ hŜ2 _ _ hcard
  exfalso
  obtain ⟨hT, hn⟩ := hF L hq hFL
  have h1 := card_dvd_of_twoInner ρ hρ hT Ŝ hŜ2
  apply hn
  rcases hcard with hc | hc
  · rw [hc] at h1; exact h1
  · rw [hc] at h1
    exact (Nat.pow_dvd_pow 2 (by norm_num : 7 ≤ 8)).trans h1

theorem card_ringAut_of_card_two_pow {K : Type} [Field K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) : Nat.card (RingAut K) = n := by
  have h1 := (even_SL2_full_automorphism_semilinear_model (F := K) (n := n) hn hK).2.2.2.1
  rw [← h1]
  exact (Nat.card_congr (outerEquivRingAut (F := K) (n := n) hK).toEquiv).symm

theorem twoInner_suzuki {a : ℕ} {K : Type} [Field K] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : TwoInner (suzukiGroup a K) := by
  intro α m hα
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨g, σ, hασ⟩ := CFSG.RankThree.PartTwo.KFacts.exists_conj_mul_szFieldAut ha hK α
  have hcard : Nat.card (RingAut K) = 2 * a + 1 := card_ringAut_of_card_two_pow (by omega) hK
  have hσ : σ ^ (2 * a + 1) = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  let τ := CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.szFieldAut a K σ
  have hτ : τ ^ (2 * a + 1) = 1 := by
    show (CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.szFieldAut a K σ) ^ (2 * a + 1) = 1
    rw [← map_pow, hσ, map_one]
  let π : MulAut (suzukiGroup a K) →* MulAut (suzukiGroup a K) ⧸ Inn (suzukiGroup a K) :=
    QuotientGroup.mk' _
  have h1 : π α = π τ := by
    rw [hασ, map_mul]
    have : π (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
    rw [this, one_mul]
  have h2 : π α ^ (2 ^ m) = 1 := by rw [← map_pow, hα, map_one]
  have h3 : π α ^ (2 * a + 1) = 1 := by rw [h1, ← map_pow, hτ, map_one]
  have hcop : Nat.gcd (2 ^ m) (2 * a + 1) = 1 :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr (by exact ⟨a, rfl⟩))
  have h4 : π α ^ (Nat.gcd (2 ^ m) (2 * a + 1)) = 1 := pow_gcd_eq_one.mpr ⟨h2, h3⟩
  rw [hcop, pow_one] at h4
  exact (QuotientGroup.eq_one_iff _).mp h4

theorem numFactAt_sz8 : NumFactAt (fun L _ => SuzukiModel L 2 3) :=
  numFactAt_of_twoInner fun L _ _ _ hF => by
    obtain ⟨-, a, ha, K, _, hKfin, hf, hKc, ⟨e⟩⟩ := hF
    have ha1 : a = 1 := by omega
    subst ha1
    have hK : Nat.card K = 2 ^ (2 * 1 + 1) := hKc
    refine ⟨TwoInner.of_mulEquiv e (twoInner_suzuki ha hK), ?_⟩
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
    norm_num

end Insp7

end CFSG.Quasithin
