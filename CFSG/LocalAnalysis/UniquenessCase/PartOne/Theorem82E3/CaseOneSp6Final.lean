module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneSp6Dichotomy
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneLieExit
import CFSG.LocalAnalysis.StronglyEmbedded.GammaOne
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneSp6Wreath

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326 (K326P2S ZWr z2Of)
open CFSG.LocalAnalysis.UniquenessCase.PartOne
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
  (K6c K7 LieFam811 IsLie811 IsSignedCoords qPlusPi)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Case811Sylow

variable {c : Ctx82E3 D}

theorem sp6Excluded_of_inputs (h : Case811Sylow c) (hK6c : K6c) (hK7 : K7)
    (hN7 : K7Sp6Planes) (hN8 : K7Sp6Weight3) (hD1 : Sp6SylowWreath) (hK326 : K326P2S) :
    h.Sp6Excluded := by
  intro f p hlie hp hpq _
  obtain ⟨s⟩ := SignedLift.nonempty h hK6c hlie (by intro hh; cases hh)
  have hdvd : ∀ X : Subgroup G, X ≤ h.A → Nat.card X = 3 →
      p ∣ Nat.card (c.L ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) :=
    fun X hXA hXc => h.dvd_card_inf_centralizer_of_k7 hK7 hlie hp hpq hXA hXc
  have hgood : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → (∃ i, v i = 0) → GoodPoint D.M (s.pt v) :=
    fun v hv hz => s.good_of_weight_le_two hN7 hlie hp hpq hv hz
  have h100 : (![1, 0, 0] : Fin 3 → ZMod 3) ≠ 0 := by decide
  have hNA : Subgroup.normalizer (h.A : Set G) ≤ D.M :=
    h.normalizer_A_le hp hdvd (s.pt_mem_A ![1, 0, 0]) (s.orderOf_pt h100)
      (hgood _ h100 ⟨1, rfl⟩)
  have hPG : CFSG.ABGLocalTools.IsSylowOf 3 h.P ⊤ := h.isSylowOf_top (h.normalizer_P_le hNA)
  obtain ⟨n, hn, ⟨e⟩⟩ := h.exists_zwr hD1 hlie
  obtain ⟨w, hw3, hwc, hwΩ⟩ := s.exists_center_weight3 hn e
  obtain ⟨v₁, hv₁, hv₁z, hv₁Z⟩ := s.exists_weight_one_not_mem_z2 hn e
  have hgw : GoodPoint D.M (s.pt w) :=
    s.good_center hK326 hN8 hlie hp hpq hdvd hn e hPG hNA hgood hv₁ hv₁z hv₁Z hw3 hwc hwΩ
  have hall : ∀ X : Subgroup G, X ≤ h.A → Nat.card X = 3 →
      Subgroup.normalizer (X : Set G) ≤ D.M ∧
        p ∣ Nat.card (Subgroup.normalizer (X : Set G)) := by
    intro X hXA hXc
    have hdvdN : p ∣ Nat.card (Subgroup.normalizer (X : Set G)) :=
      (hdvd X hXA hXc).trans (Subgroup.card_dvd_of_le
        (inf_le_right.trans (Subgroup.centralizer_le_normalizer _)))
    refine ⟨?_, hdvdN⟩
    obtain ⟨v, hv0, rfl⟩ := s.exists_pt_of_card_three hXA hXc
    by_cases hz : ∃ i, v i = 0
    · exact hgood v hv0 hz
    · push Not at hz
      let ε : Fin 3 → ZMod 3 := fun i => v i * (w i)⁻¹
      have hε : ∀ i, ε i ≠ 0 := fun i => mul_ne_zero (hz i) (inv_ne_zero (hw3 i))
      obtain ⟨g, -, hg⟩ := s.exists_conj 1 ε hε
      have hgM : (g : G) ∈ D.M := c.hyp81.1 g.2
      have hc := hgw.conj hgM
      rw [hg w] at hc
      have hv : (fun i => ε i * w ((1 : Equiv.Perm (Fin 3)) i)) = v := by
        funext i
        simp [ε, hw3 i]
      rwa [hv] at hc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  have hΓ : CFSG.Open.rankThreeGamma 1 3 h.A ≤ D.M :=
    CFSG.RankThree.PartOne.IsStronglyPEmbedded.rankThreeGamma_one_le (p := p) (q := 3)
      (M := D.M) (A := h.A) (c.isStronglyPEmbedded_of_mem_sigma hp) h.elemAbelian.isPGroup hall
  exact h.not_rankThreeGamma_le hΓ

end Case811Sylow

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
