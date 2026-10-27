module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerThree
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTailDFour
import CFSG.Timmesfeld.Orders.Classical
import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.Adapters.StatedClassicalUnitaryOrders
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.Sporadic.M23.M23Group
import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Arith

theorem ggAKFL_bound_of_ordSL {d a k r : ℕ} (hd : 2 ≤ d) (hr : Nat.Coprime 2 r)
    (h : (2 ^ a) ^ (d * (d - 1) / 2) * (∏ j ∈ Finset.Icc 2 d, ((2 ^ a) ^ j - 1)) /
      Nat.gcd d (2 ^ a - 1) = 2 ^ k * r) : a * (d * (d - 1) / 2) ≤ k := by
  have hgP : Nat.gcd d (2 ^ a - 1) ∣ ∏ j ∈ Finset.Icc 2 d, ((2 ^ a) ^ j - 1) := by
    refine (Nat.gcd_dvd_right _ _).trans ?_
    have h2 : (2 ^ a) ^ 2 - 1 ∣ ∏ j ∈ Finset.Icc 2 d, ((2 ^ a) ^ j - 1) :=
      Finset.dvd_prod_of_mem (fun j => (2 ^ a) ^ j - 1) (Finset.mem_Icc.mpr ⟨le_rfl, hd⟩)
    refine dvd_trans ?_ h2
    simpa using Nat.sub_dvd_pow_sub_pow (2 ^ a) 1 2
  have h' := h
  rw [Nat.mul_div_assoc _ hgP] at h'
  have hdvd : 2 ^ (a * (d * (d - 1) / 2)) ∣ 2 ^ k * r := by
    rw [pow_mul]
    exact Dvd.intro _ h'
  have hcop : Nat.Coprime (2 ^ (a * (d * (d - 1) / 2))) r := Nat.Coprime.pow_left _ hr
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right hdvd)

theorem ggAKFL_choose_two_le {d t s : ℕ} (hdt : t ≤ d) (hts : 2 * s ≤ t * (t - 1)) :
    s ≤ d * (d - 1) / 2 := by
  have h : t * (t - 1) ≤ d * (d - 1) := Nat.mul_le_mul hdt (Nat.sub_le_sub_right hdt 1)
  exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)

theorem ggAKFL_ordSL_ne_altSix {d a : ℕ} (hd : 2 ≤ d) (ha : 1 ≤ a) :
    (2 ^ a) ^ (d * (d - 1) / 2) * (∏ j ∈ Finset.Icc 2 d, ((2 ^ a) ^ j - 1)) /
      Nat.gcd d (2 ^ a - 1) ≠ 360 := by
  intro h
  have hb := ggAKFL_bound_of_ordSL (k := 3) (r := 45) hd (by norm_num) (h.trans (by norm_num))
  have hd3 : d ≤ 3 := by
    by_contra h4
    have h6 := ggAKFL_choose_two_le (s := 6) (by omega : 4 ≤ d) (by norm_num)
    have := Nat.mul_le_mul ha h6
    omega
  interval_cases d
  · have ha3 : a ≤ 3 := by norm_num at hb; omega
    interval_cases a <;> revert h <;> decide
  · have ha1 : a ≤ 1 := by norm_num at hb; omega
    interval_cases a
    revert h
    decide

theorem ggAKFL_ordSL_ne_uFourTwo {d a : ℕ} (hd : 2 ≤ d) (ha : 1 ≤ a) :
    (2 ^ a) ^ (d * (d - 1) / 2) * (∏ j ∈ Finset.Icc 2 d, ((2 ^ a) ^ j - 1)) /
      Nat.gcd d (2 ^ a - 1) ≠ 25920 := by
  intro h
  have hb := ggAKFL_bound_of_ordSL (k := 6) (r := 405) hd (by norm_num) (h.trans (by norm_num))
  have hd4 : d ≤ 4 := by
    by_contra h5
    have h10 := ggAKFL_choose_two_le (s := 10) (by omega : 5 ≤ d) (by norm_num)
    have := Nat.mul_le_mul ha h10
    omega
  interval_cases d
  · have ha6 : a ≤ 6 := by norm_num at hb; omega
    interval_cases a <;> revert h <;> decide
  · have ha2 : a ≤ 2 := by norm_num at hb; omega
    interval_cases a <;> revert h <;> decide
  · have ha1 : a ≤ 1 := by norm_num at hb; omega
    interval_cases a
    revert h
    decide

theorem ggAKFL_ordSL_ne_dFourTwo {d a : ℕ} (hd : 2 ≤ d) (ha : 1 ≤ a) :
    (2 ^ a) ^ (d * (d - 1) / 2) * (∏ j ∈ Finset.Icc 2 d, ((2 ^ a) ^ j - 1)) /
      Nat.gcd d (2 ^ a - 1) ≠ 174182400 := by
  intro h
  have hb := ggAKFL_bound_of_ordSL (k := 12) (r := 42525) hd (by norm_num)
    (h.trans (by norm_num))
  have hd5 : d ≤ 5 := by
    by_contra h6
    have h15 := ggAKFL_choose_two_le (s := 15) (by omega : 6 ≤ d) (by norm_num)
    have := Nat.mul_le_mul ha h15
    omega
  interval_cases d
  · have ha12 : a ≤ 12 := by norm_num at hb; omega
    interval_cases a <;> revert h <;> decide
  · have ha4 : a ≤ 4 := by norm_num at hb; omega
    interval_cases a <;> revert h <;> decide
  · have ha2 : a ≤ 2 := by norm_num at hb; omega
    interval_cases a <;> revert h <;> decide
  · have ha1 : a ≤ 1 := by norm_num at hb; omega
    interval_cases a
    revert h
    decide

theorem ggAKFL_card_of_uFourTwo {X : Type} [Group X] (h : LieModel X .PSU 4 2 1) :
    Nat.card X = 25920 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_four_two (h.statedClassicalModel (by decide))

theorem ggAKFL_card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

end Arith

section PSL

theorem ggAKFL_card_of_isComponentOf_PSL {G : Type} [Group G] [Finite G] {n f : ℕ}
    {ψ : (ggU .PSL n f).K →* G} {G₀ : Subgroup G}
    (hpres : GGPresentsG0 G₀ (ggU .PSL n f).D .PSL n f ψ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {y : G} (hy : y ^ p = 1) (hdiag : GGPsiInnerDiag (ggU .PSL n f).D ψ y)
    {C : Subgroup G} (hC : IsComponentOf C (G₀ ⊓ Subgroup.centralizer {y})) :
    ∃ d a : ℕ, 2 ≤ d ∧ f ≤ a ∧ Nat.card (↥C ⧸ Subgroup.center ↥C) =
      (2 ^ a) ^ (d * (d - 1) / 2) * (∏ j ∈ Finset.Icc 2 d, ((2 ^ a) ^ j - 1)) /
        Nat.gcd d (2 ^ a - 1) := by
  obtain ⟨⟨hadm, hrk⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  obtain ⟨-, hf, hn, -⟩ := hadm
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [← hrange, ← ggCentralizer_zpowers_eq] at hC
  obtain ⟨A, hA⟩ : ∃ A : GL (Fin (m + 1)) (GaloisField 2 f),
      (y⁻¹, A) ∈ LinFusion.ggInducedPairs ψ :=
    LinFusion.exists_mem_ggInducedPairs (y := y⁻¹) hrk ψ hker (by rwa [inv_inv])
  have hA' : (y, A⁻¹) ∈ LinFusion.ggInducedPairs ψ := by
    have h := (LinFusion.ggInducedPairs ψ).inv_mem hA
    rwa [Prod.inv_mk, inv_inv] at h
  have hEA : ∀ e ∈ Subgroup.zpowers y, ∃ B, (e, B) ∈ LinFusion.ggInducedPairs ψ := by
    intro e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    have h := (LinFusion.ggInducedPairs ψ).zpow_mem hA' k
    have e : ((y, A⁻¹) : G × GL (Fin (m + 1)) (GaloisField 2 f)) ^ k = (y ^ k, A⁻¹ ^ k) :=
      rfl
    exact ⟨A⁻¹ ^ k, e ▸ h⟩
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨d, D, _, _, hd, hD2, hFD, ⟨e⟩⟩ := ggAKFT_exists_psl_of_isComponentOf_sl
    (F := GaloisField 2 f) hker hp hp2 (ggIsPGroup_zpowers_of_pow_eq_one hy) hEA hC
  obtain ⟨a, ha⟩ : ∃ a : ℕ, Nat.card D = 2 ^ a := by
    have : Fintype D := Fintype.ofFinite D
    obtain ⟨k, -, hk⟩ := FiniteField.card D 2
    exact ⟨k, by rw [Nat.card_eq_fintype_card, hk]⟩
  have haf : f ≤ a := by
    have h1 : 2 ^ f ≤ 2 ^ a :=
      calc 2 ^ f = Nat.card (GaloisField 2 f) := hF.symm
        _ ≤ Nat.card D := hFD
        _ = 2 ^ a := ha
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hPSL : Nat.card (Matrix.SpecialLinearGroup (Fin d) D ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin d) D)) =
      Nat.card D ^ (d * (d - 1) / 2) * (∏ j ∈ Finset.Icc 2 d, (Nat.card D ^ j - 1)) /
        Nat.gcd d (Nat.card D - 1) :=
    (Nat.card_congr (projectiveSpecialLinearGroupEquivStatedProj d D).toEquiv).trans
      (CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by omega))
  refine ⟨d, a, hd, haf, ?_⟩
  rw [Nat.card_congr e.toEquiv, hPSL, ha]

theorem ggAKFL_not_excThree_PSL {G : Type} [Group G] [Finite G] {n f : ℕ}
    {ψ : (ggU .PSL n f).K →* G} {G₀ : Subgroup G}
    (hpres : GGPresentsG0 G₀ (ggU .PSL n f).D .PSL n f ψ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {y : G} (hy : y ^ p = 1) (hdiag : GGPsiInnerDiag (ggU .PSL n f).D ψ y)
    {C : Subgroup G} (hC : IsComponentOf C (G₀ ⊓ Subgroup.centralizer {y})) :
    ¬ GGStepTwoExcThreeType C := by
  obtain ⟨d, a, hd, haf, hcard⟩ := ggAKFL_card_of_isComponentOf_PSL hpres hp hp2 hy hdiag hC
  have ha : 1 ≤ a := hpres.1.1.2.1.trans haf
  rintro (hU | he | hD4)
  · exact ggAKFL_ordSL_ne_uFourTwo hd ha (hcard.symm.trans (ggAKFL_card_of_uFourTwo hU))
  · obtain ⟨e⟩ := he
    exact ggAKFL_ordSL_ne_altSix hd ha (hcard.symm.trans
      ((Nat.card_congr e.toEquiv).trans ggAKFL_card_alternatingGroup_six))
  · exact ggAKFL_ordSL_ne_dFourTwo hd ha (hcard.symm.trans (ggAKFT_card_of_dFourTwo hD4))

end PSL

section Tags

@[expose] def GGStepTwoChoiceThreeTag (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    ¬ GGStepTwoLinearType p t f →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ → p = 3 →
        GGStepTwoExcThreeType L₁ →
          ∃ m ∈ ggG0 p B x L D J ⊓ Subgroup.normalizer (Bs : Set G),
            ∃ g ∈ L₁, (∃ l ∈ L₁, g * l ≠ l * g) ∧
              g ∈ Subgroup.centralizer (D.map (MulAut.conj m⁻¹).toMonoidHom : Set G) ∧
              Nat.Coprime (orderOf g) p

@[expose] def GGStepTwoChoiceThreeTwoTag (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n : ℕ) (ψ : (ggU t n 1).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n 1).D t n 1 ψ → GGSixStepOne p B Bs x L D J →
    ¬ GGStepTwoLinearType p t 1 →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ → p = 3 →
        GGStepTwoExcThreeType L₁ →
          ∃ m ∈ ggG0 p B x L D J ⊓ Subgroup.normalizer (Bs : Set G),
            ∃ g ∈ L₁, (∃ l ∈ L₁, g * l ≠ l * g) ∧
              g ∈ Subgroup.centralizer (D.map (MulAut.conj m⁻¹).toMonoidHom : Set G) ∧
              Nat.Coprime (orderOf g) p

@[expose] def GGLayerNotUFourAltSixTag (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU t n f).D t n f ψ → 2 ≤ f →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ y : G, y ^ p = 1 → y ∈ Subgroup.normalizer (G₀ : Set G) →
      GGPsiInnerDiag (ggU t n f).D ψ y →
      ∀ C : Subgroup G, IsComponentOf C (G₀ ⊓ Subgroup.centralizer {y}) →
        ¬ LieModel (↥C ⧸ Subgroup.center ↥C) .PSU 4 2 1 ∧
          IsEmpty ((↥C ⧸ Subgroup.center ↥C) ≃* alternatingGroup (Fin 6))

theorem ggStepTwoChoiceThreeInput_of_tags (h : ∀ t, GGStepTwoChoiceThreeTag t) :
    GGStepTwoChoiceThreeInput := by
  intro G _ _ p B Bs x L D J t n f ψ
  exact h t G p B Bs x L D J n f ψ

theorem ggStepTwoChoiceThreeTag_of_parts {t : StatedLieTag} (h1 : GGStepTwoChoiceThreeTwoTag t)
    (hD : GGLayerNotDFourTwoTag t) (hUA : GGLayerNotUFourAltSixTag t) :
    GGStepTwoChoiceThreeTag t := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 hlin b L₁ hpair hp3 hT
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  rcases Nat.lt_or_ge f 2 with hf2 | hf2
  · obtain rfl : f = 1 := by omega
    exact h1 G p B Bs x L D J n ψ hctx s1 hlin b L₁ hpair hp3 hT
  · exfalso
    have hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ :=
      ⟨hctx.2.2.2.1, hctx.2.2.2.2.1, hctx.2.2.2.2.2.1.1, hctx.2.2.2.2.2.1.2⟩
    have hb := hctx.bstar.2.1.2 b hpair.1
    have hbN := hctx.bstar_le_normalizer hpair.1
    have hbd := hctx.2.2.2.2.2.2.1.2 b hpair.1
    have hUA' := hUA G n f ψ _ hpres hf2 p hctx.prime hctx.ne_two b hb hbN hbd L₁ hpair.2.2.1
    rcases hT with hU | he | hD4
    · exact hUA'.1 hU
    · obtain ⟨e⟩ := he
      exact hUA'.2.false e
    · exact hD G n f ψ _ hpres hf2 p hctx.prime hctx.ne_two b hb hbN hbd L₁ hpair.2.2.1 hD4

theorem ggStepTwoChoiceThreeTag_PSL : GGStepTwoChoiceThreeTag .PSL := by
  intro G _ _ p B Bs x L D J n f ψ hctx _ _ b L₁ hpair _ hT
  exact absurd hT (ggAKFL_not_excThree_PSL
    ⟨hctx.2.2.2.1, hctx.2.2.2.2.1, hctx.2.2.2.2.2.1.1, hctx.2.2.2.2.2.1.2⟩ hctx.prime
    hctx.ne_two (hctx.bstar.2.1.2 b hpair.1) (hctx.2.2.2.2.2.2.1.2 b hpair.1) hpair.2.2.1)

theorem ggStepTwoChoiceThreeTwoTag_PSU : GGStepTwoChoiceThreeTwoTag .PSU := by
  intro G _ _ p B Bs x L D J n ψ _ _ hlin b L₁ _ hp3 _
  subst hp3
  exact absurd (Or.inr ⟨rfl, by norm_num⟩) hlin

theorem ggStepTwoChoiceThreeTag_of_placeholder (t : StatedLieTag)
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits) : GGStepTwoChoiceThreeTag t := by
  intro G _ _ p B Bs x L D J n f ψ hctx
  have hrk := hctx.2.2.2.1.2
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact absurd hrk (show ¬ 2 ≤ 0 by omega)

theorem ggStepTwoChoiceThreeTag_POmegaOdd : GGStepTwoChoiceThreeTag .POmegaOdd :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hctx => absurd rfl hctx.2.2.2.1.1.2.2.2

theorem ggLayerNotUFourAltSixTag_PSL : GGLayerNotUFourAltSixTag .PSL := by
  intro G _ _ n f ψ G₀ hpres _ p hp hp2 y hy _ hdiag C hC
  have h := ggAKFL_not_excThree_PSL hpres hp hp2 hy hdiag hC
  exact ⟨fun hU => h (Or.inl hU), ⟨fun e => h (Or.inr (Or.inl ⟨e⟩))⟩⟩

theorem ggLayerNotUFourAltSixTag_of_placeholder (t : StatedLieTag)
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits) : GGLayerNotUFourAltSixTag t := by
  intro G _ _ n f ψ G₀ hpres
  have hrk := hpres.1.2
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact absurd hrk (show ¬ 2 ≤ 0 by omega)

theorem ggLayerNotUFourAltSixTag_POmegaOdd : GGLayerNotUFourAltSixTag .POmegaOdd :=
  fun _ _ _ _ _ _ _ hpres => absurd rfl hpres.1.1.2.2.2

end Tags

section Remaining

@[expose] def GGStepTwoChoiceThreeTwoRest : Prop :=
  GGStepTwoChoiceThreeTwoTag .PSp ∧ GGStepTwoChoiceThreeTwoTag .POmegaPlus ∧
    GGStepTwoChoiceThreeTwoTag .POmegaMinus ∧ GGStepTwoChoiceThreeTwoTag .F4 ∧
      GGStepTwoChoiceThreeTwoTag .E6 ∧ GGStepTwoChoiceThreeTwoTag .E7 ∧
        GGStepTwoChoiceThreeTwoTag .E8 ∧ GGStepTwoChoiceThreeTwoTag .twistedE6

@[expose] def GGLayerNotUFourAltSixRest : Prop :=
  GGLayerNotUFourAltSixTag .PSU ∧ GGLayerNotUFourAltSixTag .PSp ∧
    GGLayerNotUFourAltSixTag .POmegaPlus ∧ GGLayerNotUFourAltSixTag .POmegaMinus ∧
      GGLayerNotUFourAltSixTag .F4 ∧ GGLayerNotUFourAltSixTag .E6 ∧
        GGLayerNotUFourAltSixTag .E7 ∧ GGLayerNotUFourAltSixTag .E8 ∧
          GGLayerNotUFourAltSixTag .twistedE6

theorem ggStepTwoChoiceThreeInput_of_remaining
    (hD : GGLayerNotDFourTwoTag .PSU ∧ GGLayerNotDFourTwoTag .PSp ∧
      GGLayerNotDFourTwoTag .POmegaPlus ∧ GGLayerNotDFourTwoTag .POmegaMinus ∧
        GGLayerNotDFourTwoTag .F4 ∧ GGLayerNotDFourTwoTag .E6 ∧ GGLayerNotDFourTwoTag .E7 ∧
          GGLayerNotDFourTwoTag .E8 ∧ GGLayerNotDFourTwoTag .twistedE6)
    (hUA : GGLayerNotUFourAltSixRest) (h2 : GGStepTwoChoiceThreeTwoRest) :
    GGStepTwoChoiceThreeInput := by
  obtain ⟨dU, dSp, dPl, dMi, dF4, dE6, dE7, dE8, dT⟩ := hD
  obtain ⟨uU, uSp, uPl, uMi, uF4, uE6, uE7, uE8, uT⟩ := hUA
  obtain ⟨cSp, cPl, cMi, cF4, cE6, cE7, cE8, cT⟩ := h2
  refine ggStepTwoChoiceThreeInput_of_tags fun t => ?_
  cases t with
  | PSL => exact ggStepTwoChoiceThreeTag_PSL
  | PSU => exact ggStepTwoChoiceThreeTag_of_parts ggStepTwoChoiceThreeTwoTag_PSU dU uU
  | PSp => exact ggStepTwoChoiceThreeTag_of_parts cSp dSp uSp
  | POmegaOdd => exact ggStepTwoChoiceThreeTag_POmegaOdd
  | POmegaPlus => exact ggStepTwoChoiceThreeTag_of_parts cPl dPl uPl
  | POmegaMinus => exact ggStepTwoChoiceThreeTag_of_parts cMi dMi uMi
  | F4 => exact ggStepTwoChoiceThreeTag_of_parts cF4 dF4 uF4
  | E6 => exact ggStepTwoChoiceThreeTag_of_parts cE6 dE6 uE6
  | E7 => exact ggStepTwoChoiceThreeTag_of_parts cE7 dE7 uE7
  | E8 => exact ggStepTwoChoiceThreeTag_of_parts cE8 dE8 uE8
  | twistedE6 => exact ggStepTwoChoiceThreeTag_of_parts cT dT uT
  | G2 => exact ggStepTwoChoiceThreeTag_of_placeholder _ (Or.inl rfl)
  | trialityD4 => exact ggStepTwoChoiceThreeTag_of_placeholder _ (Or.inr (Or.inl rfl))
  | twistedB2 =>
    exact ggStepTwoChoiceThreeTag_of_placeholder _ (Or.inr (Or.inr (Or.inl rfl)))
  | twistedG2 =>
    exact ggStepTwoChoiceThreeTag_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | twistedF4 =>
    exact ggStepTwoChoiceThreeTag_of_placeholder _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  | Tits =>
    exact ggStepTwoChoiceThreeTag_of_placeholder _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

end Remaining

end CFSG.StandardType
