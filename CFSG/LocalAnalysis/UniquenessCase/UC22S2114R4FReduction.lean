module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3FLift
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07Card
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Thin
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR2Alpha
import CFSG.Mathlib.Arithmetic.TwoPowSubOnePrimes
import CFSG.LocalAnalysis.UniquenessCase.UC22P22i
import CFSG.LocalAnalysis.UniquenessCase.UC22Sec7Three
import CFSG.LocalAnalysis.UniquenessCase.UCFront07CardFour
import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3FInner

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedThree BadNoStrongThree c76Three_of_inputs)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114r4f_false_of_fieldData_of_isStronglyPEmbedded
    {D : Data G} {Ch : Choice2011 G}
    (h74 : F07.R74Card D) (hH : H1930 D)
    (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M)
    {b : G} (hbB : b ∈ c.B0) (hbL : b ∈ normalizer (L : Set G))
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hbr : orderOf b = r)
    (hrK : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    {X : Subgroup (BarInf L)} (hXp : IsPGroup p ↥X) (hXc : ¬ IsCyclic ↥X)
    (hXfix : ∀ x ∈ X, inducedBarInfAutHom L ⟨b, hbL⟩ x = x)
    {q : ℕ} (hq : q.Prime) (hq7 : 7 ≤ q) (hqr : q ≠ r)
    (hqK : ¬ q ∣ Nat.card (CFSG.solvableRadical ↥L))
    {A : Type} [CommGroup A] [Finite A] (hA : IsPGroup q A) (hAc : ¬ IsCyclic A)
    (κ : A →* A) (hκ : ∀ a, κ a = a → a = 1)
    (ι : A →* BarInf L) (hι : Function.Injective ι)
    (hθι : ∀ a, inducedBarInfAutHom L ⟨b, hbL⟩ (ι a) = ι (κ a)) :
    False := by
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by omega
  have hN := uc22s2112r2_normalizer hH c hL.1.le hbB (by rw [hbr]; exact hr)
  have : Fact p.Prime := ⟨hp⟩
  have hbP : IsPGroup r ↥(zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbr, pow_one])
  have hC := uc22s2114r3f_two_le_pRank_centralizer (zpowers_le.2 hbL) hbP hrK hp2 hXp hXc
    (uc22s2114r3f_fix_zpowers hbL hXfix)
  have hpN : 1 < CFSG.Open.pRank p (normalizer ((zpowers b : Subgroup G) : Set G) ⊓ D.M) := by
    have := hC.trans (CFSG.SectionRank.pRank_mono hp.one_lt ((inf_le_inf_left L
      (centralizer_le (Set.singleton_subset_iff.2 (mem_zpowers b)))).trans hN.2.2.2))
    omega
  have h74b := h74 p _ ⟨hp, hp2, hsp, hN.1, hN.2.1, hpN⟩
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨ψ, hψ, hψL, hbψ⟩ :=
    uc22s2114r3f_exists_lift hbL hr hbr hrK hqK hA ι hι κ hθι
  have h2 := uc22s2114r3f_two_lt_card (D := D) hq (by omega) hr hr2 hqr hA hAc κ hκ ψ hψ
    (fun a => hL.1.le (hψL a)) (c.hBM hbB) hbr hbψ
  have hle := Subgroup.card_le_of_le (inf_le_inf_left (F07.Q7 D) hN.2.2.1)
  omega

theorem uc22s2114r4f_false_of_fieldData
    {D : Data G} {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D)
    (h74 : F07.R74Card D) (hH : H1930 D)
    (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M)
    {b : G} (hbB : b ∈ c.B0) (hbL : b ∈ normalizer (L : Set G))
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hbr : orderOf b = r)
    (hrK : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpσ : p ∈ D.sig)
    {X : Subgroup (BarInf L)} (hXp : IsPGroup p ↥X) (hXc : ¬ IsCyclic ↥X)
    (hXfix : ∀ x ∈ X, inducedBarInfAutHom L ⟨b, hbL⟩ x = x)
    {q : ℕ} (hq : q.Prime) (hq7 : 7 ≤ q) (hqr : q ≠ r)
    (hqK : ¬ q ∣ Nat.card (CFSG.solvableRadical ↥L))
    {A : Type} [CommGroup A] [Finite A] (hA : IsPGroup q A) (hAc : ¬ IsCyclic A)
    (κ : A →* A) (hκ : ∀ a, κ a = a → a = 1)
    (ι : A →* BarInf L) (hι : Function.Injective ι)
    (hθι : ∀ a, inducedBarInfAutHom L ⟨b, hbL⟩ (ι a) = ι (κ a)) :
    False := by
  exact uc22s2114r4f_false_of_fieldData_of_isStronglyPEmbedded h74 hH c hL hbB hbL
    hr hr5 hbr hrK hp hp2
    (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) hpσ)
    hXp hXc hXfix hq hq7 hqr hqK hA hAc κ hκ ι hι hθι

@[expose] def S21_14R4FInner (D : Data G) (Ch : Choice2011 G) : Prop :=
  ∀ (_ : UC6S846.SigmaStd D) (_ : F07.R76Sig D) (_ : F07.R74Card D),
    H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, IsChev (BarInf L) 2 →
    (∀ n : ℕ, LieRankTwoEven (BarInf L) n → IsPowTwo n) →
    ∀ l f : ℕ, 4 ≤ l → PartTwo.S17.CHasLieRank (BarInf L) l f → 3 ≤ c.n →
    c.B0 ≤ normalizer (L : Set G) →
    (∀ b ∈ c.B0, CentralizesBar b L → b = 1) →
    (Odd c.n ∨ (LieModel (BarInf L) .PSL 5 2 f ∧ Odd f ∧ 3 ≤ f)) →
    (∀ r : ℕ, r.Prime → 5 ≤ r → r ∣ 2 ^ c.n - 1 → r ∣ f) →
    ∀ (b : G), b ∈ c.B0 → ∀ (hbL : b ∈ normalizer (L : Set G)) (r : ℕ),
      r.Prime → 5 ≤ r → orderOf b = r → r ∣ 2 ^ c.n - 1 → r ∣ f →
      inducedBarInfAutHom L ⟨b, hbL⟩ ∈
        (MulAut.conj : BarInf L →* MulAut (BarInf L)).range →
      False

@[expose] def S21_14R4FFieldData (D : Data G) (Ch : Choice2011 G) : Prop :=
  ∀ (_ : UC6S846.SigmaStd D) (_ : F07.R76Sig D) (_ : F07.R74Card D),
    H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, IsChev (BarInf L) 2 →
    (∀ n : ℕ, LieRankTwoEven (BarInf L) n → IsPowTwo n) →
    ∀ l f : ℕ, 4 ≤ l → PartTwo.S17.CHasLieRank (BarInf L) l f → 3 ≤ c.n →
    c.B0 ≤ normalizer (L : Set G) →
    (∀ b ∈ c.B0, CentralizesBar b L → b = 1) →
    (Odd c.n ∨ (LieModel (BarInf L) .PSL 5 2 f ∧ Odd f ∧ 3 ≤ f)) →
    (∀ r : ℕ, r.Prime → 5 ≤ r → r ∣ 2 ^ c.n - 1 → r ∣ f) →
    ∀ (b : G), b ∈ c.B0 → ∀ (hbL : b ∈ normalizer (L : Set G)) (r : ℕ),
      r.Prime → 5 ≤ r → orderOf b = r → r ∣ 2 ^ c.n - 1 → r ∣ f →
      inducedBarInfAutHom L ⟨b, hbL⟩ ∉
        (MulAut.conj : BarInf L →* MulAut (BarInf L)).range →
      (¬ r ∣ Nat.card (CFSG.solvableRadical ↥L)) ∧
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∈ D.sig ∧
        ∃ X : Subgroup (BarInf L), IsPGroup p ↥X ∧ ¬ IsCyclic ↥X ∧
          ∀ x ∈ X, inducedBarInfAutHom L ⟨b, hbL⟩ x = x) ∧
      (∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧
        ¬ q ∣ Nat.card (CFSG.solvableRadical ↥L) ∧
        ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
          ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* BarInf L, Function.Injective ι ∧
            ∀ a, inducedBarInfAutHom L ⟨b, hbL⟩ (ι a) = ι (κ a))

theorem s21_14R4F_of_inner_fieldData {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h76 : F07.R76Sig D) (h74 : F07.R74Card D)
    (hInner : S21_14R4FInner D Ch) (hData : S21_14R4FFieldData D Ch) :
    S21_14R4F D Ch := by
  intro hH c L hL hX hpow l f hl hlr hn3 hBL hfaith hcase hall
  obtain ⟨r, hr, hr5, hrn⟩ := CFSG.exists_prime_five_le_dvd_two_pow_sub_one hn3
  have hrf : r ∣ f := hall r hr hr5 hrn
  obtain ⟨b, hb, hbr⟩ := uc22p22i_exists_elt_of_mem_piSet
    (show r ∈ piSet c.B0 by rw [c.hpi]; exact ⟨hr, hrn⟩)
  have hbL := hBL hb
  have hb1 : inducedBarInfAutHom L ⟨b, hbL⟩ ≠ 1 := fun h1 => by
    have h := uc22s2114_eq_one_of_inducedBarInfAutHom_eq_one hL hBL hfaith hb h1
    rw [h, orderOf_one] at hbr
    exact hr.ne_one hbr.symm
  by_cases hin : inducedBarInfAutHom L ⟨b, hbL⟩ ∈
      (MulAut.conj : BarInf L →* MulAut (BarInf L)).range
  · exact (hInner hSg h76 h74 hH c L hL hX hpow l f hl hlr hn3 hBL hfaith hcase hall
      b hb hbL r hr hr5 hbr hrn hrf hin).elim
  · obtain ⟨hrK, ⟨p, hp, hp2, hpσ, X, hXp, hXc, hXfix⟩,
      ⟨q, hq, hq7, hqr, hqK, A, _, _, hAq, hAcyc, κ, hκ, ι, hι, hθι⟩⟩ :=
      hData hSg h76 h74 hH c L hL hX hpow l f hl hlr hn3 hBL hfaith hcase hall
        b hb hbL r hr hr5 hbr hrn hrf hin
    exact (uc22s2114r4f_false_of_fieldData hSg h74 hH c hL hb hbL hr hr5 hbr hrK
      hp hp2 hpσ hXp hXc hXfix hq hq7 hqr hqK hAq hAcyc κ hκ ι hι hθι).elim

theorem s21_14R4F_dataOfSetup4_of_inner_fieldData
    (hSE : StronglyEmbeddedFive) (hK3 : StronglyEmbeddedThree)
    (hB3 : BadNoStrongThree) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma) (hPart : PartIAt S.M)
    {Ch : Choice2011 G}
    (hInner : S21_14R4FInner (UC6.dataOfSetup4 hS hU S) Ch)
    (hData : S21_14R4FFieldData (UC6.dataOfSetup4 hS hU S) Ch) :
    S21_14R4F (UC6.dataOfSetup4 hS hU S) Ch := by
  have hC76 := c76Three_of_inputs hSE hK3 hB3 hS hU S
  have h76 : F07.R76Sig (UC6.dataOfSetup4 hS hU S) := fun p hp _ hsp => by
    by_cases h3 : 3 ∈ CFSG.Open.uniqueFourBeta G
    · exact hC76 hMS h3 p hp hsp
    · exact UC6.conclusion76_dataOfSetup4 hSE hS hU S h3 hp hsp
  have h74 : F07.R74Card (UC6.dataOfSetup4 hS hU S) :=
    F07.r74Card_dataOfSetup4 hSE hK3 hB3 hS hU S hMS hPart.1
  exact s21_14R4F_of_inner_fieldData (UC6S846.sigmaStd_dataOfSetup4 hS hU S) h76 h74 hInner hData

end CFSG.LocalAnalysis.UniquenessCase.UC22
