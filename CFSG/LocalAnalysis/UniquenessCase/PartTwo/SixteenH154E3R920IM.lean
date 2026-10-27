module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920Cfg
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs462
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920IMSyl
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920IMRed
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920IMFix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920IMOdd
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XBasic
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93c
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3OmegaA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F09 (Hyp97 I9)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.GroupTheory.ThreeTranspositions (HasE9)

variable {G : Type} [Group G] [Finite G]

namespace R920Cfg

variable {D : Data G} {L D₃ A : Subgroup G}

private theorem r920im_prime_eq_three_or_seven (c : R920Cfg D L D₃ A) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E : Subgroup G} (hEL : E ≤ L) (hEcard : Nat.card E = p) :
    p = 3 ∨ p = 7 := by
  have hcardB : Nat.card (Bar2 L) = 504 := by
    rw [s16h_e3_omega_card_of_isL2 c.isL2]
    decide
  have hdvdL : p ∣ Nat.card ↥L := by
    rw [← hEcard]
    exact Subgroup.card_dvd_of_le hEL
  have hdecomp : Nat.card ↥L = Nat.card (Bar2 L) * Nat.card (CFSG.pCore 2 ↥L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)
  have hdvd : p ∣ Nat.card (Bar2 L) * Nat.card (CFSG.pCore 2 ↥L) := hdecomp ▸ hdvdL
  have hpk : ¬ p ∣ Nat.card (CFSG.pCore 2 ↥L) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    rw [hk]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hdvdB : p ∣ 504 := hcardB ▸ (hp.dvd_mul.mp hdvd).resolve_right hpk
  have h504 : (504 : ℕ) = 2 ^ 3 * (3 ^ 2 * 7) := by norm_num
  rw [h504] at hdvdB
  rcases hp.dvd_mul.mp hdvdB with h8 | h37
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h8)) hp2
  · rcases hp.dvd_mul.mp h37 with h9 | h7
    · left
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h9)
    · right
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).mp h7

theorem I9_le_M (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (hK46 : UCK.K46Semireg)
    (c : R920Cfg D L D₃ A) {Y H S : Subgroup G} (h97 : Hyp97 D Y H D₃ S) (hY : Opp 3 Y = L)
    (hSH : CFSG.ABGLocalTools.IsSylowOf 2 S H) : I9 H ≤ D.M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hIM
  have hHt : H ≠ ⊤ := ne_top_of_hyp97 D h97
  obtain ⟨⟨hY9, hH9, hD₃X, -⟩, -, -, hSY⟩ := h97
  have hYH : Y ≤ H := hH9.1
  have hYM : Y ≤ D.M := hY9.1
  have hLY : L ≤ Y := hY ▸ F09.opp_le_self 3 Y
  have hYL : Y ≤ normalizer (L : Set G) := by
    rw [← hY]
    exact F09.le_normalizer_opp_self 3 Y
  have hD₃L : D₃ ≤ L := hY ▸ hD₃X
  have hLH : L ≤ H := hLY.trans hYH
  have hHK : CFSG.Open.IsKGroup ↥H :=
    CFSG.Open.IsKProper.isKGroup D.standing.kProper H hHt
  have hIleH : F09.I9 H ≤ H := Subgroup.map_subtype_le (CFSG.pPrimeCore 3 ↥H)
  have hKK : CFSG.Open.IsKGroup ↥L := CFSG.Open.IsKGroup.of_le hHK hLH
  have hKG : CFSG.Open.IsKGroup ↥(F09.I9 H ⊔ Y) :=
    CFSG.Open.IsKGroup.of_le hHK (sup_le hIleH hYH)
  have hE9 : ¬ HasE9 ↥(Opp 3 Y) := F09.not_hasE9_opp ⟨hY9, hH9, hD₃X, c.D₃_card⟩
  have hE9L : ¬ HasE9 ↥L := hY ▸ hE9
  have hCZ : centralizer (D₃ : Set G) ≤ D.M :=
    (Subgroup.centralizer_le_normalizer (D₃ : Set G)).trans
      (CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal c.D₃_mem)
  have hHI : H ≤ normalizer (F09.I9 H : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh x hx
    have hx' : x ∈ (CFSG.pPrimeCore 3 ↥H).map H.subtype := hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx'
    exact Subgroup.mem_map.mpr
      ⟨⟨h, hh⟩ * y * ⟨h, hh⟩⁻¹,
        (CFSG.pPrimeCore_normal (p := 3) (G := ↥H)).conj_mem y hy ⟨h, hh⟩, rfl⟩
  have hI3 : ¬ 3 ∣ Nat.card (F09.I9 H) := by
    change ¬ 3 ∣ Nat.card ((CFSG.pPrimeCore 3 ↥H).map H.subtype)
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥H))
  have hLgen : ∀ B : Subgroup G, B ≤ L → L ≤ normalizer (B : Set G) → D₃ ≤ B → B = L :=
    fun B hBL hLB hD₃B => eq_of_normal_of_isL2 c.mem.2.1 c.isL2 hBL hLB hD₃B c.D₃_card
  obtain ⟨r, U, W, hr, -, hUW, hUle, hWM, hUMleW, hfix, hmin⟩ :=
    exists_minimal_chief_factor_Y hSch hKG hD₃L hLY hYL c.D₃_card hYM hCZ c.mem.2.1 hLgen
      (hYH.trans hHI) hI3 hIM
  by_cases hr2 : r = 2
  · have hUH : U ≤ H := hUle.trans hIleH
    exact false_of_chief_factor_two hSH hUH hSY.le (hSY.le.trans hYM) (hr2 ▸ hUW) hUMleW
  · by_cases hr7 : r = 7
    · exact false_of_chief_factor_seven D.maxLocal (c.A_le.trans hLY) c.A_card c.A_mem
        (hr7 ▸ hUW) hUMleW
    · haveI : Fact r.Prime := ⟨hr⟩
      have hW3 : ¬ 3 ∣ Nat.card W := fun h =>
        hI3 (h.trans (Subgroup.card_dvd_of_le (hUW.1.le.trans hUle)))
      have hU7 : ¬ 7 ∣ Nat.card U :=
        not_seven_dvd_card_of_minimal_chief_factor hr7 c.mem c.isL2 hLY hYL hD₃L hUW hUle
          hWM hW3 hUMleW hfix hmin
      obtain ⟨U₁, hWU₁, hU₁U, hLU₁, -, hUW₁⟩ :=
        exists_chief_factor_under_of_le_normalizer hLY hUW
      have hfix₁ : ∀ u ∈ U₁, (∀ x ∈ D₃, x * u * x⁻¹ * u⁻¹ ∈ W) → u ∈ W :=
        fun u hu h => hfix u (hU₁U hu) h
      have hU₁nW : U₁ ≤ normalizer (W : Set G) := by
        rw [Subgroup.le_normalizer_iff]
        intro x hx y hy
        exact hUW.2.2.2.1 x (hU₁U hx) y hy
      have hU₁M : U₁ ⊓ D.M ≤ W :=
        (le_inf (inf_le_left.trans hU₁U) inf_le_right).trans hUMleW
      have hfixA : ∀ (p : ℕ) (A' : Subgroup G), p.Prime → p ≠ 2 → A' ≤ L →
          Nat.card A' = p → ∀ u ∈ U₁, (∀ a ∈ A', a * u * a⁻¹ * u⁻¹ ∈ W) → u ∈ W := by
        intro p A' hp hp2 hA'L hA'card u hu hfixu
        rcases r920im_prime_eq_three_or_seven c hp hp2 hA'L hA'card with hp3 | hp7
        · have hA'card3 : Nat.card A' = 3 := hA'card.trans hp3
          have hAu : A' ∈ uniqueSet D.M := c.mem_uniqueSet_of_card_three hA'L hA'card3
          have hUp : ¬ p ∣ Nat.card U₁ := by
            rw [hp3]
            exact fun h => hI3 (h.trans (Subgroup.card_dvd_of_le (hU₁U.trans hUle)))
          exact mem_of_fixed_coset_of_coprime hp D.maxLocal hA'card hAu
            (hA'L.trans hLU₁) (hA'L.trans (hLY.trans hUW.2.2.1))
            hWU₁ hU₁nW hUp hU₁M hu hfixu
        · have hA'card7 : Nat.card A' = 7 := hA'card.trans hp7
          have hAu : A' ∈ uniqueSet D.M := c.mem_uniqueSet_of_card_seven hA'L hA'card7
          have hUp : ¬ p ∣ Nat.card U₁ := by
            rw [hp7]
            exact fun h => hU7 (h.trans (Subgroup.card_dvd_of_le hU₁U))
          exact mem_of_fixed_coset_of_coprime hp D.maxLocal hA'card hAu
            (hA'L.trans hLU₁) (hA'L.trans (hLY.trans hUW.2.2.1))
            hWU₁ hU₁nW hUp hU₁M hu hfixu
      exact false_of_odd_chief_factor hK46 hKK hE9L c.mem.2.1 hD₃L c.D₃_card hLgen hr hr2
        hUW₁ hfix₁ hfixA ⟨A, c.A_le, c.A_card⟩

end R920Cfg

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
