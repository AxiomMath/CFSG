module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.R920L2OddChain
public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs462
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.R920L2OddIMRed
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.R920L2OddIMFrob
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920IMSyl
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920IMFix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XBasic
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93c
import CFSG.NumberTheory.TwoPowAddOneOdd
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.ABGLocalTools (IsChiefFactorUnder)
open CFSG.GroupTheory.ThreeTranspositions (HasE9)

variable {G : Type} [Group G] [Finite G]

private structure R920C3Setup (D : Data G) (L D₃ Y H S : Subgroup G) : Prop where
  hYH : Y ≤ H
  hYM : Y ≤ D.M
  hLY : L ≤ Y
  hYL : Y ≤ normalizer (L : Set G)
  hD₃L : D₃ ≤ L
  hLH : L ≤ H
  hHK : CFSG.Open.IsKGroup ↥H
  hIleH : F09.I9 H ≤ H
  hKK : CFSG.Open.IsKGroup ↥L
  hKG : CFSG.Open.IsKGroup ↥(F09.I9 H ⊔ Y)
  hE9L : ¬ HasE9 ↥L
  hCZ : centralizer (D₃ : Set G) ≤ D.M
  hHI : H ≤ normalizer (F09.I9 H : Set G)
  hI3 : ¬ 3 ∣ Nat.card (F09.I9 H)
  hLgen : ∀ B : Subgroup G, B ≤ L → L ≤ normalizer (B : Set G) → D₃ ≤ B → B = L
  hSY : IsSylowOf 2 S Y

private theorem seven_le_of_prime_dvd_two_pow_sub_one {n p : ℕ} (hn : Odd n) (hp : p.Prime)
    (hpn : p ∣ 2 ^ n - 1) : 7 ≤ p := by
  have hp2 : p ≠ 2 := by
    intro h
    subst h
    have hodd : Odd (2 ^ n - 1) :=
      Nat.Even.sub_odd (Nat.two_pow_pos n)
        (Even.pow_of_ne_zero (a := (2 : ℕ)) even_two hn.pos.ne') odd_one
    obtain ⟨k, hk⟩ := hodd
    obtain ⟨j, hj⟩ := hpn
    omega
  have hp3 : p ≠ 3 := by
    intro h
    subst h
    exact (CFSG.NumberTheory.not_dvd_two_pow_sub_one_of_dvd_two_pow_add_one
      (r := 3) (n := 1) (m := n) (by norm_num) (by norm_num) (by norm_num) hn) hpn
  have hp5 : p ≠ 5 := by
    intro h
    subst h
    exact (CFSG.NumberTheory.not_dvd_two_pow_sub_one_of_dvd_two_pow_add_one
      (r := 5) (n := 2) (m := n) (by norm_num) (by norm_num) (by norm_num) hn) hpn
  by_contra h
  have hlt : p < 7 := by omega
  have hp2le : 2 ≤ p := hp.two_le
  interval_cases p
  · exact hp2 rfl
  · exact hp3 rfl
  · norm_num at hp
  · exact hp5 rfl
  · norm_num at hp

private theorem r920c3_setup {D : Data G} {L D₃ A : Subgroup G} {n : ℕ}
    (c : R920CfgL2 D L D₃ A n) {Y H S : Subgroup G} (h97 : F09.Hyp97 D Y H D₃ S)
    (hY : Opp 3 Y = L) : R920C3Setup D L D₃ Y H S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
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
  exact ⟨hYH, hYM, hLY, hYL, hD₃L, hLH, hHK, hIleH, hKK, hKG, hE9L, hCZ, hHI, hI3, hLgen,
    hSY⟩

private theorem r920c3_case_ne (hK462 : UCK.K462) {D : Data G} {L D₃ A : Subgroup G} {n : ℕ}
    (c : R920CfgL2 D L D₃ A n) {Y H U W : Subgroup G} {r : ℕ}
    (hLY : L ≤ Y) (hYL : Y ≤ normalizer (L : Set G)) (hD₃L : D₃ ≤ L)
    (hKK : CFSG.Open.IsKGroup ↥L) (hE9L : ¬ HasE9 ↥L)
    (hI3 : ¬ 3 ∣ Nat.card (F09.I9 H))
    (hLgen : ∀ B : Subgroup G, B ≤ L → L ≤ normalizer (B : Set G) → D₃ ≤ B → B = L)
    (hr : r.Prime) (hr2 : r ≠ 2) (hrs : r ≠ Nat.card A)
    (hUW : IsChiefFactorUnder r Y U W) (hUle : U ≤ F09.I9 H)
    (hWM : W ≤ D.M) (hUMleW : U ⊓ D.M ≤ W)
    (hfix : ∀ u ∈ U, (∀ x ∈ D₃, x * u * x⁻¹ * u⁻¹ ∈ W) → u ∈ W)
    (hmin : ∀ V : Subgroup G, V ≤ F09.I9 H → Y ≤ normalizer (V : Set G) → ¬ V ≤ D.M →
      Nat.card U ≤ Nat.card V) : False := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hs : (Nat.card A).Prime := c.A_prime
  have hs7 : 7 ≤ Nat.card A :=
    seven_le_of_prime_dvd_two_pow_sub_one c.odd c.A_prime c.A_dvd
  have hs2 : Nat.card A ≠ 2 := by omega
  have hW3 : ¬ 3 ∣ Nat.card W := fun h =>
    hI3 (h.trans (Subgroup.card_dvd_of_le (hUW.1.le.trans hUle)))
  have hUs : ¬ Nat.card A ∣ Nat.card U :=
    not_dvd_card_of_minimal_chief_factor_L2 hs hs2 hrs c.mem c.isL2 hLY hYL hD₃L hUW hUle
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
  have hfixA : ∀ u ∈ U₁, (∀ a ∈ A, a * u * a⁻¹ * u⁻¹ ∈ W) → u ∈ W := by
    intro u hu hfixu
    have hA_U1 : A ≤ normalizer (U₁ : Set G) := c.A_le.trans hLU₁
    have hA_W : A ≤ normalizer (W : Set G) := c.A_le.trans (hLY.trans hUW.2.2.1)
    have hUs1 : ¬ Nat.card A ∣ Nat.card U₁ :=
      fun h => hUs (h.trans (Subgroup.card_dvd_of_le hU₁U))
    exact mem_of_fixed_coset_of_coprime c.A_prime D.maxLocal rfl c.A_mem hA_U1 hA_W
      hWU₁ hU₁nW hUs1 hU₁M hu hfixu
  have h5n : 5 ≤ n := c.five_le
  exact false_of_odd_chief_factor_L2 hK462 hKK hE9L c.mem.2.1 c.isL2 (by omega) hD₃L
    c.D₃_card hLgen hr hr2 hUW₁ hfix₁ c.A_le c.A_prime rfl hs7 c.A_dvd hfixA

theorem I9_le_M_of_isL2_odd (hK462 : UCK.K462) (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    {D : Data G} {L D₃ A : Subgroup G} {n : ℕ} (c : R920CfgL2 D L D₃ A n)
    {Y H S : Subgroup G} (h97 : F09.Hyp97 D Y H D₃ S) (hY : Opp 3 Y = L)
    (hSH : IsSylowOf 2 S H) : F09.I9 H ≤ D.M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hIM
  obtain ⟨hYH, hYM, hLY, hYL, hD₃L, hLH, hHK, hIleH, hKK, hKG, hE9L, hCZ, hHI, hI3, hLgen,
    hSY⟩ := r920c3_setup c h97 hY
  obtain ⟨r, U, W, hr, -, hUW, hUle, hWM, hUMleW, hfix, hmin⟩ :=
    exists_minimal_chief_factor_Y hSch hKG hD₃L hLY hYL c.D₃_card hYM hCZ c.mem.2.1 hLgen
      (hYH.trans hHI) hI3 hIM
  by_cases hr2 : r = 2
  · exact false_of_chief_factor_two hSH (hUle.trans hIleH) hSY.le (hSY.le.trans hYM)
      (hr2 ▸ hUW) hUMleW
  · by_cases hrs : r = Nat.card A
    · exact false_of_chief_factor_prime c.A_prime D.maxLocal (c.A_le.trans hLY) rfl c.A_mem
        (hrs ▸ hUW) hUMleW
    · exact r920c3_case_ne hK462 c hLY hYL hD₃L hKK hE9L hI3 hLgen hr hr2 hrs
        hUW hUle hWM hUMleW hfix hmin

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
