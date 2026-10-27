module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16NineOpp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3L4Alpha
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3L4Norm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3L4Sub
public import CFSG.LocalAnalysis.UniquenessCase.UC9R96Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Cent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open S18 (tilOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

private theorem s16t_l4_prime_dvd_of_quot {Z : Subgroup G}
    {Ψ : ↥Z →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (h : Close16Quot3 Z (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) Ψ) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hqZ : q ∣ Nat.card ↥Z) : q = 3 ∨ q = 7 := by
  rw [h.card_eq, close16_card_sl_three_two] at hqZ
  rcases (Nat.Prime.dvd_mul hq).1 hqZ with hk | h168
  · exfalso
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥Ψ.ker)).1 h.ker_two
    rw [hn] at hk
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow hk))
  · have h168' : q ∣ 2 ^ 3 * 3 * 7 := by norm_num; exact h168
    rcases (Nat.Prime.dvd_mul hq).1 h168' with h1 | h7
    · rcases (Nat.Prime.dvd_mul hq).1 h1 with h8 | h3
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1
          (hq.dvd_of_dvd_pow h8)) hq2
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 h3)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h7)

private theorem s16t_l4_exists_card_three_opp {Z : Subgroup G}
    {Ψ : ↥Z →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (h : Close16Quot3 Z (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) Ψ) :
    ∃ D₃ : Subgroup G, D₃ ≤ Opp 3 Z ∧ Nat.card D₃ = 3 := by
  have hdvd := Subgroup.card_dvd_of_surjective
    (Ψ.subgroupMap_surjective ((Opp 3 Z).subgroupOf Z))
  have hsurj := h.opp_surjective
  rw [hsurj, Subgroup.card_top,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (close16_opp_le 3 Z)).toEquiv] at hdvd
  have h3 : 3 ∣ Nat.card ↥(Opp 3 Z) := h.three_dvd.trans hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Opp 3 Z)) 3 h3
  refine ⟨(Subgroup.zpowers x).map (Opp 3 Z).subtype, ?_, ?_⟩
  · exact fun g ⟨y, _, hy⟩ => hy ▸ y.2
  · rw [Subgroup.card_map_of_injective (Opp 3 Z).subtype_injective, Nat.card_zpowers, hx]

theorem s16t_l4_uniqueMax_of_ptStab (hS : S16tL4Setting D V₀ V L hV)
    (hSP : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M) (h61 : UC6.R6_1 D)
    (h921 : R9_21Opp D) (h96 : UC9R96.R9_6At7 D) (h78 : R7_8At3 D)
    (hV₀ : V₀ ≠ ⊥) {Y : Subgroup G} (hY : S16tL4Pack D V₀ V L hV Y) {w : G} (hw : w ∈ V)
    (hpt : Close16PtStab (lBar V₀ V hV L) (tilOf V₀ V hV w hw)) :
    UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨Ψ, hΨ, hker⟩ := s16t_l4_zc_quot hS hY hw hpt
  set Z : Subgroup G := Y ⊓ centralizer ({w} : Set G) with hZdef
  have hZM : Z ≤ D.M := inf_le_left.trans hY.le
  have hN7 : ∀ A : Subgroup G, A ≤ Y → Nat.card A = 7 → normalizer (A : Set G) ≤ D.M :=
    fun A hAY hA => s16t_l4_normalizer_seven_le h78 hSP hS hV₀ hY hAY hA
  rcases h921 hSP Z hΨ.opp_ne_bot hZM (hΨ.pCore_ne_bot hker) (s16t_l4_alpha hS hY hw hpt)
      hΨ.opp_index with huniq | hY2
  · exact uc22p22u_uniqueMax_mono D (le_inf hZM inf_le_right) inf_le_left huniq
  · exfalso
    obtain ⟨hY9, hne, hsub, -⟩ := hY2
    obtain ⟨N, hNmem, hNM⟩ : ∃ N ∈ calMOf Z, N ≠ D.M := by
      by_contra hcon
      apply hne
      ext N
      constructor
      · intro hN
        by_contra h
        exact hcon ⟨N, hN, h⟩
      · intro hN
        rw [Set.mem_singleton_iff] at hN
        rw [hN]
        exact ⟨D.maxLocal, hZM⟩
    have hNH : N ∈ F09.calH9 D Z := by
      rcases hsub hNmem with h | h
      · exact h
      · exact absurd (Set.mem_singleton_iff.1 h) hNM
    have hfix : ∀ x ∈ Y ⊓ N, ⁅x, w⁆ ∈ V₀ :=
      s16t_l4_fix_of_inf hS h61 hY hw hpt hNmem.1 hNmem.2 hNH.2.1
    have hcalC := s16t_l4_opp_mem_calC hS hY hw hpt hNmem.2 hfix
    obtain ⟨D₃, hD₃, hD₃card⟩ := s16t_l4_exists_card_three_opp hΨ
    obtain ⟨e⟩ := hΨ.opp_bar2
    have hnorm : ∀ A : Subgroup G, A ≤ Opp 3 Z → (Nat.card A).Prime → Odd (Nat.card A) →
        normalizer (A : Set G) ≤ D.M := by
      intro A hAX hAp hAodd
      have hAZ : A ≤ Z := hAX.trans (close16_opp_le 3 Z)
      have hAne2 : Nat.card A ≠ 2 := fun h => by
        rw [h] at hAodd
        exact absurd hAodd (by decide)
      rcases s16t_l4_prime_dvd_of_quot hΨ hAp hAne2 (Subgroup.card_dvd_of_le hAZ) with h3 | h7
      · have hA3 : IsPGroup 3 ↥A := IsPGroup.of_card (n := 1) (by rw [h3]; norm_num)
        have hAne : A ≠ ⊥ := fun h => by
          rw [h, Subgroup.card_bot] at h3
          exact absurd h3 (by norm_num)
        exact hSP.normalizer_le hAne hA3 (hAZ.trans hZM)
      · exact hN7 A (hAZ.trans inf_le_left) h7
    exact h96 Z N D₃ ⟨hY9, hNH, hD₃, hD₃card⟩ (UC9R96.ne_top_of_mem_calMOf D hNmem) hcalC
      (close16_isL2Odd_seven e) hnorm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
