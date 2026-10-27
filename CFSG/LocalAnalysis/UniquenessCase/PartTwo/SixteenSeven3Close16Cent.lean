module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Alpha
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16NineOpp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Sub
public import CFSG.LocalAnalysis.UniquenessCase.UC9R96Defs
public import CFSG.LocalAnalysis.WeakClosure81.Eleven
public import CFSG.LocalAnalysis.WeakClosure81.ThreeOneMap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem close16_isL2Odd_seven {X : Type} [Group X]
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : IsL2Odd X 7 :=
  CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism X
    (CFSG.LocalAnalysis.WeakClosure81.ThreeOne.isL3_of_mulEquiv e)

private theorem close16_prime_dvd_of_quot {Z : Subgroup G}
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

private theorem close16_exists_card_three_opp {Z : Subgroup G}
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

theorem close16_centralizer_le (hS : Close16Setting D V L hV)
    (hSP : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M) (h61 : UC6.R6_1 D)
    (h921 : R9_21Opp D) (h96 : UC9R96.R9_6At7 D) {Y : Subgroup G}
    (hY : Close16Pack D V L hV Y) {z : G} (hz : z ∈ V ⊓ centralizer (D.T : Set G)) (hz1 : z ≠ 1)
    (hN7 : ∀ A : Subgroup G, A ≤ Y → Nat.card A = 7 → normalizer (A : Set G) ≤ D.M) :
    centralizer ({z} : Set G) ≤ D.M := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨Ψ, hΨ, hker⟩ := close16_zc_quot hS hY hz hz1
  set Z : Subgroup G := Y ⊓ centralizer ({z} : Set G) with hZdef
  have hZM : Z ≤ D.M := inf_le_left.trans hY.le
  have hzV : z ∈ V := (Subgroup.mem_inf.1 hz).1
  have hcen : centralizer ({z} : Set G) ≤ normalizer (Subgroup.zpowers z : Set G) :=
    CFSG.RankThree.PartOne.StrongP.centralizer_singleton_le_normalizer_zpowers z
  have hz2 : z ^ 2 = 1 := hV.2 z hzV
  have hzord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hzp : IsPGroup 2 ↥(Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzord]; norm_num)
  have hzne : Subgroup.zpowers z ≠ ⊥ := fun h => hz1 (Subgroup.zpowers_eq_bot.1 h)
  rcases h921 hSP Z hΨ.opp_ne_bot hZM (hΨ.pCore_ne_bot hker) (close16_alpha hS hY hz hz1)
      hΨ.opp_index with huniq | hY2
  · exact hcen.trans (CFSG.LocalAnalysis.WeakClosure81.normalizer_le_of_uniqueMax huniq hzne hzp
      (inf_le_right.trans hcen))
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
    have hYN : Y ⊓ N = Y ⊓ centralizer ({z} : Set G) :=
      close16_inf_eq hS h61 hY hz hz1 hNmem.1 hNmem.2 hNH.2.1
    have hcalC := close16_opp_mem_calC hS hY hz hz1 hYN
    obtain ⟨D₃, hD₃, hD₃card⟩ := close16_exists_card_three_opp hΨ
    obtain ⟨e⟩ := hΨ.opp_bar2
    have hnorm : ∀ A : Subgroup G, A ≤ Opp 3 Z → (Nat.card A).Prime → Odd (Nat.card A) →
        normalizer (A : Set G) ≤ D.M := by
      intro A hAX hAp hAodd
      have hAZ : A ≤ Z := hAX.trans (close16_opp_le 3 Z)
      have hAne2 : Nat.card A ≠ 2 := fun h => by
        rw [h] at hAodd
        exact absurd hAodd (by decide)
      rcases close16_prime_dvd_of_quot hΨ hAp hAne2 (Subgroup.card_dvd_of_le hAZ) with h3 | h7
      · have hA3 : IsPGroup 3 ↥A := IsPGroup.of_card (n := 1) (by rw [h3]; norm_num)
        have hAne : A ≠ ⊥ := fun h => by
          rw [h, Subgroup.card_bot] at h3
          exact absurd h3 (by norm_num)
        exact hSP.normalizer_le hAne hA3 (hAZ.trans hZM)
      · exact hN7 A (hAZ.trans inf_le_left) h7
    exact h96 Z N D₃ ⟨hY9, hNH, hD₃, hD₃card⟩ (UC9R96.ne_top_of_mem_calMOf D hNmem) hcalC
      (close16_isL2Odd_seven e) hnorm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
