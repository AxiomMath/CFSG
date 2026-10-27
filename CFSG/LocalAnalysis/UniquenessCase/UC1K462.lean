module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K462Basic
public import CFSG.LocalAnalysis.UniquenessCase.UC6K42j
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL2Main
public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs462

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UCK.Insp (InspPair)
open scoped MatrixGroups
open UC46

theorem k462_of_inputs (hK42 : K42) (h45 : K45Odd) (hQ : QuasisimpleOfCentral)
    (hL : K46Quasisimple) (hL2 : InspL2) (hI2L2 : Insp2L2) (hI2L3 : Insp2L3)
    (hI2J1 : Insp2J1) : K462 := by
  intro p _ hp G _ _ hK V _ _ _ ρ hρ hirr D hD hDG hfix h3 hperf
  have h : Hyp p G V ρ D := ⟨⟨hp, hK, hρ, hirr, hD, hDG, hfix⟩, h3, hperf⟩
  have hno : ∀ R : Subgroup G, InspPair 2 D R → False := by
    rintro R ⟨hp2, hab, hne, hn, hc⟩
    exact no_abelian_two hK42 h.toHyp45 R hp2 hab hne hn hc
  rcases h45 p G V ρ D h with hc | hA
  · obtain ⟨hqs, -, -⟩ := hQ p G V ρ D h hc
    rcases hL G hK hqs h3 with ⟨p', f, hmodel⟩ | ⟨p', f, hmod, hmodel⟩ | ⟨p', f, hmod, hmodel⟩ |
      hspor | hSL
    · by_cases hp2 : p' = 2
      · subst hp2
        by_cases hodd : Odd f
        · exact Or.inr (Or.inl ⟨f, hodd, hmodel⟩)
        · exfalso
          obtain ⟨U, hU⟩ := (hI2L2 G f hmodel 3 Nat.prime_three (by norm_num)
            (three_dvd_two_pow_sub_one (Nat.not_odd_iff_even.1 hodd))).2 D hD
          exact hno U hU
      · exfalso
        obtain ⟨S, hSel, hS4, hDS, hSc⟩ := hL2 G p' f hp2 hmodel h3 D hD
        exact hno S ⟨IsPGroup.of_card (n := 2) (by rw [hS4]; norm_num), hSel.1,
          fun hbot => by rw [hbot] at hS4; simp at hS4, hDS, hSc⟩
    · exact (hno _ (hI2L3 G (Or.inl ⟨p', f, hmod, hmodel⟩) D hD).choose_spec).elim
    · exact (hno _ (hI2L3 G (Or.inr ⟨p', f, hmod, hmodel⟩) D hD).choose_spec).elim
    · exact (hno _ (hI2J1 G hspor D hD).choose_spec).elim
    · exact Or.inl hSL
  · exact Or.inr (Or.inr hA)

theorem k46semireg_of_inputs (hK42 : K42) (h462 : K462) (hI2L2 : Insp2L2)
    (hZ : ZassenhausPerfect) : K46Semireg := by
  intro p _ hp G _ _ hK V _ _ _ ρ hρ hirr D hD hDG hfix h3 hperf hodd
  rcases h462 p hp G hK V ρ hρ hirr D hD hDG hfix h3 hperf with
    ⟨F, _, _, hFodd, ⟨φ⟩⟩ | ⟨n, hn, hmodel⟩ | hA
  · left
    have hsemi := sl2_semiregular hp hFodd φ ρ hρ hirr hodd
    have hcard : Nat.card G ≠ 1 := by
      intro h1
      have := Subgroup.card_le_card_group D
      omega
    exact hZ p G hperf V ρ hρ hsemi hcard
  · exfalso
    haveI := hirr
    haveI : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra (ZMod p) G) ρ.asModule
    obtain ⟨hpp, hf1, -, hne22, -⟩ := hmodel.admissible
    have hn1 : n ≠ 1 := by
      intro h; apply hne22; rw [h]; norm_num
    have hn2 : 2 ≤ n := by omega
    have hbig : 2 ^ n - 1 ≠ 1 := by
      have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      omega
    set r := (2 ^ n - 1).minFac with hr_def
    have hr : r.Prime := Nat.minFac_prime hbig
    have hrd : r ∣ 2 ^ n - 1 := Nat.minFac_dvd _
    have hr2 : r ≠ 2 := by
      intro h
      have h1 : 2 ∣ 2 ^ n - 1 := h ▸ hrd
      have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
      have := Nat.one_le_two_pow (n := n)
      omega
    obtain ⟨⟨A, hA⟩, hU⟩ := hI2L2 G n hmodel r hr hr2 hrd
    have hfixA := hodd r A hr hr2 hA
    have hrp : r ≠ p := by
      intro h
      subst h
      have hAp : IsPGroup r A := IsPGroup.of_card (n := 1) (by rw [hA]; simp)
      exact fixV_ne_bot_of_pGroup (ρ := ρ) hAp hfixA
    obtain ⟨U, hUp, hUab, hUne, hAU, hAc⟩ := hU A hA
    have h2p : 2 ≠ p := by omega
    exact (hK42 p Fact.out G hK V ρ hρ 2 r Nat.prime_two hr h2p hrp (Ne.symm hr2) A hA hfixA U hUp
      hUne hAU hAc).1 hUab
  · exact Or.inr hA

theorem k462_of_named (h45 : K45Odd) (hQ : QuasisimpleOfCentral) (hL : K46Quasisimple)
    (hI2L2 : Insp2L2) (hI2L3 : Insp2L3) (hI2J1 : Insp2J1) : K462 :=
  k462_of_inputs CFSG.LocalAnalysis.UniquenessCase.UC6.k42_uc6 h45 hQ hL inspL2_holds hI2L2
    hI2L3 hI2J1

theorem k46semireg_of_named (h45 : K45Odd) (hQ : QuasisimpleOfCentral) (hL : K46Quasisimple)
    (hI2L2 : Insp2L2) (hI2L3 : Insp2L3) (hI2J1 : Insp2J1) (hZ : ZassenhausPerfect) :
    K46Semireg :=
  k46semireg_of_inputs CFSG.LocalAnalysis.UniquenessCase.UC6.k42_uc6
    (k462_of_named h45 hQ hL hI2L2 hI2L3 hI2J1) hI2L2 hZ

end CFSG.LocalAnalysis.UniquenessCase.UCK
