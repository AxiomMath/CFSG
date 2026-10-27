module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyFiveConclusion
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyFiveMinimal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyFiveNatural
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyFiveStepD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsD

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem seventeen_fiftyfive (D : Data G)
    (h109 : Inputs1719.UC2_10_9 D) (h127 : R127 D)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h111 : W3Thm111 G)
    (h143 : Inputs1719.W4Thm14_3)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V) (h3 : R17_3At D V₀ V)
    (h171 : R17_1At D V₀ V hV) :
    R17_55At D V₀ V := by
  intro L hLM hLN n hshape s hso hsn r hr hrdvd X hXL hXcard heq
  obtain ⟨hV₀, X', hX'K, hX'T, hX'card, hInU', hUTP⟩ :=
    seventeen_fiftyfive_stepA_core D h109 h3 hV hLM hLN hshape hso hsn hr hrdvd hXL hXcard heq
  obtain ⟨hPcalC, hPN, hPshape, -⟩ := perfectCore_of_isL2_or_isSz_1755 hLM hLN hshape
  have hPKM : CFSG.Quasithin.perfectCore L ≤ D.M := hPcalC.1.le
  have hsimple : IsSimpleGroup (Bar2 (CFSG.Quasithin.perfectCore L)) :=
    isSimpleGroup_bar2_of_isL2_or_isSz hPshape
  have hKZ : ⁅CFSG.Quasithin.perfectCore L, D.Z⁆ ≠ ⊥ :=
    commutator_Z_ne_bot_of_uc2_10_9 h109 hso hr hrdvd hX'K hPKM hX'T hX'card hInU' hUTP
  obtain ⟨V', -, hV'ne, hW, hnotTI, hKVeq, hK2, hV'el, hB, hO2⟩ :=
    exists_inCalW_min_commutator h127 hV.2 hPcalC hPN hsimple hUTP hKZ
  have hMV : D.M ≤ Subgroup.normalizer (V' : Set G) := hW.1.1.2.2.1
  have hM0 : D.M ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hKV : barSub (⊥ : Subgroup G) V' hV'el (CFSG.Quasithin.perfectCore L) ≠ ⊥ := by
    intro hbot
    have hct : CFSG.Quasithin.perfectCore L ≤ F11.CTilde D.M ⊥ V' :=
      (CFSG.LocalAnalysis.WeakClosure81.barSub_eq_bot_iff hV'el hMV hM0 hPKM).1 hbot
    rw [uc22p22u_cTilde_bot] at hct
    have hcent : CFSG.Quasithin.perfectCore L ≤
        Subgroup.centralizer (V' : Set G) := hct.trans inf_le_right
    exact hV'ne (hKVeq.symm.trans
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcent))
  have hs3 : 3 ≤ s := by
    rcases hso with ⟨k, hk⟩
    have hs1 : s ≠ 1 := by
      rintro rfl
      have h1 : r ∣ 1 := by simpa using hrdvd
      exact hr.not_dvd_one h1
    omega
  have h3n : 3 ≤ n := by
    have hnpos : 0 < n := by
      rcases hshape with h | h
      · exact lt_of_lt_of_le (by norm_num) (s13_two_le_of_isL2 h)
      · exact lt_of_lt_of_le (by norm_num) (s13_odd_three_le_of_isSz h).2
    exact hs3.trans (Nat.le_of_dvd hnpos hsn)
  have hn4 : n ≠ 4 := by
    rintro rfl
    have hs4 : s ≤ 4 := Nat.le_of_dvd (by norm_num) hsn
    rcases hso with ⟨k, hk⟩
    interval_cases s
    · norm_num at hsn
    · omega
  have hnat := seventeen_fiftyfive_natural_of_min D hx h61 h126 h111 h143 hV.2 hW hV'el hB hO2
    hPcalC hPN hK2 hKV hUTP h3n hn4 hPshape
  obtain ⟨P, hP⟩ := seventeen_fiftyfive_inPStar_of_natural D hx h61 hSg hW hnotTI hV'el hB
    hPcalC hPN hK2 hsimple hnat
  subst hV₀
  exact h171.1 P hP

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
