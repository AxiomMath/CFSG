module

public import CFSG.LocalAnalysis.StandardType.GGQ2TableBI1Exc
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreE6Two
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallTits
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestG2
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanksTri
public import CFSG.LocalAnalysis.StandardType.GGStdUFourExcl
import CFSG.LocalAnalysis.StandardType.GGQ2TableBI1Sp
import CFSG.LocalAnalysis.StandardType.GGQ2TableBI1U
import CFSG.LocalAnalysis.StandardType.GGQ2TableBI1Omega
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBVac
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTri
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestVac
import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreNarrow
import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreOrth
import CFSG.LocalAnalysis.StandardType.GGCorFourTwoRestTwo
import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperRestLabels
import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperRestDefs
import CFSG.LocalAnalysis.StandardType.GGTableBTwDThree
import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section NotTB


theorem ggQ2TableBI1FailOn_notTB : GGQ2TableBI1FailOn fun lab => ¬ GGQ2TBLabel lab := by
  intro G _ _ p B Bs x L D J hset hp hI1 _ hM
  subst hp
  exfalso
  have hC : GGConfig 3 B Bs x L D J := hset.1.1
  have hne : B ≠ Bs := by
    rintro rfl
    refine hI1 fun b hb hc => ?_
    rw [hC.2.2.1.2.2.2.2.2.2]
    exact ⟨hb, Subgroup.mem_centralizer_iff.mpr fun j hj => (hc j hj).symm⟩
  obtain ⟨hL, lab, hlab, hraw⟩ := hM
  have hfix : ∀ S : ℕ → LargeEvenLabel → Prop, S 3 lab → GGInnerDiagOnLabel S 3 Bs L :=
    fun S hS => ⟨hL, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, _, hP⟩ => ⟨hs, hna, θ, hS, hP⟩) hraw⟩
  have hEQ : ∀ lab₀ : LargeEvenLabel, LargeEvenLabelAll lab₀ (fun R _ I _ =>
      (∃ r, GGTorusLift 3 r R ∧ GGInnerDiagBound 3 r R I) ∧
        ∃ r, GGTorusLift 3 r R ∧ GGIRankLe 3 r R I) → lab = lab₀ → False := by
    intro lab₀ h0 he
    have hM₀ := largeEvenMarking_and_labelAll (S := fun l => l = lab₀)
      (fun l _ hl => by rw [hl]; exact h0)
      (fun _ _ _ _ _ _ hP => hP.1) (hfix (fun _ l => l = lab₀) he)
    obtain ⟨-, _, _, hraw₀⟩ := hM₀
    obtain ⟨R, _, I, F, hbody⟩ := largeEvenRawDatum_exists hraw₀
    obtain ⟨-, -, θ, hcont⟩ := hbody
    obtain ⟨⟨-, hBN, h3⟩, ⟨r₁, hl₁, hb⟩, r₂, hl₂, hr⟩ := hcont
    exact hne (bstar_eq_of_bound_rank hC.1 hC.2.1
      (ggLNoncyclicInput_holds G 3 B x L hC.1) hL θ (hC.2.1.1.trans hBN)
      (fun b hb => h3 b (hC.2.1.1 hb)) hl₁ hb hl₂ hr)
  have hsp : ∀ t l, LargeEvenSplit 3 ⟨t, l, 1⟩ := fun _ _ =>
    Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  have hSM : ∀ lab₀ : LargeEvenLabel, lab₀.n = 1 →
      LargeEvenLabelAll lab₀ (fun R _ I _ => ∀ X : Subgroup (MulAut R),
        (X : Set (MulAut R)) ⊆ I → IsElemAbelian 3 X → Nat.card X < 3 ^ 3) →
      lab = lab₀ → False := by
    intro lab₀ hn₀ h0 he
    have hsp₀ : LargeEvenSplit 3 lab₀ := by
      obtain ⟨t₀, l₀, n₀⟩ := lab₀
      dsimp only at hn₀
      subst hn₀
      exact hsp t₀ l₀
    refine ggThmIHyp_false_of_labelAll (S := fun p l => p = 3 ∧ l = lab₀)
      (fun _ l _ _ hl _ => by
        obtain ⟨rfl, rfl⟩ := hl
        exact h0) hC.1 ?_
    refine largeEvenMarking_mono (fun l R _ I _ θ hP =>
      ⟨⟨rfl, hP.1⟩, ?_, hC.2.1.1.trans hP.2.1,
        fun b hb => hP.2.2 b (hC.2.1.1 hb)⟩) (hfix (fun _ l => l = lab₀) he)
    rw [hP.1]
    exact hsp₀
  obtain ⟨-, -, -, -, -, -, -, ⟨hn2, hnTB⟩, -⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨t, l, n⟩ := lab
  have hn : n = 1 := by
    have h1 : 1 ≤ n := hlab.1
    have h2 : n < 2 := hn2
    omega
  subst hn
  cases t with
  | A =>
    exact (hEQ _ (largeEvenLabelAll_and
      (largeEvenLabelAll_innerDiag_twoThree hlab ⟨rfl, rfl, Or.inl rfl⟩)
      (IOneRest.largeEvenLabelAll_iRank_twoThree hlab ⟨rfl, rfl, Or.inl rfl⟩)) rfl).elim
  | twA =>
    have hl : 2 ≤ l ∧ (l = 2 → 2 ≤ 1) := hlab.2
    rcases (show l = 3 ∨ 4 ≤ l by omega) with rfl | h4
    · exact (not_ggInnerDiagOnLabel_u4 hC (hfix _ ⟨Or.inl rfl, rfl, rfl⟩)).elim
    · exact hnTB (Or.inl ⟨rfl, h4⟩)
  | B =>
    have hl : 2 ≤ l ∧ (l = 2 → 2 ≤ 1) := hlab.2
    rcases (show l = 3 ∨ 4 ≤ l by omega) with rfl | h4
    · exact (hEQ _ (largeEvenLabelAll_bstarEq_spSix ⟨Or.inl rfl, rfl, rfl, rfl⟩) rfl).elim
    · exact hnTB (Or.inr (Or.inl ⟨Or.inl rfl, h4⟩))
  | C =>
    have hl : 2 ≤ l ∧ (l = 2 → 2 ≤ 1) := hlab.2
    rcases (show l = 3 ∨ 4 ≤ l by omega) with rfl | h4
    · exact (hEQ _ (largeEvenLabelAll_bstarEq_spSix ⟨Or.inr rfl, rfl, rfl, rfl⟩) rfl).elim
    · exact hnTB (Or.inr (Or.inl ⟨Or.inr rfl, h4⟩))
  | D =>
    have hl : 3 ≤ l := hlab.2
    rcases (show l = 3 ∨ l = 4 ∨ 5 ≤ l by omega) with rfl | rfl | h5
    · exact (hEQ _ (largeEvenLabelAll_and
        (largeEvenLabelAll_innerDiag_twoThree hlab ⟨rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩)
        (IOneRest.largeEvenLabelAll_iRank_twoThree hlab
          ⟨rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩)) rfl).elim
    · exact hnTB (Or.inr (Or.inr (Or.inl ⟨rfl, by decide, le_rfl⟩)))
    · rcases Nat.even_or_odd l with he | ho
      · exact hnTB (Or.inr (Or.inr (Or.inl ⟨rfl, he, show 4 ≤ l by omega⟩)))
      · exact (hEQ _ (largeEvenLabelAll_bstarEq_orthEq Nat.prime_three (by norm_num)
          (Or.inr ⟨rfl, h5, ho, rfl, rfl⟩)) rfl).elim
  | twD =>
    have hl : 2 ≤ l := hlab.2
    rcases (show l = 2 ∨ l = 3 ∨ l = 4 ∨ 5 ≤ l by omega) with rfl | rfl | rfl | h5
    · exact (hSM _ rfl (largeEvenLabelAll_card_lt_linearTwo Nat.prime_three (by norm_num) hlab
        (Or.inr ⟨rfl, rfl⟩)) rfl).elim
    · exact (not_ggInnerDiagOnLabel_u4 hC (hfix _ ⟨Or.inr rfl, rfl, rfl⟩)).elim
    · exact (hEQ _ (largeEvenLabelAll_bstarEq_orthEq Nat.prime_three (by norm_num)
        (Or.inl ⟨rfl, le_rfl, by decide, by norm_num, by norm_num⟩)) rfl).elim
    · rcases Nat.even_or_odd l with he | ho
      · exact (hEQ _ (largeEvenLabelAll_bstarEq_orthEq Nat.prime_three (by norm_num)
          (Or.inl ⟨rfl, show 4 ≤ l by omega, he, by norm_num, by norm_num⟩)) rfl).elim
      · exact hnTB (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, ho, show 4 ≤ l by omega⟩))))
  | E6 =>
    exact (hEQ _ (largeEvenLabelAll_bstarEq_e6Two ⟨rfl, rfl, rfl⟩) rfl).elim
  | E7 => exact hnTB (by simp [GGQ2TBLabel])
  | E8 => exact hnTB (by simp [GGQ2TBLabel])
  | F4 => exact hnTB (by simp [GGQ2TBLabel])
  | twE6 => exact hnTB (by simp [GGQ2TBLabel])
  | triD4 =>
    exact (hSM _ rfl (TableBExcSmallRest.largeEvenLabelAll_card_lt_triD4
      (fun _ => TableBExcSmallRanks.ggTriD4ThreeRankInput_holds) Nat.prime_three hlab rfl
      (hsp _ _)) rfl).elim
  | G2 =>
    have h : l = 0 ∧ 2 ≤ 1 := hlab.2
    omega
  | twB2 =>
    have h : l = 0 ∧ Odd 1 ∧ 3 ≤ 1 := hlab.2
    omega
  | twF4 =>
    have h : l = 0 ∧ Odd 1 ∧ 3 ≤ 1 := hlab.2
    omega
  | B2der =>
    exact (hSM _ rfl (largeEvenLabelAll_card_lt_b2derThree ⟨rfl, rfl⟩) rfl).elim
  | G2der =>
    exact (hSM _ rfl (TableBExcSmallRest.largeEvenLabelAll_card_lt_G2der Nat.prime_three hlab
      rfl (hsp _ _)) rfl).elim
  | twF4der =>
    exact (hSM _ rfl (TableBExcSmallRest.largeEvenLabelAll_card_lt_twF4der_holds Nat.prime_three
      hlab rfl (hsp _ _)) rfl).elim

end NotTB


theorem ggQ2TableBI1FailOn_notHeart :
    GGQ2TableBI1FailOn fun lab =>
      ¬ ((lab.tag = .twA ∧ 4 ≤ lab.rank ∧ 3 ∣ lab.rank + 1) ∨ lab.tag = .twE6) := by
  have hfail : GGQ2TableBI1FailOn fun lab =>
      GGQ2TBSpLabel lab ∨ GGQ2TBULabel lab ∨ GGQ2TBOmegaLabel lab ∨ GGQ2TBExcLabel lab ∨
        ¬ GGQ2TBLabel lab :=
    ggQ2TableBI1FailOn_sp.or (ggQ2TableBI1FailOn_unitary.or
      (ggQ2TableBI1FailOn_omega.or (ggQ2TableBI1FailOn_exc.or ggQ2TableBI1FailOn_notTB)))
  have hST : ∀ lab, ¬ ((lab.tag = .twA ∧ 4 ≤ lab.rank ∧ 3 ∣ lab.rank + 1) ∨
      lab.tag = .twE6) →
      GGQ2TBSpLabel lab ∨ GGQ2TBULabel lab ∨ GGQ2TBOmegaLabel lab ∨ GGQ2TBExcLabel lab ∨
        ¬ GGQ2TBLabel lab := by
    rintro ⟨tag, rank, n⟩ hh
    by_cases hTB : GGQ2TBLabel ⟨tag, rank, n⟩
    · dsimp only [GGQ2TBSpLabel, GGQ2TBULabel, GGQ2TBOmegaLabel, GGQ2TBExcLabel]
      dsimp only [GGQ2TBLabel] at hTB
      rcases hTB with ⟨rfl, h4⟩ | ⟨hBC, h4⟩ | ⟨rfl, he, h4⟩ |
        ⟨rfl, ho, h4⟩ | rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl ⟨rfl, h4, fun hd => hh (Or.inl ⟨rfl, h4, hd⟩)⟩)
      · rcases hBC with rfl | rfl
        · exact Or.inl ⟨Or.inl rfl, h4⟩
        · exact Or.inl ⟨Or.inr rfl, h4⟩
      · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, he, h4⟩)))
      · exact Or.inr (Or.inr (Or.inl (Or.inr ⟨rfl, ho, h4⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl rfl))))
      · exact (hh (Or.inr rfl)).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl rfl)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr rfl)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hTB)))
  intro G _ _ p B Bs x L D J hset hp hI1 _ hM
  exact hfail hset hp hI1 (largeEvenMarking_mono
    (fun lab R _ I _ θ hP => ⟨⟨hP.1.1, hST lab hP.1.2⟩, hP.2⟩) hM)

end CFSG.StandardType

end
