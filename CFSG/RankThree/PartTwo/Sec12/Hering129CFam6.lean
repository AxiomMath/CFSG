module

public import CFSG.RankThree.PartTwo.Sec12.Hering129CFam2
public import CFSG.RankThree.PartTwo.Sec12.Hering129CFam1
public import CFSG.RankThree.PartTwo.Sec12.Hering129CFamG2
public import CFSG.RankThree.PartTwo.Sec12.Hering129CFamSyl

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

namespace Hering129C

@[expose] def KFCensus46SixL3Pi : Prop :=
  KFCensusOn (fun Q _ => ∃ n : ℕ, 1 ≤ n ∧
    (Nonempty (Q ≃* projSL 3 (GaloisField 2 n)) ∨ Nonempty (Q ≃* projSU 3 2 n) ∨
      Sec4.IsSLThreeEpsAt Q (2 ^ n)) ∧ Sec4.IsSLThreePiAny Q)

@[expose] def KFCensus46SixU4 : Prop :=
  KFCensusOn (fun Q _ => ∃ n : ℕ, 1 ≤ n ∧ Nonempty (Q ≃* projSU 4 2 n))

@[expose] def KFCensus46SixD42 : Prop :=
  KFCensusOn (fun Q _ => Blueprint.ChevalleyExceptionalModel Q .trialityD4 2 1)

@[expose] def KFCensus46SixF4 : Prop :=
  KFCensusOn (fun Q _ => ∃ f : ℕ, Blueprint.ReeTitsModel Q .twistedF4 2 f ∨
    Blueprint.ReeTitsModel Q .Tits 2 f)

theorem four_le_two_pow {f : ℕ} (h : 3 ≤ 2 ^ f) : 4 ≤ 2 ^ f := by
  have hf : 2 ≤ f := by
    by_contra hlt
    push Not at hlt
    interval_cases f <;> simp at h
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

theorem kFCensus46Six_of
    (h1 : KFCensus46SixL3Pi) (h2 : KFCensus46SixU4) (h3 : KFCensus46SixD42)
    (h4 : KFCensus46SixF4) : KFCensus46Six := by
  intro Q Lb _ _ _ c a I X f hQ hD
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnot3 : ∀ n : ℕ, ¬ 3 ∣ 2 ^ n := fun n h =>
    absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  rcases hQ with (⟨n, hn, hX⟩ | ⟨f', hf⟩) | ⟨n, hn, hX⟩
  · rcases hX with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    ·
      exfalso
      obtain ⟨g, hg⟩ := (ppair_self hD).map e
      exact hg.false_of_comm_centralizer (comm_centralizer_projSL_two
        (S := projSL 2 (GaloisField 2 n)) (MulEquiv.refl _) _ hg.orderOf_s)
    ·
      by_cases hπ : Sec4.IsSLThreePiAny Q
      · exact h1 Q Lb c a I X f ⟨n, hn, Or.inl ⟨e⟩, hπ⟩ hD
      · exact (census_false_of_cyclic_sylow hD
          (isCyclic_sylow_of_isL3_not_pi (p := 2) (by norm_num) hn (Or.inr (Or.inl ⟨e⟩))
            hπ)).elim
    ·
      by_cases hπ : Sec4.IsSLThreePiAny Q
      · exact h1 Q Lb c a I X f ⟨n, hn, Or.inr (Or.inl ⟨e⟩), hπ⟩ hD
      · exact (census_false_of_cyclic_sylow hD
          (isCyclic_sylow_of_isL3_not_pi (p := 2) (by norm_num) hn (Or.inr (Or.inr ⟨e⟩))
            hπ)).elim
    ·
      exfalso
      obtain ⟨g, hg⟩ := (ppair_self hD).map e
      refine hg.false_of_abelian_sylow (sylow_comm_projSp_two ?_)
      rw [GaloisField.card 2 n (by omega)]
      exact hnot3 n
    ·
      exact h2 Q Lb c a I X f ⟨n, hn, ⟨e⟩⟩ hD
  · rcases hf with hG2 | hD4 | hSz | hF4 | hTits
    ·
      obtain ⟨r, hrc, hrp, hr3, hG⟩ := isG2D4_of_chevalley_G2 hG2
      have h4r : 4 ≤ r.card := by
        rw [hrc]
        rw [hrc] at hr3
        exact four_le_two_pow hr3
      exact census_concl_of_isG2D4 hD r 1 hG h4r (by omega) (fun h => absurd h (by norm_num))
    ·
      by_cases hf2 : 2 ≤ f'
      · obtain ⟨r, hrc, hrp, hG⟩ := isG2D4_of_chevalley_D4 hD4
        have h4r : 4 ≤ r.card := by
          rw [hrc]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ f' := Nat.pow_le_pow_right (by norm_num) hf2
        exact census_concl_of_isG2D4 hD r 3 hG h4r (by omega) (fun _ => by omega)
      · have hf1 : f' = 1 := by
          have := hD4.1.2.1
          omega
        subst hf1
        exact h3 Q Lb c a I X f hD4 hD
    ·
      exfalso
      exact ThinCatalog.not_three_dvd_card_of_suzukiModel hSz
        (hD.orderOf_c ▸ orderOf_dvd_natCard c)
    · exact h4 Q Lb c a I X f ⟨f', Or.inl hF4⟩ hD
    · exact h4 Q Lb c a I X f ⟨f', Or.inr hTits⟩ hD
  ·
    by_cases hπ : Sec4.IsSLThreePiAny Q
    · exact h1 Q Lb c a I X f ⟨n, hn, Or.inr (Or.inr hX), hπ⟩ hD
    · exact (census_false_of_cyclic_sylow hD
        (isCyclic_sylow_of_isL3_not_pi (p := 2) (by norm_num) hn (Or.inl hX) hπ)).elim

end Hering129C

end CFSG.RankThree.PartTwo.Sec12
