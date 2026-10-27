module

public import CFSG.RankThree.PartTwo.Sec13.K135K3Sylow
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4Q11
public import CFSG.Milestones.ASVolI.A3Spor.Out

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier

theorem k3_J4
    {S : Type} [Group S] [Finite S]
    (e : S ≃* NativeSporadic.J4) :
    ∀ P : Subgroup (MulAut S), IsPGroup 11 P → 11 ^ 3 ≤ Nat.card P →
      ∀ α : MulAut S, α ^ 3 = 1 → (∀ π ∈ P, α * π = π * α) → α = 1 := by
  have hsimp := CFSG.Sporadic.J4.fam_j4_simplicity
  have hcard : Nat.card NativeSporadic.J4 = 86775571046077562880 := CFSG.Sporadic.J4.card_J4
  have hnp : ¬ Nat.Prime 86775571046077562880 := by norm_num
  haveI : IsSimpleGroup NativeSporadic.J4 := hsimp.2.2
  haveI : Finite NativeSporadic.J4 := hsimp.1
  have hcen : Subgroup.center S = ⊥ := by
    refine center_eq_bot_of_simple_card (X := NativeSporadic.J4) e ?_
    intro hp
    rw [hcard] at hp
    exact hnp hp
  have hodd : ∀ β : MulAut S, Odd (orderOf β) → ∃ l : S, β = MulAut.conj l :=
    CFSG.ASVolI.burnsideA315s_oddInner_J4 e
  have hinner := (CFSG.Sporadic.J4Schreier.R3E_J4_outer_automorphism_group_no_large_primes
    ⟨e⟩).2 11 (by norm_num) (by norm_num)
  intro P hP hcard' α hα hcomm
  refine k3_of_data hcen hodd (fun A hA => hinner A hA) ?_ P hP hcard' α hα hcomm
  intro Q hQ hQcard l hl3 hcommQ
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have θ : S ≃* ↥CFSG.Sporadic.J4.J :=
    e.trans (CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat)
  haveI : Finite ↥CFSG.Sporadic.J4.J := Finite.of_equiv S θ.toEquiv
  have hC : Subgroup.centralizer ((Q11Sylow : Subgroup ↥CFSG.Sporadic.J4.J) : Set ↥CFSG.Sporadic.J4.J)
      ≤ (Q11Sylow : Subgroup ↥CFSG.Sporadic.J4.J) := by
    rw [Q11Sylow_coe]
    exact CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.centralizer_Q11_le
  have hcardQ : Nat.card (Q11Sylow : Subgroup ↥CFSG.Sporadic.J4.J) ≤ Nat.card Q := by
    rw [Q11Sylow_coe, card_Q11]
    exact hQcard
  exact @eq_one_of_sylow_centralizer S ↥CFSG.Sporadic.J4.J _
    (Subgroup.toGroup CFSG.Sporadic.J4.J) _ 11 _ (by norm_num) θ Q11Sylow hC Q hQ hcardQ l hl3
    hcommQ

end CFSG.RankThree.PartTwo.Sec13.F135Last
