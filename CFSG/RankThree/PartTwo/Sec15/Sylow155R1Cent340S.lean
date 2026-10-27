module

public import CFSG.RankThree.S4Free.StellmacherHosts
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent340Comp
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent340E
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent340Fit
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent340Op
public import CFSG.RankThree.PartTwo.Sec3.AlternatingSLTwoLocalRank

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

theorem res1340_mulAut_eq_one {L : Type*} [Group L] [Finite L]
    [Group.IsPerfect L] {N : Subgroup L} [N.Normal] (hN : Group.IsSolvable N)
    (hN3 : ¬ 3 ∣ Nat.card N) (hsimple : IsSimpleGroup (L ⧸ N)) {E : Subgroup L}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    {S : Type} [Group S] [Finite S] (hS3 : ¬ 3 ∣ Nat.card S) (hS2 : CFSG.pCore 2 S = ⊥)
    (hSz : CFSG.RankThree.S4Free.SzSections S)
    (hrank : ∀ p : ℕ, p.Prime → 5 ≤ p → CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 2)
    (φ : L →* MulAut S) : φ = 1 := by
  have hZ : ∀ J : Subgroup S, CFSG.IsComponent J → Subgroup.center ↥J = ⊥ := fun J hJ =>
    res1340_center_eq_bot_of_isComponent hS2 hSz hJ
  have hthree : ∀ J₁ J₂ J₃ : Subgroup S, CFSG.IsComponent J₁ → CFSG.IsComponent J₂ →
      CFSG.IsComponent J₃ → J₁ = J₂ ∨ J₁ = J₃ ∨ J₂ = J₃ := fun J₁ J₂ J₃ h₁ h₂ h₃ =>
    res1340_eq_or_eq_of_pRank_five (hrank 5 (by norm_num) le_rfl) hZ
      (fun J hJ => res1340_five_dvd_card_of_isComponent hSz hJ) h₁ h₂ h₃
  have hlayer : ∀ l : L, ∀ s ∈ CFSG.layer S, φ l s = s :=
    res1340_fixes_layer hN hN3 hsimple hE hE9 hS3 hSz hZ hthree φ
  have hpCore : ∀ p : ℕ, p.Prime → ∀ l : L, ∀ s ∈ CFSG.pCore p S, φ l s = s := by
    intro p hp l s hs
    have : Fact p.Prime := ⟨hp⟩
    by_cases hp2 : p = 2
    · subst hp2
      rw [hS2, Subgroup.mem_bot] at hs
      rw [hs, map_one]
    by_cases hp3 : p = 3
    ·
      subst hp3
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 3) (G := S))
      have hk0 : k = 0 := by
        by_contra hk0
        refine hS3 ((dvd_pow_self 3 hk0).trans ?_)
        rw [← hk]
        exact Subgroup.card_subgroup_dvd_card _
      rw [hk0, pow_zero, Subgroup.card_eq_one] at hk
      rw [hk, Subgroup.mem_bot] at hs
      rw [hs, map_one]
    have hp5 : 5 ≤ p := by
      rcases hp.eq_two_or_odd' with h | ⟨m, hm⟩
      · exact absurd h hp2
      · have := hp.two_le
        omega
    have hDrank : CFSG.Open.pRank p (⊤ : Subgroup ↥(CFSG.pCore p S)) ≤ 2 :=
      calc CFSG.Open.pRank p (⊤ : Subgroup ↥(CFSG.pCore p S))
          ≤ CFSG.Open.pRank p ((⊤ : Subgroup ↥(CFSG.pCore p S)).map (CFSG.pCore p S).subtype) :=
            CFSG.SectionRank.pRank_le_map hp.one_lt (CFSG.pCore p S).subtype
              (CFSG.pCore p S).subtype_injective _
        _ ≤ CFSG.Open.pRank p (⊤ : Subgroup S) := CFSG.SectionRank.pRank_mono hp.one_lt le_top
        _ ≤ 2 := hrank p hp hp5
    have h1 := res1340_mulAut_eq_one_of_pRank_le_two hN hN3 hsimple hE hE9 hp5
      (CFSG.pCore_isPGroup (p := p) (G := S)) hDrank
      ((Sec3.restrictCharacteristic (CFSG.pCore p S)).comp φ)
    have h2 : Sec3.restrictCharacteristic (CFSG.pCore p S) (φ l) = 1 := by
      simpa using congrArg (fun f : L →* MulAut ↥(CFSG.pCore p S) => f l) h1
    have h3 := congrArg
      (fun σ : MulAut ↥(CFSG.pCore p S) => ((σ ⟨s, hs⟩ : ↥(CFSG.pCore p S)) : S)) h2
    simpa [Sec3.restrictCharacteristic_apply_coe] using h3
  exact res1340_mulAut_eq_one_of_fixes_generalizedFitting φ
    (res1340_fixes_generalizedFitting φ (res1340_fixes_fittingSubgroup φ hpCore) hlayer)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
