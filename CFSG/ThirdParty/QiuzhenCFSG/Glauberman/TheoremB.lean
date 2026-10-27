module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_2
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremA
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma6_3
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.InvolvedQuotient

namespace CFSG
end CFSG
open CFSG

/-!
# Glauberman's Theorem B

The strong-induction proof of condition `(C_p)` from non-involvement of `Qd(p)`.
The trivial-`p`-core branch uses Theorem 5.1; the nontrivial-`p`-core branch uses
Theorem 5.2, Theorem A, and Lemma 6.3 on smaller subquotients.
-/

open scoped Pointwise commutatorElement

namespace CFSG.Glauberman

universe u

/-- Glauberman's Theorem B ([6], §2, p. 1105): if `p` is odd and `Qd(p)` is not
involved in the finite group `G`, then the ZJ characteristic functor satisfies
condition `(C_p)` on every Sylow `p`-subgroup of `G`. -/
public theorem theoremB {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {G : Type u} [Group G] [Finite G] (S : Sylow p G) :
    ¬ Involved (Qd p) G →
      ∀ W : Set G, W.Nonempty → W ⊆ (S : Subgroup G) →
        ∀ g : G, conjSubset g W ⊆ (S : Subgroup G) →
          ∃ c n : G,
            c ∈ Subgroup.centralizer W ∧
              n ∈ Subgroup.normalizer ((ZJ (G := G) S.toSubgroup : Subgroup G) : Set G) ∧
                g = c * n := by
  classical
  intro hInvG
  change Cp (zjCharacteristicFunctor p) S
  let P : ℕ → Prop := fun n =>
    ∀ (G : Type u) [Group G] [Finite G], Nat.card G = n →
      ¬ Involved (Qd p) G → SatisfiesCp (zjCharacteristicFunctor p) G
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        dsimp only [P]
        intro G _ _ hGcard hInv
        by_cases hpdiv : p ∣ Nat.card G
        · by_cases hcore : pCore p G = ⊥
          · intro S
            apply theorem5_1 S
            left
            intro S₂ H hZleH hHleS₂
            let N : Subgroup G := Subgroup.normalizer (H : Set G)
            have hS₂ne : (S₂ : Subgroup G) ≠ ⊥ :=
              Sylow.ne_bot_of_dvd_card S₂ hpdiv
            have hZne : Zsub (S₂ : Subgroup G) ≠ ⊥ := by
              change centerIn (G := G) (S₂ : Subgroup G) ≠ ⊥
              have : Nontrivial ↥(S₂ : Subgroup G) :=
                (Subgroup.nontrivial_iff_ne_bot (S₂ : Subgroup G)).2 hS₂ne
              have hcenter_ne_bot : Subgroup.center ↥(S₂ : Subgroup G) ≠ ⊥ :=
                ne_of_gt (IsPGroup.bot_lt_center (p := p)
                  (G := ↥(S₂ : Subgroup G)) S₂.isPGroup')
              intro hcenterIn_bot
              apply hcenter_ne_bot
              ext z
              constructor
              · intro hz
                have hzCenterIn : ((z : ↥(S₂ : Subgroup G)) : G) ∈
                    centerIn (G := G) (S₂ : Subgroup G) := by
                  refine ⟨z.property, ?_⟩
                  intro y hy
                  have hcomm := Subgroup.mem_center_iff.mp hz ⟨y, hy⟩
                  exact congrArg Subtype.val hcomm
                have hzBot : ((z : ↥(S₂ : Subgroup G)) : G) ∈
                    (⊥ : Subgroup G) := by
                  simpa [hcenterIn_bot] using hzCenterIn
                have hz_one : ((z : ↥(S₂ : Subgroup G)) : G) = 1 := by
                  simpa using hzBot
                exact Subtype.ext hz_one
              · intro hz
                rw [Subgroup.mem_bot] at hz
                simp [hz]
            have hHne : H ≠ ⊥ := by
              intro hHbot
              apply hZne
              apply le_bot_iff.mp
              simpa [hHbot] using hZleH
            have hNne : N ≠ ⊤ := by
              intro hNtop
              have hHnormal : H.Normal :=
                Subgroup.normalizer_eq_top_iff.mp (by simpa [N] using hNtop)
              have hHp : IsPGroup p H := IsPGroup.to_le S₂.isPGroup' hHleS₂
              have hHcore : H ≤ pCore p G :=
                le_pCore_of_normal_isPGroup hHnormal hHp
              apply hHne
              apply le_bot_iff.mp
              simpa [hcore] using hHcore
            have hNcard : Nat.card ↥N < Nat.card G := by
              have hNlt : N < (⊤ : Subgroup G) := lt_top_iff_ne_top.mpr hNne
              simpa using natCard_lt_of_subgroup_lt hNlt
            have hNcard_n : Nat.card ↥N < n := by
              simpa [← hGcard] using hNcard
            have hInvN : ¬ Involved (Qd p) ↥N := by
              intro h
              exact hInv (involved_of_involved_subgroup h)
            exact ih (Nat.card ↥N) hNcard_n (↥N) rfl hInvN
          · apply theorem5_2 (zjCharacteristicFunctor p)
            · intro H N _ hcentral S₀
              have hstable : pStable p (H ⧸ N) :=
                (lemma6_3 (p := p) hpodd (G := G)).mp hInv H N
              change (ZJ (G := H ⧸ N) (S₀ : Subgroup (H ⧸ N))).Normal
              let : (ZJ (G := H ⧸ N) (S₀ : Subgroup (H ⧸ N))).Characteristic :=
                TheoremA.theoremA hpodd S₀ hstable hcentral
              infer_instance
            · intro H N _ hcard
              have hcard_n : Nat.card (H ⧸ N) < n := by
                simpa [← hGcard] using hcard
              have hInvHN : ¬ Involved (Qd p) (H ⧸ N) := by
                intro h
                exact hInv (involved_of_involved_subgroup
                  (involved_of_involved_quotient N h))
              exact ih (Nat.card (H ⧸ N)) hcard_n (H ⧸ N) rfl hInvHN
            · exact hcore
        · intro S
          have hScard : Nat.card (S : Subgroup G) = 1 := by
            rw [Sylow.card_eq_multiplicity S,
              Nat.factorization_eq_zero_of_not_dvd hpdiv, pow_zero]
          have hSbot : (S : Subgroup G) = ⊥ :=
            Subgroup.card_eq_one.mp hScard
          intro W hWne hWle g hWg
          refine ⟨g, 1, ?_, by simp, by simp⟩
          rw [Subgroup.mem_centralizer_iff]
          intro w hw
          have hwS := hWle hw
          rw [hSbot] at hwS
          have hw1 : w = 1 := by simpa using hwS
          simp [hw1]
  exact hP (Nat.card G) G rfl hInvG S

#print axioms theoremB

end CFSG.Glauberman
