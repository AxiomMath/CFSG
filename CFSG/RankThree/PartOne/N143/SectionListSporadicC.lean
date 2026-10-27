module

public import CFSG.RankThree.PartOne.N143.SectionListProof
public import CFSG.RankThree.PartOne.S11d.OutPCyclicThetaClosed
import CFSG.RankThree.PartOne.N143.Co1TwoRank
import CFSG.Sporadic.NativeFinite

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly TauCeti Subgroup
open CFSG.Blueprint.NativeSporadic (Carrier IsSporadic)

theorem co1TwoPowFive :
    ∀ (T : Type) [Group T], IsSporadic T .Co1 →
      ∃ U : Subgroup T, IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ (3 + 2) := by
  intro T _ ⟨e⟩
  have hfin : Finite (Carrier .Co1) := CFSG.Sporadic.finite_carrier_of_ne_M .Co1 (by decide)
  have : Finite T := Finite.of_equiv _ e.toEquiv.symm
  exact (co1_two_rank_at_least_five T ⟨e⟩).1

theorem sporadic_no_seven_center
    {s : SporadicName} (hs : s ∈ Census3.sporadicsThm3) {M : Type} [Group M] [Finite M]
    (hM : CFSG.IsQuasisimple M) (e : (M ⧸ center M) ≃* (CFSGIndex.sporadic s).Group) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ) : ¬ ℓ ∣ Nat.card (center M) := by
  intro hdvd
  have : Group.IsPerfect M := hM.1
  obtain ⟨c⟩ := TCB.nonempty_carrier_mulEquiv_group s
  obtain ⟨hpair, hnot⟩ := Mult.sporadic_residual_of_center (e.trans c.symm) hℓ (by omega) hdvd
  refine hnot ?_
  rcases hpair with ⟨rfl, -⟩ | ⟨rfl, hs7⟩ | rfl
  · omega
  · rcases hs7 with rfl | rfl | rfl | rfl | rfl
    · exact absurd hs (by simp [Census3.sporadicsThm3])
    · exact absurd hs (by simp [Census3.sporadicsThm3])
    · exact MultRes.sporadicKernelTrivial_th_seven
    · exact absurd hs (by simp [Census3.sporadicsThm3])
    · exact MultRes.sporadicKernelTrivial_on_seven
  · exact absurd hs (by simp [Census3.sporadicsThm3])

theorem lowTwoRankSectionListFor_sporadic :
    LowTwoRankSectionListFor IsSporadicIndex := by
  have hCo1 := co1TwoPowFive
  intro L _ _ hK he H M _ _ hM π hπ hU ⟨i, hi, ⟨e⟩⟩
  cases i with
  | cyclic p hp => exact absurd hi (by simp [IsSporadicIndex])
  | alternating n hn => exact absurd hi (by simp [IsSporadicIndex])
  | lie d => exact absurd hi (by simp [IsSporadicIndex])
  | sporadic s =>
    by_cases hs : s ∈ Census3.sporadicsThm3
    · exact ⟨Census3.TheoremThreeList.of_sporadic hs e, fun ℓ hℓ h7 =>
        sporadic_no_seven_center hs hM e hℓ h7⟩
    · exfalso
      have : IsSimpleGroup (M ⧸ center M) := hM.2.1
      have hnonab : ∃ a b : M ⧸ center M, a * b ≠ b * a := hM.2.2
      obtain ⟨c⟩ := TCB.nonempty_carrier_mulEquiv_group s
      let e2 : (M ⧸ center M) ≃* Carrier s := e.trans c.symm
      let ψ : H →* M ⧸ center M := (QuotientGroup.mk' (center M)).comp π
      have hψs : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hπ
      let ψ' : H →* Carrier s := (e2 : (M ⧸ center M) →* Carrier s).comp ψ
      have hψ's : Function.Surjective ψ' := e2.surjective.comp hψs
      let iso : (H ⧸ ψ'.ker) ≃* Carrier s := QuotientGroup.quotientKerEquivOfSurjective ψ' hψ's
      have hoff : s = .Co1 ∨ s = .Fi22 ∨ s = .Fi23 ∨ s = .Fi24Prime ∨ s = .B ∨ s = .M := by
        cases s <;> simp [Census3.sporadicsThm3] at hs ⊢
      have hsec := sporadicSectionCases_closed
      have he' : CFSG.twoLocalOddRank L ≤ 3 := by
        rw [← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank]
        exact he
      have he4 : 4 ≤ CFSG.Assembly.evenRank L → False := fun h => by omega
      rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨U, hUab, hUcard⟩ := hCo1 (M ⧸ center M) ⟨e2⟩
        exact hU ⟨U, hUab, hUcard⟩
      · exact he4 (hsec.fi22 L H ψ'.ker ⟨iso⟩)
      · exact he4 (hsec.fi23 L H ψ'.ker ⟨iso⟩)
      · exact he4 (hsec.fi24 L H ψ'.ker ⟨iso⟩)
      · exact he4 (hsec.b L H ψ'.ker ⟨iso⟩)
      · exact he4 (hsec.m L H ψ'.ker (M ⧸ center M) hnonab ⟨iso.trans e2.symm⟩ ⟨e2⟩)

end CFSG.RankThree.PartOne.N143
