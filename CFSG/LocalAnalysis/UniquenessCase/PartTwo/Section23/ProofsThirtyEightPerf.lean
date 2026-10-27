module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsPerfect
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwoCommutators

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def S23_38_perf_Oq (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ X : Subgroup G,
    X ≤ CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) → c.B0 ≤ Subgroup.normalizer (X : Set G) →
    (∀ b ∈ c.B0, b ≠ 1 → Subgroup.closure {z : G | ∃ x ∈ X, z = ⁅x, b⁆} = X) →
    barImage D.M X ≤ Subgroup.centralizer (CFSG.pCore q (Bar2 D.M) : Set (Bar2 D.M))

theorem s23_38_perf_of (D : Data G) (Ch : Choice2011 G) (h37 : S23_37 D Ch)
    (hOq : S23_38_perf_Oq D Ch)
    (hn3 : H1930 D → ∀ c : Ctx23L D Ch, 3 ≤ c.n) : S23_38_perf D Ch := by
  intro h1930 c X hX hB0norm hperf
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS_le_T : CFSG.Open.pCoreOf 2 (c.L ⊔ D.T) ≤ D.T :=
    uc22p20b_pCoreOf_le_T D le_sup_right
  have hX_le_M : X ≤ D.M := hX.trans (hS_le_T.trans D.sylowM.le)
  have hX2 : IsPGroup 2 X :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (c.L ⊔ D.T)).to_le hX
  obtain ⟨b1, hb1B0, hb1ne, hb1res⟩ := uc22s2338_exists_b1 D c h1930 hn3
  have hXbar_centE : barImage D.M X ≤
      Subgroup.centralizer (CFSG.layer (Bar2 D.M) : Set (Bar2 D.M)) := by
    rw [← hperf b1 hb1B0 hb1ne]
    exact uc22s2338_barImage_closure_le_centralizer_layer D Ch h37 h1930 c hb1B0 hb1res hX_le_M
  have hXbar_centF : barImage D.M X ≤
      Subgroup.centralizer (CFSG.fittingSubgroup (Bar2 D.M) : Set (Bar2 D.M)) := by
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
    refine CFSG.subgroup_le_centralizer_iSup_of_le_centralizer
      (fun p : (Nat.card (Bar2 D.M)).primeFactors => CFSG.pCore (p : ℕ) (Bar2 D.M)) ?_
    intro p
    have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    by_cases hp2 : (p : ℕ) = 2
    · rw [hp2, uc22p20c_pCore_quotient_pCore (H := ↥D.M) (p := 2)]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Subgroup.mem_bot.mp hy]
      simp
    · exact hOq h1930 c (p : ℕ) hp hp2 X hX hB0norm hperf
  exact le_pCoreOf_two_of_barImage_centralizes hX_le_M hX2 hXbar_centF hXbar_centE

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
