module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Basic.Finite.Defs

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreCentralizerT1
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreLayerASeven
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.DihedralStructure
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Cyclic first case: both reflections invert every nontrivial `q`-core, `q ≠ 3`

Supporting fact 2 for the Theorem-C inputs.  For each nontrivial odd
`q`-core of `U` with `q ≠ 3`, Step B's dichotomy says each of `t₁`, `t₂`
either inverts or centralizes the core.  Both centralizing is impossible by
`firstCase_cyclic_S_not_centralizes_nontrivial_qCore` because
`S = ⟨t₁, t₂⟩`; a mixed pair would orient the core and force `q = 3` by
the A₇-layer Step A theorem.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the cyclic first-case A₇ model, both reflections invert every
nontrivial `q`-core of `U` for `q ≠ 3`. -/
public theorem firstCase_cyclic_reflections_invert_qCore_of_ne_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7)))
    (hp3 : od.p = 3)
    {q : ℕ} (hq : q.Prime)
    (hqne : qCoreOf od.d.bg.U q ≠ ⊥) (hq3 : q ≠ 3) :
    qCoreOf od.d.bg.U q ≤ od.d.I1 ∧ qCoreOf od.d.bg.U q ≤ od.d.I2 := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have hHhat : c.Hhat = c.H := cyclicCore_hhat_eq hmin c hcyclic
  have hUeq : c.U = od.d.bg.U := firstCase_U_eq_bg_U c od.d
  have hr1 : c.IsReflection od.d.bg.t1 := by
    constructor
    · simpa [od.d.S_eq] using od.d.bg.t1_mem_S
    · simpa [od.d.S0_eq] using od.d.bg.t1_not_mem_S0
  have hr2 : c.IsReflection od.d.bg.t2 := by
    constructor
    · simpa [od.d.S_eq] using od.d.bg.t2_mem_S
    · simpa [od.d.S0_eq] using od.d.bg.t2_not_mem_S0
  let Pq : Subgroup G := qCoreOf od.d.bg.U q
  have hcase1 : Pq ≤ od.d.I1 ∨
      od.d.bg.t1 ∈ Subgroup.centralizer (Pq : Set G) := by
    simpa [Pq, hUeq] using
      (primeCore_le_invertedHall_or_reflection_centralizes
        c od.d.bg.t1 hr1 od.d.I1 od.d.I1_inverted od.d.I1_hall hq)
  have hcase2 : Pq ≤ od.d.I2 ∨
      od.d.bg.t2 ∈ Subgroup.centralizer (Pq : Set G) := by
    simpa [Pq, hUeq] using
      (primeCore_le_invertedHall_or_reflection_centralizes
        c od.d.bg.t2 hr2 od.d.I2 od.d.I2_inverted od.d.I2_hall hq)
  rcases hcase1 with hle1 | hcent1
  · rcases hcase2 with hle2 | hcent2
    · exact ⟨hle1, hle2⟩
    · let d' : FirstCaseBGData c := swapFirstCaseBGData c od.d
      let od' : FirstCaseOrientedPrimeData c := {
        d := d'
        p := q
        p_prime := hq
        primeCore_ne_bot := by
          simpa [hUeq] using hqne
        t1_centralizes := by
          simpa [d', swap_t1_eq, hUeq] using hcent2
        primeCore_le_I2 := by
          simpa [d', swap_I2_eq, hUeq] using hle1
      }
      have hqeq : q = 3 :=
        firstCase_cyclic_oriented_prime_eq_three hmin c hfirst hcyclic od'
      exact False.elim (hq3 hqeq)
  · rcases hcase2 with hle2 | hcent2
    · let od' : FirstCaseOrientedPrimeData c := {
        d := od.d
        p := q
        p_prime := hq
        primeCore_ne_bot := by
          simpa [hUeq] using hqne
        t1_centralizes := by
          simpa [hUeq] using hcent1
        primeCore_le_I2 := by
          simpa [hUeq] using hle2
      }
      have hqeq : q = 3 :=
        firstCase_cyclic_oriented_prime_eq_three hmin c hfirst hcyclic od'
      exact False.elim (hq3 hqeq)
    · have hSleC : (od.d.bg.S : Subgroup G) ≤
          Subgroup.centralizer (Pq : Set G) := by
        rw [BenderGlauberman.Hyp11.S_eq_closure_t1_t2 od.d.bg]
        refine (Subgroup.closure_le _).2 ?_
        intro x hx
        simp at hx
        rcases hx with rfl | rfl
        · exact hcent1
        · exact hcent2
      exact False.elim ((firstCase_cyclic_S_not_centralizes_nontrivial_qCore
        hmin c od hfirst hHhat hU Q M hMmax hMN hSM fd hV2 hA7 hp3 hqne) hSleC)

end CFSG.GorensteinWalter
