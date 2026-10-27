module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreSourceNormalizerWitness
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreCentralizerT1
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 3: the centralizer core `C_B(P) ≠ 1`

The corrected `PP^g` witness (`X = B ∩ P·P^g`, `P = O_p(U)`) is
nontrivial, and the repaired `P ∩ P^g = ⊥` (`firstCase_P_inf_Pg_eq_bot`)
makes `[P, P^g] = 1`.  Hence `P·P^g` centralizes the abelian `P`, so the
witness subgroup `X` centralizes `P` as well; since `X ≤ B`, this is a
nontrivial element of `C_B(P)`.  With `firstCase_cyclic_CB_ne_of_a7`
the landed reduction `firstCase_cyclic_primeCore_le_M_of_a7_of_CB_ne`
closes the centralizer core `O₃(U) ≤ M`.

No `sorry`, `admit`, `axiom`, or `opaque` is used.
-/

noncomputable section
namespace CFSG.GorensteinWalter
universe u

/-- In the cyclic first-case A₇ model, the centralizer `C_B(P)` of the
selected odd core `P = O_p(U)` in `B` is nontrivial. -/
public theorem firstCase_cyclic_CB_ne_of_a7
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c) (hHhat : c.Hhat = c.H)
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
    (hp3 : od.p = 3) :
    od.d.bg.B ⊓ Subgroup.centralizer
      (qCoreOf od.d.bg.U od.p : Set G) ≠ ⊥ := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let P : Subgroup G := qCoreOf od.d.bg.U od.p
  obtain ⟨X, hXne, hXle, _hBnorm, hXcent⟩ :=
    firstCase_cyclic_exists_B_normalized_nontrivial_le_B_inter_M
      hmin c od hfirst hHhat hU Q M hMmax hMN hSM fd hV2 hA7 hp3
  have hXleCB : X ≤ od.d.bg.B ⊓ Subgroup.centralizer (P : Set G) := by
    intro x hx
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_inf.mp (hXle hx)).1, hXcent hx⟩
  intro hbot
  apply hXne
  apply le_bot_iff.mp
  intro x hx
  have hxCB : x ∈ od.d.bg.B ⊓ Subgroup.centralizer (P : Set G) := hXleCB hx
  rw [hbot] at hxCB
  exact Subgroup.mem_bot.mp hxCB

/-- In the cyclic first-case A₇ model, the selected odd core
`P = O_p(U)` lies in the maximal overgroup `M`. -/
public theorem firstCase_cyclic_primeCore_le_M_of_a7
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c) (hHhat : c.Hhat = c.H)
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
    (hp3 : od.p = 3) :
    qCoreOf od.d.bg.U od.p ≤ M :=
  firstCase_cyclic_primeCore_le_M_of_a7_of_CB_ne
    hmin c od hfirst hHhat hU Q M hMmax hMN hSM fd hV2 hA7 hp3
    (firstCase_cyclic_CB_ne_of_a7
      hmin c od hfirst hHhat hU Q M hMmax hMN hSM fd hV2 hA7 hp3)

end CFSG.GorensteinWalter
