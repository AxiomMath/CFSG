module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseInvolutionOddCoreDisjoint
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27QuotientIndex
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4: the odd-core quotient preserves the size of `K`
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The quotient map `M → M/O₂′(M)` is injective on the inverted subgroup
`K` supplied by equations (1)--(2), in cardinal form. -/
public theorem secondCase_involution_K_quotient_card_eq_card
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w) :
    ∃ K B : Subgroup G, ∃ s : d.E,
      (K : Set G) = invertedElements (c.U ⊓ w.M) (s : G) ∧
      IsCyclic K ∧
      B = centralizerIn (c.U ⊓ w.M) (s : G) ∧
      K ⊔ B = c.U ⊓ w.M ∧
      Nat.card ((K.subgroupOf w.M).map
        (QuotientGroup.mk' (pPrimeCore 2 w.M))) = Nat.card K := by
  classical
  obtain ⟨K, B, s, hK_eq, hK_cyc, hB_def, hjoinX, hdisj⟩ :=
    secondCase_involution_K_inf_oddCore_eq_bot c w d
  let M : Subgroup G := w.M
  let O : Subgroup M := pPrimeCore 2 M
  let q : M →* M ⧸ O := QuotientGroup.mk' O
  have hInf : K.subgroupOf M ⊓ O = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxK : (x : G) ∈ K := Subgroup.mem_subgroupOf.mp hx.1
    have hxO : (x : G) ∈ oddCoreOf M := by
      exact Subgroup.mem_map.mpr ⟨x, hx.2, rfl⟩
    have hxbot : (x : G) ∈ K ⊓ oddCoreOf M := ⟨hxK, hxO⟩
    rw [hdisj] at hxbot
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    exact Subgroup.mem_bot.mp hxbot
  have hformula := card_map_eq_card_mul_card_ker q (K.subgroupOf M)
  have hker : q.ker = O := by
    simpa [q] using QuotientGroup.ker_mk' O
  rw [hker, hInf, Subgroup.card_bot, mul_one] at hformula
  have hsubcard : Nat.card (K.subgroupOf M) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (H := K) (K := M) (by
        intro x hx
        change x ∈ (K : Set G) at hx
        rw [hK_eq] at hx
        exact hx.1.2)).toEquiv
  have hmapcard : Nat.card ((K.subgroupOf M).map q) = Nat.card K := by
    exact hformula.symm.trans hsubcard
  refine ⟨K, B, s, hK_eq, hK_cyc, hB_def, hjoinX, ?_⟩
  change Nat.card ((K.subgroupOf M).map q) = Nat.card K
  exact hmapcard

end CFSG.GorensteinWalter
