module

public import CFSG.Quasithin.Vol2.Ch3E213MDefs
public import CFSG.Quasithin.Vol2.Ch3E213MFam
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bSylow

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.Open CFSG.QuasithinUnique B6
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp card_antiSp)

@[expose] def Sp4Member {G : Type} [Group G] (H T M V : Subgroup G) (g : G) (F₀ : Type)
    [Field F₀] : Prop :=
  g ∈ H ∧
    E2.Pair (Ch3n.pairI V g) (T ⊓ Ch3n.pairI V g) (M ⊓ Ch3n.pairI V g) V g ∧
    CharTwo (Ch3n.pairI V g) ∧ Ch3n.pairI V g ≠ V ∧
    kerIn (M ⊓ Ch3n.pairI V g) (Ch3n.pairI V g) = pCoreOf 2 (Ch3n.pairI V g) ∧
    (∃ ψ : ↥(Ch3n.pairI V g) →* antiSp F₀, Function.Surjective ψ ∧
      ψ.ker = (kerIn (M ⊓ Ch3n.pairI V g) (Ch3n.pairI V g)).subgroupOf (Ch3n.pairI V g)) ∧
    (kerIn (M ⊓ Ch3n.pairI V g) (Ch3n.pairI V g) ⊓ V).relIndex V ≤ Nat.card F₀ ^ 2

theorem e213Concl_of_sp4Member {G : Type} [Group G] [Finite G] {H T M V : Subgroup G} {g : G}
    {F₀ : Type} [Field F₀] [Finite F₀] [CharP F₀ 2] (h : Sp4Member H T M V g F₀) :
    E213Concl H T M V := by
  obtain ⟨hg, hpair, hc2, hne, -, ⟨ψ, hψs, hψk⟩, hVB⟩ := h
  obtain ⟨e, he1, hq⟩ := CFSG.QuasithinUnique.Setup.X7b.exists_card_eq_two_pow (K := F₀)
  have hcard : (kerIn (M ⊓ Ch3n.pairI V g) (Ch3n.pairI V g)).relIndex (Ch3n.pairI V g) =
      Nat.card (antiSp F₀) := by
    rw [Subgroup.relIndex, Subgroup.index, ← hψk]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).toEquiv
  refine ⟨g, hg, hpair, hc2, hne, relIndex_le_of_sp4 hpair hc2 he1 ?_ ?_⟩
  · rw [hcard, card_antiSp hq]
    refine Dvd.dvd.mul_left (Dvd.dvd.mul_left ?_ _) _
    have h4 : (2 ^ e) ^ 4 - 1 = ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 2 + 1) := by
      have h1 : 1 ≤ (2 ^ e) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      zify [h1, Nat.one_le_pow 4 (2 ^ e) (by positivity)]
      ring
    rw [h4]
    exact Dvd.intro_left _ rfl
  · calc (kerIn (M ⊓ Ch3n.pairI V g) (Ch3n.pairI V g) ⊓ V).relIndex V ≤ Nat.card F₀ ^ 2 := hVB
      _ = 2 ^ (2 * e) := by rw [hq, ← pow_mul, mul_comm]

end CFSG.Quasithin.Ch3E213M
