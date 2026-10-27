module

public import CFSG.Quasithin.Vol2.Ch3E215MSp4
public import CFSG.Quasithin.Vol2.GoldschmidtRes2WBase

public section

namespace CFSG.Quasithin.Res2

open CFSG.Open CFSG.QuasithinUnique B6 Ch3E213M CFSG.Timmesfeld
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp card_antiSp)

variable {G : Type} [Group G] [Finite G] {X T M V : Subgroup G} {g : G}

theorem e215DataW_of_sp4 (h : E2.Pair X T M V g) (hchar : CharTwo X)
    {F₀ : Type} [Field F₀] [Finite F₀] [CharP F₀ 2] (ψ : ↥X →* antiSp F₀)
    (hψs : Function.Surjective ψ) (hψk : ψ.ker = (kerIn M X).subgroupOf X)
    (hJ : IsPGroup 2 ↥(kerIn M X)) (hrank : (kerIn M X ⊓ V).relIndex V ≤ Nat.card F₀ ^ 2) :
    E215DataW X M V g := by
  by_cases hlt : (kerIn M X ⊓ V).relIndex V < (V ⊓ B6.conjSub g V).relIndex (kerIn M X ⊓ V)
  · exact Or.inl hlt
  · exact Or.inr
      (Ch3E215M.Sp4.commutator_eq_bot_of_sp4 h hchar ψ hψs hψk hJ ((not_lt.1 hlt).trans hrank))

theorem e215DataW_of_sp4Member {H : Subgroup G} {F₀ : Type} [Field F₀] [Finite F₀]
    [CharP F₀ 2] (hm : Sp4Member H T M V g F₀) :
    E215DataW (Ch3n.pairI V g) (M ⊓ Ch3n.pairI V g) V g := by
  obtain ⟨-, hpair, hc2, -, hJ, ⟨ψ, hψs, hψk⟩, hVB⟩ := hm
  refine e215DataW_of_sp4 hpair hc2 ψ hψs hψk ?_ hVB
  rw [hJ]
  exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _

theorem e215ConclW_of_sp4Member {H : Subgroup G} {F₀ : Type} [Field F₀] [Finite F₀]
    [CharP F₀ 2] (hm : Sp4Member H T M V g F₀) : E215ConclW H T M V := by
  intro _
  have hdata := e215DataW_of_sp4Member hm
  obtain ⟨hg, hpair, hc2, hne, -, ⟨ψ, hψs, hψk⟩, hVB⟩ := hm
  obtain ⟨e, he1, hq⟩ := CFSG.QuasithinUnique.Setup.X7b.exists_card_eq_two_pow (K := F₀)
  have hcard : (kerIn (M ⊓ Ch3n.pairI V g) (Ch3n.pairI V g)).relIndex (Ch3n.pairI V g) =
      Nat.card (antiSp F₀) := by
    rw [Subgroup.relIndex, Subgroup.index, ← hψk]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).toEquiv
  refine ⟨g, hg, hpair, hc2, hne, relIndex_le_of_sp4 hpair hc2 he1 ?_ ?_, hdata⟩
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

theorem sp4MemberE215W_holds :
    ∀ (G : Type) [Group G] [Finite G] (H T M V : Subgroup G) (g : G) (F₀ : Type) [Field F₀]
      [Finite F₀] [CharP F₀ 2], Sp4Member H T M V g F₀ → E215ConclW H T M V :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hm => e215ConclW_of_sp4Member hm

end CFSG.Quasithin.Res2
