module

public import CFSG.Quasithin.Vol2.Ch3E215MSp4E
public import CFSG.Quasithin.Vol2.Ch3E215MDefs
public import CFSG.Quasithin.Vol2.Ch3E213MP6AC

public section

namespace CFSG.Quasithin.Ch3E215M.Sp4

open CFSG.Open CFSG.QuasithinUnique B6 Ch3E213M CFSG.Timmesfeld
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp card_antiSp)

variable {G : Type} [Group G] [Finite G] {X T M V : Subgroup G} {g : G}

theorem commutator_eq_bot_of_sp4 (h : E2.Pair X T M V g) (hchar : CharTwo X)
    {F₀ : Type} [Field F₀] [Finite F₀] [CharP F₀ 2] (ψ : ↥X →* antiSp F₀)
    (hψs : Function.Surjective ψ) (hψk : ψ.ker = (kerIn M X).subgroupOf X)
    (hJ : IsPGroup 2 ↥(kerIn M X))
    (hb : (V ⊓ B6.conjSub g V).relIndex (kerIn M X ⊓ V) ≤ Nat.card F₀ ^ 2) :
    ⁅kerIn M X ⊓ V, B6.conjSub g (kerIn M X ⊓ V)⁆ = ⊥ := by
  obtain ⟨e, he, hq⟩ := CFSG.QuasithinUnique.Setup.X7b.exists_card_eq_two_pow (K := F₀)
  have hPZ : (V ⊓ B6.conjSub g V).relIndex ((kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V)) ≤
      2 ^ (4 * e) := by
    rw [relIndex_P_eq h]
    calc _ ≤ (Nat.card F₀ ^ 2) ^ 2 := Nat.pow_le_pow_left hb 2
      _ = 2 ^ (4 * e) := by rw [hq, ← pow_mul, ← pow_mul]; congr 1; ring
  obtain ⟨r, x, hr, hx, hxo⟩ := exists_mem_orderOf_ppd hq he ψ hψs
  have hk : 0 < 4 * e := by omega
  have hPZeq := relIndex_P_eq_two_pow h hchar hk hr hx hxo hPZ
  obtain ⟨b₀, hb₀B, hb₀Z⟩ : ∃ b₀ ∈ kerIn M X ⊓ V, b₀ ∉ V ⊓ B6.conjSub g V := by
    by_contra hall
    push Not at hall
    have h1 : (V ⊓ B6.conjSub g V).relIndex (kerIn M X ⊓ V) = 1 :=
      Subgroup.relIndex_eq_one.2 hall
    rw [relIndex_P_eq h, h1, one_pow] at hPZeq
    have h2 : 1 < 2 ^ (4 * e) := Nat.one_lt_two_pow (by omega)
    omega
  have hexp : ∀ p ∈ (kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V), p * p = 1 := by
    intro p hp
    by_cases hpZ : p ∈ V ⊓ B6.conjSub g V
    · have h1 := h.elem.2 p hpZ.1
      rwa [pow_two] at h1
    · obtain ⟨y, hy, hyp⟩ := exists_mem_conj_mul h hchar hJ hq he ψ hψs hψk hPZ
        (le_sup_left (a := kerIn M X ⊓ V) hb₀B) hp hb₀Z hpZ
      have hwy : y * ((y * b₀ * y⁻¹)⁻¹ * p) * y⁻¹ = (y * b₀ * y⁻¹)⁻¹ * p :=
        conj_eq_of_mem_Z h hy hyp
      have e1 : p = y * (b₀ * ((y * b₀ * y⁻¹)⁻¹ * p)) * y⁻¹ := by
        calc p = (y * b₀ * y⁻¹) * ((y * b₀ * y⁻¹)⁻¹ * p) := by group
          _ = (y * b₀ * y⁻¹) * (y * ((y * b₀ * y⁻¹)⁻¹ * p) * y⁻¹) := by rw [hwy]
          _ = y * (b₀ * ((y * b₀ * y⁻¹)⁻¹ * p)) * y⁻¹ := by group
      have hbw : (b₀ * ((y * b₀ * y⁻¹)⁻¹ * p)) * (b₀ * ((y * b₀ * y⁻¹)⁻¹ * p)) = 1 := by
        have h1 := h.elem.2 _ (V.mul_mem hb₀B.2 hyp.1)
        rwa [pow_two] at h1
      rw [e1]
      calc y * (b₀ * ((y * b₀ * y⁻¹)⁻¹ * p)) * y⁻¹ *
            (y * (b₀ * ((y * b₀ * y⁻¹)⁻¹ * p)) * y⁻¹)
          = y * ((b₀ * ((y * b₀ * y⁻¹)⁻¹ * p)) * (b₀ * ((y * b₀ * y⁻¹)⁻¹ * p))) * y⁻¹ := by
            group
        _ = 1 := by rw [hbw, mul_one, mul_inv_cancel]
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro b hb a ha
  have hbP : b ∈ (kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V) :=
    le_sup_left (a := kerIn M X ⊓ V) hb
  have haP : a ∈ (kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V) :=
    le_sup_right (b := B6.conjSub g (kerIn M X ⊓ V)) ha
  have h1 := hexp _ (Subgroup.mul_mem _ hbP haP)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hexp b hbP)
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hexp a haP)
  rw [Subgroup.mem_bot, commutatorElement_def, hb', ha']
  calc b * a * b * a = (b * a) * (b * a) := by group
    _ = 1 := h1

theorem e215DataOf_of_sp4 (h : E2.Pair X T M V g) (hchar : CharTwo X)
    {F₀ : Type} [Field F₀] [Finite F₀] [CharP F₀ 2] (ψ : ↥X →* antiSp F₀)
    (hψs : Function.Surjective ψ) (hψk : ψ.ker = (kerIn M X).subgroupOf X)
    (hJ : IsPGroup 2 ↥(kerIn M X)) (hrank : (kerIn M X ⊓ V).relIndex V ≤ Nat.card F₀ ^ 2) :
    E215DataOf X M V g := by
  by_cases hlt : (kerIn M X ⊓ V).relIndex V < (V ⊓ B6.conjSub g V).relIndex (kerIn M X ⊓ V)
  · exact Or.inl hlt
  · exact Or.inr fun _ =>
      commutator_eq_bot_of_sp4 h hchar ψ hψs hψk hJ ((not_lt.1 hlt).trans hrank)

theorem e215DataOf_of_sp4Member {H : Subgroup G} {F₀ : Type} [Field F₀] [Finite F₀]
    [CharP F₀ 2] (hm : Sp4Member H T M V g F₀) :
    E215DataOf (Ch3n.pairI V g) (M ⊓ Ch3n.pairI V g) V g := by
  obtain ⟨-, hpair, hc2, -, hJ, ⟨ψ, hψs, hψk⟩, hVB⟩ := hm
  refine e215DataOf_of_sp4 hpair hc2 ψ hψs hψk ?_ hVB
  rw [hJ]
  exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _

theorem e215Concl_of_sp4Member {H : Subgroup G} {F₀ : Type} [Field F₀] [Finite F₀]
    [CharP F₀ 2] (hm : Sp4Member H T M V g F₀) : E215Concl H T M V := by
  have hdata := e215DataOf_of_sp4Member hm
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

theorem sp4MemberE215_holds :
    ∀ (G : Type) [Group G] [Finite G] (H T M V : Subgroup G) (g : G) (F₀ : Type) [Field F₀]
      [Finite F₀] [CharP F₀ 2], Sp4Member H T M V g F₀ → E215Concl H T M V :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hm => e215Concl_of_sp4Member hm

end CFSG.Quasithin.Ch3E215M.Sp4
