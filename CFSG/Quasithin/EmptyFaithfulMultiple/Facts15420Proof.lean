module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs5
public import CFSG.Quasithin.Background.F420Sp4
public import CFSG.Quasithin.Background.F420Alt
public import CFSG.Quasithin.Background.F420M11
public import CFSG.Quasithin.Background.F420Ln2
public import CFSG.Quasithin.Background.F420L33
public import CFSG.Sporadic.He.Simple

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open (quasithinIsSylowTwo)
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem facts15420_autPSL2Even : ∀ (X : Type) [Group X] (n : ℕ),
    StatedClassicalModel X .PSL 2 2 n →
    ∀ S : Subgroup X, quasithinIsSylowTwo S → ∀ y : X, orderOf y = 3 →
      ∀ α : MulAut X, (∀ s ∈ S, α s = s) → α y = y → α = 1 :=
  fun _ _ _ h _ hS _ hy α hα hαy => F420.eq_one_of_fix_sylow_of_statedPSL_two_two h hS hy α hα hαy

theorem facts15420_autPSL2Odd
    : ∀ (X : Type) [Group X] (q : ℕ), q.Prime → q ≠ 2 →
    StatedClassicalModel X .PSL 2 q 1 → ∀ S : Subgroup X, quasithinIsSylowTwo S →
      ∀ α β γ : MulAut X, (∀ s ∈ S, α s = s) → (∀ s ∈ S, β s = s) → α ≠ 1 → β ≠ 1 → α ≠ β →
        α * β = β * α → α * α = 1 → β * β = 1 → γ * α = α * γ → γ * β = β * γ →
          γ = 1 ∨ γ = α ∨ γ = β ∨ γ = α * β :=
  fun _ _ _ hq hq2 h _ hS α β γ hα hβ hα1 hβ1 hαβ hc ha hb hγα hγβ =>
    F420.mem_klein_of_fix_sylow_of_statedPSL_two_odd hq hq2 h hS α β γ hα hβ hα1 hβ1 hαβ hc ha hb
      hγα hγβ

theorem facts15420_autSmallCentralizer : ∀ (X : Type) [Group X],
    (StatedClassicalModel X .PSL 3 3 1 ∨ Nonempty (X ≃* ↥(StatedSL 3 (ZMod 3))) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) ∨
      StatedClassicalModel X .PSL 4 2 1 ∨ StatedClassicalModel X .PSL 5 2 1) →
    ∀ S : Subgroup X, quasithinIsSylowTwo S → ∀ α β : MulAut X, (∀ s ∈ S, α s = s) →
      (∀ s ∈ S, β s = s) → α * β = β * α → α * α = 1 → β * β = 1 → α = 1 ∨ β = 1 ∨ α = β := by
  intro X _ h
  have key : F420.NoFourCentralizing X := by
    rcases h with h | h | h | h | h
    · exact F420.noFourCentralizing_of_l33 (Or.inl h)
    · exact F420.noFourCentralizing_of_l33 (Or.inr h)
    · obtain ⟨e⟩ := h
      exact F420.NoFourCentralizing.of_mulEquiv (Y := F420.M11G) e F420.noFourCentralizing_m11
    · exact F420.noFourCentralizing_of_statedPSL_two (by norm_num) h
    · exact F420.noFourCentralizing_of_statedPSL_two (by norm_num) h
  exact key

theorem facts15420_heartAlt : ∀ m : ℕ, 5 ≤ m → m ≤ 8 → ∀ S : Subgroup (alternatingGroup (Fin m)),
    quasithinIsSylowTwo S → ∃ g : alternatingGroup (Fin m), orderOf g = 3 ∧
      ∀ x : evenWeight m,
        (∀ s ∈ S, permWeight m (s : Equiv.Perm (Fin m)) x - x ∈ constWeight m) →
          permWeight m (g : Equiv.Perm (Fin m)) x - x ∈ constWeight m :=
  F420.exists_orderOf_eq_three_heart

theorem facts15420_natSp4 : ∀ (F : Type) [Field F] [Fintype F], Fintype.card F = 4 →
    ∀ S : Subgroup ↥(StatedSp 2 F), quasithinIsSylowTwo S → ∃ g : ↥(StatedSp 2 F),
      orderOf g = 3 ∧ ∀ v : Fin 2 ⊕ Fin 2 → F,
        (∀ s ∈ S,
          ((s : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).mulVec v = v) →
          ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).mulVec v = v :=
  fun _ _ _ hF S hS => F420.exists_orderOf_eq_three_fix_of_sylow_statedSp hF S hS

theorem facts15420_cardPSL2Two : ∀ (X : Type) [Group X] (n : ℕ),
    StatedClassicalModel X .PSL 2 2 n → Nat.card X = 2 ^ n * (4 ^ n - 1) :=
  fun _ _ _ h => F420.card_of_statedPSL_two_two h

theorem facts15420_cardPSL2Odd : ∀ (X : Type) [Group X] (q : ℕ), q.Prime → q ≠ 2 →
    StatedClassicalModel X .PSL 2 q 1 → 2 * Nat.card X = q * (q ^ 2 - 1) :=
  fun _ _ _ hq hq2 h => F420.two_mul_card_of_statedPSL_two_odd hq hq2 h

theorem facts15420_cardL33 : ∀ (X : Type) [Group X],
    (StatedClassicalModel X .PSL 3 3 1 ∨ Nonempty (X ≃* ↥(StatedSL 3 (ZMod 3)))) →
      Nat.card X = 5616 :=
  fun _ _ h => F420.card_of_l33 h

theorem facts15420_cardM11 : ∀ (X : Type) [Group X],
    Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) → Nat.card X = 7920 :=
  fun _ _ h => F420.card_of_m11 h

theorem facts15420_cardL42 : ∀ (X : Type) [Group X], StatedClassicalModel X .PSL 4 2 1 →
    Nat.card X = 20160 :=
  fun _ _ h => F420.card_of_l42 h

theorem facts15420_cardL52 : ∀ (X : Type) [Group X], StatedClassicalModel X .PSL 5 2 1 →
    Nat.card X = 9999360 :=
  fun _ _ h => F420.card_of_l52 h

theorem facts15420_cardU33 : ∀ (X : Type) [Group X], StatedClassicalModel X .PSU 3 3 1 →
    Nat.card X = 6048 :=
  fun _ _ h => F420.card_of_u33 h

theorem facts15420_centerPSL : ∀ (X : Type) [Group X] (n p f : ℕ),
    StatedClassicalModel X .PSL n p f → Subgroup.center X = ⊥ :=
  fun _ _ _ _ _ h => F420.center_eq_bot_of_statedPSL h

theorem facts15420_centerSL33M11 : ∀ (X : Type) [Group X],
    (Nonempty (X ≃* ↥(StatedSL 3 (ZMod 3))) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) → Subgroup.center X = ⊥ := by
  intro X _ h
  rcases h with h | h
  · obtain ⟨e⟩ := h
    exact F420.center_eq_bot_of_mulEquiv' e F420.center_statedSL_three_three
  · obtain ⟨e⟩ := h
    exact F420.center_eq_bot_of_mulEquiv' (Y := F420.M11G) e F420.center_m11_eq_bot

theorem facts15420_cardHe : ∀ (X : Type) [Group X],
    Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .He) → Nat.card X = 4030387200 := by
  rintro X _ ⟨e⟩
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Sporadic.He.card_He

theorem facts15420_centerHe : ∀ (X : Type) [Group X],
    Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .He) → Subgroup.center X = ⊥ := by
  rintro X _ ⟨e⟩
  refine F420.center_eq_bot_of_mulEquiv' e ?_
  have hs : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .He) :=
    CFSG.Sporadic.He.isSimpleGroup_He
  rcases hs.eq_bot_or_eq_top_of_normal
      (Subgroup.center (CFSG.Blueprint.NativeSporadic.Carrier .He)) with h | h
  · exact h
  · exfalso
    have : IsMulCommutative (CFSG.Blueprint.NativeSporadic.Carrier .He) :=
      ⟨⟨fun a b => (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)⟩⟩
    have hp := Group.is_simple_iff_prime_card.1 hs
    rw [show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .He) = 4030387200 from
      CFSG.Sporadic.He.card_He] at hp
    exact absurd hp (by norm_num)

structure Facts15420Rest : Prop where
  ffLinear : ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v * v = 1) →
    ∀ Γ L : Subgroup (MulAut V), G64.IsQuotientOfSQTKCat ↥Γ → L ≤ Γ →
      (L.subgroupOf Γ).Normal →
      Γ ⊓ Subgroup.centralizer (L : Set (MulAut V)) = ⊥ →
      ((∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
          Nonempty (↥L ≃* ↥(StatedSL 3 F))) ∨
        Nonempty (↥L ≃* ↥(StatedSL 4 (ZMod 2))) ∨ Nonempty (↥L ≃* ↥(StatedSL 5 (ZMod 2)))) →
      (∃ A : Subgroup (MulAut V), IsFFStarOffender Γ A) →
      ∀ S : Subgroup (MulAut V), IsSylowTwoOf S L →
        ∃ g ∈ L, orderOf g = 3 ∧ ∀ v ∈ fixV S ⊓ commV L, g v = v
  autHe : HeAutCentralizer

theorem facts15420_of_rest
    (h : Facts15420Rest) : Facts15420 where
  autPSL2Even := facts15420_autPSL2Even
  autPSL2Odd := facts15420_autPSL2Odd
  autSmallCentralizer := facts15420_autSmallCentralizer
  heartAlt := facts15420_heartAlt
  natSp4 := facts15420_natSp4
  ffLinear := h.ffLinear
  cardPSL2Two := facts15420_cardPSL2Two
  cardPSL2Odd := facts15420_cardPSL2Odd
  cardL33 := facts15420_cardL33
  cardM11 := facts15420_cardM11
  cardL42 := facts15420_cardL42
  cardL52 := facts15420_cardL52
  cardU33 := facts15420_cardU33
  centerPSL := facts15420_centerPSL
  centerSL33M11 := facts15420_centerSL33M11
  autHe := h.autHe
  cardHe := facts15420_cardHe
  centerHe := facts15420_centerHe

end CFSG.Quasithin.EmptyFaithfulMultiple
