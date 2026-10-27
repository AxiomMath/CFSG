module

public import CFSG.Quasithin.H13.GoldschmidtU43BPhi

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

@[expose] def vapp (g : MulAut (Multiplicative V4)) (v : V4) : V4 :=
  Multiplicative.toAdd (g (Multiplicative.ofAdd v))

@[expose] def StabA (τ α : V4) : Set (MulAut (Multiplicative V4)) :=
  {g | g ∈ Oq ∧ Aset τ α (vapp g τ) ∧ Aset τ α (vapp g α)}

@[expose] def FixA (τ α : V4) : Set (MulAut (Multiplicative V4)) :=
  {g | g ∈ Oq ∧ vapp g τ = τ ∧ vapp g α = α}

theorem vapp_eq_app (g : MulAut (Multiplicative V4)) (v : V4) : vapp g v = app (colsOf g) v :=
  app_colsOf g v

theorem card_StabA_le {τ α : V4} (h : LinePair τ α) : Nat.card (StabA τ α) ≤ 12 := by
  classical
  let f : StabA τ α → {x : OC // PresA τ α x} := fun g =>
    ⟨toOC ⟨g.1, g.2.1⟩, by
      unfold PresA
      rw [toOC_cols, ← vapp_eq_app, ← vapp_eq_app]
      exact ⟨g.2.2.1, g.2.2.2⟩⟩
  have hf : Function.Injective f := by
    intro g g' hg
    have := toOC_injective (congrArg Subtype.val hg)
    have h2 : (⟨g.1, g.2.1⟩ : ↥Oq).1 = (⟨g'.1, g'.2.1⟩ : ↥Oq).1 := congrArg Subtype.val this
    exact Subtype.ext h2
  calc Nat.card (StabA τ α) ≤ Nat.card {x : OC // PresA τ α x} :=
        Nat.card_le_card_of_injective f hf
    _ = (Finset.univ.filter (PresA τ α)).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ ≤ 12 := card_presA_le τ α h

theorem card_FixA_le {τ α : V4} (h : LinePair τ α) : Nat.card (FixA τ α) ≤ 2 := by
  classical
  let f : FixA τ α → {x : OC // FixPair τ α x} := fun g =>
    ⟨toOC ⟨g.1, g.2.1⟩, by
      unfold FixPair
      rw [toOC_cols, ← vapp_eq_app, ← vapp_eq_app]
      exact ⟨g.2.2.1, g.2.2.2⟩⟩
  have hf : Function.Injective f := by
    intro g g' hg
    have := toOC_injective (congrArg Subtype.val hg)
    have h2 : (⟨g.1, g.2.1⟩ : ↥Oq).1 = (⟨g'.1, g'.2.1⟩ : ↥Oq).1 := congrArg Subtype.val this
    exact Subtype.ext h2
  calc Nat.card (FixA τ α) ≤ Nat.card {x : OC // FixPair τ α x} :=
        Nat.card_le_card_of_injective f hf
    _ = (Finset.univ.filter (FixPair τ α)).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ ≤ 2 := card_fixPair_le τ α h

theorem exists_rho {τ α : V4} (h : LinePair τ α) :
    ∃ ρ : MulAut (Multiplicative V4), ρ ∈ StabA τ α ∧ ρ ≠ 1 ∧ ρ ^ 3 = 1 ∧ vapp ρ τ ≠ τ := by
  obtain ⟨x, hx3, hxA, hxτ⟩ := exists_order_three τ α h
  refine ⟨ofOC x, ⟨ofOC_mem x, ?_, ?_⟩, ?_⟩
  · rw [vapp_eq_app, colsOf_ofOC]; exact hxA.1
  · rw [vapp_eq_app, colsOf_ofOC]; exact hxA.2
  · have h3 := (ord3_colsOf_iff (ofOC x)).1 (by rw [colsOf_ofOC]; exact hx3)
    exact ⟨h3.1, h3.2, by rw [vapp_eq_app, colsOf_ofOC]; exact hxτ⟩

namespace Hyp

variable {G : Type} [Group G] {z : G} (h : Hyp z)
include h

theorem range_act_le : (h.act).range ≤ Oq := by
  rintro _ ⟨x, rfl⟩
  exact h.act_mem_Oq x

theorem mem_range_of_pow_three [Finite G] {g : MulAut (Multiplicative V4)} (hg : g ∈ Oq)
    (h3 : g ^ 3 = 1) : g ∈ (h.act).range := by
  have hle := h.range_act_le
  have e1 := Subgroup.relIndex_mul_card (h.act).range Oq
  rw [inf_of_le_left hle, h.card_range_act, card_Oq] at e1
  have hri : (h.act).range.relIndex Oq = 2 := by omega
  obtain ⟨a, haO, ha⟩ := Subgroup.relIndex_eq_two_iff.mp hri
  have hsq : ∀ b ∈ Oq, b * b ∈ (h.act).range := by
    intro b hb
    by_cases hbm : b ∈ (h.act).range
    · exact mul_mem hbm hbm
    · have h1 : b * a ∈ (h.act).range := by
        rcases ha b hb with ⟨h1, _⟩ | ⟨h2, _⟩
        · exact h1
        · exact absurd h2 hbm
      by_contra hbb
      have h2 : (b * b) * a ∈ (h.act).range := by
        rcases ha (b * b) (mul_mem hb hb) with ⟨h1, _⟩ | ⟨h2, _⟩
        · exact h1
        · exact absurd h2 hbb
      apply hbm
      have e : b = ((b * b) * a) * (b * a)⁻¹ := by group
      rw [e]
      exact mul_mem h2 ((h.act).range.inv_mem h1)
  have e : g = (g * g) * (g * g) := by
    calc g = g * (g ^ 3) := by rw [h3, mul_one]
      _ = g * (g * (g * g)) := by rw [pow_three]
      _ = (g * g) * (g * g) := by simp only [mul_assoc]
  rw [e]
  exact mul_mem (hsq g hg) (hsq g hg)

theorem card_map_act_mul [Finite G] (X : Subgroup G) (hUX : Uz z ≤ X) (hXH : X ≤ Hz z) :
    Nat.card ((X.subgroupOf (Hz z)).map h.act) * 32 = Nat.card X := by
  have e1 := Subgroup.relIndex_mul_card (h.act).ker (X.subgroupOf (Hz z))
  rw [Subgroup.relIndex_ker, h.ker_act] at e1
  have hle : (Uz z).subgroupOf (Hz z) ≤ X.subgroupOf (Hz z) := fun x hx => hUX hx
  rw [inf_of_le_left hle] at e1
  have h2 : Nat.card ((Uz z).subgroupOf (Hz z)) = 32 := by
    rw [← h.card_U]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Uz_le_Hz z)).toEquiv
  have h3 : Nat.card (X.subgroupOf (Hz z)) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv
  rw [h2, h3] at e1
  exact e1


theorem card_le_of_act [Finite G] (X : Subgroup G) (hXH : X ≤ Hz z) {n m : ℕ}
    (h1 : Nat.card ((X.subgroupOf (Hz z)).map h.act) ≤ n) (h2 : Nat.card ↥(X ⊓ Uz z) ≤ m) :
    Nat.card X ≤ n * m := by
  have e1 := Subgroup.relIndex_mul_card (h.act).ker (X.subgroupOf (Hz z))
  rw [Subgroup.relIndex_ker, h.ker_act] at e1
  have hinf : (Uz z).subgroupOf (Hz z) ⊓ X.subgroupOf (Hz z) = (Uz z ⊓ X).subgroupOf (Hz z) := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have h3 : Nat.card ((Uz z ⊓ X).subgroupOf (Hz z)) = Nat.card ↥(Uz z ⊓ X) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans (Uz_le_Hz z))).toEquiv
  have h4 : Nat.card (X.subgroupOf (Hz z)) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv
  have h5 : Nat.card ↥(Uz z ⊓ X) = Nat.card ↥(X ⊓ Uz z) := by rw [inf_comm]
  rw [hinf, h3, h4, h5] at e1
  rw [← e1]
  exact Nat.mul_le_mul h1 h2

end Hyp

end CFSG.Quasithin.H13.U43
