module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DDefs

public section

namespace CFSG.StandardType.HdRo7D

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7DCardAux_ext {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {m : ℕ} {b : Module.Basis (Fin m) (ZMod p) V} {a₁ a₂ : V ≃ₗ[ZMod p] V}
    (h : ∀ i, a₁ (b i) = a₂ (b i)) : a₁ = a₂ := by
  have hlin : (a₁ : V →ₗ[ZMod p] V) = (a₂ : V →ₗ[ZMod p] V) := b.ext h
  exact LinearEquiv.ext (fun v => congrArg (fun f : V →ₗ[ZMod p] V => f v) hlin)

private lemma hdRo7DCardAux_injective (hN : DNormalizerLeaf) {n : ℕ} {V : Type}
    [AddCommGroup V] [Module (ZMod 3) V] [Fact (Nat.Prime 3)]
    {b : Module.Basis (Fin (n + 1)) (ZMod 3) V} {H A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hD : DLinData 3 n V b H A) :
    ∃ f : {a : V ≃ₗ[ZMod 3] V // a ∈ H ∧ a (b 0) = b 0} →
        Equiv.Perm (Fin (n + 1)) × (Fin (n + 1) → Bool), Function.Injective f := by
  classical
  have hn5 : 5 ≤ n := by have := hD.hn; omega
  let d : (a : {a : V ≃ₗ[ZMod 3] V // a ∈ H ∧ a (b 0) = b 0}) → C2SP 3 b a.1 := fun a =>
    hN 3 rfl n hn5 V b a.1 (hD.hStab a.1 (hD.hHA a.2.1) a.2.2) a.2.2
  let σ : (a : {a : V ≃ₗ[ZMod 3] V // a ∈ H ∧ a (b 0) = b 0}) → Equiv.Perm (Fin (n + 1)) :=
    fun a => Classical.choose (d a)
  let c : (a : {a : V ≃ₗ[ZMod 3] V // a ∈ H ∧ a (b 0) = b 0}) → Fin (n + 1) → ZMod 3 :=
    fun a => Classical.choose (Classical.choose_spec (d a))
  have hspec : ∀ a, σ a 0 = 0 ∧ c a 0 = 1 ∧ (∀ i, c a i = 1 ∨ c a i = -1) ∧
      ∀ i, a.1 (b i) = c a i • b (σ a i) := fun a =>
    Classical.choose_spec (Classical.choose_spec (d a))
  let f : (a : {a : V ≃ₗ[ZMod 3] V // a ∈ H ∧ a (b 0) = b 0}) →
      Equiv.Perm (Fin (n + 1)) × (Fin (n + 1) → Bool) := fun a =>
    (σ a, fun i => decide (c a i = 1))
  refine ⟨f, ?_⟩
  intro a₁ a₂ heq
  have hσ : σ a₁ = σ a₂ := congrArg Prod.fst heq
  have hb : (fun i => decide (c a₁ i = 1)) = fun i => decide (c a₂ i = 1) :=
    congrArg Prod.snd heq
  have hc : c a₁ = c a₂ := by
    funext i
    have h1 := (hspec a₁).2.2.1 i
    have h2 := (hspec a₂).2.2.1 i
    have hi := congrFun hb i
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp_all
  refine Subtype.ext (hdRo7DCardAux_ext (b := b) fun i => ?_)
  rw [(hspec a₁).2.2.2 i, (hspec a₂).2.2.2 i, hσ, hc]

theorem d_reduceV_card (hN : DNormalizerLeaf) {p : ℕ} [Fact p.Prime] {n : ℕ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {b : Module.Basis (Fin (n + 1)) (ZMod p) V}
    {H A : Subgroup (V ≃ₗ[ZMod p] V)} (hD : DLinData p n V b H A) :
    Nat.card H ≤ 6 ^ (n + 1) * (n + 1).factorial := by
  obtain rfl : p = 3 := hD.hp
  have hn6 : 6 ≤ n := hD.hn
  have : NeZero (n + 1) := ⟨by omega⟩
  have : Fintype V := Fintype.ofEquiv (Fin (n + 1) → ZMod 3) b.equivFun.toEquiv.symm
  have : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun e f h => LinearEquiv.ext (fun v => congrFun h v))
  have : Fintype (V ≃ₗ[ZMod 3] V) := Fintype.ofFinite _
  have : Fintype H := Fintype.ofFinite _
  have : Fintype ↥(MulAction.orbit H (b 0)) := Fintype.ofFinite _
  have : Fintype ↥(MulAction.stabilizer H (b 0)) := Fintype.ofFinite _
  have hVcard : Fintype.card V = 3 ^ (n + 1) := by
    rw [Fintype.card_congr b.equivFun.toEquiv, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  have hOS : Fintype.card (MulAction.orbit H (b 0)) *
      Fintype.card (MulAction.stabilizer H (b 0)) = Fintype.card H :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group H (b 0)
  have horbit : Fintype.card (MulAction.orbit H (b 0)) ≤ 3 ^ (n + 1) := by
    rw [← hVcard]
    exact Fintype.card_le_of_injective (fun v : ↥(MulAction.orbit H (b 0)) => v.1)
      Subtype.val_injective
  have hstab' : Nat.card {a : V ≃ₗ[ZMod 3] V // a ∈ H ∧ a (b 0) = b 0} ≤
      (n + 1).factorial * 2 ^ (n + 1) := by
    obtain ⟨f, hf⟩ := hdRo7DCardAux_injective hN hD
    have hcard : Nat.card (Equiv.Perm (Fin (n + 1)) × (Fin (n + 1) → Bool)) =
        (n + 1).factorial * 2 ^ (n + 1) := by
      rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin,
        Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    calc Nat.card {a : V ≃ₗ[ZMod 3] V // a ∈ H ∧ a (b 0) = b 0}
        ≤ Nat.card (Equiv.Perm (Fin (n + 1)) × (Fin (n + 1) → Bool)) :=
          Nat.card_le_card_of_injective f hf
      _ = (n + 1).factorial * 2 ^ (n + 1) := hcard
  let e : {a : V ≃ₗ[ZMod 3] V // a ∈ H ∧ a (b 0) = b 0} ≃ ↥(MulAction.stabilizer H (b 0)) :=
    { toFun := fun p => ⟨⟨p.1, p.2.1⟩, p.2.2⟩
      invFun := fun q => ⟨q.1.1, q.1.2, by
        have hq := q.2
        change q.1.1 (b 0) = b 0 at hq
        exact hq⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl }
  have hstab : Fintype.card (MulAction.stabilizer H (b 0)) ≤
      (n + 1).factorial * 2 ^ (n + 1) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_congr e]
    exact hstab'
  calc Nat.card H = Fintype.card H := Nat.card_eq_fintype_card
    _ = Fintype.card (MulAction.orbit H (b 0)) *
          Fintype.card (MulAction.stabilizer H (b 0)) := hOS.symm
    _ ≤ 3 ^ (n + 1) * ((n + 1).factorial * 2 ^ (n + 1)) := Nat.mul_le_mul horbit hstab
    _ = 3 ^ (n + 1) * 2 ^ (n + 1) * (n + 1).factorial := by ring
    _ = (3 * 2) ^ (n + 1) * (n + 1).factorial := by rw [← mul_pow]
    _ = 6 ^ (n + 1) * (n + 1).factorial := by norm_num

end CFSG.StandardType.HdRo7D
