
module

public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.Sporadic.Schreier.RuCentersMain

@[expose] public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31

theorem rep_commutA {a b : Array ℕ} {g h : Equiv.Perm (Fin 4060)} (ha : Rep 4060 a g)
    (hb : Rep 4060 b h) : Rep 4060 (commutA a b) (g * h * g⁻¹ * h⁻¹) :=
  rep_compA (rep_compA (rep_compA ha hb) (rep_ruInv' ha)) (rep_ruInv' hb)

section Facts

theorem ruKGensA_size : ruKGensA.size = 8 := by simp [ruKGensA, ruKWords]

theorem ruKGensA_mem {i : ℕ} (hi : i < 8) : ruKGensA[i]! ∈ ruKGensA.toList := by
  rw [getElem!_pos ruKGensA i (by rw [ruKGensA_size]; exact hi)]
  exact Array.getElem_mem_toList _

theorem mem_center_ruK_iff
    (x : ↥ruK) :
    x ∈ Subgroup.center ↥ruK ↔ (x : Equiv.Perm (Fin 4060)) ∈ ruESub := by
  rw [ruE_eq_center]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [← Subtype.ext hyx]

theorem card_center_ruK :
    Nat.card (Subgroup.center ↥ruK) = 8 := by
  rw [← card_ruESub, ruE_eq_center, Subgroup.card_map_of_injective ruK.subtype_injective]

theorem comm_of_gens' {Γ : Type*} [Group Γ] (s : Set Γ) (hc : ∀ g ∈ s, ∀ h ∈ s, g * h = h * g) :
    ∀ x ∈ Subgroup.closure s, ∀ y ∈ Subgroup.closure s, x * y = y * x := by
  have h1 : ∀ g ∈ s, ∀ y ∈ Subgroup.closure s, Commute g y := by
    intro g hg y hy
    induction hy using Subgroup.closure_induction with
    | mem h hh => exact hc g hg h hh
    | one => exact Commute.one_right g
    | mul a b _ _ ha hb => exact ha.mul_right hb
    | inv a _ ha => exact ha.inv_right
  intro x hx y hy
  have : Commute x y := by
    induction hx using Subgroup.closure_induction with
    | mem g hg => exact h1 g hg y hy
    | one => exact Commute.one_left y
    | mul a b _ _ ha hb => exact ha.mul_left hb
    | inv a _ ha => exact ha.inv_left
  exact this.eq

theorem sq_of_gens' {Γ : Type*} [Group Γ] (s : Set Γ) (hc : ∀ g ∈ s, ∀ h ∈ s, g * h = h * g)
    (hsq : ∀ g ∈ s, g * g = 1) : ∀ x ∈ Subgroup.closure s, x * x = 1 := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem g hg => exact hsq g hg
  | one => simp
  | mul a b ha hb iha ihb =>
    have hab : a * b = b * a := comm_of_gens' s hc a ha b hb
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [iha, ihb, one_mul]
  | inv a ha iha => rw [← mul_inv_rev, iha, inv_one]

theorem isE2_of_card' {V : Type} [Group V] [Finite V] (hc : ∀ x y : V, x * y = y * x)
    (hsq : ∀ x : V, x * x = 1) {n : ℕ} (hcard : Nat.card V = 2 ^ n) :
    CFSG.Quasithin.IsE2 n V := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
  have h2 : ∀ x : Additive V, (2 : ℕ) • x = 0 := by
    intro x
    have : (2 : ℕ) • Additive.ofMul (Additive.toMul x) =
        Additive.ofMul (Additive.toMul x ^ 2) := by
      rw [ofMul_pow]
    have hx : Additive.ofMul (Additive.toMul x) = x := rfl
    rw [hx] at this
    rw [this, pow_two, hsq]
    rfl
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule h2
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  let b := Module.finBasis (ZMod 2) (Additive V)
  have hd : Module.finrank (ZMod 2) (Additive V) = n := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    have hcard' : Nat.card (Additive V) = 2 ^ n := hcard
    rw [hcard', Nat.card_zmod] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  let e : Additive V ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
    b.equivFun.trans (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (finCongr hd.symm))
  exact ⟨AddEquiv.toMultiplicativeRight e.toAddEquiv⟩

theorem rep_bEA (i : Fin 3) : Rep 4060 (bEA.getD i #[]) (vE i) := by
  have hl : i.val < bEA.length := by simp [bEA, wsA, basisEW]
  have h := (List.forall₂_iff_get.mp hbE).2 i hl (by simp)
  simp only [List.get_eq_getElem, List.getElem_ofFn] at h
  rw [List.getD_eq_getElem _ _ hl]
  exact h

theorem vE_eq_commut {i a b : ℕ} (hi : i < 3) (ha : a < 8) (hb : b < 8)
    (h : eqA 4060 (commutA ruKGensA[a]! ruKGensA[b]!) (bEA.getD i #[]) = true) :
    vE ⟨i, hi⟩ = ruKGens.getD a 1 * ruKGens.getD b 1 * (ruKGens.getD a 1)⁻¹ *
      (ruKGens.getD b 1)⁻¹ :=
  (eq_of_eqA (rep_commutA (rep_ruKGens a ha) (rep_ruKGens b hb)) (rep_bEA ⟨i, hi⟩) h).symm

theorem rep_xgens :
    (∀ h < 2, Rep 4060 (#[xEA, cjA nEA (ruInv nEA) xEA] : Array (Array ℕ))[h]!
      ([xE, nE * xE * nE⁻¹].getD h 1)) ∧
    ∀ h < 2, Rep 4060 (#[ruInv xEA, ruInv (cjA nEA (ruInv nEA) xEA)] : Array (Array ℕ))[h]!
      ([xE, nE * xE * nE⁻¹].getD h 1)⁻¹ := by
  have h1 := rep_cjA rep_nE (rep_ruInv' rep_nE) rep_xE
  exact ⟨rep_getD_two' rep_xE h1, rep_getD_two_inv' (rep_ruInv' rep_xE) (rep_ruInv' h1)⟩

theorem rep_r30 : Rep 4060 root30A r30 :=
  rep_conjA (rep_abA (by decide)) rep_ruZ

end Facts

end CFSG.Quasithin.KGC31.Ru

end
