module

public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UCK (fixV)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem card_sup_uc6 {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {D Q : Subgroup G} (hD : Nat.card D = r)
    (hQ2 : IsPGroup 2 Q) (hDQ : D ≤ normalizer (Q : Set G)) :
    Nat.card ↥(Q ⊔ D) = Nat.card Q * Nat.card D := by
  let H : Subgroup G := Q ⊔ D
  have hQH : Q ≤ H := le_sup_left
  have hDH : D ≤ H := le_sup_right
  have hHN : H ≤ normalizer (Q : Set G) := sup_le Subgroup.le_normalizer hDQ
  let K : Subgroup ↥H := Q.subgroupOf H
  let R : Subgroup ↥H := D.subgroupOf H
  have hKnormal : K.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).2 hHN
  let eK : ↥K ≃* ↥Q := Subgroup.subgroupOfEquivOfLe hQH
  let eR : ↥R ≃* ↥D := Subgroup.subgroupOfEquivOfLe hDH
  have hKcard : Nat.card K = Nat.card Q := Nat.card_congr eK.toEquiv
  have hRcard : Nat.card R = Nat.card D := Nat.card_congr eR.toEquiv
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ2
  have hcop : Nat.Coprime (Nat.card Q) (Nat.card D) := by
    rw [hn, hD]
    exact Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hr).2 (Ne.symm hr2))
  have hdisj : Disjoint K R := by
    rw [Subgroup.disjoint_def]
    intro y hyK hyR
    have h1 : orderOf y ∣ Nat.card Q := by
      have := orderOf_dvd_natCard (⟨y, hyK⟩ : ↥K)
      rwa [Subgroup.orderOf_mk, hKcard] at this
    have h2 : orderOf y ∣ Nat.card D := by
      have := orderOf_dvd_natCard (⟨y, hyR⟩ : ↥R)
      rwa [Subgroup.orderOf_mk, hRcard] at this
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hsupK : K ⊔ R = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQH hDH]
    exact Subgroup.subgroupOf_self (Q ⊔ D)
  have hmul : (K : Set ↥H) * (R : Set ↥H) = Set.univ := by
    rw [← Subgroup.normal_mul K R, hsupK]
    rfl
  have hKR : K.IsComplement' R := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul
  rw [← hKR.card_mul, hKcard, hRcard]

theorem not_dvd_card_sup_uc6 {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrp : r ≠ p) {D Q : Subgroup G} (hD : Nat.card D = r) (hQ2 : IsPGroup 2 Q)
    (hDQ : D ≤ normalizer (Q : Set G)) : ¬ p ∣ Nat.card ↥(Q ⊔ D) := by
  rw [card_sup_uc6 hr hr2 hD hQ2 hDQ, hD]
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ2
  rw [hn]
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h2 | h2
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2))
  · exact hrp ((Nat.prime_dvd_prime_iff_eq hp hr).1 h2).symm

theorem exists_irreducible_uc6 {p r : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrp : r ≠ p) {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : Representation (ZMod p) G V) (hρ : Function.Injective ρ) {D Q : Subgroup G}
    (hD : Nat.card D = r) (hQ2 : IsPGroup 2 Q) (hQne : Q ≠ ⊥)
    (hDQ : D ≤ normalizer (Q : Set G)) :
    ∃ W : Submodule (ZMod p) V, (∀ h ∈ Q ⊔ D, ∀ w ∈ W, ρ h w ∈ W) ∧
      (∃ q ∈ Q, ∃ w ∈ W, ρ q w ≠ w) ∧
      ∀ U : Submodule (ZMod p) V, U ≤ W → (∀ h ∈ Q ⊔ D, ∀ u ∈ U, ρ h u ∈ U) → U = ⊥ ∨ U = W := by
  classical
  let H : Subgroup G := Q ⊔ D
  let ρH : Representation (ZMod p) ↥H V := ρ.comp H.subtype
  haveI : NeZero (Nat.card ↥H : ZMod p) := ⟨by
    intro h
    exact not_dvd_card_sup_uc6 (Fact.out : p.Prime) hp2 hr hr2 hrp hD hQ2 hDQ
      ((ZMod.natCast_eq_zero_iff (Nat.card ↥H) p).1 h)⟩
  haveI hss : Representation.IsSemisimpleRepresentation ρH := inferInstance
  let P : Submodule (ZMod p) V → Prop := fun W =>
    (∀ h ∈ H, ∀ w ∈ W, ρ h w ∈ W) ∧ ∃ q ∈ Q, ∃ w ∈ W, ρ q w ≠ w
  have hPtop : P ⊤ := by
    refine ⟨fun h _ w _ => Submodule.mem_top, ?_⟩
    obtain ⟨q, hq1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hQne
    have hρq : ρ (q : G) ≠ 1 := fun h => hq1 (Subtype.ext (hρ (by rw [h]; simp)))
    obtain ⟨w, hw⟩ : ∃ w, ρ (q : G) w ≠ w := by
      by_contra hcon
      push Not at hcon
      exact hρq (LinearMap.ext fun w => by simpa using hcon w)
    exact ⟨q, q.2, w, Submodule.mem_top, hw⟩
  obtain ⟨W, hWP, hWmin⟩ :=
    (wellFounded_lt (α := Submodule (ZMod p) V)).has_min {W | P W} ⟨⊤, hPtop⟩
  refine ⟨W, hWP.1, hWP.2, fun U hUW hUinv => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hU0, hUW'⟩ := hcon
  obtain ⟨c, hc⟩ := ComplementedLattice.exists_isCompl
    (⟨U, fun g v hv => hUinv g g.2 v hv⟩ : Subrepresentation ρH)
  have hcdisj : U ⊓ c.toSubmodule = ⊥ := by
    have := hc.1.eq_bot
    exact congrArg Subrepresentation.toSubmodule this
  have hcsup : U ⊔ c.toSubmodule = ⊤ := by
    have := hc.2.eq_top
    exact congrArg Subrepresentation.toSubmodule this
  have hcinv : ∀ h ∈ H, ∀ v ∈ c.toSubmodule, ρ h v ∈ c.toSubmodule := fun h hh v hv =>
    c.apply_mem_toSubmodule ⟨h, hh⟩ hv
  have hQtriv : ∀ X : Submodule (ZMod p) V, X < W → (∀ h ∈ H, ∀ x ∈ X, ρ h x ∈ X) →
      ∀ q ∈ Q, ∀ x ∈ X, ρ q x = x := by
    intro X hXW hXinv q hq x hx
    by_contra hne
    exact hWmin X ⟨hXinv, q, hq, x, hx, hne⟩ hXW
  have hU_lt : U < W := lt_of_le_of_ne hUW hUW'
  have hU''_lt : c.toSubmodule ⊓ W < W := by
    refine lt_of_le_of_ne inf_le_right fun h => ?_
    have hWc : W ≤ c.toSubmodule := by
      intro w hw
      have : w ∈ c.toSubmodule ⊓ W := by rw [h]; exact hw
      exact this.1
    apply hU0
    rw [eq_bot_iff, ← hcdisj]
    exact le_inf le_rfl (hUW.trans hWc)
  have hU''inv : ∀ h ∈ H, ∀ x ∈ c.toSubmodule ⊓ W, ρ h x ∈ c.toSubmodule ⊓ W := fun h hh x hx =>
    ⟨hcinv h hh x hx.1, hWP.1 h hh x hx.2⟩
  have hQU := hQtriv U hU_lt hUinv
  have hQU'' := hQtriv _ hU''_lt hU''inv
  obtain ⟨q, hqQ, w, hwW, hw⟩ := hWP.2
  apply hw
  have hwsplit : w ∈ U ⊔ c.toSubmodule := by rw [hcsup]; exact Submodule.mem_top
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hwsplit
  have hvW : v ∈ W := by
    have : v = (u + v) - u := by abel
    rw [this]
    exact W.sub_mem hwW (hUW hu)
  rw [map_add, hQU q hqQ u hu, hQU'' q hqQ v ⟨hv, hvW⟩]

end CFSG.LocalAnalysis.UniquenessCase.UC6
