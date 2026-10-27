module

public import CFSG.Quasithin.Background.A3Structure320Basic
public import CFSG.Quasithin.Background.A3Structure320Radical
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Quasithin.Background.A3Structure316

public section

namespace CFSG.Quasithin

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

namespace A318P

theorem mem_of_conjNormal_inner {X : Type} [Group X] {S : Subgroup X} [S.Normal]
    (hC : ∀ c : X, (∀ s ∈ S, c * s = s * c) → c = 1) {x : X}
    (hx : (MulAut.conjNormal x : MulAut ↥S) ∈ inner ↥S) : x ∈ S := by
  obtain ⟨s, hs⟩ := hx
  have key : ∀ (a : X), (∀ t ∈ S, a * t * a⁻¹ = x * t * x⁻¹) →
      ∀ t ∈ S, (a⁻¹ * x) * t = t * (a⁻¹ * x) := by
    intro a h t ht
    have h' := h t ht
    calc a⁻¹ * x * t = a⁻¹ * (x * t * x⁻¹) * x := by group
      _ = a⁻¹ * (a * t * a⁻¹) * x := by rw [h']
      _ = t * (a⁻¹ * x) := by group
  have hcomm := key (s : X) (fun t ht => by
    have h := congrArg (fun φ : MulAut ↥S => (φ ⟨t, ht⟩ : X)) hs
    simpa only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
      InvMemClass.coe_inv] using h)
  have h1 := hC _ hcomm
  have : x = s := by
    have := mul_eq_one_iff_eq_inv.1 h1
    simpa using this.symm
  rw [this]
  exact s.2

theorem mem_of_orderOf_pow_of_not_dvd_outer {X : Type} [Group X] {S : Subgroup X} [S.Normal]
    (hC : ∀ c : X, (∀ s ∈ S, c * s = s * c) → c = 1)
    {p : ℕ} (hp : p.Prime) (hout : ¬ p ∣ Nat.card (Outer ↥S)) {x : X} {k : ℕ}
    (hx : orderOf x = p ^ k) : x ∈ S := by
  apply mem_of_conjNormal_inner hC
  set φ : Outer ↥S := QuotientGroup.mk' (inner ↥S) (MulAut.conjNormal x) with hφ
  have h1 : orderOf φ ∣ p ^ k := by
    rw [← hx]
    exact (orderOf_map_dvd _ _).trans (orderOf_map_dvd _ _)
  have h2 : orderOf φ ∣ Nat.card (Outer ↥S) := orderOf_dvd_natCard φ
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp).1 h1
  have hj0 : j = 0 := by
    by_contra hne
    exact hout ((dvd_pow_self p hne).trans (hj' ▸ h2))
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj'
  rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hj'
  exact hj'

theorem le_oPrimeResidualOf_of_isSimpleGroup {X : Type} [Group X] [Finite X] {S : Subgroup X}
    [S.Normal] {p : ℕ} (hp : p.Prime) [IsSimpleGroup ↥S] (hpS : p ∣ Nat.card S) :
    S ≤ oPrimeResidualOf p (⊤ : Subgroup X) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hpS
  have hN : Subgroup.normalClosure ({y} : Set ↥S) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure ({y} : Set ↥S))
      with h | h
    · exfalso
      have hmem : y ∈ Subgroup.normalClosure ({y} : Set ↥S) := Subgroup.subset_normalClosure rfl
      rw [h, Subgroup.mem_bot] at hmem
      rw [hmem, orderOf_one] at hy
      exact hp.one_lt.ne hy
    · exact h
  have hle : Subgroup.normalClosure ({y} : Set ↥S) ≤
      (oPrimeResidualOf p (⊤ : Subgroup X)).comap S.subtype := by
    rw [Subgroup.normalClosure]
    refine (Subgroup.closure_le _).2 ?_
    intro z hz
    obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 hz
    obtain ⟨c, hc⟩ := isConj_iff.1 hconj
    rw [Set.mem_singleton_iff] at ha
    subst ha
    have hz : (S.subtype z : X) = (c : X) * (a : X) * (c : X)⁻¹ := by
      rw [← hc]
      simp
    have hord : orderOf (S.subtype z) = p := by
      have h := orderOf_injective (MulAut.conj (c : X)).toMonoidHom
        (MulAut.conj (c : X)).injective (a : X)
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
      rw [hz, h, Subgroup.orderOf_coe, hy]
    exact Subgroup.subset_closure ⟨Subgroup.mem_top _, 1, by rw [hord, pow_one]⟩
  intro s hs
  have : (⟨s, hs⟩ : ↥S) ∈ Subgroup.normalClosure ({y} : Set ↥S) := hN ▸ Subgroup.mem_top _
  exact hle this

theorem oPrimeResidualOf_eq_of_forall {X : Type} [Group X] [Finite X] {S : Subgroup X} [S.Normal]
    {p : ℕ} (hp : p.Prime) [IsSimpleGroup ↥S] (hpS : p ∣ Nat.card S)
    (h : ∀ (x : X) (k : ℕ), orderOf x = p ^ k → x ∈ S) :
    oPrimeResidualOf p (⊤ : Subgroup X) = S := by
  refine le_antisymm ((Subgroup.closure_le S).2 ?_)
    (le_oPrimeResidualOf_of_isSimpleGroup hp hpS)
  rintro x ⟨-, k, hk⟩
  exact h x k hk

theorem oPrimeResidualOf_eq_of_not_dvd_outer {X : Type} [Group X] [Finite X] {S : Subgroup X}
    [S.Normal] (hC : ∀ c : X, (∀ s ∈ S, c * s = s * c) → c = 1) {p : ℕ} (hp : p.Prime)
    [IsSimpleGroup ↥S] (hpS : p ∣ Nat.card S) (hout : ¬ p ∣ Nat.card (Outer ↥S)) :
    oPrimeResidualOf p (⊤ : Subgroup X) = S :=
  oPrimeResidualOf_eq_of_forall hp hpS fun _ _ hk => mem_of_orderOf_pow_of_not_dvd_outer hC hp hout hk

theorem dvd_card_of_one_lt_pRank {X : Type} [Group X] [Finite X] {S : Subgroup X} {p : ℕ}
    (hp : p.Prime) (h : 1 < CFSG.Open.pRank p S) : p ∣ Nat.card S := by
  obtain ⟨E, hES, -, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt S
  have hdvd : Nat.card E ∣ Nat.card S := Subgroup.card_dvd_of_le hES
  rw [hcard] at hdvd
  exact (dvd_pow_self p (by omega)).trans hdvd

theorem three_le_pRank_of_centralizes {X : Type} [Group X] [Finite X] {S : Subgroup X} {p : ℕ}
    [hp : Fact p.Prime] {σ : X} (hσ : orderOf σ = p) (hσS : σ ∉ S) {E : Subgroup X}
    (hES : E ≤ S) (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2)
    (hc : ∀ e ∈ E, σ * e = e * σ) : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  have hX : IsElemAbelian p (Subgroup.zpowers σ) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 b.2
      apply Subtype.ext
      change (a : X) * b = b * a
      rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hσ, pow_orderOf_eq_one,
        one_zpow]
  have hXcard : Nat.card (Subgroup.zpowers σ) = p ^ 1 := by
    rw [Nat.card_zpowers, hσ, pow_one]
  have := A320.pRank_add_le (p := p) (⊥ : Subgroup X)
    (by simpa [Nat.dvd_one] using hp.out.ne_one) hX hE
    (fun x hx e he => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [Subgroup.mem_bot, commutatorElement_def]
      have h1 : Commute σ e := hc e he
      have h2 : Commute (σ ^ m) e := h1.zpow_left m
      rw [h2.eq]
      group)
    (fun x hx e he hxe => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      have h1 : σ ^ m * e = 1 := Subgroup.mem_bot.1 hxe
      have h2 : σ ^ m ∈ E := by
        have : σ ^ m = e⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [this]
        exact E.inv_mem he
      have h3 : σ ^ m = 1 := by
        by_contra hne
        apply hσS
        apply hES
        have hmem : σ ∈ Subgroup.zpowers (σ ^ m) :=
          A320.mem_zpowers_of_mem_zpowers_prime hσ (Subgroup.mem_zpowers_iff.2 ⟨m, by simp⟩) hne
        exact (Subgroup.zpowers_le.2 h2) hmem
      refine ⟨h3, ?_⟩
      rw [h3, one_mul] at h1
      exact h1)
    hXcard hcard
  omega

end A318P

end CFSG.Quasithin
