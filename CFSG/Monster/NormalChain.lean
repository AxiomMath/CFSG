module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs

public section

namespace CFSG.Monster

variable {H : Type*} [Group H]

theorem mem_map_center_iff {Q : Subgroup H} {x : H} :
    x ∈ (Subgroup.center Q).map Q.subtype ↔ x ∈ Q ∧ ∀ y ∈ Q, y * x = x * y := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q.2, fun y hy => ?_⟩
    have := Subgroup.mem_center_iff.1 hq ⟨y, hy⟩
    exact congrArg Subtype.val this
  · rintro ⟨hxQ, hx⟩
    refine ⟨⟨x, hxQ⟩, Subgroup.mem_center_iff.2 fun y => Subtype.ext (hx y y.2), rfl⟩

theorem normal_map_center (Q : Subgroup H) [hQ : Q.Normal] :
    ((Subgroup.center Q).map Q.subtype).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨hxQ, hxc⟩ := mem_map_center_iff.1 hx
  refine mem_map_center_iff.2 ⟨hQ.conj_mem x hxQ g, fun y hy => ?_⟩
  have h1 := hxc (g⁻¹ * y * g) (by simpa using hQ.conj_mem y hy g⁻¹)
  calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
    _ = g * x * g⁻¹ * y := by group

theorem normal_eq_of_prime_central_irreducible {p : ℕ} (hp : p.Prime) {Q Z : Subgroup H}
    [hQ : Q.Normal] (hZ : Z = (Subgroup.center Q).map Q.subtype) (hZp : Nat.card Z = p)
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ Z) (hQZ : Z ≠ Q)
    (hsimple : IsSimpleGroup (H ⧸ Q))
    (hfaith : ∀ h : H, (∀ x ∈ Q, h * x * h⁻¹ * x⁻¹ ∈ Z) → h ∈ Q)
    (hirr : ∀ R : Subgroup H, R.Normal → Z ≤ R → R ≤ Q → R = Z ∨ R = Q) :
    Z.Normal ∧ ⊥ < Z ∧ Z < Q ∧ Q < ⊤ ∧
      ∀ N : Subgroup H, N.Normal → N = ⊥ ∨ N = Z ∨ N = Q ∨ N = ⊤ := by
  subst hZ
  set Z := (Subgroup.center Q).map Q.subtype with hZdef
  have hZn : Z.Normal := normal_map_center Q
  have hZQ : Z ≤ Q := fun x hx => (mem_map_center_iff.1 hx).1
  have hfin : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZp]; exact hp.ne_zero)
  have hZbot : Z ≠ ⊥ := by
    intro h
    have : Nat.card Z = 1 := by rw [h, Subgroup.card_bot]
    rw [hZp] at this
    exact hp.one_lt.ne' this
  have hQtop : Q ≠ ⊤ := by
    intro h
    have := hsimple.toNontrivial
    subst h
    apply not_subsingleton (H ⧸ (⊤ : Subgroup H))
    constructor
    intro a b
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    exact QuotientGroup.eq.2 (Subgroup.mem_top _)
  refine ⟨hZn, bot_lt_iff_ne_bot.2 hZbot, lt_of_le_of_ne hZQ hQZ, lt_top_iff_ne_top.2 hQtop,
    fun N hN => ?_⟩
  set R := N ⊓ Q with hRdef
  have hRn : R.Normal := Subgroup.normal_inf_normal N Q
  have hRQ : R ≤ Q := inf_le_right
  have hR : R = ⊥ ∨ R = Z ∨ R = Q := by
    by_cases hZR : Z ≤ R
    · exact .inr (hirr R hRn hZR hRQ)
    · left
      have hRZ : R ⊓ Z = ⊥ := by
        have hdvd : Nat.card (R ⊓ Z : Subgroup H) ∣ p := hZp ▸ Subgroup.card_dvd_of_le inf_le_right
        rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
        · exact Subgroup.eq_bot_of_card_eq _ h1
        · exfalso
          apply hZR
          have := Subgroup.eq_of_le_of_card_ge (inf_le_right : R ⊓ Z ≤ Z) (by rw [h1, hZp])
          rw [← this]
          exact inf_le_left
      refine (Subgroup.eq_bot_iff_forall R).2 fun r hr => ?_
      have hrN : r ∈ N := (Subgroup.mem_inf.1 hr).1
      have hrQ : r ∈ Q := (Subgroup.mem_inf.1 hr).2
      have hrZ : r ∈ Z := by
        refine mem_map_center_iff.2 ⟨hrQ, fun y hy => ?_⟩
        have hc : r * y * r⁻¹ * y⁻¹ ∈ R ⊓ Z := by
          refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, hcomm r hrQ y hy⟩
          · have := hN.conj_mem r⁻¹ (inv_mem hrN) y
            have h2 := mul_mem hrN this
            simpa [mul_assoc] using h2
          · exact mul_mem (mul_mem (mul_mem hrQ hy) (inv_mem hrQ)) (inv_mem hy)
        rw [hRZ, Subgroup.mem_bot] at hc
        have : r * y = y * r := by
          calc r * y = (r * y * r⁻¹ * y⁻¹) * (y * r) := by group
            _ = y * r := by rw [hc, one_mul]
        exact this.symm
      have : r ∈ R ⊓ Z := Subgroup.mem_inf.2 ⟨hr, hrZ⟩
      rw [hRZ, Subgroup.mem_bot] at this
      exact this
  rcases hR with hR | hR | hR
  ·
    have hNQ : N ≤ Q := by
      intro n hn
      refine hfaith n fun x hx => ?_
      have hmem : n * x * n⁻¹ * x⁻¹ ∈ R := by
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · have := hN.conj_mem n⁻¹ (inv_mem hn) x
          have h2 := mul_mem hn this
          simpa [mul_assoc] using h2
        · exact mul_mem (hQ.conj_mem x hx n) (inv_mem hx)
      rw [hR, Subgroup.mem_bot] at hmem
      rw [hmem]
      exact one_mem _
    left
    rw [← hR, hRdef, inf_eq_left.2 hNQ]
  · have hNQ : N ≤ Q := by
      intro n hn
      refine hfaith n fun x hx => ?_
      have hmem : n * x * n⁻¹ * x⁻¹ ∈ R := by
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · have := hN.conj_mem n⁻¹ (inv_mem hn) x
          have h2 := mul_mem hn this
          simpa [mul_assoc] using h2
        · exact mul_mem (hQ.conj_mem x hx n) (inv_mem hx)
      rwa [hR] at hmem
    right; left
    rw [← hR, hRdef, inf_eq_left.2 hNQ]
  ·
    have hQN : Q ≤ N := by rw [← hR]; exact inf_le_left
    have hmapn : (N.map (QuotientGroup.mk' Q)).Normal :=
      Subgroup.Normal.map hN _ (QuotientGroup.mk'_surjective Q)
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple _ hmapn with h | h
    · right; right; left
      refine le_antisymm ?_ hQN
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
      exact h
    · right; right; right
      refine eq_top_iff.2 fun g _ => ?_
      have hg : (QuotientGroup.mk' Q g) ∈ N.map (QuotientGroup.mk' Q) := h ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hng⟩ := hg
      have hq : n⁻¹ * g ∈ Q := by
        rw [← QuotientGroup.eq]
        exact hng
      have := mul_mem hn (hQN hq)
      simpa using this

theorem normal_eq_of_prime_central_irreducible' {p : ℕ} (hp : p.Prime) {Q Z : Subgroup H}
    [Q.Normal] (hZ : ∀ x, x ∈ Z ↔ x ∈ Q ∧ ∀ y ∈ Q, y * x = x * y) (hZp : Nat.card Z = p)
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ Z) (hQZ : Z ≠ Q)
    (hsimple : IsSimpleGroup (H ⧸ Q))
    (hfaith : ∀ h : H, (∀ x ∈ Q, h * x * h⁻¹ * x⁻¹ ∈ Z) → h ∈ Q)
    (hirr : ∀ R : Subgroup H, R.Normal → Z ≤ R → R ≤ Q → R = Z ∨ R = Q) :
    Z.Normal ∧ ⊥ < Z ∧ Z < Q ∧ Q < ⊤ ∧
      ∀ N : Subgroup H, N.Normal → N = ⊥ ∨ N = Z ∨ N = Q ∨ N = ⊤ :=
  normal_eq_of_prime_central_irreducible hp
    (Subgroup.ext fun x => (hZ x).trans mem_map_center_iff.symm) hZp hcomm hQZ hsimple hfaith hirr

end CFSG.Monster
