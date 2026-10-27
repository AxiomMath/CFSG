module

public import CFSG.Permutation.UnitaryThreeRecognition.TorusIndex
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem faithful_of_isSimpleGroup [IsSimpleGroup G] (h2 : IsMultiplyPretransitive G Ω 2)
    {x y : Ω} (hxy : x ≠ y) : ∀ g : G, (∀ z : Ω, g • z = z) → g = 1 := by
  intro g hg
  have hker : g ∈ (MulAction.toPermHom G Ω).ker := by
    rw [MonoidHom.mem_ker]; ext z; exact hg z
  rcases (MonoidHom.normal_ker (MulAction.toPermHom G Ω)).eq_bot_or_eq_top with h | h
  · rw [h] at hker; exact hker
  · exfalso
    obtain ⟨g', hg'x, -⟩ := MulAction.is_two_pretransitive_iff.mp h2 hxy hxy.symm
    have hg'k : g' ∈ (MulAction.toPermHom G Ω).ker := by rw [h]; trivial
    rw [MonoidHom.mem_ker] at hg'k
    have := congrArg (fun π : Equiv.Perm Ω => π x) hg'k
    simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.coe_one, id] at this
    exact hxy (this.symm.trans hg'x)

theorem isRootSubgroup_of {Q : Subgroup G} {α : Ω} (hQ : Q ≤ stabilizer G α)
    (hQn : (Q.subgroupOf (stabilizer G α)).Normal)
    (hreg : ∀ β γ : Ω, β ≠ α → γ ≠ α → ∃! u : Q, (u : G) • β = γ) : IsRootSubgroup Q α where
  le_stabilizer := hQ
  normal g hg x hx := by
    have := hQn.conj_mem ⟨x, hQ hx⟩ hx ⟨g, hg⟩
    exact this
  regular := hreg

theorem exists_unique_involution {T : Subgroup G} [Finite T] [IsCyclic T]
    (heven : 2 ∣ Nat.card T) :
    ∃ j ∈ T, j * j = 1 ∧ j ≠ 1 ∧ ∀ t ∈ T, t * t = 1 → t = 1 ∨ t = j := by
  classical
  have : Fintype T := Fintype.ofFinite T
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 heven
  have hx2 : x * x = 1 := by rw [← sq, ← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by intro e; rw [e, orderOf_one] at hx; exact absurd hx (by decide)
  refine ⟨x, x.2, congrArg Subtype.val hx2, fun e => hx1 (Subtype.ext e), ?_⟩
  intro t ht htt
  by_contra hne
  push Not at hne
  have hS := IsCyclic.card_pow_eq_one_le (α := T) (n := 2) two_pos
  set y : T := ⟨t, ht⟩
  have hy1 : y ≠ 1 := fun e => hne.1 (congrArg Subtype.val e)
  have hyx : y ≠ x := fun e => hne.2 (congrArg Subtype.val e)
  have hsub : ({1, x, y} : Finset T) ⊆ Finset.univ.filter (fun z : T => z ^ 2 = 1) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hz with rfl | rfl | rfl
    · exact one_pow 2
    · rw [sq]; exact hx2
    · rw [sq]; exact Subtype.ext htt
  have hcard : ({1, x, y} : Finset T).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hyx.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hx1.symm, hy1.symm⟩
  have := Finset.card_le_card hsub
  omega

theorem gcd_three_facts {q : ℕ} (hq : Odd q) :
    (Nat.gcd (q + 1) 3 = 1 ∨ Nat.gcd (q + 1) 3 = 3) ∧ Nat.gcd (q + 1) 3 ∣ q ^ 2 - 1 := by
  refine ⟨?_, ?_⟩
  · rcases (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_right (q + 1) 3) with h | h
    · exact Or.inl h
    · exact Or.inr h
  · have h1 : q + 1 ∣ q ^ 2 - 1 := by
      obtain ⟨m, rfl⟩ := hq
      exact ⟨2 * m, by rw [show (2 * m + 1) ^ 2 - 1 = (2 * m + 1 + 1) * (2 * m) by
        rw [sq]; ring_nf; omega]⟩
    exact (Nat.gcd_dvd_left (q + 1) 3).trans h1

namespace IsRootSubgroup

variable {Q : Subgroup G} {a : Ω} (hQ : IsRootSubgroup Q a)
include hQ

noncomputable def pairStabEquivQuotient [(Q.subgroupOf (stabilizer G a)).Normal] {b : Ω}
    (hb : b ≠ a) : pairStab G a b ≃* (stabilizer G a ⧸ Q.subgroupOf (stabilizer G a)) := by
  have hTH : pairStab G a b ≤ stabilizer G a := fun t ht => ht.1
  refine MulEquiv.ofBijective ((QuotientGroup.mk' (Q.subgroupOf (stabilizer G a))).comp
    (Subgroup.inclusion hTH)) ⟨?_, ?_⟩
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro t ht
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at ht
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subgroup.disjoint_def.mp (hQ.disjoint_pairStab hb) ht t.2)
  · intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ y
    obtain ⟨x, hx, t, ht, hg⟩ := hQ.exists_mul_pairStab hb g.2
    refine ⟨⟨t, ht⟩, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    have h1 : (t : G)⁻¹ * (g : G) ∈ Q := by
      rw [hg]
      have := hQ.normal t⁻¹ ((pairStab G a b).inv_mem ht).1 x hx
      have e : t⁻¹ * (x * t) = t⁻¹ * x * t⁻¹⁻¹ := by group
      rw [e]; exact this
    exact h1

theorem exists_swap_involution [Finite G] [Finite Ω] {b : Ω} (hb : b ≠ a)
    (htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w)
    (hfaith : ∀ g : G, (∀ x : Ω, g • x = x) → g = 1)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    {j : G} (hj : j ∈ pairStab G a b) (hj2 : j * j = 1) (hj1 : j ≠ 1)
    (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j)
    {p f : ℕ} (hpp : p.Prime) (hp : 3 ≤ p) (hf : 1 ≤ f)
    (hQcard : Nat.card Q = p ^ (3 * f)) (hΩcard : Nat.card Ω = p ^ (3 * f) + 1)
    (hTdvd : Nat.card (pairStab G a b) ∣ p ^ (2 * f) - 1) :
    ∃ s : G, s * s = 1 ∧ s • a = b ∧ ∃ k : G, s = k⁻¹ * j * k := by
  have hc := hQ.card_conjSwap_eq hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hQcard hΩcard hTdvd
  have hq : 3 ≤ p ^ f := le_trans hp (Nat.le_self_pow (by omega) p)
  have hpos : 0 < Nat.card (ConjSwap G j a b) := by rw [hc]; omega
  have : Finite (ConjSwap G j a b) := inferInstance
  obtain ⟨⟨s, ⟨k, rfl⟩, hsa⟩⟩ := (Nat.card_pos_iff.mp hpos).1
  refine ⟨k⁻¹ * j * k, ?_, hsa, k, rfl⟩
  calc k⁻¹ * j * k * (k⁻¹ * j * k) = k⁻¹ * (j * j) * k := by group
    _ = 1 := by rw [hj2]; group

end IsRootSubgroup

end CFSG.UnitaryThreeRecognition
