module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

theorem commutator_sup_zpowers_le {X : Type*} [Group X] (L : Subgroup X) {a : X}
    (ha : ∀ l ∈ L, l * a = a * l) :
    ⁅L ⊔ Subgroup.zpowers a, L ⊔ Subgroup.zpowers a⁆ ≤ L := by
  have hcomm : ∀ l ∈ L, ∀ k : ℤ, Commute (a ^ k) l := fun l hl k =>
    ((show Commute l a from ha l hl).zpow_right k).symm
  obtain ⟨K, hKmem⟩ : ∃ K : Subgroup X, ∀ x, x ∈ K ↔ ∃ l ∈ L, ∃ k : ℤ, x = l * a ^ k := by
    refine ⟨{ carrier := {x | ∃ l ∈ L, ∃ k : ℤ, x = l * a ^ k}
              one_mem' := ⟨1, L.one_mem, 0, by simp⟩
              mul_mem' := ?_
              inv_mem' := ?_ }, fun x => Iff.rfl⟩
    · rintro _ _ ⟨l, hl, k, rfl⟩ ⟨l', hl', m, rfl⟩
      refine ⟨l * l', L.mul_mem hl hl', k + m, ?_⟩
      calc l * a ^ k * (l' * a ^ m) = l * (a ^ k * l') * a ^ m := by simp only [mul_assoc]
        _ = l * (l' * a ^ k) * a ^ m := by rw [(hcomm l' hl' k).eq]
        _ = l * l' * (a ^ k * a ^ m) := by simp only [mul_assoc]
        _ = l * l' * a ^ (k + m) := by rw [zpow_add]
    · rintro _ ⟨l, hl, k, rfl⟩
      refine ⟨l⁻¹, L.inv_mem hl, -k, ?_⟩
      rw [mul_inv_rev, zpow_neg]
      exact ((hcomm l hl k).inv_left.inv_right).eq
  have hK : L ⊔ Subgroup.zpowers a ≤ K := by
    apply sup_le
    · intro x hx
      exact (hKmem x).2 ⟨x, hx, 0, by simp⟩
    · exact Subgroup.zpowers_le.2 ((hKmem a).2 ⟨1, L.one_mem, 1, by simp⟩)
  have key : ∀ p q u v : X, Commute u q → Commute v p → Commute v u →
      @Bracket.bracket X X commutatorElement (p * u) (q * v) =
        @Bracket.bracket X X commutatorElement p q := by
    intro p q u v huq hvp hvu
    have e1 : p * u * (q * v) = p * q * (u * v) := by
      calc p * u * (q * v) = p * (u * q) * v := by simp only [mul_assoc]
        _ = p * (q * u) * v := by rw [huq.eq]
        _ = p * q * (u * v) := by simp only [mul_assoc]
    have e2 : q * v * (p * u) = q * p * (u * v) := by
      calc q * v * (p * u) = q * (v * p) * u := by simp only [mul_assoc]
        _ = q * (p * v) * u := by rw [hvp.eq]
        _ = q * p * (v * u) := by simp only [mul_assoc]
        _ = q * p * (u * v) := by rw [hvu.eq]
    rw [commutatorElement_def, commutatorElement_def]
    calc p * u * (q * v) * (p * u)⁻¹ * (q * v)⁻¹
        = (p * u * (q * v)) * (q * v * (p * u))⁻¹ := by group
      _ = (p * q * (u * v)) * (q * p * (u * v))⁻¹ := by rw [e1, e2]
      _ = p * q * p⁻¹ * q⁻¹ := by group
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨l, hl, k, rfl⟩ := (hKmem g₁).1 (hK hg₁)
  obtain ⟨l', hl', m, rfl⟩ := (hKmem g₂).1 (hK hg₂)
  rw [key l l' (a ^ k) (a ^ m) (hcomm l' hl' k) (hcomm l hl m) (Commute.zpow_zpow_self a m k),
    commutatorElement_def]
  exact L.mul_mem (L.mul_mem (L.mul_mem hl hl') (L.inv_mem hl)) (L.inv_mem hl')

theorem eq_top_of_forall_pow_three_mem {X : Type*} [Group X] [IsSimpleGroup X] {U : Subgroup X}
    {z : X} (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) (hU : ∀ x : X, x ^ 3 = 1 → x ∈ U) : U = ⊤ := by
  have hN : Subgroup.normalClosure ({z} : Set X) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure ({z} : Set X))
      with h | h
    · exfalso
      have hzmem : z ∈ Subgroup.normalClosure ({z} : Set X) :=
        Subgroup.subset_normalClosure (Set.mem_singleton z)
      rw [h, Subgroup.mem_bot] at hzmem
      exact hz1 hzmem
    · exact h
  have hle : Subgroup.normalClosure ({z} : Set X) ≤ U := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro x hx
    obtain ⟨b, hb, hbx⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    obtain ⟨c, rfl⟩ := isConj_iff.1 hbx
    rw [Set.mem_singleton_iff.1 hb]
    refine hU _ ?_
    rw [conj_pow, hz3]
    simp
  rw [hN] at hle
  exact top_unique hle

theorem map_commutator_subgroupOf {X Q : Type*} [Group X] [Group Q] {M Z : Subgroup X}
    (hZM : Z ≤ M) (f : ↥M →* Q) :
    (⁅Z, Z⁆.subgroupOf M).map f = ⁅(Z.subgroupOf M).map f, (Z.subgroupOf M).map f⁆ := by
  have hmapZ : Subgroup.map M.subtype ⁅Z.subgroupOf M, Z.subgroupOf M⁆ = ⁅Z, Z⁆ := by
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hZM]
  have key : ⁅Z, Z⁆.subgroupOf M = ⁅Z.subgroupOf M, Z.subgroupOf M⁆ := by
    have h := Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective M)
      ⁅Z.subgroupOf M, Z.subgroupOf M⁆
    rw [hmapZ] at h
    exact h
  rw [key, Subgroup.map_commutator]

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
