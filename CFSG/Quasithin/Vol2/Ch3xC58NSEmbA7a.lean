module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Quasithin.C58NS.Emb

open Equiv

theorem five_le_ncard_orbit {α : Type*} {H : Subgroup (Perm α)} [Finite H] [IsSimpleGroup H]
    (hH : Nat.card H = 60) {i : α} (hi : ∃ h ∈ H, h i ≠ i) :
    5 ≤ (MulAction.orbit H i).ncard := by
  set S := MulAction.stabilizer H i with hS
  have hidx : S.index = (MulAction.orbit H i).ncard := MulAction.index_stabilizer H i
  have hdvd := Subgroup.index_normalCore_dvd_factorial_index S
  rcases (Subgroup.normalCore_normal S).eq_bot_or_eq_top with hb | ht
  · rw [hb, Subgroup.index_bot, hH, hidx] at hdvd
    by_contra hlt
    push Not at hlt
    interval_cases h : (MulAction.orbit H i).ncard <;> revert hdvd <;> decide
  · exfalso
    obtain ⟨h, hh, hne⟩ := hi
    have hle := Subgroup.normalCore_le S
    rw [ht, top_le_iff] at hle
    have hmem : (⟨h, hh⟩ : H) ∈ S := by rw [hle]; exact Subgroup.mem_top _
    exact hne (MulAction.mem_stabilizer_iff.mp hmem)

@[expose] def fixSet {α : Type*} (H : Subgroup (Perm α)) : Set α := {j | ∀ h ∈ H, h j = j}

theorem mem_fixSet {α : Type*} {H : Subgroup (Perm α)} {j : α} :
    j ∈ fixSet H ↔ ∀ h ∈ H, h j = j :=
  Iff.rfl

theorem mem_fixSet_of_mem_normalizer {α : Type*} {H : Subgroup (Perm α)} {d : Perm α}
    (hd : d ∈ Subgroup.normalizer (H : Set (Perm α))) {j : α} (hj : j ∈ fixSet H) :
    d j ∈ fixSet H := by
  intro h hh
  have h1 : d⁻¹ * h * d ∈ H := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hd) h).mp hh
    simpa using this
  have h2 := hj _ h1
  simp only [Perm.mul_apply] at h2
  have := congrArg d h2
  simpa using this

theorem exists_orbit_eq_compl_fixSet {H : Subgroup (Perm (Fin 7))} [IsSimpleGroup H]
    (hH : Nat.card H = 60) :
    ∃ i, MulAction.orbit H i = (fixSet H)ᶜ ∧
      ((MulAction.orbit H i).ncard = 5 ∨ (MulAction.orbit H i).ncard = 6) := by
  classical
  obtain ⟨h, hh, h1⟩ : ∃ h ∈ H, h ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : H = ⊥ := (Subgroup.eq_bot_iff_forall H).mpr hcon
    rw [this, Subgroup.card_bot] at hH
    omega
  obtain ⟨i, hi⟩ : ∃ i, h i ≠ i := by
    by_contra hcon
    push Not at hcon
    exact h1 (Equiv.ext hcon)
  have hmoved : ∀ j, j ∉ fixSet H → 5 ≤ (MulAction.orbit H j).ncard := by
    intro j hj
    rw [mem_fixSet] at hj
    push Not at hj
    exact five_le_ncard_orbit hH hj
  have hiF : i ∉ fixSet H := fun hF => hi (hF h hh)
  have hsub : MulAction.orbit H i ⊆ (fixSet H)ᶜ := by
    rintro _ ⟨g, rfl⟩ hF
    apply hiF
    intro k hk
    have hc : (g : Perm (Fin 7)) * k * (g : Perm (Fin 7))⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem g.2 hk) (H.inv_mem g.2)
    have h2 := hF _ hc
    have h3 : (g : Perm (Fin 7)) (k i) = (g : Perm (Fin 7)) i := by
      simpa [Perm.mul_apply, Subgroup.smul_def, Perm.smul_def] using h2
    exact (g : Perm (Fin 7)).injective h3
  have hcard : ∀ s : Set (Fin 7), s.ncard ≤ 7 := fun s => by
    have := Set.ncard_le_ncard (Set.subset_univ s)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  have hsup : (fixSet H)ᶜ ⊆ MulAction.orbit H i := by
    intro j hj
    by_contra hji
    have hdisj : Disjoint (MulAction.orbit H i) (MulAction.orbit H j) := by
      rw [Set.disjoint_left]
      intro k hki hkj
      apply hji
      rw [MulAction.mem_orbit_iff] at hki hkj ⊢
      obtain ⟨a, rfl⟩ := hki
      obtain ⟨b, hb⟩ := hkj
      exact ⟨b⁻¹ * a, by rw [mul_smul, ← hb, inv_smul_smul]⟩
    have h1 := Set.ncard_union_eq hdisj
    have h2 := hcard (MulAction.orbit H i ∪ MulAction.orbit H j)
    have h3 := hmoved i hiF
    have h4 := hmoved j hj
    omega
  have hdvd : (MulAction.orbit H i).ncard ∣ 60 := by
    rw [← MulAction.index_stabilizer, ← hH]
    exact Subgroup.index_dvd_card _
  have h5 := hmoved i hiF
  have h7 := hcard (MulAction.orbit H i)
  refine ⟨i, Set.Subset.antisymm hsub hsup, ?_⟩
  interval_cases hk : (MulAction.orbit H i).ncard <;> omega

@[expose] def sigma4 : Perm (Fin 7) := swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5

theorem sigma4_pow_four : sigma4 ^ 4 = 1 := by decide

theorem sigma4_sq_ne_one : sigma4 ^ 2 ≠ 1 := by decide

theorem sigma4_mem : sigma4 ∈ alternatingGroup (Fin 7) := by
  rw [Perm.mem_alternatingGroup, sigma4]
  simp [Perm.sign_mul, Perm.sign_swap']

theorem sigma4_pair (a b : Fin 7) (hab : a ≠ b) (ha : sigma4 a = a ∨ sigma4 a = b)
    (hb : sigma4 b = a ∨ sigma4 b = b) : (a = 4 ∧ b = 5) ∨ (a = 5 ∧ b = 4) := by
  revert a b
  decide

theorem exists_conj_sigma4_mem {D : Subgroup (Perm (Fin 7))} (hDA : D ≤ alternatingGroup (Fin 7))
    (hD : Nat.card D = 8) : ∃ g ∈ alternatingGroup (Fin 7), g⁻¹ * sigma4 * g ∈ D := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := alternatingGroup (Fin 7) with hA
  have hcardA : Nat.card A = 2520 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  set D' : Subgroup A := D.subgroupOf A with hD'
  have hD'c : Nat.card D' = 8 := by
    rw [← hD]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDA).toEquiv
  have hD'p : IsPGroup 2 D' := IsPGroup.of_card (n := 3) (by rw [hD'c]; norm_num)
  obtain ⟨Q, hDQ⟩ := hD'p.exists_le_sylow
  have hQ : (Q : Subgroup A) = D' := by
    refine (Subgroup.eq_of_le_of_card_ge hDQ ?_).symm
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp Q.isPGroup'
    have hdvd : 2 ^ k ∣ 2520 := by
      rw [← hk, ← hcardA]
      exact Subgroup.card_subgroup_dvd_card (Q : Subgroup A)
    have hk3 : k ≤ 3 := by
      by_contra hk4
      have h16 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      have := h16.trans hdvd
      norm_num at this
    rw [hk, hD'c]
    calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
      _ = 8 := by norm_num
  set s : A := ⟨sigma4, sigma4_mem⟩ with hs
  have hs4 : s ^ 2 ^ (1 + 1) = 1 := Subtype.ext (by simpa using sigma4_pow_four)
  have hs2 : ¬ s ^ 2 ^ 1 = 1 := fun h =>
    sigma4_sq_ne_one (by simpa using congrArg Subtype.val h)
  have hord : orderOf s = 2 ^ (1 + 1) := orderOf_eq_prime_pow hs2 hs4
  have hZp : IsPGroup 2 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hord])
  obtain ⟨R, hR⟩ := hZp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A Q R
  have hsR : s ∈ (R : Subgroup A) := hR (Subgroup.mem_zpowers s)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hsR
  have h1 : g⁻¹ * s * g ∈ D' := by
    rw [← hQ]
    simpa [MulAut.smul_def, MulAut.conj_apply] using hsR
  refine ⟨(g : Perm (Fin 7)), g.2, ?_⟩
  have h2 := Subgroup.mem_subgroupOf.mp h1
  simpa using h2

end CFSG.Quasithin.C58NS.Emb
