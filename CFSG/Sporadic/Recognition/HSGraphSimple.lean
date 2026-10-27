module

public import CFSG.Sporadic.Recognition.HSGraphGroup
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Sporadic.Recognition.HSGraph

open MulAction

theorem isSimpleGroup_of_stabilizer_simple {G : Type*} [Group G] [Finite G] {V : Type*}
    [MulAction G V] [Finite V] (v : V) (hfaith : ∀ g : G, (∀ w : V, g • w = w) → g = 1)
    (hG : Nat.card G = 44352000) (hV : Nat.card V = 100) (htrans : IsPretransitive G V)
    (hsimple : IsSimpleGroup (stabilizer G v))
    (horb : ∀ T : Set V, v ∈ T → (∀ g ∈ stabilizer G v, ∀ t ∈ T, g • t ∈ T) →
      T.ncard = 1 ∨ T.ncard = 23 ∨ T.ncard = 78 ∨ T.ncard = 100)
    (h11 : ∃ h ∈ stabilizer G v, h ^ 11 = 1 ∧ ∀ w : V, h • w = w → w = v) :
    IsSimpleGroup G := by
  classical
  have hnt : Nontrivial G := by
    refine Finite.one_lt_card_iff_nontrivial.1 ?_
    rw [hG]
    norm_num
  refine ⟨fun N hN => ?_⟩
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  refine Or.inr ?_
  have hmem : ∀ n ∈ N, ∀ g : G, g⁻¹ * n * g ∈ N := fun n hn g => by
    simpa using hN.conj_mem n hn g⁻¹
  have hinv : ∀ g ∈ stabilizer G v, ∀ t ∈ orbit N v, g • t ∈ orbit N v := by
    rintro g hg _ ⟨⟨n, hn⟩, rfl⟩
    refine ⟨⟨g * n * g⁻¹, hN.conj_mem n hn g⟩, ?_⟩
    change (g * n * g⁻¹) • v = g • (n • v)
    rw [mul_smul (g * n) g⁻¹ v, mem_stabilizer_iff.1 (inv_mem hg), mul_smul g n v]
  have hO : (orbit N v).ncard = 1 ∨ (orbit N v).ncard = 100 := by
    have h1 := horb (orbit N v) (mem_orbit_self v : v ∈ orbit N v) hinv
    have hdvd : (orbit N v).ncard ∣ 44352000 := by
      have h2 := ncard_orbit_mul_card_stabilizer N v
      have h3 := Subgroup.card_subgroup_dvd_card N
      rw [hG] at h3
      exact (Dvd.intro _ h2).trans h3
    rcases h1 with h | h | h | h
    · exact Or.inl h
    · rw [h] at hdvd
      norm_num at hdvd
    · rw [h] at hdvd
      norm_num at hdvd
    · exact Or.inr h
  rcases hO with h1 | h100
  ·
    exfalso
    apply hbot
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h1
    have hfix : ∀ n ∈ N, n • v = v := by
      intro n hn
      have h1 : n • v ∈ orbit N v := ⟨⟨n, hn⟩, rfl⟩
      have h2 : v ∈ orbit N v := (mem_orbit_self v : v ∈ orbit N v)
      rw [ha, Set.mem_singleton_iff] at h1 h2
      rw [h1, h2]
    refine eq_bot_iff.2 fun n hn => ?_
    rw [Subgroup.mem_bot]
    refine hfaith n fun w => ?_
    obtain ⟨g, rfl⟩ := htrans.exists_smul_eq v w
    have e : n • g • v = g • ((g⁻¹ * n * g) • v) := by
      rw [← mul_smul, ← mul_smul]
      group
    rw [e, hfix _ (hmem n hn g)]
  · have huniv : orbit N v = Set.univ := by
      refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
      rw [Set.ncard_univ, hV, h100]
    have hK : (N.subgroupOf (stabilizer G v)).Normal := hN.subgroupOf _
    rcases hsimple.eq_bot_or_eq_top_of_normal (N.subgroupOf (stabilizer G v)) with hK | hK
    ·
      exfalso
      have htriv : ∀ n ∈ N, n • v = v → n = 1 := by
        intro n hn hnv
        have : (⟨n, mem_stabilizer_iff.2 hnv⟩ : stabilizer G v) ∈ N.subgroupOf (stabilizer G v) :=
          hn
        rw [hK, Subgroup.mem_bot] at this
        exact congrArg Subtype.val this
      have hNcard : Nat.card N = 100 := by
        have h2 := ncard_orbit_mul_card_stabilizer N v
        have h3 : stabilizer N v = ⊥ := by
          refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
          exact Subtype.ext (htriv x.1 x.2 (mem_stabilizer_iff.1 hx))
        rw [h3, Subgroup.card_bot, mul_one, h100] at h2
        exact h2.symm
      obtain ⟨h, hh, hh11, hfixpt⟩ := h11
      refine false_of_fixed_point_free_aut_hundred hNcard (MulAut.conjNormal h) ?_ ?_
      · rw [← map_pow, hh11, map_one]
      · intro x hx
        have hcomm : h * (x : G) * h⁻¹ = x := by
          have := congrArg Subtype.val hx
          rwa [MulAut.conjNormal_apply] at this
        have hfixv : h • ((x : G) • v) = (x : G) • v := by
          have hc : h * (x : G) = (x : G) * h := mul_inv_eq_iff_eq_mul.1 hcomm
          rw [← mul_smul, hc, mul_smul, mem_stabilizer_iff.1 hh]
        exact Subtype.ext (htriv x x.2 (hfixpt _ hfixv))
    ·
      rw [Subgroup.subgroupOf_eq_top] at hK
      refine eq_top_iff.2 fun g _ => ?_
      have hg : g • v ∈ orbit N v := by
        rw [huniv]
        trivial
      obtain ⟨⟨n, hn⟩, hnv⟩ := hg
      have hnv' : n • v = g • v := hnv
      have hs : n⁻¹ * g ∈ stabilizer G v := by
        rw [mem_stabilizer_iff, mul_smul, ← hnv', ← mul_smul, inv_mul_cancel, one_smul]
      have := N.mul_mem hn (hK hs)
      simpa using this

end CFSG.Sporadic.Recognition.HSGraph
