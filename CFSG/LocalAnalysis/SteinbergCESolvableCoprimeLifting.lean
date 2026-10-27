module

public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis

open CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.CoprimeFixedPoint
open scoped commutatorElement

universe u v

theorem exists_normal_prime_index {A : Type u} [Group A] [Finite A] [Group.IsSolvable A]
    [Nontrivial A] : ∃ M : Subgroup A, M.Normal ∧ (Nat.card (A ⧸ M)).Prime := by
  classical
  let := Fintype.ofFinite (Subgroup A)
  have hbot : (⊥ : Subgroup A) ∈ Finset.univ.filter fun M : Subgroup A => M.Normal ∧ M ≠ ⊤ := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Subgroup.normal_bot, bot_ne_top⟩
  obtain ⟨M, hM, hMmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun M : Subgroup A => M.Normal ∧ M ≠ ⊤) (fun M => Nat.card M) ⟨⊥, hbot⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM hMmax
  obtain ⟨hMn, hMtop⟩ := hM
  have : M.Normal := hMn
  have hnt : Nontrivial (A ⧸ M) := QuotientGroup.nontrivial_iff.mpr hMtop
  have hsimple : IsSimpleGroup (A ⧸ M) := by
    refine ⟨fun L hL => ?_⟩
    have hLc : (L.comap (QuotientGroup.mk' M)).Normal := hL.comap _
    have hML : M ≤ L.comap (QuotientGroup.mk' M) := by
      intro m hm
      rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff m).mpr hm]
      exact L.one_mem
    by_cases htop : L.comap (QuotientGroup.mk' M) = ⊤
    · right
      rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective M) L, htop,
        ← MonoidHom.range_eq_map, QuotientGroup.range_mk']
    · left
      have hle : Nat.card M ≤ Nat.card (L.comap (QuotientGroup.mk' M)) :=
        Subgroup.card_le_of_le hML
      have heq : L.comap (QuotientGroup.mk' M) = M :=
        (Subgroup.eq_of_le_of_card_ge hML (hMmax _ ⟨hLc, htop⟩)).symm
      rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective M) L, heq,
        QuotientGroup.map_mk'_self]
  have hcomm : IsMulCommutative (A ⧸ M) := by
    have hc : commutator (A ⧸ M) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (A ⧸ M)) with h | h
      · exact h
      · exact absurd h (Group.IsSolvable.commutator_lt_top_of_nontrivial (A ⧸ M)).ne
    refine ⟨⟨fun a b => ?_⟩⟩
    have h1 : ⁅a, b⁆ ∈ commutator (A ⧸ M) :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  exact ⟨M, hMn, Group.is_simple_iff_prime_card.mp hsimple⟩

@[expose] def fixSub {A : Type u} {G : Type v} [Group A] [Group G] (α : A →* MulAut G)
    (S : Subgroup A) : Subgroup G where
  carrier := {x | ∀ a ∈ S, α a x = x}
  mul_mem' {x y} hx hy a ha := by rw [map_mul, hx a ha, hy a ha]
  one_mem' a _ := map_one _
  inv_mem' {x} hx a ha := by rw [map_inv, hx a ha]

theorem solvable_coprime_fixed_point_lifting {A : Type u} {G : Type v} [Group A] [Group G]
    [Finite A] [Finite G] (hA : Group.IsSolvable A) (α : A →* MulAut G) (N : Subgroup G)
    [N.Normal] (hN : ∀ a : A, ∀ n ∈ N, α a n ∈ N) (hcop : Nat.Coprime (Nat.card A) (Nat.card N)) :
    {q : G ⧸ N | ∀ a : A, quotientAction α N hN a q = q} =
      (QuotientGroup.mk' N) '' {c : G | ∀ a : A, α a c = c} := by
  classical
  refine Set.Subset.antisymm ?_ ?_
  swap
  · rintro _ ⟨c, hc, rfl⟩ a
    change ((α a c : G) : G ⧸ N) = (c : G ⧸ N)
    rw [hc a]
  suffices key : ∀ (n : ℕ) {B : Type u} [Group B] [Finite B], Nat.card B = n →
      Group.IsSolvable B → ∀ β : B →* MulAut G, (∀ b : B, ∀ x ∈ N, β b x ∈ N) →
        Nat.Coprime (Nat.card B) (Nat.card N) → ∀ g : G,
          (∀ b : B, ((β b g : G) : G ⧸ N) = (g : G ⧸ N)) →
            ∃ c : G, (∀ b : B, β b c = c) ∧ (c : G ⧸ N) = g by
    intro q hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨c, hc, hcg⟩ := key _ rfl hA α hN hcop g (fun a => hq a)
    exact ⟨c, hc, hcg⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B _ _ hcard hsolv β hβ hcop' g hg
  by_cases hnt : Nontrivial B
  swap
  · have : Subsingleton B := not_nontrivial_iff_subsingleton.mp hnt
    refine ⟨g, fun b => ?_, rfl⟩
    rw [Subsingleton.elim b 1, map_one, MulAut.one_apply]
  obtain ⟨M, hMn, hMp⟩ := exists_normal_prime_index (A := B)
  set q := Nat.card (B ⧸ M) with hq
  have : Fact q.Prime := ⟨hMp⟩
  have hMlt : Nat.card M < n := by
    rw [← hcard, ← Subgroup.card_mul_index M]
    have h1 : M.index = q := (Subgroup.index_eq_card M).symm
    have h2 := hMp.two_le
    have h3 : 0 < Nat.card M := Nat.card_pos
    nlinarith
  have hMcop : Nat.Coprime (Nat.card M) (Nat.card N) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card M) hcop'
  obtain ⟨g₁, hg₁, hg₁g⟩ := ih (Nat.card M) hMlt rfl inferInstance (β.comp M.subtype)
    (fun b x hx => hβ b x hx) hMcop g (fun b => hg b)
  have hfixinv : ∀ b : B, ∀ x ∈ fixSub β M, β b x ∈ fixSub β M := by
    intro b x hx m hm
    have h1 := hx (b⁻¹ * m * b) (hMn.conj_mem' m hm b)
    calc β m (β b x) = β b (β (b⁻¹ * m * b) x) := by
          rw [← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
          congr 2
          group
      _ = β b x := by rw [h1]
  have hg₁M : g₁ ∈ fixSub β M := fun m hm => hg₁ ⟨m, hm⟩
  set N₁ : Subgroup G := N ⊓ fixSub β M with hN₁
  let Q : Sylow q B := default
  have hQM : (Q : Subgroup B) ⊔ M = ⊤ := by
    let P := Q.mapSurjective (QuotientGroup.mk'_surjective M)
    have hP : (P : Subgroup (B ⧸ M)) = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Sylow.card_eq_multiplicity, ← hq, hMp.factorization_self, pow_one]
    have h1 : (Q : Subgroup B).map (QuotientGroup.mk' M) = ⊤ := hP
    have h2 := congrArg (Subgroup.comap (QuotientGroup.mk' M)) h1
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at h2
  have hgg : ∀ b : B, g₁⁻¹ * β b g₁ ∈ N := by
    intro b
    have h1 : ((β b g₁ : G) : G ⧸ N) = (g₁ : G ⧸ N) := by
      have h2 := hg b
      have h3 : quotientAction β N hβ b (g₁ : G ⧸ N) = quotientAction β N hβ b (g : G ⧸ N) := by
        rw [hg₁g]
      rw [quotientAction_mk, quotientAction_mk] at h3
      rw [h3, h2, hg₁g]
    exact QuotientGroup.eq.mp h1.symm
  have hinv : ∀ a : (Q : Subgroup B), ∀ x : G, g₁⁻¹ * x ∈ N₁ →
      g₁⁻¹ * (β.comp (Q : Subgroup B).subtype) a x ∈ N₁ := by
    intro a x hx
    have h1 : g₁⁻¹ * (β.comp (Q : Subgroup B).subtype) a x =
        (g₁⁻¹ * β a g₁) * β a (g₁⁻¹ * x) := by
      change g₁⁻¹ * β a x = (g₁⁻¹ * β a g₁) * β a (g₁⁻¹ * x)
      rw [map_mul, map_inv]
      group
    rw [h1]
    refine N₁.mul_mem ⟨hgg a, ?_⟩ ⟨hβ a _ hx.1, hfixinv a _ hx.2⟩
    exact (fixSub β M).mul_mem ((fixSub β M).inv_mem hg₁M) (hfixinv a _ hg₁M)
  have hcopq : ¬ q ∣ Nat.card N₁ := by
    intro h
    have hqB : q ∣ Nat.card B := by
      rw [hq, ← Subgroup.index_eq_card]
      exact Subgroup.index_dvd_card M
    have hqN : q ∣ Nat.card N := h.trans (Subgroup.card_dvd_of_le inf_le_left)
    have h3 := Nat.dvd_gcd hqB hqN
    rw [hcop'.gcd_eq_one, Nat.dvd_one] at h3
    exact hMp.one_lt.ne' h3
  obtain ⟨c, hc, hcfix⟩ := (coprime_invariant_coset_fixed q Q.isPGroup'
    (β.comp (Q : Subgroup B).subtype) N₁ hcopq g₁).2 hinv
  refine ⟨c, fun b => ?_, ?_⟩
  ·
    let S : Subgroup B :=
      { carrier := {b | β b c = c}
        one_mem' := by simp
        mul_mem' := fun {a b} ha hb => by
          change β (a * b) c = c
          rw [map_mul, MulAut.mul_apply]
          change β a (β b c) = c
          rw [show β b c = c from hb]
          exact ha
        inv_mem' := fun {a} ha => by
          change β a⁻¹ c = c
          conv_lhs => rw [← show β a c = c from ha]
          rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] }
    have hcM : c ∈ fixSub β M := by
      have h1 := (fixSub β M).mul_mem hg₁M hc.2
      rwa [mul_inv_cancel_left] at h1
    have hQS : (Q : Subgroup B) ≤ S := fun a ha => hcfix ⟨a, ha⟩
    have hMS : M ≤ S := fun m hm => hcM m hm
    have hS : S = ⊤ := by
      rw [eq_top_iff, ← hQM]
      exact sup_le hQS hMS
    have hb : b ∈ S := by rw [hS]; exact Subgroup.mem_top b
    exact hb
  · rw [← hg₁g]
    exact (QuotientGroup.eq.mpr hc.1).symm

end CFSG.LocalAnalysis
