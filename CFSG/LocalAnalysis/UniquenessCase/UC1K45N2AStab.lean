module

public import CFSG.Quasithin.Recognition.Kleidman.F204.W2FFU1
public import Mathlib.Algebra.Module.Equiv.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup
open scoped BigOperators

abbrev Alt5 : Type := ↥(alternatingGroup (Fin 5))

def stab {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W)) (w : W) : Subgroup Alt5 where
  carrier := {g | ρ g w = w}
  mul_mem' := by
    intro a b ha hb
    show ρ (a * b) w = w
    rw [map_mul, LinearEquiv.mul_apply, hb, ha]
  one_mem' := by
    show ρ 1 w = w
    simp
  inv_mem' := by
    intro a ha
    have h : ρ a⁻¹ w = ρ a⁻¹ (ρ a w) := by rw [ha]
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one] at h
    simpa using h

@[simp]
lemma mem_stab {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W)) (w : W) (g : Alt5) :
    g ∈ stab ρ w ↔ ρ g w = w := Iff.rfl

lemma card_stab {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W)) (w : W) :
    Nat.card (stab ρ w) = Nat.card {g : Alt5 // ρ g w = w} :=
  Nat.card_congr (Equiv.subtypeEquivRight (fun g => Iff.rfl))

def orderThreeStabEquiv {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W)) (w : W) :
    {g : Alt5 // orderOf g = 3 ∧ ρ g w = w} ≃ {g : stab ρ w // orderOf g = 3} where
  toFun g := ⟨⟨g.1, g.2.2⟩, by
    rw [← Subgroup.orderOf_coe]
    exact g.2.1⟩
  invFun g := ⟨g.1.1, ⟨by rw [Subgroup.orderOf_coe, g.2], g.1.2⟩⟩
  left_inv g := Subtype.ext rfl
  right_inv g := Subtype.ext rfl

lemma card_order_three_fixing_eq_stab {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W)) (w : W) :
    Nat.card {g : Alt5 // orderOf g = 3 ∧ ρ g w = w} =
    Nat.card {g : stab ρ w // orderOf g = 3} :=
  Nat.card_congr (orderThreeStabEquiv ρ w)

lemma card_alt5 : Nat.card Alt5 = 60 := by
  change Nat.card (alternatingGroup (Fin 5)) = 60
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num [Nat.factorial]

noncomputable def orderThreeSet : Finset Alt5 :=
  Finset.univ.filter (fun g => orderOf g = 3)

lemma card_orderThreeSet : orderThreeSet.card = 20 := by
  unfold orderThreeSet
  have h : (Finset.univ.filter fun g : Alt5 => orderOf g = 3) =
      (Finset.univ.filter fun g : Alt5 => g ^ 3 = 1 ∧ g ≠ 1) := by
    apply Finset.filter_congr
    intro g _
    exact orderOf_eq_prime_iff
  rw [h]
  decide +kernel

lemma card_nonzero_fixed {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Fintype W]
    [DecidableEq W] (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W)) (g : Alt5)
    (h4 : Nat.card {w : W // ρ g w = w} = 4) :
    ((Finset.univ.filter fun w : W => w ≠ 0).filter fun w => ρ g w = w).card = 3 := by
  classical
  rw [Finset.filter_filter]
  have hfix : (Finset.univ.filter fun w : W => ρ g w = w).card = 4 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact h4
  have hzero : (0 : W) ∈ Finset.univ.filter (fun w : W => ρ g w = w) := by
    simp
  have hEq : (Finset.univ.filter fun w : W => w ≠ 0 ∧ ρ g w = w) =
      (Finset.univ.filter fun w : W => ρ g w = w).filter (fun w => w ≠ 0) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [hEq, Finset.filter_ne', Finset.card_erase_of_mem hzero, hfix]

lemma card_le_twelve_of_ne_top (S : Subgroup Alt5) (hS : S ≠ ⊤) :
    Nat.card S ≤ 12 := by
  have hindex : 5 ≤ S.index :=
    CFSG.Quasithin.Kleidman.F204.alt5_index_ge_five_of_ne_top S hS
  have hmul : Nat.card S * S.index = 60 := by
    rw [Subgroup.card_mul_index, card_alt5]
  have h5 : Nat.card S * 5 ≤ Nat.card S * S.index := Nat.mul_le_mul_left _ hindex
  rw [hmul] at h5
  omega

lemma card_dvd_sixty (S : Subgroup Alt5) : Nat.card S ∣ 60 :=
  ⟨S.index, by rw [Subgroup.card_mul_index, card_alt5]⟩

lemma inf_eq_bot_of_card_three_ne {G : Type} [Group G] [Finite G] {H K : Subgroup G}
    (hH : Nat.card H = 3) (hK : Nat.card K = 3) (hne : H ≠ K) : H ⊓ K = ⊥ := by
  classical
  by_contra hbot
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have hyH : (y : G) ∈ H := (Subgroup.mem_inf.mp y.2).1
  have hyK : (y : G) ∈ K := (Subgroup.mem_inf.mp y.2).2
  have hyne : (y : G) ≠ 1 := by
    intro h
    exact hy1 (Subtype.ext h)
  have hdvdH : orderOf (y : G) ∣ 3 := by
    have h := Subgroup.orderOf_dvd_natCard H hyH
    rwa [hH] at h
  have ho3 : orderOf (y : G) = 3 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hdvdH with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hyne
    · exact h3
  have hzH : Subgroup.zpowers (y : G) = H := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyH) ?_
    rw [hH, Nat.card_zpowers, ho3]
  have hzK : Subgroup.zpowers (y : G) = K := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyK) ?_
    rw [hK, Nat.card_zpowers, ho3]
  exact hne (hzH.symm.trans hzK)

lemma eq_twelve_of_dvd_sixty_of_three_dvd {n : ℕ} (h9 : 9 ≤ n) (hle : n ≤ 12)
    (hdiv : n ∣ 60) (h3 : 3 ∣ n) : n = 12 := by
  interval_cases n
  · norm_num at hdiv
  · norm_num at h3
  · norm_num at h3
  · rfl

lemma order_three_mem_zpowers_of_card_ne_twelve (S : Subgroup Alt5) (hS : S ≠ ⊤)
    (h12 : Nat.card S ≠ 12) {g : S} (hg : orderOf g = 3) {x : S} (hx : orderOf x = 3) :
    x ∈ Subgroup.zpowers g := by
  classical
  by_contra hxH
  let H : Subgroup S := Subgroup.zpowers g
  let K : Subgroup S := Subgroup.zpowers x
  have hHcard : Nat.card H = 3 := by
    change Nat.card (Subgroup.zpowers g) = 3
    rw [Nat.card_zpowers, hg]
  have hKcard : Nat.card K = 3 := by
    change Nat.card (Subgroup.zpowers x) = 3
    rw [Nat.card_zpowers, hx]
  have hne : H ≠ K := by
    intro heq
    have hxK : x ∈ K := by
      change x ∈ Subgroup.zpowers x
      exact Subgroup.mem_zpowers x
    rw [← heq] at hxK
    exact hxH hxK
  have hinf : H ⊓ K = ⊥ := inf_eq_bot_of_card_three_ne hHcard hKcard hne
  have h9 : 9 ≤ Nat.card S := by
    have hdisj : Disjoint H K := disjoint_iff.mpr hinf
    have hle' := Nat.card_le_card_of_injective
      (fun p : H × K => (p.1 : S) * (p.2 : S))
      (Subgroup.mul_injective_of_disjoint hdisj)
    rw [Nat.card_prod, hHcard, hKcard] at hle'
    simpa using hle'
  have h3dvd : 3 ∣ Nat.card S := by
    have h := Subgroup.orderOf_dvd_natCard S (x := (g : Alt5)) g.2
    rwa [Subgroup.orderOf_coe, hg] at h
  have h12' : Nat.card S = 12 :=
    eq_twelve_of_dvd_sixty_of_three_dvd h9 (card_le_twelve_of_ne_top S hS)
      (card_dvd_sixty S) h3dvd
  exact h12 h12'

theorem card_order_three_le_two_of_ne_top_of_card_ne_twelve
    (S : Subgroup Alt5) (hS : S ≠ ⊤) (h12 : Nat.card S ≠ 12) :
    Nat.card {g : S // orderOf g = 3} ≤ 2 := by
  classical
  by_contra hle
  push Not at hle
  have hpos : 0 < Nat.card {g : S // orderOf g = 3} := by omega
  obtain ⟨⟨g, hg⟩, _⟩ := Nat.card_pos_iff.mp hpos
  let H : Subgroup S := Subgroup.zpowers g
  have hHcard : Nat.card H = 3 := by
    change Nat.card (Subgroup.zpowers g) = 3
    rw [Nat.card_zpowers, hg]
  have hmem : ∀ x : S, orderOf x = 3 → x ∈ H := by
    intro x hx
    exact order_three_mem_zpowers_of_card_ne_twelve S hS h12 hg hx
  have hcard_le : Nat.card {x : S // orderOf x = 3} ≤
      Nat.card {y : H // y ≠ 1} := by
    refine Nat.card_le_card_of_injective
      (fun x : {x : S // orderOf x = 3} =>
        (⟨⟨(x : S), hmem x x.2⟩, ?_⟩ : {y : H // y ≠ 1})) ?_
    · intro h
      have hx1 : (x : S) ≠ 1 := by
        intro h1
        have h1' : orderOf (x : S) = 1 := by rw [h1, orderOf_one]
        omega
      exact hx1 (congrArg (fun z : H => (z : S)) h)
    · intro x y hxy
      exact Subtype.ext (congrArg (fun z : {y : H // y ≠ 1} => ((z : H) : S)) hxy)
  have hH2 : Nat.card {y : H // y ≠ 1} = 2 := by
    have h1 : Nat.card {y : H // y ≠ 1} =
        (Finset.univ.filter fun y : H => y ≠ 1).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [h1, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ (1 : H)),
      Finset.card_univ, ← Nat.card_eq_fintype_card, hHcard]
  omega

lemma card_nonzero_vectors {W : Type} [Zero W] [Fintype W] [DecidableEq W]
    (hW : Fintype.card W = 16) :
    (Finset.univ.filter fun w : W => w ≠ 0).card = 15 := by
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ (0 : W)),
    Finset.card_univ, hW]

lemma sum_fixed_nonzero_vectors {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Fintype W] [DecidableEq W] (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W))
    (h4 : ∀ g : Alt5, orderOf g = 3 → Nat.card {w : W // ρ g w = w} = 4) :
    ∑ g ∈ orderThreeSet,
      ((Finset.univ.filter fun w : W => w ≠ 0).filter fun w => ρ g w = w).card = 60 := by
  classical
  have hinner : ∀ g ∈ orderThreeSet,
      ((Finset.univ.filter fun w : W => w ≠ 0).filter fun w => ρ g w = w).card = 3 := by
    intro g hg
    exact card_nonzero_fixed ρ g (h4 g (by simpa [orderThreeSet] using hg))
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, card_orderThreeSet]
  norm_num

lemma sum_fixed_pairs_eq {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Fintype W] [DecidableEq W] (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W)) :
    ∑ g ∈ orderThreeSet,
        ((Finset.univ.filter fun w : W => w ≠ 0).filter fun w => ρ g w = w).card =
      ∑ w ∈ Finset.univ.filter (fun w : W => w ≠ 0),
        (orderThreeSet.filter fun g => ρ g w = w).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]

lemma sum_stabilizers_le_thirty {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Fintype W] [DecidableEq W] (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W))
    (h0 : ∀ w : W, (∀ g, ρ g w = w) → w = 0)
    (hW : Fintype.card W = 16)
    (hno : ∀ w : W, w ≠ 0 → Nat.card {g : Alt5 // ρ g w = w} ≠ 12) :
    ∑ w ∈ Finset.univ.filter (fun w : W => w ≠ 0),
      (orderThreeSet.filter fun g => ρ g w = w).card ≤ 30 := by
  classical
  have hbound : ∀ w ∈ Finset.univ.filter (fun w : W => w ≠ 0),
      (orderThreeSet.filter fun g => ρ g w = w).card ≤ 2 := by
    intro w hw
    have hw0 : w ≠ 0 := (Finset.mem_filter.mp hw).2
    have hS : stab ρ w ≠ ⊤ := by
      intro htop
      apply hw0
      apply h0 w
      intro g
      have hg : g ∈ stab ρ w := by
        rw [htop]
        simp
      exact (mem_stab ρ w g).mp hg
    have h12 : Nat.card (stab ρ w) ≠ 12 := by
      intro h
      exact hno w hw0 (by rw [← card_stab ρ w]; exact h)
    have hcount : (orderThreeSet.filter fun g => ρ g w = w).card =
        Nat.card {g : stab ρ w // orderOf g = 3} := by
      unfold orderThreeSet
      rw [Finset.filter_filter]
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
        card_order_three_fixing_eq_stab ρ w]
    rw [hcount]
    exact card_order_three_le_two_of_ne_top_of_card_ne_twelve (stab ρ w) hS h12
  calc
    ∑ w ∈ Finset.univ.filter (fun w : W => w ≠ 0),
        (orderThreeSet.filter fun g => ρ g w = w).card
        ≤ ∑ w ∈ Finset.univ.filter (fun w : W => w ≠ 0), 2 :=
          Finset.sum_le_sum hbound
    _ = 30 := by
      rw [Finset.sum_const, card_nonzero_vectors hW]
      norm_num

theorem a5_exists_vector_stab_twelve (W : Type) [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W]
    (ρ : ↥(alternatingGroup (Fin 5)) →* (W ≃ₗ[ZMod 2] W)) (hW : Nat.card W = 16)
    (h0 : ∀ w : W, (∀ g, ρ g w = w) → w = 0)
    (hd : ∀ g : ↥(alternatingGroup (Fin 5)), orderOf g = 3 →
      Nat.card {w : W // ρ g w = w} = 4) :
    ∃ w : W, w ≠ 0 ∧ Nat.card {g : ↥(alternatingGroup (Fin 5)) // ρ g w = w} = 12 := by
  classical
  letI : Fintype W := Fintype.ofFinite W
  by_contra hcon
  push Not at hcon
  have hW16 : Fintype.card W = 16 := by
    rw [← Nat.card_eq_fintype_card]
    exact hW
  have hLHS := sum_fixed_nonzero_vectors ρ hd
  have hdbl := sum_fixed_pairs_eq ρ
  have hRHS := sum_stabilizers_le_thirty ρ h0 hW16 hcon
  rw [← hdbl, hLHS] at hRHS
  norm_num at hRHS

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

end
