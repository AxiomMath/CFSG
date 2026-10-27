module

public import CFSG.RankThree.GroupTheory.ClassThreeTorsion
public import CFSG.LocalAnalysis.SectionRank.Ccomm.RankTwo
public import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.CharacterTheory.OddOrderBasics.Solvability

public section

namespace CFSG.RankThree.PGroups

open Subgroup

variable {P : Type*} [Group P] [Finite P] {p : ℕ}

theorem card_le_pow_three_of_pow_eq_one (hp : p.Prime) (hP : IsPGroup p P)
    (hrank : pRank p P ≤ 2) {W : Subgroup P} (hW : ∀ w ∈ W, w ^ p = 1) :
    Nat.card W ≤ p ^ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  refine (SectionRank.Ccomm.rank_two_exponent_prime_order_bound (hP.to_subgroup W)
    (fun w => Subtype.ext (by rw [coe_pow, hW w w.2, coe_one])) ?_).1
  calc Open.pRank p (⊤ : Subgroup W)
      ≤ Open.pRank p (⊤ : Subgroup P) :=
        SectionRank.pRank_top_le_of_injective hp.one_lt W.subtype W.subtype_injective
    _ = pRank p P := (SectionRank.pRank_eq_open_pRank_top p P).symm
    _ ≤ 2 := hrank

theorem rank_two_torsion_mul_closed_aux (hp : p.Prime) (hp3 : 3 < p) (hP : IsPGroup p P)
    (hrank : pRank p P ≤ 2) (n : ℕ) :
    ∀ Q : Subgroup P, Nat.card Q = n →
      ∀ x ∈ Q, ∀ y ∈ Q, x ^ p = 1 → y ^ p = 1 → (x * y) ^ p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Q hQ x hx y hy hxp hyp
  by_cases hxy : y ∈ zpowers x
  · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hxy
    rw [(Commute.self_zpow x k).mul_pow, hxp, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hxp, one_zpow]
  have hx₀ : x ∈ closure {x, y} := subset_closure (Set.mem_insert x _)
  have hy₀ : y ∈ closure {x, y} := subset_closure (Set.mem_insert_of_mem x rfl)
  have hQ₀ : closure {x, y} ≤ Q :=
    (closure_le Q).2 (Set.insert_subset hx (Set.singleton_subset_iff.2 hy))
  by_cases hlt : closure {x, y} < Q
  · exact ih _ (hQ ▸ card_lt_of_lt hlt) _ rfl x hx₀ y hy₀ hxp hyp
  have hQeq : closure {x, y} = Q := (lt_or_eq_of_le hQ₀).resolve_left hlt
  set x' : Q := ⟨x, hx⟩
  have hne : zpowers x' ≠ ⊤ := by
    intro htop
    have hy' : (⟨y, hy⟩ : Q) ∈ zpowers x' := htop ▸ mem_top _
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hy'
    exact hxy (mem_zpowers_iff.mpr ⟨k, by
      have := congrArg Subtype.val hk
      rwa [coe_zpow] at this⟩)
  obtain ⟨M, hM, hxM⟩ := (eq_top_or_exists_le_coatom (zpowers x')).resolve_left hne
  have hMn : M.Normal := (OddOrderBasics.p_group_maximal_index (hP.to_subgroup Q) M hM).1
  set M' : Subgroup P := M.map Q.subtype with hM'
  have hM'card : Nat.card M' < n := by
    rw [hM', card_map_of_injective Q.subtype_injective, ← hQ, ← card_top (G := Q)]
    exact card_lt_of_lt hM.lt_top
  set D : Subgroup P := closure {w : P | w ∈ M' ∧ w ^ p = 1}
  have hD : ∀ z ∈ D, z ^ p = 1 := fun z hz =>
    (closure_torsion_pow_eq_one (ih _ hM'card M' rfl) hz).2
  have hxD : x ∈ D := subset_closure ⟨⟨x', hxM (mem_zpowers x'), rfl⟩, hxp⟩
  have hgM : ∀ g ∈ Q, ∀ w ∈ M', g⁻¹ * w * g ∈ M' := by
    rintro g hg _ ⟨m, hm, rfl⟩
    refine ⟨(⟨g, hg⟩ : Q)⁻¹ * m * ⟨g, hg⟩, ?_, rfl⟩
    simpa using hMn.conj_mem m hm (⟨g, hg⟩ : Q)⁻¹
  have hyN : y ∈ normalizer (D : Set P) := by
    rw [mem_normalizer_iff'']
    intro h
    refine ⟨fun hh => conj_mem_closure_torsion (hgM y hy) hh, fun hh => ?_⟩
    have := conj_mem_closure_torsion (hgM y⁻¹ (Q.inv_mem hy)) hh
    rwa [show y⁻¹⁻¹ * (y⁻¹ * h * y) * y⁻¹ = h by group] at this
  have hycard : Nat.card (zpowers y) ≤ p := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hyp)
  have hQle : Q ≤ D ⊔ zpowers y := hQeq ▸ (closure_le _).2
    (Set.insert_subset (mem_sup_left hxD) (Set.singleton_subset_iff.2 (mem_sup_right
      (mem_zpowers y))))
  have hcardQ : Nat.card Q ≤ p ^ 4 := by
    have h1 := Set.natCard_mul_le (s := (D : Set P)) (t := (zpowers y : Set P))
    rw [← coe_mul_of_right_le_normalizer_left D _ (zpowers_le.2 hyN)] at h1
    calc Nat.card Q ≤ Nat.card (D ⊔ zpowers y : Subgroup P) := card_le_of_le hQle
      _ ≤ Nat.card D * Nat.card (zpowers y) := h1
      _ ≤ p ^ 3 * p :=
        Nat.mul_le_mul (card_le_pow_three_of_pow_eq_one hp hP hrank hD) hycard
      _ = p ^ 4 := by ring
  have hγ := lowerCentralSeries_three_eq_bot_of_card_le_pow_four (hP.to_subgroup Q) hcardQ
  have h := torsion_mul_closed_aux hp hp3 (hP.to_subgroup Q) hγ _ ⊤ rfl x' (mem_top _)
    ⟨y, hy⟩ (mem_top _) (Subtype.ext (by rw [coe_pow]; exact hxp))
    (Subtype.ext (by rw [coe_pow]; exact hyp))
  have h' := congrArg Subtype.val h
  rwa [coe_pow, coe_mul, coe_one] at h'

theorem rank_two_large_prime_torsion_exponent (hp : p.Prime) (hp3 : 3 < p) (hP : IsPGroup p P)
    (hrank : pRank p P ≤ 2) :
    ((omega₁ P (p := p) : Subgroup P) : Set P) = {x : P | x ^ p = 1} ∧
      (∀ x ∈ omega₁ P (p := p), x ^ p = 1) ∧ Nat.card (omega₁ P (p := p)) ≤ p ^ 3 := by
  have hclosed : ∀ x y : P, x ^ p = 1 → y ^ p = 1 → (x * y) ^ p = 1 := fun x y hx hy =>
    rank_two_torsion_mul_closed_aux hp hp3 hP hrank _ ⊤ rfl x (mem_top x) y (mem_top y) hx hy
  let T : Subgroup P :=
    { carrier := {x : P | x ^ p = 1}
      mul_mem' := fun {x y} hx hy => hclosed x y hx hy
      one_mem' := one_pow p
      inv_mem' := fun {x} hx => by
        change x⁻¹ ^ p = 1
        rw [inv_pow, show x ^ p = 1 from hx, inv_one] }
  have hΩ : omega₁ P (p := p) = T := by
    rw [omega₁, omega, pow_one]
    exact closure_eq T
  have hset : ((omega₁ P (p := p) : Subgroup P) : Set P) = {x : P | x ^ p = 1} := by
    rw [hΩ]
    rfl
  have hmem : ∀ x ∈ omega₁ P (p := p), x ^ p = 1 := fun x hx => by
    rw [← SetLike.mem_coe, hset] at hx
    exact hx
  exact ⟨hset, hmem, card_le_pow_three_of_pow_eq_one hp hP hrank hmem⟩

end CFSG.RankThree.PGroups
