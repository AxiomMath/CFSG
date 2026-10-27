module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432CoverIndex
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Invariant

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

theorem three_dvd_index_of_not_pow_dvd {G : Type} [Group G] [Finite G] (C : Subgroup G) {n : ℕ}
    (hG : 3 ^ n ∣ Nat.card G) (hC : ¬ 3 ^ n ∣ Nat.card C) : 3 ∣ C.index := by
  by_contra h3
  have hcop : Nat.Coprime (3 ^ n) C.index :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)
  rw [← Subgroup.card_mul_index C] at hG
  exact hC (hcop.dvd_of_dvd_mul_right hG)

theorem not_three_pow_ten_dvd_of_dvd_of_le {c : ℕ} (hpos : 0 < c) (hd : 4245696 ∣ c)
    (hle : c ≤ 63685439) : ¬ 3 ^ 10 ∣ c := by
  obtain ⟨k, rfl⟩ := hd
  have hk : k < 15 := by omega
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; omega)
  intro h
  norm_num at h
  interval_cases k <;> omega

theorem exists_commuting_pair_of_elemAbelian_nine {G : Type} [Group G] [Finite G] {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hcard : Nat.card E = 9) :
    ∃ x ∈ E, ∃ y ∈ E, x * y = y * x ∧ y ∉ Subgroup.zpowers x ∧ x ≠ 1 := by
  obtain ⟨hcomm, hexp⟩ := hE
  have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard]; norm_num)
  obtain ⟨x0, hx0⟩ := exists_ne (1 : E)
  have hxE : (x0 : G) ∈ E := x0.2
  have hx1 : (x0 : G) ≠ 1 := fun h => hx0 (Subtype.ext h)
  have hx : orderOf (x0 : G) = 3 := orderOf_eq_prime (hexp _ hxE) hx1
  obtain ⟨y, hyE, hyn⟩ : ∃ y ∈ E, y ∉ Subgroup.zpowers (x0 : G) := by
    by_contra hno
    push_neg at hno
    have hle : E ≤ Subgroup.zpowers (x0 : G) := fun y hy => hno y hy
    have hcard' := Subgroup.card_le_of_le hle
    rw [hcard, Nat.card_zpowers, hx] at hcard'
    norm_num at hcard'
  have hc : (x0 : G) * y = y * (x0 : G) :=
    congrArg Subtype.val (hcomm.is_comm.comm (⟨(x0 : G), hxE⟩ : E) ⟨y, hyE⟩)
  exact ⟨x0, hxE, y, hyE, hc, hyn, hx1⟩

theorem witness_of_conj_pair {G : Type} [Group G] {z x y : G} (hz3 : z ^ 3 = 1)
    (hx : IsConj x z ∨ IsConj x (z ^ 2)) (hy : IsConj y z ∨ IsConj y (z ^ 2))
    (hc : x * y = y * x) (hn : y ∉ Subgroup.zpowers x) :
    ∃ g : G, (g * z * g⁻¹) * z = z * (g * z * g⁻¹) ∧ g * z * g⁻¹ ∉ Subgroup.zpowers z := by
  have hsq : z ^ 2 = z⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hz3)
  obtain ⟨k, hk⟩ : ∃ k : G, k * x * k⁻¹ = z ∨ k * x * k⁻¹ = z⁻¹ := by
    rcases hx with h | h
    · obtain ⟨k, hk⟩ := isConj_iff.mp h
      exact ⟨k, Or.inl hk⟩
    · obtain ⟨k, hk⟩ := isConj_iff.mp h
      exact ⟨k, Or.inr (hk.trans hsq)⟩
  obtain ⟨hc', hn'⟩ := commute_notMem_of_conj k hc hn hk
  obtain ⟨m, hm⟩ : ∃ m : G, m * y * m⁻¹ = z ∨ m * y * m⁻¹ = z⁻¹ := by
    rcases hy with h | h
    · obtain ⟨m, hm⟩ := isConj_iff.mp h
      exact ⟨m, Or.inl hm⟩
    · obtain ⟨m, hm⟩ := isConj_iff.mp h
      exact ⟨m, Or.inr (hm.trans hsq)⟩
  refine ⟨k * m⁻¹, ?_⟩
  rcases hm with hm | hm
  · have he : k * m⁻¹ * z * (k * m⁻¹)⁻¹ = k * y * k⁻¹ := by
      rw [← hm]
      group
    rw [he]
    exact ⟨hc', hn'⟩
  · have he : k * m⁻¹ * z * (k * m⁻¹)⁻¹ = (k * y * k⁻¹)⁻¹ := by
      have hz : z = (m * y * m⁻¹)⁻¹ := by rw [hm, inv_inv]
      rw [hz]
      group
    rw [he]
    refine ⟨Commute.inv_left (show Commute (k * y * k⁻¹) z from hc'), fun hmem => hn' ?_⟩
    simpa using inv_mem hmem

theorem witness_of_elemAbelian_nine {G : Type} [Group G] [Finite G] {z : G} (hz3 : z ^ 3 = 1)
    {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 3 E) (hcard : Nat.card E = 9)
    (hcl : ∀ x ∈ E, x ≠ 1 → IsConj x z ∨ IsConj x (z ^ 2)) :
    ∃ g : G, (g * z * g⁻¹) * z = z * (g * z * g⁻¹) ∧ g * z * g⁻¹ ∉ Subgroup.zpowers z := by
  obtain ⟨x, hxE, y, hyE, hc, hyn, hx1⟩ := exists_commuting_pair_of_elemAbelian_nine hE hcard
  have hy1 : y ≠ 1 := fun h => hyn (h ▸ one_mem _)
  exact witness_of_conj_pair hz3 (hcl x hxE hx1) (hcl y hyE hy1) hc hyn

theorem listRow_of_three_classes {S : Type} [Group S] [Finite S] {a b c : S}
    (hcov : ∀ s : S, orderOf s = 3 → ∃ k d : S, (d = a ∨ d = b ∨ d = c) ∧ ∃ e : ℕ,
      (e = 1 ∨ e = 2) ∧ k * d ^ e * k⁻¹ = s)
    (hoa : orderOf a = 3) (hob : orderOf b = 3) (hoc : orderOf c = 3)
    (hia : 3 ∣ (Subgroup.centralizer ({a} : Set S)).index)
    (hw : ∃ g : S, (g * b * g⁻¹) * b = b * (g * b * g⁻¹) ∧ g * b * g⁻¹ ∉ Subgroup.zpowers b)
    (hic : 3 ∣ (Subgroup.centralizer ({c} : Set S)).index) : ListRow S := by
  refine listRow_of_cover_or_index ({a, b, c} : Set S) ?_ ?_ ?_
  · intro d hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with rfl | rfl | rfl <;> assumption
  · intro s hs
    obtain ⟨k, d, hd, e, he, hke⟩ := hcov s hs
    refine ⟨k, d, ?_, e, he, hke⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact hd
  · intro d hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with rfl | rfl | rfl
    · exact Or.inl hia
    · exact Or.inr hw
    · exact Or.inl hic

end CFSG.RankThree.PartTwo.Sec4.RonanK432
