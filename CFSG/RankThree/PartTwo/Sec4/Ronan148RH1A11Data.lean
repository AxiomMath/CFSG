module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1A11Gen
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1A8

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.Ronan148S
open Equiv Equiv.Perm

abbrev A11 : Type := alternatingGroup (Fin 11)

@[expose] def a11c1 : A11 := ⟨swap 0 1 * swap 1 2, by rw [mem_alternatingGroup]; decide⟩
@[expose] def a11c2 : A11 := ⟨swap 3 4 * swap 4 5, by rw [mem_alternatingGroup]; decide⟩
@[expose] def a11c3 : A11 := ⟨swap 6 7 * swap 7 8, by rw [mem_alternatingGroup]; decide⟩
@[expose] def a11z : A11 :=
  ⟨swap 0 3 * swap 3 6 * swap 1 4 * swap 4 7 * swap 2 5 * swap 5 8,
    by rw [mem_alternatingGroup]; decide⟩
@[expose] def a11t : A11 := ⟨swap 6 7 * swap 9 10, by rw [mem_alternatingGroup]; decide⟩
@[expose] def a11s12 : A11 :=
  ⟨swap 0 3 * swap 1 4 * swap 2 5 * swap 9 10, by rw [mem_alternatingGroup]; decide⟩
@[expose] def a11s13 : A11 :=
  ⟨swap 0 6 * swap 1 7 * swap 2 8 * swap 9 10, by rw [mem_alternatingGroup]; decide⟩
@[expose] def a11i1 : A11 := ⟨swap 0 1 * swap 9 10, by rw [mem_alternatingGroup]; decide⟩

@[expose] def a11F : Subgroup A11 := Subgroup.zpowers a11c1 ⊔ Subgroup.zpowers a11c2
@[expose] def a11A0 : Subgroup A11 := a11F ⊔ Subgroup.zpowers a11c3

theorem a11_facts : a11c1 ^ 3 = 1 ∧ a11c2 ^ 3 = 1 ∧ a11c3 ^ 3 = 1 ∧ a11c1 * a11c2 = a11c2 * a11c1 ∧
    a11c1 * a11c3 = a11c3 * a11c1 ∧ a11c2 * a11c3 = a11c3 * a11c2 ∧ a11c1 ≠ 1 ∧ a11c2 ≠ 1 ∧
    a11c2 ≠ a11c1 ∧ a11c2 ≠ a11c1⁻¹ ∧ a11z ^ 3 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem exists_pow_of_mem_zpowers {c w : A11} (hc3 : c ^ 3 = 1) (hw : w ∈ Subgroup.zpowers c) :
    ∃ k : ℕ, k < 3 ∧ w = c ^ k := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  refine ⟨(k % 3).toNat, by omega, ?_⟩
  have h1 : c ^ k = c ^ (k % 3) := zpow_eq_zpow_emod' k hc3
  rw [h1, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))]

theorem mem_sup_zpowers {H : Subgroup A11} {c x : A11} (hc3 : c ^ 3 = 1)
    (hcomm : ∀ h ∈ H, h * c = c * h) (hx : x ∈ H ⊔ Subgroup.zpowers c) :
    ∃ h ∈ H, ∃ k : ℕ, k < 3 ∧ x = h * c ^ k := by
  have hc : ∀ u ∈ H, ∀ v ∈ Subgroup.zpowers c, u * v = v * u := by
    intro u hu v hv
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact ((Commute.zpow_right (show Commute u c from hcomm u hu) j)).eq
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc).2
  have hx' : x ∈ ((H ⊔ Subgroup.zpowers c : Subgroup _) : Set _) := hx
  rw [hset] at hx'
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨k, hk, rfl⟩ := exists_pow_of_mem_zpowers hc3 hv
  exact ⟨u, hu, k, hk, rfl⟩

theorem mem_a11F {x : A11} (hx : x ∈ a11F) :
    ∃ i j : ℕ, i < 3 ∧ j < 3 ∧ x = a11c1 ^ i * a11c2 ^ j := by
  obtain ⟨h1, h2, -, h12, -, -, -, -, -, -, -⟩ := a11_facts
  obtain ⟨h, hh, j, hj, rfl⟩ := mem_sup_zpowers h2 (fun h hh => by
    obtain ⟨i, -, rfl⟩ := exists_pow_of_mem_zpowers h1 hh
    exact ((Commute.pow_left (show Commute a11c1 a11c2 from h12) i)).eq) hx
  obtain ⟨i, hi, rfl⟩ := exists_pow_of_mem_zpowers h1 hh
  exact ⟨i, j, hi, hj, rfl⟩

theorem mem_a11A0 {x : A11} (hx : x ∈ a11A0) :
    ∃ i j k : ℕ, i < 3 ∧ j < 3 ∧ k < 3 ∧ x = a11c1 ^ i * a11c2 ^ j * a11c3 ^ k := by
  obtain ⟨-, -, h3, -, h13, h23, -, -, -, -, -⟩ := a11_facts
  obtain ⟨h, hh, k, hk, rfl⟩ := mem_sup_zpowers h3 (fun h hh => by
    obtain ⟨i, j, -, -, rfl⟩ := mem_a11F hh
    rw [mul_assoc, ((Commute.pow_left (show Commute a11c2 a11c3 from h23) j)).eq, ← mul_assoc,
      ((Commute.pow_left (show Commute a11c1 a11c3 from h13) i)).eq, mul_assoc]) hx
  obtain ⟨i, j, hi, hj, rfl⟩ := mem_a11F hh
  exact ⟨i, j, k, hi, hj, hk, rfl⟩

theorem a11F_e9 : CFSG.Assembly.IsElemAbelian 3 a11F ∧ Nat.card a11F = 9 := by
  obtain ⟨h1, h2, -, h12, -, -, h11, h21, h2a, h2ai, -⟩ := a11_facts
  exact e9_of_commute h1 h11 h2 h12 (not_mem_zpowers_of_ne h1 h21 h2a h2ai)

theorem a11A0_e27 : CFSG.Assembly.IsElemAbelian 3 a11A0 ∧ Nat.card a11A0 = 27 := by
  obtain ⟨-, -, h3, -, h13, h23, -, -, -, -, -⟩ := a11_facts
  have hc : ∀ x ∈ a11F, ∀ y ∈ Subgroup.zpowers a11c3, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, j, -, -, rfl⟩ := mem_a11F hx
    obtain ⟨k, -, rfl⟩ := exists_pow_of_mem_zpowers h3 hy
    rw [mul_assoc, ((Commute.pow_pow (show Commute a11c2 a11c3 from h23) j k)).eq, ← mul_assoc,
      ((Commute.pow_pow (show Commute a11c1 a11c3 from h13) i k)).eq, mul_assoc]
  have hinf : a11F ⊓ Subgroup.zpowers a11c3 = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxF, hx3⟩
    obtain ⟨i, j, hi, hj, rfl⟩ := mem_a11F hxF
    obtain ⟨k, hk, hk'⟩ := exists_pow_of_mem_zpowers h3 hx3
    rw [Subgroup.mem_bot]
    revert hk'
    interval_cases i <;> interval_cases j <;> interval_cases k <;> decide
  refine ⟨CFSG.RankThree.PartTwo.Sec13.isElemAbelian_sup a11F_e9.1
    (CFSG.RankThree.PartTwo.Sec13.isElemAbelian_zpowers h3) hc, ?_⟩
  rw [a11A0, card_sup_of_commute_of_inf hc hinf, a11F_e9.2, Nat.card_zpowers,
    orderOf_eq_prime h3 (by decide)]

theorem a11_movers_mem : a11s12 ∈ Subgroup.normalizer (a11A0 : Set A11) ∧
    a11s13 ∈ Subgroup.normalizer (a11A0 : Set A11) ∧
    a11i1 ∈ Subgroup.normalizer (a11A0 : Set A11) := by
  have hgen : ∀ n : A11, n * a11c1 * n⁻¹ ∈ a11A0 → n * a11c2 * n⁻¹ ∈ a11A0 →
      n * a11c3 * n⁻¹ ∈ a11A0 → n ∈ Subgroup.normalizer (a11A0 : Set A11) := by
    intro n h1 h2 h3
    refine mem_normalizer_of_map_le ?_
    rw [a11A0, a11F, Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers,
      MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Subgroup.zpowers_le]
    · exact h1
    · exact h2
    · exact h3
  have m1 : a11c1 ∈ a11A0 := Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  have m2 : a11c2 ∈ a11A0 :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have m3 : a11c3 ∈ a11A0 := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have e1 : a11s12 * a11c1 * a11s12⁻¹ = a11c2 ∧ a11s12 * a11c2 * a11s12⁻¹ = a11c1 ∧
      a11s12 * a11c3 * a11s12⁻¹ = a11c3 ∧ a11s13 * a11c1 * a11s13⁻¹ = a11c3 ∧
      a11s13 * a11c2 * a11s13⁻¹ = a11c2 ∧ a11s13 * a11c3 * a11s13⁻¹ = a11c1 ∧
      a11i1 * a11c1 * a11i1⁻¹ = a11c1 ^ 2 ∧ a11i1 * a11c2 * a11i1⁻¹ = a11c2 ∧
      a11i1 * a11c3 * a11i1⁻¹ = a11c3 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
  obtain ⟨e11, e12, e13, e21, e22, e23, e31, e32, e33⟩ := e1
  refine ⟨hgen _ ?_ ?_ ?_, hgen _ ?_ ?_ ?_, hgen _ ?_ ?_ ?_⟩
  · rw [e11]; exact m2
  · rw [e12]; exact m1
  · rw [e13]; exact m3
  · rw [e21]; exact m3
  · rw [e22]; exact m2
  · rw [e23]; exact m1
  · rw [e31]; exact Subgroup.pow_mem _ m1 2
  · rw [e32]; exact m2
  · rw [e33]; exact m3

theorem a11_move (s : A11) (hs : s ∈ a11A0) (hs1 : s ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (a11A0 : Set A11),
      n ∉ Subgroup.normalizer ((Subgroup.zpowers s : Subgroup A11) : Set A11) := by
  obtain ⟨i, j, k, hi, hj, hk, rfl⟩ := mem_a11A0 hs
  have key : ∀ n : A11, ∀ t : A11, t ^ 3 = 1 →
      n * t * n⁻¹ ≠ 1 → n * t * n⁻¹ ≠ t → n * t * n⁻¹ ≠ t⁻¹ →
      n ∉ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup A11) : Set A11) :=
    fun n t ht h1 h2 h3 => not_mem_normalizer_of_conj (not_mem_zpowers_of_ne ht h1 h2 h3)
  interval_cases i <;> interval_cases j <;> interval_cases k
  · exact absurd (by decide) hs1
  · exact ⟨a11s13, a11_movers_mem.2.1, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a11s13, a11_movers_mem.2.1, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a11s12, a11_movers_mem.1, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a11s12, a11_movers_mem.1, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a11s12, a11_movers_mem.1, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a11s12, a11_movers_mem.1, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a11s12, a11_movers_mem.1, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a11s12, a11_movers_mem.1, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a11s12, a11_movers_mem.1, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a11s12, a11_movers_mem.1, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a11s12, a11_movers_mem.1, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a11s13, a11_movers_mem.2.1, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a11i1, a11_movers_mem.2.2, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a11i1, a11_movers_mem.2.2, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a11s13, a11_movers_mem.2.1, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a11i1, a11_movers_mem.2.2, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a11i1, a11_movers_mem.2.2, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a11s12, a11_movers_mem.1, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a11s12, a11_movers_mem.1, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a11s12, a11_movers_mem.1, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a11s13, a11_movers_mem.2.1, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a11i1, a11_movers_mem.2.2, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a11i1, a11_movers_mem.2.2, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a11s13, a11_movers_mem.2.1, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a11i1, a11_movers_mem.2.2, key _ _ (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨a11i1, a11_movers_mem.2.2, key _ _ (by decide) (by decide) (by decide) (by decide)⟩

theorem a11z_conj : a11z * a11c1 * a11z⁻¹ = a11c2 ∧ a11z * a11c2 * a11z⁻¹ = a11c3 ∧
    a11z * a11c3 * a11z⁻¹ = a11c1 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem a11z_mem_normalizer : a11z ∈ Subgroup.normalizer (a11A0 : Set A11) := by
  obtain ⟨e1, e2, e3⟩ := a11z_conj
  refine mem_normalizer_of_map_le ?_
  rw [a11A0, a11F, Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers,
    MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Subgroup.zpowers_le]
  · show a11z * a11c1 * a11z⁻¹ ∈ _
    rw [e1]; exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  · show a11z * a11c2 * a11z⁻¹ ∈ _
    rw [e2]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  · show a11z * a11c3 * a11z⁻¹ ∈ _
    rw [e3]; exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))

theorem a11z_pow_not_mem {l : ℕ} (hl1 : 1 ≤ l) (hl2 : l < 3) : a11z ^ l ∉ a11A0 := by
  intro h
  obtain ⟨i, j, k, hi, hj, hk, hx⟩ := mem_a11A0 h
  revert hx
  interval_cases l <;> interval_cases i <;> interval_cases j <;> interval_cases k <;> decide

@[expose] def a11P0 : Subgroup A11 := a11A0 ⊔ Subgroup.zpowers a11z

theorem a11P0_spec : Nat.card a11P0 = 81 ∧
    ∀ x ∈ a11P0, ∃ l : ℕ, l < 3 ∧ ∃ a ∈ a11A0, x = a11z ^ l * a := by
  set N : Subgroup A11 := Subgroup.normalizer (a11A0 : Set A11) with hN
  have hAN : a11A0 ≤ N := Subgroup.le_normalizer
  set A' : Subgroup N := a11A0.subgroupOf N with hA'
  haveI : A'.Normal := Subgroup.normal_in_normalizer
  set z' : N := ⟨a11z, a11z_mem_normalizer⟩ with hz'
  have hz3 : z' ^ 3 = 1 := Subtype.ext (by simpa [hz'] using a11_facts.2.2.2.2.2.2.2.2.2.2)
  have hset := Subgroup.mul_normal (Subgroup.zpowers z') A'
  have hmk1 : QuotientGroup.mk' A' z' ≠ 1 := by
    rw [Ne, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    intro h
    exact a11z_pow_not_mem (l := 1) le_rfl (by norm_num)
      (by rw [pow_one]; exact Subgroup.mem_subgroupOf.mp h)
  have hmk3 : (QuotientGroup.mk' A' z') ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
  have himg : (QuotientGroup.mk : N → N ⧸ A') '' (Subgroup.zpowers z' : Set N) =
      ((Subgroup.zpowers (QuotientGroup.mk' A' z') : Subgroup (N ⧸ A')) : Set (N ⧸ A')) := by
    rw [← MonoidHom.map_zpowers, Subgroup.coe_map]
    rfl
  have hcard' : Nat.card ↥(((Subgroup.zpowers z' ⊔ A' : Subgroup N) : Set N)) = 81 := by
    rw [hset, Subgroup.card_mul_eq_card_subgroup_mul_card_quotient, himg]
    have hA'c : Nat.card A' = 27 := by
      rw [hA', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv, a11A0_e27.2]
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hzc : Nat.card ↥((Subgroup.zpowers (QuotientGroup.mk' A' z') : Subgroup (N ⧸ A')) :
        Set (N ⧸ A')) = 3 := by
      change Nat.card (Subgroup.zpowers (QuotientGroup.mk' A' z')) = 3
      rw [Nat.card_zpowers, orderOf_eq_prime hmk3 hmk1]
    rw [hA'c, hzc]
  have hmap : (Subgroup.zpowers z' ⊔ A').map N.subtype = a11P0 := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hA', Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hAN, a11P0, sup_comm]
    rfl
  refine ⟨?_, ?_⟩
  · rw [← hmap, Subgroup.card_map_of_injective N.subtype_injective]
    exact hcard'
  · intro x hx
    rw [← hmap] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    have hu' : u ∈ ((Subgroup.zpowers z' ⊔ A' : Subgroup N) : Set N) := hu
    rw [hset] at hu'
    obtain ⟨v, hv, a, ha, rfl⟩ := Set.mem_mul.mp hu'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    refine ⟨(k % 3).toNat, by omega, (a : A11), ha, ?_⟩
    have h1 : z' ^ k = z' ^ (k % 3) := zpow_eq_zpow_emod' k hz3
    rw [h1, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))]
    simp [hz']

theorem a11_comm_z (i j k : Fin 3) (l : Fin 2)
    (h : a11c1 ^ (i : ℕ) * a11c2 ^ (j : ℕ) * a11c3 ^ (k : ℕ) * a11z ^ ((l : ℕ) + 1) =
      a11z ^ ((l : ℕ) + 1) * (a11c1 ^ (i : ℕ) * a11c2 ^ (j : ℕ) * a11c3 ^ (k : ℕ))) :
    i = j ∧ j = k := by
  revert h
  revert i j k l
  decide

theorem eq_a11A0_of_le {A : Subgroup A11} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) (hAP : A ≤ a11P0) : A = a11A0 := by
  obtain ⟨hP0, hP0el⟩ := a11P0_spec
  by_contra hne
  have hnle : ¬ A ≤ a11A0 := fun hle =>
    hne (Subgroup.eq_of_le_of_card_ge hle (by rw [a11A0_e27.2, hA27]))
  obtain ⟨x, hxA, hxA0⟩ := Set.not_subset.mp hnle
  obtain ⟨l, hl, a, ha, rfl⟩ := hP0el x (hAP hxA)
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact hxA0 (by simpa using ha)
  have hdiag : a11A0 ⊓ A ≤ Subgroup.zpowers (a11c1 * a11c2 * a11c3) := by
    rintro b ⟨hb0, hbA⟩
    have hbx : b * (a11z ^ l * a) = a11z ^ l * a * b :=
      congrArg Subtype.val (hA.1.is_comm.comm ⟨b, hbA⟩ ⟨_, hxA⟩)
    have hab : a * b = b * a :=
      congrArg Subtype.val (a11A0_e27.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb0⟩)
    have hbz : b * a11z ^ l = a11z ^ l * b := by
      have : b * a11z ^ l * a = a11z ^ l * b * a := by
        calc b * a11z ^ l * a = b * (a11z ^ l * a) := by group
          _ = a11z ^ l * a * b := hbx
          _ = a11z ^ l * (a * b) := by group
          _ = a11z ^ l * (b * a) := by rw [hab]
          _ = a11z ^ l * b * a := by group
      exact mul_right_cancel this
    obtain ⟨i, j, k, hi, hj, hk, rfl⟩ := mem_a11A0 hb0
    have hl' : l = ((⟨l - 1, by omega⟩ : Fin 2) : ℕ) + 1 := by simp; omega
    rw [hl'] at hbz
    obtain ⟨hij, hjk⟩ := a11_comm_z ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ ⟨l - 1, by omega⟩ hbz
    have hij' : i = j := congrArg Fin.val hij
    have hjk' : j = k := congrArg Fin.val hjk
    subst hij' hjk'
    refine ⟨(i : ℤ), ?_⟩
    show (a11c1 * a11c2 * a11c3) ^ (i : ℤ) = _
    obtain ⟨-, -, -, h12, h13, h23, -, -, -, -, -⟩ := a11_facts
    have hc : Commute (a11c1 * a11c2) a11c3 :=
      (Commute.mul_left (show Commute a11c1 a11c3 from h13) (show Commute a11c2 a11c3 from h23))
    rw [zpow_natCast, hc.mul_pow, (show Commute a11c1 a11c2 from h12).mul_pow]
  have hle3 : Nat.card ↥(a11A0 ⊓ A) ≤ 3 := by
    have := Subgroup.card_le_of_le hdiag
    rw [Nat.card_zpowers] at this
    have h3 : orderOf (a11c1 * a11c2 * a11c3) = 3 :=
      orderOf_eq_prime (by decide) (by decide)
    omega
  have hne0 : ∀ K : Subgroup A11, a11A0.relIndex K ≠ 0 := fun K h0 => by
    have h := Subgroup.relIndex_mul_card (H := a11A0) (K := K)
    rw [h0, zero_mul] at h
    exact (Nat.card_pos (α := K)).ne' h.symm
  have hrel : a11A0.relIndex A ≤ a11A0.relIndex a11P0 :=
    Subgroup.relIndex_le_of_le_right hAP (hne0 _)
  have hrel3 : a11A0.relIndex a11P0 = 3 := by
    have h := Subgroup.relIndex_mul_card (H := a11A0) (K := a11P0)
    have hle : a11A0 ≤ a11P0 := le_sup_left
    rw [inf_of_le_left hle, hP0, a11A0_e27.2] at h
    omega
  have hmul := Subgroup.relIndex_mul_card (H := a11A0) (K := A)
  rw [hA27] at hmul
  have hpos : 0 < a11A0.relIndex A := Nat.pos_of_ne_zero (hne0 _)
  have : a11A0.relIndex A * Nat.card ↥(a11A0 ⊓ A) ≤ 3 * 3 :=
    Nat.mul_le_mul (hrel.trans hrel3.le) hle3
  omega

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
