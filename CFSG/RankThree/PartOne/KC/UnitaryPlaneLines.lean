module

public import CFSG.RankThree.PartOne.KC.UnitaryPlaneProjection
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.RankThree.PartOne.KCUnitaryPlane

variable {P : Type*} [Group P] [Fintype P] {p : ℕ}

structure IsPlane (p : ℕ) (P : Type*) [Group P] : Prop where
  prime : p.Prime
  card : Nat.card P = p ^ 2
  pow : ∀ x : P, x ^ p = 1

instance instFiniteSubgroup : Finite (Subgroup P) :=
  Finite.of_injective (fun L : Subgroup P => (L : Set P)) SetLike.coe_injective

open scoped _root_.Classical in
@[expose] noncomputable def lines (p : ℕ) (P : Type*) [Group P] [Fintype P] : Finset (Subgroup P) :=
  haveI : Fintype (Subgroup P) := Fintype.ofFinite _
  Finset.univ.filter (fun L : Subgroup P => Nat.card L = p)

theorem mem_lines {L : Subgroup P} : L ∈ lines p P ↔ Nat.card L = p := by
  classical
  simp [lines]

namespace IsPlane

variable (hP : IsPlane p P)
include hP

omit [Fintype P] in
theorem orderOf_eq {x : P} (hx : x ≠ 1) : orderOf x = p := by
  have := Fact.mk hP.prime
  exact orderOf_eq_prime (hP.pow x) hx

omit [Fintype P] in
theorem card_zpowers {x : P} (hx : x ≠ 1) : Nat.card (Subgroup.zpowers x) = p := by
  rw [Nat.card_zpowers, hP.orderOf_eq hx]

theorem zpowers_eq {L : Subgroup P} (hL : Nat.card L = p) {x : P} (hxL : x ∈ L) (hx : x ≠ 1) :
    Subgroup.zpowers x = L := by
  apply Subgroup.eq_of_le_of_card_ge
  · rw [Subgroup.zpowers_le]
    exact hxL
  · rw [hL, hP.card_zpowers hx]

theorem inf_eq_bot {L M : Subgroup P} (hL : Nat.card L = p) (hM : Nat.card M = p) (hne : L ≠ M) :
    L ⊓ M = ⊥ := by
  by_contra h
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h
  have hx' : ((x : ↥(L ⊓ M)) : P) ≠ 1 := fun h' => hx1 (Subtype.ext h')
  exact hne ((hP.zpowers_eq hL x.2.1 hx').symm.trans (hP.zpowers_eq hM x.2.2 hx'))

theorem zpowers_mem_lines {x : P} (hx : x ≠ 1) : Subgroup.zpowers x ∈ lines p P :=
  mem_lines.mpr (hP.card_zpowers hx)

open scoped _root_.Classical in
theorem card_lines : (lines p P).card = p + 1 := by
  have hp := hP.prime
  set Pstar : Finset P := Finset.univ.filter (fun x : P => x ≠ 1) with hPstar
  have h1 : Pstar.card = p ^ 2 - 1 := by
    rw [hPstar, Finset.filter_ne' Finset.univ (1 : P), Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ← Nat.card_eq_fintype_card, hP.card]
  have h2 : ∀ x ∈ Pstar, Subgroup.zpowers x ∈ lines p P := fun x hx =>
    hP.zpowers_mem_lines (by simpa [hPstar] using hx)
  have h3 : ∀ L ∈ lines p P, (Pstar.filter (fun x => Subgroup.zpowers x = L)).card = p - 1 := by
    intro L hL
    have hLc : Nat.card L = p := mem_lines.mp hL
    have e : Pstar.filter (fun x => Subgroup.zpowers x = L) =
        (Finset.univ.filter (fun x : P => x ∈ L)).erase 1 := by
      ext x
      simp only [Finset.mem_filter, hPstar, Finset.mem_univ, true_and, Finset.mem_erase]
      constructor
      · rintro ⟨hx1, hxL⟩
        exact ⟨hx1, hxL ▸ Subgroup.mem_zpowers x⟩
      · rintro ⟨hx1, hxL⟩
        exact ⟨hx1, hP.zpowers_eq hLc hxL hx1⟩
    rw [e, Finset.card_erase_of_mem (by simp), card_filter_mem, hLc]
  have h4 := Finset.card_eq_sum_card_fiberwise h2
  rw [Finset.sum_congr rfl h3, Finset.sum_const, smul_eq_mul, h1] at h4
  have hp1 : 1 ≤ p := hp.one_lt.le
  have h5 : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  have hpos : 0 < p - 1 := by have := hp.two_le; omega
  rw [h5] at h4
  exact (Nat.eq_of_mul_eq_mul_right hpos h4).symm

end IsPlane


section Rep

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  (ρ : P →* LinearMap.GeneralLinearGroup K V)

open scoped _root_.Classical in
@[expose] noncomputable def starSet (P : Type*) [Group P] [Fintype P] : Finset P :=
  Finset.univ.filter (fun x : P => x ≠ 1)

open scoped _root_.Classical in
theorem mem_starSet {x : P} : x ∈ starSet P ↔ x ≠ 1 := by simp [starSet]

open scoped _root_.Classical in
theorem sumOp_eq_one_add (L : Subgroup P) :
    sumOp ρ L = 1 + ∑ x ∈ (starSet P).filter (fun x => x ∈ L), act ρ x := by
  unfold sumOp
  have h1 : (1 : P) ∈ Finset.univ.filter (fun x : P => x ∈ L) := by simp
  rw [← Finset.add_sum_erase _ _ h1, act_one]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext x
  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, mem_starSet]

open scoped _root_.Classical in
theorem sumOp_top_eq_one_add :
    sumOp ρ ⊤ = 1 + ∑ x ∈ starSet P, act ρ x := by
  rw [sumOp_eq_one_add]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext x
  simp

open scoped _root_.Classical in
theorem IsPlane.filter_zpowers_eq (hP : IsPlane p P) {L : Subgroup P} (hL : Nat.card L = p) :
    (starSet P).filter (fun x => Subgroup.zpowers x = L) =
      (starSet P).filter (fun x => x ∈ L) := by
  ext x
  simp only [Finset.mem_filter, mem_starSet]
  constructor
  · rintro ⟨hx1, hxL⟩
    exact ⟨hx1, hxL ▸ Subgroup.mem_zpowers x⟩
  · rintro ⟨hx1, hxL⟩
    exact ⟨hx1, hP.zpowers_eq hL hxL hx1⟩

open scoped _root_.Classical in
theorem IsPlane.sum_lines_filter (hP : IsPlane p P) {M : Type*} [AddCommMonoid M] (f : P → M) :
    ∑ L ∈ lines p P, ∑ x ∈ (starSet P).filter (fun x => x ∈ L), f x = ∑ x ∈ starSet P, f x := by
  have h2 : ∀ x ∈ starSet P, Subgroup.zpowers x ∈ lines p P := fun x hx =>
    hP.zpowers_mem_lines (mem_starSet.mp hx)
  rw [← Finset.sum_fiberwise_of_maps_to h2 f]
  refine Finset.sum_congr rfl fun L hL => ?_
  rw [hP.filter_zpowers_eq (mem_lines.mp hL)]

open scoped _root_.Classical in
theorem IsPlane.sum_lines_sumOp (hP : IsPlane p P) :
    ∑ L ∈ lines p P, sumOp ρ L = (p : K) • (1 : Module.End K V) + sumOp ρ ⊤ := by
  rw [Finset.sum_congr rfl (fun L _ => sumOp_eq_one_add ρ L), Finset.sum_add_distrib,
    Finset.sum_const, hP.card_lines, hP.sum_lines_filter (fun x => act ρ x), sumOp_top_eq_one_add,
    Nat.cast_smul_eq_nsmul, add_smul, one_smul]
  abel

open scoped _root_.Classical in
theorem IsPlane.sumOp_mul_sumOp_of_ne (hP : IsPlane p P) {L M : Subgroup P}
    (hL : Nat.card L = p) (hM : Nat.card M = p) (hne : L ≠ M) :
    sumOp ρ L * sumOp ρ M = sumOp ρ ⊤ := by
  have hbot := hP.inf_eq_bot hL hM hne
  set SL := Finset.univ.filter (fun x : P => x ∈ L) with hSL
  set SM := Finset.univ.filter (fun x : P => x ∈ M) with hSM
  set g : P × P → P := fun z => z.1 * z.2 with hg
  have hinj : Set.InjOn g ↑(SL ×ˢ SM) := by
    rintro ⟨x, y⟩ hxy ⟨x', y'⟩ hxy' he
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hSL, hSM, Finset.mem_filter,
      Finset.mem_univ, true_and] at hxy hxy'
    simp only [hg] at he
    have h1 : x'⁻¹ * x = y' * y⁻¹ := by
      calc x'⁻¹ * x = x'⁻¹ * (x * y) * y⁻¹ := by group
        _ = x'⁻¹ * (x' * y') * y⁻¹ := by rw [he]
        _ = y' * y⁻¹ := by group
    have h2 : x'⁻¹ * x ∈ L ⊓ M :=
      ⟨L.mul_mem (L.inv_mem hxy'.1) hxy.1, h1 ▸ M.mul_mem hxy'.2 (M.inv_mem hxy.2)⟩
    rw [hbot, Subgroup.mem_bot] at h2
    have hx : x = x' := by
      have := congrArg (fun z => x' * z) h2
      simpa using this
    subst hx
    have : y = y' := by simpa using he
    rw [this]
  have himg : (SL ×ˢ SM).image g = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, Finset.card_product, hSL, hSM, card_filter_mem,
      card_filter_mem, hL, hM, ← Nat.card_eq_fintype_card, hP.card, sq]
  have h3 : sumOp ρ L * sumOp ρ M = ∑ z ∈ SL ×ˢ SM, act ρ (g z) := by
    unfold sumOp
    rw [Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp [hg, act_mul]
  rw [h3, ← Finset.sum_image (f := fun w => act ρ w) hinj, himg, sumOp]
  simp

end Rep

end CFSG.RankThree.PartOne.KCUnitaryPlane
