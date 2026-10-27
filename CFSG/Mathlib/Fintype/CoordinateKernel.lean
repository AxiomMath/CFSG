module

public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace Finset

variable {ι M : Type*} [Fintype ι] [Finite M]

theorem le_card_of_coordinate_kernel_bound [One M] (S : Finset ι)
    (hM : 1 < Nat.card M) {C : Set (ι → M)} {r : ℕ}
    (hC : ∀ f, (∀ i ∈ S, f i = 1) → f ∈ C)
    (hbound : Nat.card M ^ r * Nat.card C ≤ Nat.card M ^ Fintype.card ι) :
    r ≤ S.card := by
  classical
  let e : ({i : ι // i ∉ S} → M) → C :=
    fun g => ⟨fun i => if h : i ∈ S then 1 else g ⟨i, h⟩,
      hC _ (by intro i hi; simp [hi])⟩
  have he : Function.Injective e := by
    intro g g' hgg
    funext i
    have hi := congrFun (congrArg Subtype.val hgg) i.1
    simpa [e, i.2] using hi
  have hcardOutside : Nat.card {i : ι // i ∉ S} = Fintype.card ι - S.card := by
    rw [Nat.card_eq_fintype_card (α := {i : ι // i ∉ S}), Fintype.card_subtype_compl]
    simp only [Fintype.card_coe]
  have hcard : Nat.card ({i : ι // i ∉ S} → M) =
      Nat.card M ^ (Fintype.card ι - S.card) := by
    rw [Nat.card_fun, hcardOutside]
  have hle : Nat.card M ^ r * Nat.card M ^ (Fintype.card ι - S.card) ≤
      Nat.card M ^ Fintype.card ι := by
    rw [← hcard]
    exact (Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective e he)).trans hbound
  rw [← pow_add] at hle
  have h := (Nat.pow_le_pow_iff_right hM).mp hle
  have hS : S.card ≤ Fintype.card ι := S.card_le_univ
  omega

theorem lt_card_of_paired_coordinate_kernel_bound [DecidableEq ι] [Group M]
    (Spos Sneg : Finset ι)
    (hM : 1 < Nat.card M) (hdisj : Disjoint Spos Sneg) {C : Set (ι → M)} {r : ℕ}
    (hr : 0 < r)
    (hC : ∀ f, (∃ c : M, (∀ i ∈ Spos, f i = c) ∧ (∀ i ∈ Sneg, f i = c⁻¹)) → f ∈ C)
    (hbound : Nat.card M ^ r * Nat.card C ≤ Nat.card M ^ Fintype.card ι) :
    r < (Spos ∪ Sneg).card := by
  classical
  let S := Spos ∪ Sneg
  by_cases hSempty : S = ∅
  · have hSpos : Spos = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro i hi
      exact notMem_empty i (hSempty ▸ mem_union_left Sneg hi)
    have hSneg : Sneg = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro i hi
      exact notMem_empty i (hSempty ▸ mem_union_right Spos hi)
    have hall : ∀ f : ι → M, f ∈ C := by
      intro f
      apply hC f
      exact ⟨1, by simp [hSpos], by simp [hSneg]⟩
    have hcardC : Nat.card C = Nat.card M ^ Fintype.card ι := by
      have h₁ := Nat.card_le_card_of_injective (fun f : ι → M => (⟨f, hall f⟩ : C))
        (fun a b hab => Subtype.ext_iff.mp hab)
      have h₂ := Nat.card_le_card_of_injective (Subtype.val : C → (ι → M))
        Subtype.val_injective
      have hEq : Nat.card C = Nat.card (ι → M) := le_antisymm h₂ h₁
      rw [hEq, Nat.card_fun, Nat.card_eq_fintype_card (α := ι)]
    rw [hcardC] at hbound
    have hpos : 0 < Nat.card M ^ Fintype.card ι := pow_pos (by omega) _
    have hle : Nat.card M ^ r ≤ 1 :=
      Nat.le_of_mul_le_mul_right (by simpa only [one_mul] using hbound) hpos
    have hle' : Nat.card M ^ r ≤ Nat.card M ^ 0 := by simpa using hle
    have h := (Nat.pow_le_pow_iff_right hM).mp hle'
    omega
  · obtain ⟨i₀, hi₀⟩ := nonempty_iff_ne_empty.mpr hSempty
    let e : (M × ({i : ι // i ∉ S} → M)) → C :=
      fun cg => ⟨fun i => if hi : i ∈ Spos then cg.1
          else if hi' : i ∈ Sneg then cg.1⁻¹
          else cg.2 ⟨i, fun hI => (mem_union.mp hI).elim hi hi'⟩,
        hC _ ⟨cg.1, (fun i hi => dif_pos hi), (fun i hi => by
          have hni : i ∉ Spos := fun h => disjoint_left.mp hdisj h hi
          rw [dif_neg hni, dif_pos hi])⟩⟩
    have he : Function.Injective e := by
      intro cg cg' hgg
      have h₁ : (e cg).val = (e cg').val := congrArg Subtype.val hgg
      have hc : cg.1 = cg'.1 := by
        have hi := congrFun h₁ i₀
        rcases mem_union.mp hi₀ with hipos | hineg
        · simpa only [e, dif_pos hipos] using hi
        · have hni : i₀ ∉ Spos := fun h => disjoint_left.mp hdisj h hineg
          apply inv_injective
          simpa only [e, dif_neg hni, dif_pos hineg] using hi
      have hg : cg.2 = cg'.2 := by
        funext i
        have hi := congrFun h₁ i.1
        simpa only [e, dif_neg (fun h => i.2 (mem_union_left _ h)),
          dif_neg (fun h => i.2 (mem_union_right _ h))] using hi
      exact Prod.ext hc hg
    have hcardOutside : Nat.card {i : ι // i ∉ S} = Fintype.card ι - S.card := by
      rw [Nat.card_eq_fintype_card (α := {i : ι // i ∉ S}), Fintype.card_subtype_compl]
      simp only [Fintype.card_coe]
    have hcard : Nat.card (M × ({i : ι // i ∉ S} → M)) =
        Nat.card M ^ (1 + (Fintype.card ι - S.card)) := by
      rw [Nat.card_prod, Nat.card_fun, hcardOutside, pow_add, pow_one]
    have hle : Nat.card M ^ r * Nat.card M ^ (1 + (Fintype.card ι - S.card)) ≤
        Nat.card M ^ Fintype.card ι := by
      rw [← hcard]
      exact (Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective e he)).trans hbound
    rw [← pow_add] at hle
    have h := (Nat.pow_le_pow_iff_right hM).mp hle
    have hS : S.card ≤ Fintype.card ι := S.card_le_univ
    change r < S.card
    omega

end Finset
