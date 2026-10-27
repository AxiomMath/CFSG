module

public import CFSG.Monster.Code.LatticeCount
import CFSG.Fischer.NoF25.Octads

public section

namespace CFSG.Monster.Code

open scoped Finset

@[expose] noncomputable def octads : Finset (Finset (Fin 24)) := octFin.image suppFin

theorem mem_octads {O : Finset (Fin 24)} :
    O ∈ octads ↔ ∃ x ∈ C, hammingNorm x = 8 ∧ suppFin x = O := by
  simp only [octads, Finset.mem_image, mem_octFin, and_assoc]

private theorem zmod2_ne_zero_iff : ∀ a : ZMod 2, a ≠ 0 ↔ a = 1 := by decide

theorem suppFin_injective : Function.Injective suppFin := by
  intro x y h
  funext i
  have := congrArg (i ∈ ·) h
  simp only [mem_suppFin, eq_iff_iff, zmod2_ne_zero_iff] at this
  have hx : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hx (x i) with hxi | hxi <;> rcases hx (y i) with hyi | hyi <;> simp_all

theorem card_suppFin (x : Fin 24 → ZMod 2) : (suppFin x).card = hammingNorm x := rfl

private theorem add_ne_zero_iff : ∀ a b : ZMod 2, a + b ≠ 0 ↔ (a ≠ 0 ↔ ¬b ≠ 0) := by decide

theorem suppFin_add (x y : Fin 24 → ZMod 2) :
    suppFin (x + y) = symmDiff (suppFin x) (suppFin y) := by
  ext i
  simp only [mem_suppFin, Pi.add_apply, Finset.mem_symmDiff, add_ne_zero_iff]
  tauto

theorem card_octads : octads.card = 759 := by
  rw [octads, Finset.card_image_of_injective _ suppFin_injective, card_octFin]

theorem card_of_mem_octads {O : Finset (Fin 24)} (hO : O ∈ octads) : O.card = 8 := by
  obtain ⟨x, -, hx, rfl⟩ := mem_octads.1 hO
  rw [card_suppFin, hx]

theorem card_inter_le_four {O O' : Finset (Fin 24)} (hO : O ∈ octads) (hO' : O' ∈ octads)
    (hne : O ≠ O') : (O ∩ O').card ≤ 4 := by
  obtain ⟨x, hxC, hx, rfl⟩ := mem_octads.1 hO
  obtain ⟨y, hyC, hy, rfl⟩ := mem_octads.1 hO'
  have hxy : x + y ≠ 0 := by
    intro h
    apply hne
    rw [add_eq_zero_iff_eq_neg, ZModModule.neg_eq_self] at h
    rw [h]
  have h8 := eight_le_wt (C.add_mem hxC hyC) hxy
  rw [← card_suppFin, suppFin_add] at h8
  have hc := CFSG.Fischer.card_symmDiff_add_two_mul (suppFin x) (suppFin y)
  rw [card_suppFin, card_suppFin, hx, hy] at hc
  omega

theorem existsUnique_octad (Y : Finset (Fin 24)) (hY : Y.card = 5) :
    ∃! O, O ∈ octads ∧ Y ⊆ O :=
  CFSG.Fischer.steiner_of_inter octads (fun _ => card_of_mem_octads)
    (fun _ hO _ hO' hne => card_inter_le_four hO hO' hne)
    (by rw [card_octads, Fintype.card_fin]; rfl) Y hY

theorem card_filter_superset_mul_choose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒪 : Finset (Finset ι)) (hcard : ∀ O ∈ 𝒪, O.card = 8)
    (hst : ∀ Y : Finset ι, Y.card = 5 → ∃! O, O ∈ 𝒪 ∧ Y ⊆ O) (T : Finset ι) (hT : T.card ≤ 5) :
    #{O ∈ 𝒪 | T ⊆ O} * (8 - T.card).choose (5 - T.card) =
      (Fintype.card ι - T.card).choose (5 - T.card) := by
  have hP : (Finset.univ.powersetCard 5).filter (T ⊆ ·) =
      (𝒪.filter (T ⊆ ·)).biUnion fun O => (O.powersetCard 5).filter (T ⊆ ·) := by
    ext Y
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and,
      Finset.mem_biUnion]
    constructor
    · rintro ⟨hY, hTY⟩
      obtain ⟨O, ⟨hO, hYO⟩, -⟩ := hst Y hY
      exact ⟨O, ⟨hO, hTY.trans hYO⟩, ⟨hYO, hY⟩, hTY⟩
    · rintro ⟨O, -, ⟨-, hY⟩, hTY⟩
      exact ⟨hY, hTY⟩
  have hdisj : (↑(𝒪.filter (T ⊆ ·)) : Set (Finset ι)).PairwiseDisjoint
      fun O => (O.powersetCard 5).filter (T ⊆ ·) := by
    intro O hO O' hO' hne
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hO hO'
    rw [Function.onFun, Finset.disjoint_left]
    intro Y hY hY'
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hY hY'
    obtain ⟨O₀, -, hu⟩ := hst Y hY.1.2
    exact hne ((hu O ⟨hO.1, hY.1.1⟩).trans (hu O' ⟨hO'.1, hY'.1.1⟩).symm)
  have h1 := Finset.card_filter_powersetCard_subset T Finset.univ 5 (Finset.subset_univ T) hT
  rw [hP, Finset.card_biUnion hdisj, Finset.card_univ] at h1
  rw [← h1, Finset.sum_congr rfl fun O hO => Finset.card_filter_powersetCard_subset T O 5
    (Finset.mem_filter.1 hO).2 hT, Finset.sum_congr rfl fun O hO => by
      rw [hcard O (Finset.mem_filter.1 hO).1], Finset.sum_const, smul_eq_mul]

theorem card_octads_superset (T : Finset (Fin 24)) (hT : T.card ≤ 5) :
    #{O ∈ octads | T ⊆ O} * (8 - T.card).choose (5 - T.card) =
      (24 - T.card).choose (5 - T.card) := by
  have := card_filter_superset_mul_choose octads (fun _ => card_of_mem_octads)
    existsUnique_octad T hT
  rwa [Fintype.card_fin] at this

theorem octads_steiner_five_design :
    (∀ O, O ∈ octads ↔ ∃ x ∈ C, hammingNorm x = 8 ∧ suppFin x = O) ∧ octads.card = 759 ∧
    (∀ Y : Finset (Fin 24), Y.card = 5 → ∃! O, O ∈ octads ∧ Y ⊆ O) ∧
    (∀ T : Finset (Fin 24), T.card = 1 → #{O ∈ octads | T ⊆ O} = 253) ∧
    (∀ T : Finset (Fin 24), T.card = 2 → #{O ∈ octads | T ⊆ O} = 77) ∧
    (∀ T : Finset (Fin 24), T.card = 3 → #{O ∈ octads | T ⊆ O} = 21) := by
  refine ⟨fun _ => mem_octads, card_octads, existsUnique_octad, fun T hT => ?_, fun T hT => ?_,
    fun T hT => ?_⟩ <;>
  · have h := card_octads_superset T (by omega)
    rw [hT] at h
    norm_num [Nat.choose] at h
    omega

end CFSG.Monster.Code
