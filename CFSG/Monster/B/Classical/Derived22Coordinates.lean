module

public import CFSG.Monster.B.Classical.Derived22Data
public import CFSG.Monster.B.Classical.Hyperoval
import all CFSG.Fischer.F4
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.Monster.B.Classical.Mog22

open CFSG.Monster.Code CFSG.Monster.B.Classical.Plane

@[expose] def blockMasks : List ℕ :=
  [252, 3852, 61452, 983052, 15728652, 2392340, 1589780, 8463380, 4331540, 4276516, 8552996,
    1315876, 2631716, 1188164, 2167364, 4752452, 8669252, 8917380, 4465284, 2245764, 1149060,
    8536344, 4293144, 2626584, 1320984, 1605928, 2376232, 4334632, 8460328, 4460872, 8921672,
    1131592, 2263112, 2171272, 1184392, 8684680, 4737160, 13104, 52272, 3342384, 13369392, 592208,
    394832, 9474128, 6316112, 5244304, 10488464, 348304, 696464, 10487136, 5245536, 675936, 368736,
    395680, 591520, 6328480, 9461920, 50112, 15552, 12779712, 3932352, 9765632, 6947584, 234752,
    812288, 3168512, 12626176, 12604928, 3188224, 825856, 223744, 6622208, 10095616, 5844992,
    10891264, 11124736, 5685248]

@[expose] def wordOf (m : ℕ) : Fin 24 → ZMod 2 := fun i => if m.testBit i then 1 else 0

theorem suppFin_wordOf (m : ℕ) : suppFin (wordOf m) = ofMask m := by
  ext i
  simp [suppFin, wordOf, ofMask]

theorem hammingNorm_wordOf (m : ℕ) :
    hammingNorm (wordOf m) = (ofMask m : Finset (Fin 24)).card := by
  rw [← card_suppFin, suppFin_wordOf]

set_option maxHeartbeats 8000000 in
theorem blockMasks_octad : ∀ b ∈ blockMasks, wordOf (b + 3) ∈ C ∧
    (ofMask (b + 3) : Finset (Fin 24)).card = 8 := by
  decide +kernel

theorem blockMasks_spec : ∀ b ∈ blockMasks, b.testBit 0 = false ∧ b.testBit 1 = false ∧
    b < 2 ^ 24 ∧ (ofMask (b + 3) : Finset (Fin 24)) \ {0, 1} = ofMask b := by
  decide +kernel

theorem mask_ofMask_blockMasks :
    ∀ b ∈ blockMasks, mask (ofMask (b + 3) : Finset (Fin 24)) = b + 3 := by
  decide +kernel

theorem mask_ofMask_blockMasks' :
    ∀ b ∈ blockMasks, mask (ofMask b : Finset (Fin 24)) = b := by
  decide +kernel

theorem blockMasks_nodup : blockMasks.Nodup := by decide +kernel

theorem length_blockMasks : blockMasks.length = 77 := by decide +kernel

@[expose] def octads01 : Finset (Finset (Fin 24)) :=
  (blockMasks.map fun b => ofMask (b + 3)).toFinset

theorem octads01_subset : octads01 ⊆ octads.filter fun O => 0 ∈ O ∧ 1 ∈ O := by
  intro O hO
  simp only [octads01, List.mem_toFinset, List.mem_map] at hO
  obtain ⟨b, hb, rfl⟩ := hO
  obtain ⟨hC, hcard⟩ := blockMasks_octad b hb
  obtain ⟨h0, h1, -, -⟩ := blockMasks_spec b hb
  rw [Finset.mem_filter, mem_octads]
  refine ⟨⟨wordOf (b + 3), hC, by rw [hammingNorm_wordOf, hcard], suppFin_wordOf _⟩, ?_, ?_⟩
  · simp only [ofMask, Finset.mem_filter, Finset.mem_univ, true_and]
    revert b
    decide +kernel
  · simp only [ofMask, Finset.mem_filter, Finset.mem_univ, true_and]
    revert b
    decide +kernel

theorem card_octads01 : octads01.card = 77 := by
  rw [octads01, List.toFinset_card_of_nodup, List.length_map, length_blockMasks]
  refine blockMasks_nodup.map_on fun a ha b hb h => ?_
  have := congrArg mask h
  rw [mask_ofMask_blockMasks a ha, mask_ofMask_blockMasks b hb] at this
  omega

theorem card_octads_filter01 : (octads.filter fun O => 0 ∈ O ∧ 1 ∈ O).card = 77 := by
  have h := (octads_steiner_five_design.2.2.2.2.1) {0, 1} (by decide)
  convert h using 2
  ext O
  simp [Finset.insert_subset_iff]

theorem octads01_eq : octads01 = octads.filter fun O => 0 ∈ O ∧ 1 ∈ O :=
  Finset.eq_of_subset_of_card_le octads01_subset (by rw [card_octads01, card_octads_filter01])

@[expose] def ℬ₀list : Finset (Finset (Fin 24)) := (blockMasks.map ofMask).toFinset

theorem ℬ₀_eq : ℬ₀ = ℬ₀list := by
  rw [ℬ₀, ← octads01_eq, octads01, ℬ₀list]
  ext B
  simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨O, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨b, hb, ((blockMasks_spec b hb).2.2.2).symm⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨_, ⟨b, hb, rfl⟩, (blockMasks_spec b hb).2.2.2⟩

theorem card_X₀ : X₀.card = 22 := by decide

theorem mem_ℬ₀ {B : Finset (Fin 24)} :
    B ∈ ℬ₀ ↔ ∃ O ∈ octads, 0 ∈ O ∧ 1 ∈ O ∧ O \ {0, 1} = B := by
  simp only [ℬ₀, Finset.mem_image, Finset.mem_filter, and_assoc]

theorem block_spec {B : Finset (Fin 24)} (hB : B ∈ ℬ₀) : B ⊆ X₀ ∧ B.card = 6 := by
  obtain ⟨O, hO, h0, h1, rfl⟩ := mem_ℬ₀.1 hB
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [X₀, Finset.mem_filter, Finset.mem_univ, true_and]
    have h0' : i ≠ 0 := fun h => hi.2 (Or.inl h)
    have h1' : i ≠ 1 := fun h => hi.2 (Or.inr h)
    have : (i : ℕ) ≠ 0 := fun h => h0' (Fin.ext h)
    have : (i : ℕ) ≠ 1 := fun h => h1' (Fin.ext h)
    omega
  · have hsub : ({0, 1} : Finset (Fin 24)) ⊆ O := by
      intro i hi
      rw [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl <;> assumption
    rw [Finset.card_sdiff_of_subset hsub, card_of_mem_octads hO]
    rfl

theorem disjoint_X₀ {T : Finset (Fin 24)} (hT : T ⊆ X₀) : Disjoint T {0, 1} := by
  rw [Finset.disjoint_left]
  intro i hi h01
  have := hT hi
  simp only [X₀, Finset.mem_filter, Finset.mem_univ, true_and] at this
  rw [Finset.mem_insert, Finset.mem_singleton] at h01
  rcases h01 with rfl | rfl <;> simp at this

theorem existsUnique_block {T : Finset (Fin 24)} (hT : T ⊆ X₀) (h3 : T.card = 3) :
    ∃! B, B ∈ ℬ₀ ∧ T ⊆ B := by
  have hY : (T ∪ {0, 1}).card = 5 := by
    rw [Finset.card_union_of_disjoint (disjoint_X₀ hT), h3]
    rfl
  obtain ⟨O, ⟨hO, hYO⟩, hu⟩ := existsUnique_octad _ hY
  have h0 : (0 : Fin 24) ∈ O := hYO (by simp)
  have h1 : (1 : Fin 24) ∈ O := hYO (by simp)
  refine ⟨O \ {0, 1}, ⟨mem_ℬ₀.2 ⟨O, hO, h0, h1, rfl⟩, ?_⟩, ?_⟩
  · intro i hi
    rw [Finset.mem_sdiff]
    exact ⟨hYO (Finset.mem_union_left _ hi),
      Finset.disjoint_left.1 (disjoint_X₀ hT) hi⟩
  · rintro B ⟨hB, hTB⟩
    obtain ⟨O', hO', h0', h1', rfl⟩ := mem_ℬ₀.1 hB
    have : O' = O := hu O' ⟨hO', by
      intro i hi
      rcases Finset.mem_union.1 hi with hi | hi
      · exact (Finset.mem_sdiff.1 (hTB hi)).1
      · rw [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl <;> assumption⟩
    rw [this]

theorem card_ℬ₀ : ℬ₀.card = 77 := by
  rw [ℬ₀_eq, ℬ₀list, List.toFinset_card_of_nodup, List.length_map, length_blockMasks]
  refine blockMasks_nodup.map_on fun a ha b hb h => ?_
  have := congrArg mask h
  rwa [mask_ofMask_blockMasks' a ha, mask_ofMask_blockMasks' b hb] at this

@[expose] def φ : Fin 21 → Fin 24 :=
  ![8, 4, 15, 18, 21, 3, 11, 9, 10, 7, 12, 19, 23, 5, 22, 14, 16, 6, 17, 20, 13]

theorem φ_injective : Function.Injective φ := by decide

theorem image_φ : Finset.univ.image φ = X₀.erase 2 := by decide

set_option maxHeartbeats 8000000 in
theorem image_lines_eq :
    Finset.univ.image (fun a => (projLine a).image φ) =
      (ℬ₀list.filter fun B => 2 ∈ B).image fun B => B.erase 2 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
theorem preimage_blocks_eq :
    (ℬ₀list.filter fun B => 2 ∉ B).image (fun B => Finset.univ.filter fun p => φ p ∈ B) = O 2 := by
  decide +kernel

theorem mog_derived_design_coordinates :
    (X₀.card = 22 ∧ ℬ₀.card = 77 ∧ (∀ B ∈ ℬ₀, B ⊆ X₀ ∧ B.card = 6) ∧
      ∀ T ⊆ X₀, T.card = 3 → ∃! B, B ∈ ℬ₀ ∧ T ⊆ B) ∧
    Function.Injective φ ∧ Finset.univ.image φ = X₀.erase 2 ∧
    Finset.univ.image (fun a => (projLine a).image φ) =
      (ℬ₀.filter fun B => 2 ∈ B).image (fun B => B.erase 2) ∧
    (ℬ₀.filter fun B => 2 ∉ B).image (fun B => Finset.univ.filter fun p => φ p ∈ B) = O 2 ∧
    ((ℬ₀.filter fun B => 2 ∉ B).image fun B => Finset.univ.filter fun p => φ p ∈ B).card = 56 ∧
    leastMask 2 = 3276 := by
  refine ⟨⟨card_X₀, card_ℬ₀, fun B hB => block_spec hB, fun T hT h3 => existsUnique_block hT h3⟩,
    φ_injective, image_φ, ?_, ?_, ?_, rfl⟩
  · rw [ℬ₀_eq]; exact image_lines_eq
  · rw [ℬ₀_eq]; exact preimage_blocks_eq
  · rw [ℬ₀_eq, preimage_blocks_eq, card_O]

end CFSG.Monster.B.Classical.Mog22
