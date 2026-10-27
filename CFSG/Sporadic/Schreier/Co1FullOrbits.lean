
module

public import CFSG.Sporadic.Schreier.Co1FullOrbitsBase

public import CFSG.Sporadic.Schreier.Co1FullOrbCheck
public import CFSG.Sporadic.Schreier.Co1OrbEnum
public import CFSG.Sporadic.Schreier.Co1ThreeLocal
public import Mathlib.FieldTheory.Finiteness
public import CFSG.Sporadic.Schreier.Co1FullOrbCheckInputs
public import CFSG.Sporadic.Schreier.Co1XSet
public import Certificates.Data.CFSGNative.Co1.Data

public section

namespace CFSG.Sporadic.Co1Schreier

open CFSG.Sporadic.SmallF2 (toVecD toVecD_injective)
open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Matrix

local notation "gaOrbit" => kOrbit GA
local notation "rootOrbit" k:max => kOrbit GA (toVecD 24 (Native.fullRoot k))

theorem gaOrbit_two : gaOrbit (toVecD 24 2) = co1X :=
  full_orbit_two

theorem gaOrbit_root {k : ℕ} (hk : k = 2) :
    gaOrbit (toVecD 24 (Native.fullRoot k)) = enumSet (Native.fullOrb k) (Native.fullSize k) := by
  subst hk
  exact gaOrbit_two.trans co1X_eq_enumSet

theorem fullOrb_two_inj {i j : ℕ} (hi : i < 98280)
    (hj : j < 98280)
    (h : toVecD 24 ((Native.fullOrb 2).pts[i]!) = toVecD 24 ((Native.fullOrb 2).pts[j]!)) :
    i = j := by
  have himg : enumSet (Native.fullOrb 2) 98280 =
      (fun i => toVecD 24 ((Native.fullOrb 2).pts[i]!)) '' Set.Iio 98280 := by
    ext w
    simp only [enumSet, Set.mem_image, Set.mem_Iio, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
  have hc : ((fun i => toVecD 24 ((Native.fullOrb 2).pts[i]!)) '' Set.Iio 98280).ncard =
      (Set.Iio 98280).ncard := by
    rw [← himg, ← co1X_eq_enumSet, ← gaOrbit_two, ← Finset.coe_range, Set.ncard_coe_finset,
      Finset.card_range]
    exact full_orbits_ncard (k := 2) (by norm_num)
  exact Set.injOn_of_ncard_image_eq hc (Set.finite_Iio _) (Set.mem_Iio.2 hi) (Set.mem_Iio.2 hj) h

theorem orbit_disjoint {j k : ℕ} (hj : j < 4) (hk : k < 4)
    (hjk : j ≠ k) : Disjoint (rootOrbit j) (rootOrbit k) := by
  rw [Set.disjoint_left]
  intro w hwj hwk
  apply hjk
  have h := (kOrbit_eq_of_mem hwj).symm.trans (kOrbit_eq_of_mem hwk)
  have hc := congrArg Set.ncard h
  rw [full_orbits_ncard hj, full_orbits_ncard hk] at hc
  exact fullSize_inj hj hk hc

open Classical in
theorem ncard_inter {S : Submodule (ZMod 2) Vec24}
    (hS : ∀ g ∈ GA, ∀ v ∈ S, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v ∈ S)
    {k : ℕ} (hk : k < 4) :
    ((S : Set Vec24) ∩ rootOrbit k).ncard =
      if toVecD 24 (Native.fullRoot k) ∈ S then Native.fullSize k else 0 := by
  have hroot : toVecD 24 (Native.fullRoot k) ∈ rootOrbit k := mem_kOrbit_self _ _
  split_ifs with h
  · rw [Set.inter_eq_right.mpr fun w hw => mem_or_disjoint hS hroot hw h, full_orbits_ncard hk]
  · rw [Set.ncard_eq_zero, Set.eq_empty_iff_forall_notMem]
    rintro w ⟨hwS, hw⟩
    exact h (mem_or_disjoint hS hw hroot hwS)

theorem invariant_eq
    {S : Submodule (ZMod 2) Vec24}
    (hS : ∀ g ∈ GA, ∀ v ∈ S, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  classical
  have hsplit : (S : Set Vec24) = ((S : Set Vec24) ∩ rootOrbit 0 ∪ (S : Set Vec24) ∩ rootOrbit 1) ∪
      (S : Set Vec24) ∩ rootOrbit 2 ∪ (S : Set Vec24) ∩ rootOrbit 3 := by
    ext w
    simp only [Set.mem_union, Set.mem_inter_iff]
    constructor
    · intro hw
      obtain ⟨k, hk, hwk⟩ := full_orbits_cover w
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inl (Or.inl ⟨hw, hwk⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨hw, hwk⟩))
      · exact Or.inl (Or.inr ⟨hw, hwk⟩)
      · exact Or.inr ⟨hw, hwk⟩
    · rintro (((⟨hw, -⟩ | ⟨hw, -⟩) | ⟨hw, -⟩) | ⟨hw, -⟩) <;> exact hw
  have hfin : ∀ k, ((S : Set Vec24) ∩ rootOrbit k).Finite := fun _ => Set.toFinite _
  have hd : ∀ j k : ℕ, j < 4 → k < 4 → j ≠ k →
      Disjoint ((S : Set Vec24) ∩ rootOrbit j) ((S : Set Vec24) ∩ rootOrbit k) :=
    fun j k hj hk hjk =>
      (orbit_disjoint hj hk hjk).mono Set.inter_subset_right Set.inter_subset_right
  have hcard : (S : Set Vec24).ncard =
      ((S : Set Vec24) ∩ rootOrbit 0).ncard + ((S : Set Vec24) ∩ rootOrbit 1).ncard +
        ((S : Set Vec24) ∩ rootOrbit 2).ncard + ((S : Set Vec24) ∩ rootOrbit 3).ncard := by
    have d01 := hd 0 1 (by norm_num) (by norm_num) (by norm_num)
    have d02 := hd 0 2 (by norm_num) (by norm_num) (by norm_num)
    have d12 := hd 1 2 (by norm_num) (by norm_num) (by norm_num)
    have d03 := hd 0 3 (by norm_num) (by norm_num) (by norm_num)
    have d13 := hd 1 3 (by norm_num) (by norm_num) (by norm_num)
    have d23 := hd 2 3 (by norm_num) (by norm_num) (by norm_num)
    conv_lhs => rw [hsplit]
    rw [Set.ncard_union_eq ((d03.union_left d13).union_left d23)
      (((hfin 0).union (hfin 1)).union (hfin 2)) (hfin 3),
      Set.ncard_union_eq (d02.union_left d12) ((hfin 0).union (hfin 1)) (hfin 2),
      Set.ncard_union_eq d01 (hfin 0) (hfin 1)]
  have hV : Nat.card Vec24 = 2 ^ 24 := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hdvd : (S : Set Vec24).ncard ∣ 2 ^ 24 := by
    have h := AddSubgroup.card_addSubgroup_dvd_card S.toAddSubgroup
    rw [hV] at h
    rw [← Nat.card_coe_set_eq]
    exact h
  obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have h0 : toVecD 24 (Native.fullRoot 0) ∈ S := by
    rw [show Native.fullRoot 0 = 0 from rfl, CFSG.Sporadic.SmallF2.toVecD_zero]
    exact S.zero_mem
  rw [ncard_inter hS (k := 0) (by norm_num), ncard_inter hS (k := 1) (by norm_num),
    ncard_inter hS (k := 2) (by norm_num), ncard_inter hS (k := 3) (by norm_num), hm'] at hcard
  simp only [h0, ↓reduceIte] at hcard
  have key : ∀ (b₁ b₂ b₃ : Bool) (m : ℕ), m ≤ 24 →
      2 ^ m = Native.fullSize 0 + (if b₁ = true then Native.fullSize 1 else 0) +
        (if b₂ = true then Native.fullSize 2 else 0) +
        (if b₃ = true then Native.fullSize 3 else 0) →
      m = 0 ∨ m = 24 := by
    intro b₁ b₂ b₃ m hm
    revert b₁ b₂ b₃
    interval_cases m <;> decide
  rcases key (decide (toVecD 24 (Native.fullRoot 1) ∈ S))
      (decide (toVecD 24 (Native.fullRoot 2) ∈ S)) (decide (toVecD 24 (Native.fullRoot 3) ∈ S))
      m hm (by simpa only [decide_eq_true_eq] using hcard) with h | h
  · left
    rw [Submodule.eq_bot_iff]
    intro x hx
    have h1 : (S : Set Vec24).ncard = 1 := by rw [hm', h, pow_zero]
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
    have hxa : x ∈ (S : Set Vec24) := hx
    have h0a : (0 : Vec24) ∈ (S : Set Vec24) := S.zero_mem
    rw [ha, Set.mem_singleton_iff] at hxa h0a
    rw [hxa, ← h0a]
  · right
    rw [eq_top_iff]
    intro x _
    have hS : (S : Set Vec24) = Set.univ := Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
      (by rw [Set.ncard_univ, hV, hm', h]) (Set.toFinite _)
    have hx : x ∈ (S : Set Vec24) := by
      rw [hS]
      exact Set.mem_univ x
    exact hx

theorem full_binary_vector_orbits :
    (∀ v : Vec24, ∃ k : Fin 4, v ∈ gaOrbit (toVecD 24 ([0, 1, 2, 4096].getD k.val 0))) ∧
    (∀ j k : Fin 4, gaOrbit (toVecD 24 ([0, 1, 2, 4096].getD j.val 0)) =
      gaOrbit (toVecD 24 ([0, 1, 2, 4096].getD k.val 0)) → j = k) ∧
    (∀ k : Fin 4, (gaOrbit (toVecD 24 ([0, 1, 2, 4096].getD k.val 0))).ncard =
      [1, 8292375, 98280, 8386560].getD k.val 0) ∧
    (∀ (k : Fin 4) (c : ℕ), c < 2 ^ 24 →
      toVecD 24 c ∈ gaOrbit (toVecD 24 ([0, 1, 2, 4096].getD k.val 0)) →
        [0, 1, 2, 4096].getD k.val 0 ≤ c) ∧
    gaOrbit (toVecD 24 2) = co1X ∧
    (∀ v : Vec24, (gaOrbit v).ncard = 98280 → gaOrbit v = co1X) ∧
    ∀ S : Submodule (ZMod 2) Vec24,
      (∀ g ∈ GA, ∀ v ∈ S, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v ∈ S) →
        S = ⊥ ∨ S = ⊤ := by
  have hX := gaOrbit_two
  refine ⟨fun v => ?_, fun j k h => ?_, fun k => ?_, fun k c hc hck => ?_, hX, fun v hv => ?_,
    fun S hS => invariant_eq hS⟩
  · obtain ⟨k, hk, hvk⟩ := full_orbits_cover v
    exact ⟨⟨k, hk⟩, hvk⟩
  · have hc := congrArg Set.ncard h
    rw [show [0, 1, 2, 4096].getD j.val 0 = Native.fullRoot j.val from rfl,
      show [0, 1, 2, 4096].getD k.val 0 = Native.fullRoot k.val from rfl,
      full_orbits_ncard j.isLt, full_orbits_ncard k.isLt] at hc
    exact Fin.ext (fullSize_inj j.isLt k.isLt hc)
  · exact full_orbits_ncard k.isLt
  · exact full_orbits_least k.isLt hc hck
  · obtain ⟨k, hk, hvk⟩ := full_orbits_cover v
    rw [kOrbit_eq_of_mem hvk] at hv ⊢
    rw [full_orbits_ncard hk] at hv
    have hk2 : k = 2 := fullSize_inj hk (by norm_num) hv
    rw [hk2, ← hX]
    rfl

end CFSG.Sporadic.Co1Schreier
