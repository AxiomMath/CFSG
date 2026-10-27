module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixFinBA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixFinBF

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.G6 Equiv

private theorem s1611e3_sixEvenW_sixE6Nat (x : SixE6) :
    sixEvenW (s1611e3_sixE6Nat x) = true := by
  revert x
  decide +kernel

private theorem s1611e3_sixVNat_and (u : SixE6 × SixE6) :
    s1611e3_sixVNat u &&& 63 = s1611e3_sixE6Nat u.1 := by
  rw [s1611e3_sixVNat, show (63 : ℕ) = 2 ^ 6 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod, show (2 : ℕ) ^ 6 = 64 by norm_num,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (s1611e3_sixE6Nat_lt u.1)]

private theorem s1611e3_sixVNat_shift (u : SixE6 × SixE6) :
    s1611e3_sixVNat u >>> 6 = s1611e3_sixE6Nat u.2 := by
  rw [s1611e3_sixVNat, Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 6 = 64 by norm_num,
    Nat.add_mul_div_left _ _ (by norm_num : (0 : ℕ) < 64),
    Nat.div_eq_of_lt (s1611e3_sixE6Nat_lt u.1), zero_add]

theorem s1611e3_sixVNat_mem_sixVecs (u : SixE6 × SixE6) : s1611e3_sixVNat u ∈ sixVecs := by
  rw [sixVecs, List.mem_filter, List.mem_range]
  refine ⟨s1611e3_sixVNat_lt u, ?_⟩
  rw [s1611e3_sixVNat_and u, s1611e3_sixVNat_shift u]
  simp [s1611e3_sixEvenW_sixE6Nat]

private theorem s1611e3_sixVecs_length : sixVecs.length = 1024 := by
  decide +kernel

private theorem s1611e3_sixVecs_nodup : sixVecs.Nodup := by
  rw [sixVecs]
  exact List.Nodup.filter _ List.nodup_range

private theorem s1611e3_six_card : Fintype.card (SixE6 × SixE6) = 1024 := by
  decide +kernel

theorem s1611e3_exists_of_mem_sixVecs {m : Nat} (hm : m ∈ sixVecs) :
    ∃ u : SixE6 × SixE6, s1611e3_sixVNat u = m := by
  have hcard1 : (Finset.univ.image s1611e3_sixVNat).card = 1024 := by
    rw [Finset.card_image_of_injective _ s1611e3_sixVNat_injective, Finset.card_univ,
      s1611e3_six_card]
  have hcard2 : sixVecs.toFinset.card = 1024 := by
    rw [List.toFinset_card_of_nodup s1611e3_sixVecs_nodup, s1611e3_sixVecs_length]
  have hsub : Finset.univ.image s1611e3_sixVNat ⊆ sixVecs.toFinset := by
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨u, -, rfl⟩ := ha
    exact List.mem_toFinset.mpr (s1611e3_sixVNat_mem_sixVecs u)
  have heq : Finset.univ.image s1611e3_sixVNat = sixVecs.toFinset :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard1, hcard2])
  have hm' : m ∈ Finset.univ.image s1611e3_sixVNat := by
    rw [heq]
    exact List.mem_toFinset.mpr hm
  rw [Finset.mem_image] at hm'
  obtain ⟨u, -, hu⟩ := hm'
  exact ⟨u, hu⟩

private theorem s1611e3_sixVNat_one : s1611e3_sixVNat (1 : SixE6 × SixE6) = 0 := by
  simp [s1611e3_sixVNat, s1611e3_sixE6Nat_one]

private theorem s1611e3_sixVNat_diag : s1611e3_sixVNat (sixZ, sixZ) = 4095 := by
  decide +kernel

private theorem s1611e3_sixDiagGen_mul_self : (sixZ, sixZ) * (sixZ, sixZ) = 1 := by
  decide +kernel

private theorem s1611e3_zpow_eq_one_or_self {g : SixE6 × SixE6} (hg : g * g = 1) (n : ℤ) :
    g ^ n = 1 ∨ g ^ n = g := by
  have h2 : g ^ 2 = 1 := by rw [pow_two, hg]
  have hn : g ^ n = g ^ (n % (2 : ℤ)) := zpow_eq_zpow_emod' (x := g) n h2
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left; rw [hn, h]; simp
  · right; rw [hn, h]; simp

private theorem s1611e3_sixDiag_iff (x : SixE6 × SixE6) :
    x ∈ sixDiag ↔ x = 1 ∨ x = (sixZ, sixZ) := by
  rw [sixDiag, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, rfl⟩
    exact s1611e3_zpow_eq_one_or_self s1611e3_sixDiagGen_mul_self n
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

theorem s1611e3_sixKMem_iff {K : Subgroup (SixE6 × SixE6)} {Kb : Bool}
    (hK : (Kb = false ∧ K = ⊥) ∨ (Kb = true ∧ K = sixDiag)) (x : SixE6 × SixE6) :
    sixKMem Kb (s1611e3_sixVNat x) = true ↔ x ∈ K := by
  rcases hK with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [sixKMem, Subgroup.mem_bot, Bool.false_and, Bool.or_false, beq_iff_eq]
    constructor
    · intro h
      exact s1611e3_sixVNat_injective (by rw [h, s1611e3_sixVNat_one])
    · intro h
      rw [h, s1611e3_sixVNat_one]
  · simp only [sixKMem, s1611e3_sixDiag_iff, Bool.true_and, Bool.or_eq_true_iff,
      beq_iff_eq]
    constructor
    · rintro (h | h)
      · left; exact s1611e3_sixVNat_injective (by rw [h, s1611e3_sixVNat_one])
      · right; exact s1611e3_sixVNat_injective (by rw [h, s1611e3_sixVNat_diag])
    · rintro (h | h)
      · left; rw [h, s1611e3_sixVNat_one]
      · right; rw [h, s1611e3_sixVNat_diag]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
