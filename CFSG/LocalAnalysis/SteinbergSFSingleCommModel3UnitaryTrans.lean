module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherOrthogonality
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherOuterNormalizer

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped Pointwise

variable {m : ℕ} {F' : Type} [Field F']

theorem model3U4_two_le (hF' : UnitaryFieldData 2 m F') : 2 ≤ 2 ^ m := by
  have h1 : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hF'.one_le
  simpa using h1

theorem model3U4_card_group {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) :
    Nat.card (unitarySU p f K 3) = (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := by
  have := h.finite
  have hsymm : (gramForm h (1 : Matrix (Fin 3) (Fin 3) K)).IsSymm :=
    gramForm_isSymm h (by simp [Matrix.map_one])
  have hsep : (gramForm h (1 : Matrix (Fin 3) (Fin 3) K)).SeparatingLeft :=
    gramForm_separatingLeft h (by simp)
  have hSU := (CFSG.LinearGroups.unitary_full_group_order h hsymm hsep
    (Module.finrank_fin_fun K) (by norm_num)).2.1
  rw [unitarySU_eq_gramSU h, card_gramSU]
  have hprod : ∏ i ∈ Finset.Icc 2 3, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) =
      (((p ^ f : ℕ) : ℤ) ^ 2 - 1) * (((p ^ f : ℕ) : ℤ) ^ 3 + 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} by rfl, Finset.prod_pair (by norm_num)]
    ring
  rw [hprod] at hSU
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
  have hq2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ hq
  zify [hq2]
  rw [hSU]
  norm_num
  ring

theorem model3U4_trans (hF' : UnitaryFieldData 2 m F')
    (L M : isotropicLines hF' 3) : ∃ g : unitarySU 2 m F' 3, g • L = M :=
  (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_isotropic_pair_orbits hF'
    (n := 3) (by norm_num)).2.1 L M

theorem model3U4_two_trans (hF' : UnitaryFieldData 2 m F')
    (L M L' M' : isotropicLines hF' 3) (hLM : L ≠ M) (hL'M' : L' ≠ M') :
    ∃ g : unitarySU 2 m F' 3, g • L = L' ∧ g • M = M' := by
  obtain ⟨-, -, h3, h4, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_isotropic_pair_orbits hF'
      (n := 3) (by norm_num)
  have hn : ¬ ∀ x ∈ (L : Submodule F' (Fin 3 → F')), ∀ y ∈ (M : Submodule F' (Fin 3 → F')),
      CFSG.LinearGroups.stdHermForm hF' 3 x y = 0 := h4 rfl L M hLM
  have hn' : ¬ ∀ x ∈ (L' : Submodule F' (Fin 3 → F')), ∀ y ∈ (M' : Submodule F' (Fin 3 → F')),
      CFSG.LinearGroups.stdHermForm hF' 3 x y = 0 := h4 rfl L' M' hL'M'
  exact (h3 L M L' M' hLM hL'M').mpr (iff_of_false hn hn')

theorem model3U4_sub_pos (hF' : UnitaryFieldData 2 m F') : 0 < (2 ^ m) ^ 2 - 1 := by
  have h2 : 2 ^ 2 ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left (model3U4_two_le hF') 2
  have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
  omega

theorem model3U4_not_two_dvd (hF' : UnitaryFieldData 2 m F') : ¬ 2 ∣ (2 ^ m) ^ 2 - 1 := by
  have hm : m ≠ 0 := by have := hF'.one_le; omega
  have h2 : 2 ∣ (2 ^ m) ^ 2 := dvd_pow (dvd_pow_self 2 hm) two_ne_zero
  have hpos : 1 ≤ (2 ^ m) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  omega

theorem model3U4_card_omega (hF' : UnitaryFieldData 2 m F') :
    Nat.card (isotropicLines hF' 3) = (2 ^ m) ^ 3 + 1 := by
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) hF'
  obtain ⟨j, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.exists_transportLines hF' hR
  have hq2 : (2 : ℤ) ≤ (2 : ℤ) ^ m := by exact_mod_cast model3U4_two_le hF'
  have hq4 : (4 : ℤ) ≤ ((2 : ℤ) ^ m) ^ 2 := by nlinarith
  have hz : ((2 : ℤ) ^ m) ^ 2 - 1 ≠ 0 :=
    (by linarith : (0 : ℤ) < ((2 : ℤ) ^ m) ^ 2 - 1).ne'
  have hcard : ((Nat.card (hypIsotropicLines hF' 1 1) : ℕ) : ℤ) * (((2 : ℤ) ^ m) ^ 2 - 1) =
      (((2 : ℤ) ^ m) ^ 3 + 1) * (((2 : ℤ) ^ m) ^ 2 - 1) := by
    have h := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.card_hypLines
      (h := hF') (r := 1) (ε := 1) (by norm_num)
    rw [show (2 * 1 + 1 - 1 : ℕ) = 2 from rfl, show (2 * 1 + 1 : ℕ) = 3 from rfl] at h
    push_cast at h
    linear_combination h
  have hN : ((Nat.card (hypIsotropicLines hF' 1 1) : ℕ) : ℤ) = ((2 : ℤ) ^ m) ^ 3 + 1 :=
    mul_right_cancel₀ hz hcard
  have hN' : Nat.card (hypIsotropicLines hF' 1 1) = (2 ^ m) ^ 3 + 1 := by
    have h' : ((Nat.card (hypIsotropicLines hF' 1 1) : ℕ) : ℤ) =
        (((2 ^ m) ^ 3 + 1 : ℕ) : ℤ) := by
      rw [hN]; push_cast; ring
    exact_mod_cast h'
  exact (Nat.card_congr j).symm.trans hN'

theorem model3U4_ncard_omega (hF' : UnitaryFieldData 2 m F') :
    (isotropicLines hF' 3 : Set (Submodule F' (Fin 3 → F'))).ncard = (2 ^ m) ^ 3 + 1 := by
  rw [← Nat.card_coe_set_eq]
  exact model3U4_card_omega hF'

theorem model3U4_finite_omega (hF' : UnitaryFieldData 2 m F') :
    (isotropicLines hF' 3 : Set (Submodule F' (Fin 3 → F'))).Finite :=
  Set.finite_of_ncard_ne_zero (by rw [model3U4_ncard_omega hF']; exact Nat.succ_ne_zero _)

theorem model3U4_card_group_ne (hF' : UnitaryFieldData 2 m F') :
    Nat.card ↥(unitarySU 2 m F' 3) ≠ 0 := by
  rw [model3U4_card_group hF']
  have h1 : (2 ^ m) ^ 2 - 1 ≠ 0 := (model3U4_sub_pos hF').ne'
  exact mul_ne_zero (mul_ne_zero (by positivity) h1) (Nat.succ_ne_zero _)

theorem model3U4_finite_group (hF' : UnitaryFieldData 2 m F') :
    Finite ↥(unitarySU 2 m F' 3) :=
  Nat.finite_of_card_ne_zero (model3U4_card_group_ne hF')

theorem model3U4_orbit_omega (hF' : UnitaryFieldData 2 m F') {L : Submodule F' (Fin 3 → F')}
    (hL : L ∈ isotropicLines hF' 3) :
    MulAction.orbit ↥(unitarySU 2 m F' 3) L =
      (isotropicLines hF' 3 : Set (Submodule F' (Fin 3 → F'))) := by
  ext N
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact (isotropicLines hF' 3).smul_mem g hL
  · intro hN
    obtain ⟨g, hg⟩ := model3U4_trans hF' ⟨L, hL⟩ ⟨N, hN⟩
    refine ⟨g, ?_⟩
    have h2 := congrArg Subtype.val hg
    rw [SubMulAction.val_smul] at h2
    exact h2

theorem model3U4_card_stab (hF' : UnitaryFieldData 2 m F') {L : Submodule F' (Fin 3 → F')}
    (hL : L ∈ isotropicLines hF' 3) :
    Nat.card (MulAction.stabilizer ↥(unitarySU 2 m F' 3) L) =
      (2 ^ m) ^ 3 * ((2 ^ m) ^ 2 - 1) := by
  have hidx : (MulAction.stabilizer ↥(unitarySU 2 m F' 3) L).index = (2 ^ m) ^ 3 + 1 := by
    rw [MulAction.index_stabilizer, model3U4_orbit_omega hF' hL, model3U4_ncard_omega hF']
  have hcard := Subgroup.card_mul_index (H := MulAction.stabilizer ↥(unitarySU 2 m F' 3) L)
  rw [hidx, model3U4_card_group hF'] at hcard
  exact Nat.eq_of_mul_eq_mul_right (by positivity) hcard

theorem model3U4_orbit_two {L M : Submodule F' (Fin 3 → F')} (hF' : UnitaryFieldData 2 m F')
    (hL : L ∈ isotropicLines hF' 3) (hM : M ∈ isotropicLines hF' 3) (hML : M ≠ L) :
    MulAction.orbit (MulAction.stabilizer ↥(unitarySU 2 m F' 3) L) M =
      (isotropicLines hF' 3 : Set (Submodule F' (Fin 3 → F'))) \ {L} := by
  ext N
  rw [MulAction.mem_orbit_iff, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨(isotropicLines hF' 3).smul_mem (h : ↥(unitarySU 2 m F' 3)) hM,
      fun hEq => hML ?_⟩
    have h1 : (h : ↥(unitarySU 2 m F' 3)) • M = L := hEq
    have h2 : (h : ↥(unitarySU 2 m F' 3))⁻¹ • L = L :=
      MulAction.mem_stabilizer_iff.1 (Subgroup.inv_mem _ h.2)
    calc M = (h : ↥(unitarySU 2 m F' 3))⁻¹ • ((h : ↥(unitarySU 2 m F' 3)) • M) :=
          (inv_smul_smul _ _).symm
      _ = (h : ↥(unitarySU 2 m F' 3))⁻¹ • L := by rw [h1]
      _ = L := h2
  · rintro ⟨hN, hNL⟩
    have hNΩ : N ∈ isotropicLines hF' 3 := hN
    obtain ⟨g, hgL', hgM'⟩ := model3U4_two_trans hF' ⟨L, hL⟩ ⟨M, hM⟩ ⟨L, hL⟩ ⟨N, hNΩ⟩
      (fun h => hML (congrArg Subtype.val h).symm)
      (fun h => hNL (congrArg Subtype.val h).symm)
    have hgL : g • L = L := by
      have h2 := congrArg Subtype.val hgL'
      rw [SubMulAction.val_smul] at h2
      exact h2
    have hgM : g • M = N := by
      have h2 := congrArg Subtype.val hgM'
      rw [SubMulAction.val_smul] at h2
      exact h2
    exact ⟨⟨g, MulAction.mem_stabilizer_iff.2 hgL⟩, hgM⟩

theorem model3U4_ncard_diff (hF' : UnitaryFieldData 2 m F') {L : Submodule F' (Fin 3 → F')}
    (hL : L ∈ isotropicLines hF' 3) :
    ((isotropicLines hF' 3 : Set (Submodule F' (Fin 3 → F'))) \ {L}).ncard = (2 ^ m) ^ 3 := by
  have h := Set.ncard_sdiff_singleton_add_one (SetLike.mem_coe.2 hL)
    (model3U4_finite_omega hF')
  rw [model3U4_ncard_omega hF'] at h
  omega

theorem model3U4_card_two {L M : Submodule F' (Fin 3 → F')} (hF' : UnitaryFieldData 2 m F')
    (hL : L ∈ isotropicLines hF' 3) (hM : M ∈ isotropicLines hF' 3) (hML : M ≠ L) :
    Nat.card (MulAction.stabilizer (MulAction.stabilizer ↥(unitarySU 2 m F' 3) L) M) =
      (2 ^ m) ^ 2 - 1 := by
  have hidx : (MulAction.stabilizer (MulAction.stabilizer ↥(unitarySU 2 m F' 3) L) M).index =
      (2 ^ m) ^ 3 := by
    rw [MulAction.index_stabilizer, model3U4_orbit_two hF' hL hM hML,
      model3U4_ncard_diff hF' hL]
  have hcard := Subgroup.card_mul_index
    (H := MulAction.stabilizer (MulAction.stabilizer ↥(unitarySU 2 m F' 3) L) M)
  rw [hidx, model3U4_card_stab hF' hL] at hcard
  exact Nat.eq_of_mul_eq_mul_right (by positivity) (hcard.trans (Nat.mul_comm _ _))

theorem model3U4_not_two_dvd_cube (hF' : UnitaryFieldData 2 m F') : ¬ 2 ∣ (2 ^ m) ^ 3 + 1 := by
  have hm : m ≠ 0 := by have := hF'.one_le; omega
  have h2 : 2 ∣ (2 ^ m) ^ 3 := dvd_pow (dvd_pow_self 2 hm) (by norm_num)
  omega

theorem model3U4_fac (hF' : UnitaryFieldData 2 m F') :
    Nat.factorization ((2 ^ m) ^ 3 * ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1)) 2 = m * 3 := by
  have hA : (2 ^ m) ^ 2 - 1 ≠ 0 := (model3U4_sub_pos hF').ne'
  have hB : (2 ^ m) ^ 3 + 1 ≠ 0 := Nat.succ_ne_zero _
  have hq : (2 ^ m) ^ 3 ≠ 0 := by positivity
  have hodd : ¬ 2 ∣ ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1) := by
    intro h
    rcases (Nat.prime_two.dvd_mul).1 h with h1 | h1
    · exact model3U4_not_two_dvd hF' h1
    · exact model3U4_not_two_dvd_cube hF' h1
  rw [mul_assoc, Nat.factorization_mul hq (mul_ne_zero hA hB), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hodd, add_zero, ← pow_mul,
    Nat.factorization_pow_self Nat.prime_two]

theorem model3U4_card_sylow (hF' : UnitaryFieldData 2 m F')
    (R : Sylow 2 ↥(unitarySU 2 m F' 3)) :
    Nat.card (R : Subgroup ↥(unitarySU 2 m F' 3)) = (2 ^ m) ^ 3 := by
  haveI := model3U4_finite_group hF'
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Sylow.card_eq_multiplicity R
  rw [model3U4_card_group hF', model3U4_fac hF'] at h1
  refine h1.trans ?_
  rw [← pow_mul]

theorem model3U4_free (hF' : UnitaryFieldData 2 m F') (R : Sylow 2 ↥(unitarySU 2 m F' 3))
    {L M : Submodule F' (Fin 3 → F')} (hL : L ∈ isotropicLines hF' 3)
    (hfix : ∀ g ∈ (R : Subgroup ↥(unitarySU 2 m F' 3)), g • L = L)
    (hM : M ∈ isotropicLines hF' 3) (hML : M ≠ L)
    {x : ↥(unitarySU 2 m F' 3)} (hxR : x ∈ (R : Subgroup ↥(unitarySU 2 m F' 3)))
    (hxM : x • M = M) : x = 1 := by
  haveI := model3U4_finite_group hF'
  have hxH : x ∈ MulAction.stabilizer ↥(unitarySU 2 m F' 3) L :=
    MulAction.mem_stabilizer_iff.2 (hfix x hxR)
  have hyT : (⟨x, hxH⟩ : ↥(MulAction.stabilizer ↥(unitarySU 2 m F' 3) L)) ∈
      MulAction.stabilizer ↥(MulAction.stabilizer ↥(unitarySU 2 m F' 3) L) M :=
    MulAction.mem_stabilizer_iff.2 hxM
  have hA : orderOf x ∣ (2 ^ m) ^ 3 := by
    have h1 := Subgroup.orderOf_dvd_natCard (R : Subgroup ↥(unitarySU 2 m F' 3)) hxR
    rwa [model3U4_card_sylow hF' R] at h1
  have hB : orderOf x ∣ (2 ^ m) ^ 2 - 1 := by
    have h1 := Subgroup.orderOf_dvd_natCard
      (MulAction.stabilizer ↥(MulAction.stabilizer ↥(unitarySU 2 m F' 3) L) M) hyT
    rw [model3U4_card_two hF' hL hM hML] at h1
    rwa [← Subgroup.orderOf_mk x hxH]
  have hcop : Nat.Coprime ((2 ^ m) ^ 3) ((2 ^ m) ^ 2 - 1) :=
    Nat.Coprime.pow_left 3 (Nat.Coprime.pow_left m
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (model3U4_not_two_dvd hF')))
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hA hB)

theorem model3U4_cover (hF' : UnitaryFieldData 2 m F') (R : Sylow 2 ↥(unitarySU 2 m F' 3))
    {L : Submodule F' (Fin 3 → F')} (hL : L ∈ isotropicLines hF' 3)
    (hfix : ∀ g ∈ (R : Subgroup ↥(unitarySU 2 m F' 3)), g • L = L)
    {M M' : Submodule F' (Fin 3 → F')} (hM : M ∈ isotropicLines hF' 3)
    (hM' : M' ∈ isotropicLines hF' 3) (hML : M ≠ L) (hM'L : M' ≠ L) :
    ∃ g ∈ (R : Subgroup ↥(unitarySU 2 m F' 3)), g • M = M' := by
  haveI := model3U4_finite_group hF'
  have hinj : Function.Injective
      (fun g : ↥(R : Subgroup ↥(unitarySU 2 m F' 3)) => (g : ↥(unitarySU 2 m F' 3)) • M) := by
    intro g h hgh
    have hgh' : (g : ↥(unitarySU 2 m F' 3)) • M = (h : ↥(unitarySU 2 m F' 3)) • M := hgh
    have hx : (h : ↥(unitarySU 2 m F' 3))⁻¹ * (g : ↥(unitarySU 2 m F' 3)) ∈
        (R : Subgroup ↥(unitarySU 2 m F' 3)) :=
      mul_mem (Subgroup.inv_mem _ h.2) g.2
    have hxM : ((h : ↥(unitarySU 2 m F' 3))⁻¹ * (g : ↥(unitarySU 2 m F' 3))) • M = M := by
      rw [mul_smul, hgh', inv_smul_smul]
    exact Subtype.ext (inv_mul_eq_one.1 (model3U4_free hF' R hL hfix hM hML hx hxM)).symm
  have hsub : (fun g : ↥(R : Subgroup ↥(unitarySU 2 m F' 3)) => (g : ↥(unitarySU 2 m F' 3)) • M) ''
      Set.univ ⊆ (isotropicLines hF' 3 : Set (Submodule F' (Fin 3 → F'))) \ {L} := by
    rintro _ ⟨g, -, rfl⟩
    rw [Set.mem_diff]
    refine ⟨(isotropicLines hF' 3).smul_mem (g : ↥(unitarySU 2 m F' 3)) hM, fun hgL => hML ?_⟩
    have hgL' : (g : ↥(unitarySU 2 m F' 3)) • M = L := hgL
    have hginv : (g : ↥(unitarySU 2 m F' 3))⁻¹ • L = L := hfix _ (Subgroup.inv_mem _ g.2)
    calc M = (g : ↥(unitarySU 2 m F' 3))⁻¹ • (g : ↥(unitarySU 2 m F' 3)) • M :=
          (inv_smul_smul _ _).symm
      _ = (g : ↥(unitarySU 2 m F' 3))⁻¹ • L := by rw [hgL']
      _ = L := hginv
  have hfin : ((isotropicLines hF' 3 : Set (Submodule F' (Fin 3 → F'))) \ {L}).Finite :=
    (model3U4_finite_omega hF').diff
  have himg : ((fun g : ↥(R : Subgroup ↥(unitarySU 2 m F' 3)) =>
      (g : ↥(unitarySU 2 m F' 3)) • M) '' Set.univ).ncard = (2 ^ m) ^ 3 := by
    rw [Set.ncard_image_of_injective _ hinj, Set.ncard_univ, model3U4_card_sylow hF' R]
  have heq : (fun g : ↥(R : Subgroup ↥(unitarySU 2 m F' 3)) =>
      (g : ↥(unitarySU 2 m F' 3)) • M) '' Set.univ =
      (isotropicLines hF' 3 : Set (Submodule F' (Fin 3 → F'))) \ {L} :=
    Set.eq_of_subset_of_ncard_le hsub
      (le_of_eq (by rw [himg, model3U4_ncard_diff hF' hL])) hfin
  have hmem : M' ∈ (fun g : ↥(R : Subgroup ↥(unitarySU 2 m F' 3)) =>
      (g : ↥(unitarySU 2 m F' 3)) • M) '' Set.univ := by
    rw [heq, Set.mem_diff]
    exact ⟨hM', fun h => hM'L (Set.mem_singleton_iff.1 h)⟩
  obtain ⟨g, -, hg⟩ := hmem
  exact ⟨(g : ↥(unitarySU 2 m F' 3)), g.2, hg⟩

theorem model3_unitary_transitive (hF' : UnitaryFieldData 2 m F')
    (R : Sylow 2 ↥(unitarySU 2 m F' 3)) {L : Submodule F' (Fin 3 → F')}
    (hL : L ∈ isotropicLines hF' 3)
    (hfix : ∀ g ∈ (R : Subgroup ↥(unitarySU 2 m F' 3)), g • L = L)
    {M M' : Submodule F' (Fin 3 → F')} (hM : M ∈ isotropicLines hF' 3)
    (hM' : M' ∈ isotropicLines hF' 3) (hML : M ≠ L) (hM'L : M' ≠ L) :
    ∃ g ∈ (R : Subgroup ↥(unitarySU 2 m F' 3)), g • M = M' := by
  exact model3U4_cover hF' R hL hfix hM hM' hML hM'L

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
