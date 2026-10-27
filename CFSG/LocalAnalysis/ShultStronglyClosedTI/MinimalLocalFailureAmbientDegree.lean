module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureAmbientDegreeOrderFour
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingDihedralSupport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureMixedClass

public section

namespace CFSG.ShultStronglyClosedTI.AmbientDegree

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ShultStronglyClosedTI
open CFSG.ShultStronglyClosedTI.MixedClass
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

theorem order_four_count_arith {az A uH qQ q : ℕ} (hq : 2 ≤ q) (hQ : qQ = q ^ 2)
    (haz : az = A * q) (hinc : A * (qQ - 1) = uH * (q - 1)) : az * (q + 1) = uH * q := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 2 := ⟨q - 2, by omega⟩
  subst hQ haz
  have hsq : (m + 2) ^ 2 - 1 = (m + 1) * (m + 3) := Nat.sub_eq_of_eq_add (by ring)
  rw [hsq, show m + 2 - 1 = m + 1 by omega] at hinc
  have hA : A * (m + 3) = uH := by
    refine Nat.eq_of_mul_eq_mul_left (by omega : 0 < m + 1) ?_
    calc (m + 1) * (A * (m + 3)) = A * ((m + 1) * (m + 3)) := by ring
      _ = uH * (m + 1) := hinc
      _ = (m + 1) * uH := by ring
  rw [← hA]
  ring

theorem central_degree_arith {hH n cz au q d X : ℕ} (hhH : 0 < hH) (hq : 2 ≤ q)
    (hG : hH * n = cz * au) (hcz : cz * (q - 1) = hH) (hau : au = d * (q - 1) * X) :
    n = d * X := by
  refine Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hhH (by omega : 0 < q - 1)) ?_
  calc hH * (q - 1) * n = (hH * n) * (q - 1) := by ring
    _ = (cz * (q - 1)) * au := by rw [hG]; ring
    _ = hH * (q - 1) * (d * X) := by rw [hcz, hau]; ring

theorem noncentral_degree_arith {hH n cz cu au az q d X uH ch : ℕ} (hhH : 0 < hH)
    (hq : 2 ≤ q) (hG : hH * n = cz * au + cu * az) (hcz : cz * (q ^ 2 - 1) = hH)
    (hau : au = d * (q - 1) * X) (hcu : d * ch = cu) (huH : uH * ch = hH)
    (haz : az * (q + 1) = uH * q) : n * (q + 1) = d * (X + q) := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 2 := ⟨q - 2, by omega⟩
  have hsq : (m + 2) ^ 2 - 1 = (m + 1) * (m + 3) := Nat.sub_eq_of_eq_add (by ring)
  rw [hsq] at hcz
  rw [show m + 2 - 1 = m + 1 by omega] at hau
  refine Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hhH (by omega : 0 < m + 1)) ?_
  calc hH * (m + 1) * (n * (m + 2 + 1)) = (hH * n) * ((m + 1) * (m + 3)) := by ring
    _ = (cz * ((m + 1) * (m + 3))) * au + cu * (az * (m + 2 + 1)) * (m + 1) := by
        rw [hG]; ring
    _ = hH * (d * (m + 1) * X) + d * (uH * ch) * (m + 2) * (m + 1) := by
        rw [hcz, haz, hau, ← hcu]; ring
    _ = hH * (m + 1) * (d * (X + (m + 2))) := by rw [huH]; ring

variable {G : Type} [Group G] [Finite G]

theorem minimalLocalFailure_pair_involution_ambient_degree_formulas
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {u : G} (huB : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2) :
    let Q := minimalLocalFailurePairActionPointHull H z
    let Y := Subgroup.centralizer ({u} : Set G)
    let q₀ := Nat.card (Q ⊓ Y : Subgroup G)
    let d := Nat.card {omega : rightCosetSpace H | rightCosetTranslate H omega u = omega}
    let n := Nat.card (rightCosetSpace H)
    let a := InvolutionCounting.thompsonPairCount u z
    4 ≤ q₀ ∧ ∃ i : ℕ, (i = 1 ∨ i = 2 ∨ i = 3) ∧ d = q₀ ^ i + 1 ∧
      (∀ w : G, orderOf w = 2 → ¬ IsConj u w → ¬ IsConj z w → a w = 0) ∧
      a u = (q₀ ^ i + 1) * (q₀ - 1) * (q₀ ^ i * (q₀ - 1) + 1) ∧
      (Q ≤ Y → Nat.card Q = q₀ ∧ a z = 0 ∧ n = (q₀ ^ i + 1) * (q₀ ^ i * (q₀ - 1) + 1)) ∧
      (¬ Q ≤ Y → Nat.card Q = q₀ ^ 2 ∧
        a z * (q₀ + 1) = Nat.card (conjugacyWithin H u) * q₀ ∧
        n * (q₀ + 1) = (q₀ ^ i + 1) * (q₀ ^ i * (q₀ - 1) + q₀ + 1)) := by
  intro Q Y q₀ d n a
  obtain ⟨hUH, -, -, -, -, hzu, hmixed⟩ :=
    minimalLocalFailure_mixed_involution_class_closure h hcomm hsmallerR1 hbeta ht hproper huB hu
  obtain ⟨hQ, -, hQclass, -, -, -, -, -, -, -, -, -, -, -, -, -, heven, hprod⟩ :=
    CyclicPair.proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨hq₀4, -, -, hcent, hnoncent, -, hΔorbit, i, hi, hΔcard, -, hodd, -⟩ :=
    FixedPointModel.involution_centralizer_fixed_point_model h hcomm hsmallerR1 hbeta ht hproper
      huB hu
  have hdatum := h.local_datum
  have hz := hdatum.distinguished_order
  have huH : u ∈ H := pairPointStabilizer_le_point H beta huB
  have heven' : ∀ r s : G, IsConj z r → IsConj z s → Even (orderOf (r * s)) → Commute r s :=
    fun r s hr hs => heven r s (mem_pointClass_iff_isConj.mpr hr) (mem_pointClass_iff_isConj.mpr hs)
  have hprod' : ∀ r s : G, IsConj z r → IsConj z s → r ≠ s → Commute r s → IsConj z (r * s) :=
    fun r s hr hs hne hrs => mem_pointClass_iff_isConj.mp
      (hprod r s (mem_pointClass_iff_isConj.mpr hr) (mem_pointClass_iff_isConj.mpr hs) hne hrs)
  obtain ⟨hvanish, -, hzpairs, hformula⟩ :=
    InvolutionCounting.involution_pair_dihedral_support_and_odd_product_bijection hz hu hzu
      heven' hprod' hmixed
  have hzpairs' := hzpairs z (IsConj.refl z)
  have hau : a u = (q₀ ^ i + 1) * (q₀ - 1) * (q₀ ^ i * (q₀ - 1) + 1) := by
    change InvolutionCounting.thompsonPairCount u z u = _
    rw [InvolutionCounting.thompsonPairCount_eq_card_oddProductPairs hz hu hzu heven' hprod'
      hmixed (IsConj.refl u), ← hodd]
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun p => ?_
    simp only [InvolutionCounting.mem_oddProductPairs, Set.mem_inter_iff,
      mem_pointClass_iff_isConj, SetLike.mem_coe, and_assoc]
  have hCu : d * Nat.card (H ⊓ Y : Subgroup G) = Nat.card Y := by
    change Nat.card {omega : rightCosetSpace H | rightCosetTranslate H omega u = omega} * _ = _
    rw [hΔorbit]
    exact card_base_orbit_mul H Y
  have hCz : Nat.card (Subgroup.centralizer ({z} : Set G)) * (Nat.card Q - 1) = Nat.card H := by
    rw [← card_diff_one, hQclass]
    exact card_centralizer_mul_card_conjugacyWithin (point_centralizer_le hdatum)
  have huHcard : Nat.card (conjugacyWithin H u) * Nat.card (H ⊓ Y : Subgroup G) =
      Nat.card H := by
    have hmul := Subgroup.card_mul_index ((Subgroup.centralizer ({u} : Set G)).subgroupOf H)
    rw [card_subgroupOf_eq, ← conjugacyWithin_card_eq_centralizer_index, inf_comm] at hmul
    rw [mul_comm]
    exact hmul
  have hGn : Nat.card H * n = Nat.card G := by
    change Nat.card H * Nat.card (rightCosetSpace H) = _
    rw [card_rightCosetSpace]
    exact Subgroup.card_mul_index H
  have hH0 : 0 < Nat.card H := Nat.card_pos
  have hd : d = q₀ ^ i + 1 := hΔcard
  have hq₀ : 4 ≤ q₀ := hq₀4
  have hau' : a u = d * (q₀ - 1) * (q₀ ^ i * (q₀ - 1) + 1) := by rw [hd]; exact hau
  refine ⟨hq₀, i, hi, hd, fun w hw hwu hwz => hvanish w hw hwu hwz, hau, ?_, ?_⟩
  · intro hQY
    have haz : a z = 0 := thompsonPairCount_self_eq_zero hdatum hQ hQclass hu hUH hzpairs' hQY
    refine ⟨hcent hQY, haz, ?_⟩
    have hG : Nat.card H * n = Nat.card (Subgroup.centralizer ({z} : Set G)) * a u := by
      rw [hGn, hformula]
      change _ + _ * a z = _
      rw [haz, mul_zero, add_zero]
    have hQq : Nat.card Q = q₀ := hcent hQY
    have hcz : Nat.card (Subgroup.centralizer ({z} : Set G)) * (q₀ - 1) = Nat.card H := by
      rw [← hQq]
      exact hCz
    rw [central_degree_arith hH0 (by omega) hG hcz hau', hd]
  · intro hQY
    have hsq : Nat.card Q = q₀ ^ 2 := hnoncent hQY
    have hazmul := thompsonPairCount_self_eq_mul hdatum hQ hQclass hu huH hUH hzpairs' hsq
    have hinc := card_class_inter_centralizer_mul hQclass (H := H) (u := u)
    have haz : a z * (q₀ + 1) = Nat.card (conjugacyWithin H u) * q₀ :=
      order_four_count_arith (by omega) hsq hazmul hinc
    refine ⟨hsq, haz, ?_⟩
    have hG : Nat.card H * n = Nat.card (Subgroup.centralizer ({z} : Set G)) * a u +
        Nat.card (Subgroup.centralizer ({u} : Set G)) * a z := by
      rw [hGn, hformula]
    have hcz : Nat.card (Subgroup.centralizer ({z} : Set G)) * (q₀ ^ 2 - 1) = Nat.card H := by
      rw [← hsq]
      exact hCz
    rw [noncentral_degree_arith hH0 (by omega) hG hcz hau' hCu huHcard haz, hd]
    congr 1
    omega

end CFSG.ShultStronglyClosedTI.AmbientDegree
