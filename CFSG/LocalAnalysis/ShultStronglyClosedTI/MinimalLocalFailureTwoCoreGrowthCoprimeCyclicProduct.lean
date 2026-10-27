module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthCoprimePrimeActor
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthCoprimeFreeCardinal

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TwoCoreGrowthCoprime

universe u v

theorem coprime_commuting_factors_mem_zpowers_product
    {A : Type v} [Group A] (s t : A) (hst : Commute s t)
    (hcop : Nat.Coprime (orderOf s) (orderOf t)) :
    s ∈ Subgroup.zpowers (s * t) ∧ t ∈ Subgroup.zpowers (s * t) := by
  have htpow : t ^ orderOf s ∈ Subgroup.zpowers (s * t) := by
    have hpower : (s * t) ^ orderOf s = t ^ orderOf s := by
      rw [hst.mul_pow, pow_orderOf_eq_one, one_mul]
    rw [← hpower]
    exact (Subgroup.zpowers (s * t)).pow_mem (Subgroup.mem_zpowers (s * t)) _
  have ht : t ∈ Subgroup.zpowers (s * t) :=
    (Subgroup.zpowers_le.mpr htpow)
      (mem_zpowers_pow_iff.mpr hcop.gcd_eq_one)
  have hs : s ∈ Subgroup.zpowers (s * t) := by
    have hmem := (Subgroup.zpowers (s * t)).mul_mem
      (Subgroup.mem_zpowers (s * t)) ((Subgroup.zpowers (s * t)).inv_mem ht)
    simpa only [mul_inv_cancel_right] using hmem
  exact ⟨hs, ht⟩

theorem coprime_commuting_cyclic_join_data
    {G : Type u} [Group G] [Finite G] (S T : Subgroup G)
    [IsCyclic S] [IsCyclic T]
    (hTS : T ≤ Subgroup.centralizer (S : Set G))
    (hcop : Nat.Coprime (Nat.card S) (Nat.card T)) :
    IsCyclic (S ⊔ T : Subgroup G) ∧
      Nat.card (S ⊔ T : Subgroup G) = Nat.card S * Nat.card T ∧
        ∃ g : G, Subgroup.zpowers g = S ⊔ T ∧ orderOf g = Nat.card S * Nat.card T := by
  obtain ⟨s, hs⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top S).mp inferInstance
  obtain ⟨t, ht⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top T).mp inferInstance
  have hsS : s ∈ S := hs ▸ Subgroup.mem_zpowers s
  have htT : t ∈ T := ht ▸ Subgroup.mem_zpowers t
  have hst : Commute s t := hTS htT s hsS
  have hsorder : orderOf s = Nat.card S := by rw [← hs, Nat.card_zpowers]
  have htorder : orderOf t = Nat.card T := by rw [← ht, Nat.card_zpowers]
  have horder : orderOf (s * t) = Nat.card S * Nat.card T := by
    rw [hst.orderOf_mul_eq_mul_orderOf_of_coprime
      (by simpa only [hsorder, htorder] using hcop), hsorder, htorder]
  have hcard : Nat.card (S ⊔ T : Subgroup G) = Nat.card S * Nat.card T :=
    commuting_disjoint_join_card S T hTS (Subgroup.disjoint_of_coprime_natCard hcop)
  have hgen : Subgroup.zpowers (s * t) = S ⊔ T := by
    apply Subgroup.eq_of_le_of_card_ge
    · simpa only [hs, ht] using Subgroup.zpowers_mul_le_sup s t
    · rw [Nat.card_zpowers, horder, hcard]
  exact ⟨(Subgroup.isCyclic_iff_exists_zpowers_eq_top (S ⊔ T)).mpr ⟨s * t, hgen⟩,
    hcard, s * t, hgen, horder⟩

theorem ambient_odd_actor_quotient_free_of_kernel_dichotomy
    {G : Type u} [Group G] [Finite G] (M Q A : Subgroup G)
    [Subgroup.Normalizes A M] [(Q.subgroupOf M).Normal]
    (hM : IsPGroup 2 M) (hAodd : Odd (Nat.card A))
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G))
    (hInv : ∀ m : G, m ∈ M → orderOf m = 2 → m ∈ Q)
    (hdichotomy : ∀ a : G, a ∈ A → a ≠ 1 →
      (∀ m : G, m ∈ M → m ∈ Q → a * m * a⁻¹ = m → m = 1) ∨
        (∀ m : G, m ∈ M → a * m * a⁻¹ = m → m ∈ Q)) :
    let hQinv := ambient_conjugation_subgroupOf_invariant M Q A hAQ
    letI : MulDistribMulAction A (M ⧸ Q.subgroupOf M) :=
      CFSG.quotientMulDistribMulAction (A := A) (G := M) (Q.subgroupOf M) hQinv
    ∀ a : A, a ≠ 1 → ∀ m : M ⧸ Q.subgroupOf M, a • m = m → m = 1 := by
  let hQinv := ambient_conjugation_subgroupOf_invariant M Q A hAQ
  let : MulDistribMulAction A (M ⧸ Q.subgroupOf M) :=
    CFSG.quotientMulDistribMulAction (A := A) (G := M) (Q.subgroupOf M) hQinv
  change ∀ a : A, a ≠ 1 → ∀ m : M ⧸ Q.subgroupOf M, a • m = m → m = 1
  intro a ha
  apply quotient_element_fixed_eq_one_of_kernel_dichotomy hM hAodd (Q.subgroupOf M)
    hQinv (fun m hm => hInv m m.property (by simpa only [orderOf_submonoid] using hm)) a
  have haG : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
  rcases hdichotomy a a.property haG with hs | hk
  · left
    intro m hm ham
    apply Subtype.ext
    exact hs m m.property hm (by
      simpa only [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
        using congrArg Subtype.val ham)
  · right
    intro m ham
    exact hk m m.property (by
      simpa only [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
        using congrArg Subtype.val ham)

theorem scalar_centralizer_cyclic_product_card_divisor
    {G : Type u} [Group G] [Finite G] (M Q X J : Subgroup G)
    [(Q.subgroupOf M).Normal] [Subgroup.Normalizes X M] [Subgroup.Normalizes J M]
    [IsCyclic X] (hM : IsPGroup 2 M) (hQproper : ¬ M ≤ Q)
    (hInv : ∀ m : G, m ∈ M → orderOf m = 2 → m ∈ Q)
    (hXodd : Odd (Nat.card X)) (hXQ : X ≤ Subgroup.normalizer (Q : Set G))
    (hJQ : J ≤ Subgroup.normalizer (Q : Set G))
    (hJX : J ≤ Subgroup.centralizer (X : Set G)) (hdis : Disjoint X J)
    (hJfixQ : ∀ y : G, y ∈ J → ∀ m : G, m ∈ Q → y * m * y⁻¹ = m)
    (hscalar : ∀ x : G, x ∈ X → x ≠ 1 →
      ∀ m : G, m ∈ M → m ∈ Q → x * m * x⁻¹ = m → m = 1)
    (hJkernel : ∀ y : G, y ∈ J → y ≠ 1 → Odd (orderOf y) →
      ∀ m : G, m ∈ M → y * m * y⁻¹ = m → m ∈ Q)
    (y : G) (hyJ : y ∈ J) (hyOdd : Odd (orderOf y)) :
    IsCyclic (X ⊔ Subgroup.zpowers y : Subgroup G) ∧
      Nat.card (X ⊔ Subgroup.zpowers y : Subgroup G) = orderOf y * Nat.card X ∧
        orderOf y * Nat.card X ∣ Nat.card (M ⧸ Q.subgroupOf M) - 1 := by
  let T := Subgroup.zpowers y
  let E := X ⊔ T
  have hTJ : T ≤ J := Subgroup.zpowers_le.mpr hyJ
  have hTX : T ≤ Subgroup.centralizer (X : Set G) := hTJ.trans hJX
  have hcopXJ : Nat.Coprime (Nat.card X) (Nat.card J) :=
    scalar_centralizer_orders_coprime M Q X J hM hQproper hInv hXodd hXQ hJQ hJX hdis
      hJfixQ hscalar hJkernel
  have hcopXT : Nat.Coprime (Nat.card X) (Nat.card T) :=
    hcopXJ.of_dvd_right (Subgroup.card_dvd_of_le hTJ)
  obtain ⟨hEcyc, hEcard, g, hg, hgorder⟩ := coprime_commuting_cyclic_join_data X T hTX hcopXT
  have hEM : E ≤ Subgroup.normalizer (M : Set G) :=
    sup_le (Subgroup.Normalizes.le_normalizer (A := X) (K := M))
      (hTJ.trans (Subgroup.Normalizes.le_normalizer (A := J) (K := M)))
  let : Subgroup.Normalizes E M := ⟨hEM⟩
  have hEQ : E ≤ Subgroup.normalizer (Q : Set G) := sup_le hXQ (hTJ.trans hJQ)
  have hEodd : Odd (Nat.card E) := by
    rw [hEcard, Nat.card_zpowers]
    exact hXodd.mul hyOdd
  have hdichotomy : ∀ a : G, a ∈ E → a ≠ 1 →
      (∀ m : G, m ∈ M → m ∈ Q → a * m * a⁻¹ = m → m = 1) ∨
        (∀ m : G, m ∈ M → a * m * a⁻¹ = m → m ∈ Q) := by
    intro a ha hane
    obtain ⟨s, hs, t, ht, hst⟩ := (commuting_join_mem_iff X T hTX a).mp ha
    by_cases hsone : s = 1
    · have hate : a = t := by simpa only [hsone, one_mul] using hst.symm
      right
      apply hJkernel a (hate ▸ hTJ ht) hane
      have horder : orderOf a ∣ orderOf y := by
        simpa only [hate] using orderOf_dvd_of_mem_zpowers ht
      exact Odd.of_dvd_nat hyOdd horder
    · left
      intro m hm hQm ham
      have htm := hJfixQ t (hTJ ht) m hQm
      have hsm : s * m * s⁻¹ = m := by
        calc
          s * m * s⁻¹ = s * (t * m * t⁻¹) * s⁻¹ := by rw [htm]
          _ = (s * t) * m * (s * t)⁻¹ := by group
          _ = m := by rw [hst]; exact ham
      exact hscalar s hs hsone m hm hQm hsm
  let hQinv := ambient_conjugation_subgroupOf_invariant M Q E hEQ
  let : MulDistribMulAction E (M ⧸ Q.subgroupOf M) :=
    CFSG.quotientMulDistribMulAction (A := E) (G := M) (Q.subgroupOf M) hQinv
  have hfree := ambient_odd_actor_quotient_free_of_kernel_dichotomy M Q E hM hEodd
    hEQ hInv hdichotomy
  have hdiv := actor_card_dvd_card_sub_one_of_free hfree
  have hcard : Nat.card E = orderOf y * Nat.card X := by
    simpa only [E, T, Nat.card_zpowers, mul_comm] using hEcard
  exact ⟨hEcyc, hcard, by simpa only [hcard] using hdiv⟩

end CFSG.ShultStronglyClosedTI.TwoCoreGrowthCoprime
